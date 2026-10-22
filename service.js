'use strict';
// TizenVLESS service. Written for TizenBrew's service sandbox:
// single file, no __dirname, old Node (ES5 style), starts itself on load.
var net = require('net');
var tls = require('tls');
var dgram = require('dgram');
var http = require('http');
var crypto = require('crypto');
var fs = require('fs');
var os = require('os');
var qs = require('querystring');
var urlmod = require('url');
var Buffer = require('buffer').Buffer;
var timers = require('timers');
var setTimeout = timers.setTimeout;
var clearTimeout = timers.clearTimeout;

var ENV = (typeof process !== 'undefined' && process.env) ? process.env : {};
var DIRNAME = (typeof __dirname !== 'undefined') ? __dirname : null;

var cfg = {
  server: '', serverIp: '', port: 443, uuid: '', tls: true, sni: '', host: '', path: '/', allowInsecure: false,
  listen: 8080, setupPort: 8090, dnsPort: 53, httpsPort: 443, httpPort: 80,
  lan: false, privileged: false, bindIp: '127.0.0.1', answerIp: '127.0.0.1',
  webPort: 8095, sniPort: 8443, upstreamInsecure: false,
  domains: ['youtube.com', 'youtu.be', 'youtube-nocookie.com', 'googlevideo.com', 'ytimg.com', 'ggpht.com',
    'googleapis.com', 'gstatic.com', 'google.com', 'googleusercontent.com'],
  upstreamDns: ['8.8.8.8', '1.1.1.1']
};
var status = { version: '0.3.4', web: 'starting', relay: 'starting', dns: 'off', https: 'off', http: 'off', setup: 'starting', vpn: 'not configured', saved: '-', mode: 'local', answerIp: '127.0.0.1', lanIps: [] };
var handles = [];
var started = false;
// Ports actually bound (may differ from cfg.* if the preferred one was busy).
var VERSION = '0.3.4';
var ports = { setup: 0, relay: 0, web: 0 };
var PORT_TRIES = 30;

var logbuf = [];
function log() {
  var args = [].slice.call(arguments);
  try {
    var t = new Date().toISOString().slice(11, 19);
    logbuf.push(t + ' ' + args.map(function (a) { return String(a); }).join(' '));
    if (logbuf.length > 300) logbuf.shift();
  } catch (e) {}
  try { if (typeof console !== 'undefined') console.log.apply(console, ['[tizenvless]'].concat(args)); } catch (e) {}
}
function merge(a, b) { for (var k in b) { if (Object.prototype.hasOwnProperty.call(b, k)) a[k] = b[k]; } return a; }

// Listen on `base`; if the port is busy (EADDRINUSE/EACCES) try base+1, base+2, ... up to PORT_TRIES.
// A fresh server is created for every attempt (make() returns it), so a failed listen leaves no state behind.
// onBound(port, server) on success, onFail(err) when every port is taken or on any other error.
function listenScan(make, base, host, label, onBound, onFail) {
  var tries = 0;
  function attempt(port) {
    var srv = make();
    var settled = false;
    srv.once('error', function (e) {
      if (settled) return;
      settled = true;
      try { srv.close(); } catch (x) {}
      var txt = String((e && (e.code || e.errno)) || '') + ' ' + String((e && e.message) || '');
      if (/EADDRINUSE|EACCES|address already in use/i.test(txt) && tries < PORT_TRIES && port < 65535) {
        log(label + ': port ' + port + ' busy (' + txt.trim() + '), trying ' + (port + 1));
        tries++;
        attempt(port + 1);
      } else {
        onFail(e, port);
      }
    });
    srv.listen(port, host, function () {
      settled = true;
      srv.on('error', function (e) { log(label + ' runtime error:', e.message); });
      handles.push(srv);
      onBound(port, srv);
    });
  }
  attempt(base);
}

// ---- Buffer helpers (work on old Node too) ----
function bAlloc(n) { if (Buffer.alloc) return Buffer.alloc(n); var b = new Buffer(n); b.fill(0); return b; }
function bFromArr(a) { return (Buffer.from && Buffer.from !== Uint8Array.from) ? Buffer.from(a) : new Buffer(a); }
function bFromStr(s, enc) { return (Buffer.from && Buffer.from !== Uint8Array.from) ? Buffer.from(s, enc) : new Buffer(s, enc); }

// ---- config ----
function lanIps() {
  var out = [], nets;
  try { nets = os.networkInterfaces(); } catch (e) { return out; }
  for (var name in nets) {
    for (var i = 0; i < nets[name].length; i++) {
      var a = nets[name][i];
      if ((a.family === 'IPv4' || a.family === 4) && !a.internal) out.push(a.address);
    }
  }
  return out;
}
function pickLanIp(list) {
  for (var i = 0; i < list.length; i++) { if (/^(192\.168\.|10\.|172\.(1[6-9]|2\d|3[01])\.)/.test(list[i])) return list[i]; }
  return list[0] || null;
}
function secretPaths() {
  if (ENV.TV_VLESS_SECRET) return [ENV.TV_VLESS_SECRET];
  var list = [];
  if (DIRNAME) list.push(DIRNAME + '/vpn.json');
  try { list.push(os.tmpdir() + '/tizenvless-vpn.json'); } catch (e) {}
  if (ENV.HOME) list.push(ENV.HOME + '/tizenvless-vpn.json');
  return list;
}

function loadCfg() {
  if (ENV.TV_VLESS_CONFIG) {
    try { merge(cfg, JSON.parse(fs.readFileSync(ENV.TV_VLESS_CONFIG, 'utf8'))); } catch (e) { log('config error:', e.message); }
  }
  var ps = secretPaths();
  for (var i = 0; i < ps.length; i++) {
    try { merge(cfg, JSON.parse(fs.readFileSync(ps[i], 'utf8'))); status.saved = ps[i]; break; } catch (e) {}
  }
  status.vpn = (cfg.server && cfg.uuid) ? 'configured' : 'not configured';
  if (cfg.lan || ENV.TV_VLESS_LAN) {
    cfg.lan = true;
    cfg.bindIp = '0.0.0.0';
    status.lanIps = lanIps();
    var ip = ENV.TV_VLESS_IP || ((cfg.answerIp && cfg.answerIp !== '127.0.0.1') ? cfg.answerIp : pickLanIp(status.lanIps));
    cfg.answerIp = ip || '127.0.0.1';
    status.mode = 'LAN (на компьютере)';
  }
  status.answerIp = cfg.answerIp;
}

function saveVpn(v) {
  merge(cfg, v);
  var ps = secretPaths();
  var saved = null;
  for (var i = 0; i < ps.length && !saved; i++) {
    try { fs.writeFileSync(ps[i], JSON.stringify(v)); saved = ps[i]; } catch (e) {}
  }
  status.saved = saved || 'memory only (re-enter after restart)';
  status.vpn = 'configured';
}

function parseVless(link) {
  var m = String(link || '').trim().match(/^vless:\/\/([0-9a-fA-F-]{32,36})@([^:\/?#]+):(\d+)\/?(?:\?([^#]*))?(?:#.*)?$/);
  if (!m) return { error: 'Не похоже на ссылку vless://UUID@сервер:порт?...' };
  var q = qs.parse(m[4] || '');
  var type = q.type || 'tcp';
  var sec = q.security || 'none';
  if (sec === 'reality') return { error: 'Reality не поддерживается. Нужен транспорт ws (WebSocket) с tls.' };
  if (type !== 'ws') return { error: 'Поддерживается только type=ws (WebSocket). В ссылке: type=' + type };
  return { cfg: {
    server: m[2], port: parseInt(m[3], 10), uuid: m[1],
    tls: sec === 'tls', sni: q.sni || q.host || m[2], host: q.host || m[2],
    path: q.path || '/', allowInsecure: q.allowInsecure === '1' || q.allowInsecure === 'true'
  } };
}

function matches(name) {
  if (name === cfg.server || name === cfg.sni || name === cfg.host) return false;
  var d = cfg.domains || [];
  for (var i = 0; i < d.length; i++) {
    if (d[i] === '*') return true;
    if (name === d[i] || name.slice(-(d[i].length + 1)) === '.' + d[i]) return true;
  }
  return false;
}

// ---- WebSocket client (minimal) ----
function wsFrame(op, data) {
  var len = data.length;
  var head;
  if (len < 126) { head = bAlloc(2); head[1] = 0x80 | len; }
  else if (len < 65536) { head = bAlloc(4); head[1] = 0x80 | 126; head.writeUInt16BE(len, 2); }
  else { head = bAlloc(10); head[1] = 0x80 | 127; head.writeUInt32BE(0, 2); head.writeUInt32BE(len, 6); }
  head[0] = 0x80 | op;
  var mask = crypto.randomBytes(4);
  var out = bAlloc(len);
  for (var i = 0; i < len; i++) out[i] = data[i] ^ mask[i & 3];
  return Buffer.concat([head, mask, out]);
}

function wsConnect(onOpen, onMessage, onClose) {
  if (!cfg.server || !cfg.uuid) { log('VPN not configured'); setTimeout(onClose, 0); return; }
  var key = crypto.randomBytes(16).toString('base64');
  var opts = { host: cfg.serverIp || cfg.server, port: cfg.port };
  var sock;
  if (cfg.tls) {
    opts.servername = cfg.sni || cfg.server;
    opts.rejectUnauthorized = !cfg.allowInsecure;
    sock = tls.connect(opts);
  } else {
    sock = net.connect(opts);
  }
  var buf = bAlloc(0);
  var upgraded = false;
  var closed = false;
  var api = {
    send: function (d) { if (!closed) sock.write(wsFrame(0x2, d)); },
    close: function () { if (!closed) { closed = true; try { sock.destroy(); } catch (e) {} } }
  };
  function fail() { var was = closed; api.close(); if (!was) onClose(); }

  sock.on(cfg.tls ? 'secureConnect' : 'connect', function () {
    sock.write('GET ' + cfg.path + ' HTTP/1.1\r\n' +
      'Host: ' + (cfg.host || cfg.server) + '\r\n' +
      'Upgrade: websocket\r\nConnection: Upgrade\r\n' +
      'Sec-WebSocket-Key: ' + key + '\r\nSec-WebSocket-Version: 13\r\n' +
      'User-Agent: Mozilla/5.0\r\n\r\n');
  });
  sock.on('error', function (e) { log('socket error:', e.message); fail(); });
  sock.on('close', fail);

  function parse() {
    while (buf.length >= 2) {
      var op = buf[0] & 0x0f;
      var len = buf[1] & 0x7f;
      var off = 2;
      if (len === 126) { if (buf.length < 4) return; len = buf.readUInt16BE(2); off = 4; }
      else if (len === 127) { if (buf.length < 10) return; len = buf.readUInt32BE(2) * 4294967296 + buf.readUInt32BE(6); off = 10; }
      var masked = (buf[1] & 0x80) !== 0;
      var mask = null;
      if (masked) { if (buf.length < off + 4) return; mask = buf.slice(off, off + 4); off += 4; }
      if (buf.length < off + len) return;
      var payload = buf.slice(off, off + len);
      if (masked) { var p = bAlloc(len); for (var i = 0; i < len; i++) p[i] = payload[i] ^ mask[i & 3]; payload = p; }
      buf = buf.slice(off + len);
      if (op === 0x8) { fail(); return; }
      else if (op === 0x9) { sock.write(wsFrame(0xA, payload)); }
      else if (op === 0x0 || op === 0x1 || op === 0x2) { onMessage(payload); }
    }
  }

  sock.on('data', function (chunk) {
    buf = Buffer.concat([buf, chunk]);
    if (!upgraded) {
      var i = buf.indexOf('\r\n\r\n');
      if (i < 0) return;
      var head = buf.slice(0, i).toString();
      if (!/^HTTP\/1\.[01] 101/.test(head)) { log('ws handshake failed:', head.split('\r\n')[0]); fail(); return; }
      upgraded = true;
      buf = buf.slice(i + 4);
      onOpen(api);
    }
    parse();
  });
}

// ---- VLESS ----
function vlessHeader() {
  var host = arguments[0], port = arguments[1];
  var uuid = bFromStr(cfg.uuid.replace(/-/g, ''), 'hex');
  var atype, addr;
  if (net.isIPv4(host)) { atype = 1; addr = bFromArr(host.split('.').map(Number)); }
  else { atype = 2; var h = bFromStr(host, 'utf8'); addr = Buffer.concat([bFromArr([h.length]), h]); }
  var p = bAlloc(2); p.writeUInt16BE(port, 0);
  return Buffer.concat([bFromArr([0]), uuid, bFromArr([0, 1]), p, bFromArr([atype]), addr]);
}

function tunnel(host, port, client, first, onReady) {
  var gotResp = false;
  var pend = bAlloc(0);
  client.pause();
  wsConnect(function (ws) {
    var hdr = vlessHeader(host, port);
    ws.send(first && first.length ? Buffer.concat([hdr, first]) : hdr);
    if (onReady) onReady();
    client.on('data', function (d) { ws.send(d); });
    client.on('close', function () { ws.close(); });
    client.on('error', function () { ws.close(); });
    client.resume();
  }, function (msg) {
    if (!gotResp) {
      pend = Buffer.concat([pend, msg]);
      if (pend.length < 2) return;
      var need = 2 + pend[1];
      if (pend.length < need) return;
      msg = pend.slice(need);
      gotResp = true;
      pend = null;
      if (!msg.length) return;
    }
    if (!client.destroyed) client.write(msg);
  }, function () { client.destroy(); });
}

// ---- local HTTP/CONNECT proxy (+ JSON status) ----
function startProxy() {
  var server = net.createServer(function (client) {
    client.on('error', function () {});
    client.once('data', function (chunk) {
      var s = chunk.toString('binary');
      var lineEnd = s.indexOf('\r\n');
      var m = s.slice(0, lineEnd).match(/^(\w+) (\S+) HTTP\/(1\.[01])/);
      if (!m) { client.destroy(); return; }
      if (m[1] === 'CONNECT') {
        var i = m[2].lastIndexOf(':');
        var host = i > 0 ? m[2].slice(0, i) : m[2];
        var port = i > 0 ? parseInt(m[2].slice(i + 1), 10) : 443;
        var he = chunk.indexOf('\r\n\r\n');
        var rest = he >= 0 ? chunk.slice(he + 4) : bAlloc(0);
        log('CONNECT', host + ':' + port);
        tunnel(host, port, client, rest, function () {
          client.write('HTTP/1.1 200 Connection Established\r\n\r\n');
        });
      } else if (m[2].charAt(0) === '/') {
        var body = JSON.stringify(status);
        client.end('HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nAccess-Control-Allow-Origin: *\r\nConnection: close\r\nContent-Length: ' + Buffer.byteLength(body) + '\r\n\r\n' + body);
      } else {
        var u = urlmod.parse(m[2]);
        if (!u.hostname) { client.destroy(); return; }
        var p2 = parseInt(u.port || '80', 10);
        var line = m[1] + ' ' + (u.path || '/') + ' HTTP/' + m[3];
        var rest2 = bFromStr(line + s.slice(lineEnd), 'binary');
        log(m[1], u.hostname + ':' + p2);
        tunnel(u.hostname, p2, client, rest2, null);
      }
    });
  });
  server.on('error', function (e) { status.proxy = e.code || e.message; log('proxy error:', e.message); });
  server.listen(cfg.listen || 8080, '127.0.0.1', function () { status.proxy = 'ok'; log('proxy on 127.0.0.1:' + (cfg.listen || 8080)); });
  handles.push(server);
}

// ---- phone setup page ----
function startSetup() {
  function send(res, code, body) {
    res.writeHead(code, { 'Content-Type': 'text/html; charset=utf-8' });
    res.end('<!doctype html><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">' +
      '<body style="font:18px sans-serif;max-width:560px;margin:20px auto;padding:0 12px">' + body + '</body>');
  }
  function form(msg) {
    return '<h2>TizenVLESS</h2>' + (msg ? '<p><b>' + msg + '</b></p>' : '') +
      '<p>VPN: ' + status.vpn + '<br>Хранится: ' + status.saved + '</p>' +
      (cfg.lan ? '<p><b>DNS для телевизора: ' + status.answerIp + '</b><br>Все адреса этого ПК: ' + status.lanIps.join(', ') + '</p>' : '') +
      '<p><a href="/log">Журнал службы (/log)</a></p><p>Диагностика (ok = порт занят успешно):</p><pre>' + JSON.stringify(status, null, 1) + '</pre>' +
      '<form method="POST" action="/save"><p>Вставьте ссылку vless:// (ws + tls):</p>' +
      '<textarea name="link" rows="6" style="width:100%"></textarea><p><button style="font-size:20px;padding:8px 20px">Сохранить</button></p></form>';
  }
  function handler(req, res) {
    if (req.url === '/ping') { res.writeHead(200, { 'Access-Control-Allow-Origin': '*' }); res.end('ok'); return; }
    if (req.url === '/log') { res.writeHead(200, { 'Content-Type': 'text/plain; charset=utf-8', 'Access-Control-Allow-Origin': '*' }); res.end(logbuf.join('\n') || '(пусто)'); return; }
    if (req.url === '/status.json') { res.writeHead(200, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' }); res.end(JSON.stringify(status)); return; }
    if (req.method === 'POST' && req.url === '/save') {
      var body = '';
      req.on('data', function (d) { body += d; if (body.length > 8192) req.destroy(); });
      req.on('end', function () {
        var r = parseVless(qs.parse(body).link);
        if (r.error) { send(res, 400, form('Ошибка: ' + r.error)); return; }
        saveVpn(r.cfg);
        log('vpn config saved');
        send(res, 200, form('Сохранено. Сервер принят, перезапуск не нужен.'));
      });
      return;
    }
    send(res, 200, form(''));
  }
  listenScan(function () { return http.createServer(handler); }, cfg.setupPort || 8090, '0.0.0.0', 'setup', function (port) {
    ports.setup = port;
    status.setupPort = port;
    status.setup = 'ok';
    log('setup page on port ' + port);
  }, function (e) { status.setup = e.code || e.message; log('setup error:', e.message); });
}

// ---- SNI / Host proxies on 443 / 80 ----
function parseSNI(buf) {
  // hostname | null (not TLS / no SNI) | undefined (need more data)
  if (buf.length < 5 || buf[0] !== 0x16) return buf.length >= 1 ? null : undefined;
  var recLen = buf.readUInt16BE(3);
  if (buf.length < 5 + recLen) return undefined;
  try {
    var p = 5 + 4 + 2 + 32;
    p += 1 + buf[p];
    p += 2 + buf.readUInt16BE(p);
    p += 1 + buf[p];
    var extEnd = p + 2 + buf.readUInt16BE(p);
    p += 2;
    while (p + 4 <= extEnd && p + 4 <= buf.length) {
      var t = buf.readUInt16BE(p), l = buf.readUInt16BE(p + 2);
      p += 4;
      if (t === 0) { var nl = buf.readUInt16BE(p + 3); return buf.slice(p + 5, p + 5 + nl).toString(); }
      p += l;
    }
  } catch (e) {}
  return null;
}

// scan=true: walk up from `port` if it is busy and report the bound port via onBound(port).
// scan=false (443/80 for the DNS trick): the exact port or nothing.
function startSni(port, kind, bindAddr, keyName, scan, onBound, onDone) {
  var key = keyName || (kind === 'tls' ? 'https' : 'http');
  function conn(client) {
    client.on('error', function () {});
    var buf = bAlloc(0);
    function onData(chunk) {
      buf = Buffer.concat([buf, chunk]);
      var host = null;
      if (kind === 'tls') {
        var r = parseSNI(buf);
        if (r === undefined && buf.length < 16384) return;
        host = r;
      } else {
        var he = buf.indexOf('\r\n\r\n');
        if (he < 0 && buf.length < 16384) return;
        var mm = buf.toString('binary').match(/\r\nHost:\s*([^\r\n:]+)/i);
        host = mm ? mm[1].trim() : null;
      }
      client.removeListener('data', onData);
      if (!host || !matches(String(host).toLowerCase())) { log('blocked', host); client.destroy(); return; }
      log(kind, host);
      tunnel(host, kind === 'tls' ? 443 : 80, client, buf, null);
    }
    client.on('data', onData);
  }
  var host = bindAddr || cfg.bindIp || '127.0.0.1';
  function bound(p) {
    status[key] = 'ok';
    if (scan) status[key + 'Port'] = p;
    log(key + ' listening on ' + p);
    if (onBound) onBound(p);
    if (onDone) onDone();
  }
  function failed(e) {
    status[key] = e.code || e.message;
    log(key + ' bind error:', e.message);
    if (onDone) onDone();
  }
  if (scan) {
    listenScan(function () { return net.createServer(conn); }, port, host, key, bound, failed);
  } else {
    // exact port: same machinery with a single try
    var srv = net.createServer(conn);
    srv.on('error', failed);
    srv.listen(port, host, function () { bound(port); });
    handles.push(srv);
  }
}

// ---- DNS on 53 ----
function startDns() {
  var sock = dgram.createSocket('udp4');
  sock.on('error', function (e) { status.dns = e.code || e.message; log('dns error:', e.message); });
  sock.on('message', function (msg, rinfo) {
    try {
      if (msg.length < 17) return;
      var p = 12;
      var labels = [];
      while (msg[p] !== 0) {
        if (msg[p] >= 0xC0 || p >= msg.length) return;
        labels.push(msg.slice(p + 1, p + 1 + msg[p]).toString());
        p += 1 + msg[p];
      }
      var qEnd = p + 1 + 4;
      if (qEnd > msg.length) return;
      var qtype = msg.readUInt16BE(p + 1);
      var name = labels.join('.').toLowerCase();
      if (matches(name)) {
        var hdr = bAlloc(12);
        msg.copy(hdr, 0, 0, 2);
        hdr.writeUInt16BE(0x8180, 2);
        hdr.writeUInt16BE(1, 4);
        var q = msg.slice(12, qEnd);
        if (qtype === 1) {
          hdr.writeUInt16BE(1, 6);
          var ipb = String(cfg.answerIp || '127.0.0.1').split('.');
          var ans = bFromArr([0xC0, 0x0C, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, +ipb[0], +ipb[1], +ipb[2], +ipb[3]]);
          sock.send(Buffer.concat([hdr, q, ans]), 0, 12 + q.length + 16, rinfo.port, rinfo.address);
        } else {
          sock.send(Buffer.concat([hdr, q]), 0, 12 + q.length, rinfo.port, rinfo.address);
        }
        return;
      }
      var ups = cfg.upstreamDns || ['8.8.8.8'];
      var f = dgram.createSocket('udp4');
      var t = setTimeout(function () { try { f.close(); } catch (e) {} }, 4000);
      f.on('message', function (r) { clearTimeout(t); sock.send(r, 0, r.length, rinfo.port, rinfo.address); try { f.close(); } catch (e) {} });
      f.on('error', function () { clearTimeout(t); try { f.close(); } catch (e) {} });
      for (var i = 0; i < ups.length; i++) {
        var a = String(ups[i]).split(':');
        f.send(msg, 0, msg.length, parseInt(a[1] || '53', 10), a[0], function () {});
      }
    } catch (e) { log('dns handler error:', e.message); }
  });
  sock.bind(cfg.dnsPort || 53, cfg.bindIp || '127.0.0.1', function () { status.dns = 'ok'; log('dns listening on ' + (cfg.dnsPort || 53)); });
  handles.push(sock);
}


// ---- web proxy for YouTube TV (no privileged ports needed) ----
// Page is opened from http://127.0.0.1:<webPort>/tv ; this server fetches the real site over HTTPS
// through the local SNI relay -> VLESS, and rewrites absolute URLs so every request comes back here.
var https = require('https');
var zlib = require('zlib');
var agents = {};
var wcache = {};
var wcacheKeys = [];
var HOP = { 'connection': 1, 'keep-alive': 1, 'proxy-authenticate': 1, 'proxy-authorization': 1, 'te': 1, 'trailer': 1, 'transfer-encoding': 1, 'upgrade': 1 };
var TEXT_RE = /(text\/html|javascript|json|text\/css|xml|text\/plain)/i;

function agentFor(host) {
  if (!agents[host]) agents[host] = new https.Agent({ keepAlive: true, maxSockets: 8 });
  return agents[host];
}

function rewriteText(s, hostport) {
  return s.replace(/(https?:)?(\\?\/\\?\/)((?:[a-zA-Z0-9-]+\.)+[a-zA-Z]{2,})/g, function (all, proto, sep, host) {
    if (!matches(host.toLowerCase())) return all;
    var sl = sep.length > 2 ? '\\/' : '/';
    return (proto ? 'http:' : '') + sep + hostport + sl + '__h' + sl + host;
  });
}

function toUpstream(u, base) {
  if (u.indexOf(base) !== 0) return u;
  var rest = u.slice(base.length);
  var m = rest.match(/^\/__h\/([^\/?#]+)(.*)$/);
  if (m) return 'https://' + m[1] + (m[2] || '/');
  return 'https://www.youtube.com' + rest;
}

function fixLocation(loc, host, hostport) {
  if (/^\/(?!\/)/.test(loc) && host !== 'www.youtube.com') return '/__h/' + host + loc;
  return rewriteText(loc, hostport);
}

function fixCookie(c) {
  return String(c).replace(/;\s*domain=[^;]*/ig, '').replace(/;\s*secure/ig, '').replace(/;\s*samesite=[^;]*/ig, '');
}

var CLIENT_PATCH = '(function(){try{' +
  'var DOMS=__DOMS__,B=location.protocol+"//"+location.host;' +
  'function ok(h){h=String(h).toLowerCase();for(var i=0;i<DOMS.length;i++){var d=DOMS[i];if(h===d||h.slice(-d.length-1)==="."+d)return true;}return false;}' +
  'function rw(u){if(typeof u!=="string")return u;var m=u.match(/^(?:https?:)?\\/\\/([^\\/?#:]+)(?::\\d+)?([\\s\\S]*)$/i);' +
  'if(m&&ok(m[1])){var r=m[2]||"/";if(r.charAt(0)!=="/")r="/"+r;return B+"/__h/"+m[1].toLowerCase()+r;}return u;}' +
  'function rwt(s){return String(s).replace(/(https?:)?\\/\\/((?:[a-zA-Z0-9-]+\\.)+[a-zA-Z]{2,})/g,function(a,p,h){return ok(h)?B+"/__h/"+h.toLowerCase():a;});}' +
  'var of=window.fetch;if(of){window.fetch=function(i,n){if(typeof i==="string"){i=rw(i);}' +
  'else if(i&&typeof i.url==="string"){var nu=rw(i.url);if(nu!==i.url){i=new Request(nu,i);}}' +
  'else if(i&&typeof i.href==="string"){i=rw(i.href);}return of.call(this,i,n);};}' +
  'var xo=XMLHttpRequest.prototype.open;XMLHttpRequest.prototype.open=function(){var a=[].slice.call(arguments);a[1]=rw(String(a[1]));return xo.apply(this,a);};' +
  'function pp(proto,prop){try{var d=Object.getOwnPropertyDescriptor(proto,prop);if(!d||!d.set)return;' +
  'Object.defineProperty(proto,prop,{configurable:true,enumerable:d.enumerable,get:d.get,set:function(v){d.set.call(this,rw(String(v)));}});}catch(e){}}' +
  'pp(HTMLImageElement.prototype,"src");pp(HTMLScriptElement.prototype,"src");pp(HTMLLinkElement.prototype,"href");' +
  'pp(HTMLIFrameElement.prototype,"src");pp(HTMLSourceElement.prototype,"src");pp(HTMLMediaElement.prototype,"src");' +
  'var sa=Element.prototype.setAttribute;Element.prototype.setAttribute=function(n,v){if((n==="src"||n==="href"||n==="poster")&&typeof v==="string")v=rw(v);return sa.call(this,n,v);};' +
  'try{var cs=CSSStyleDeclaration.prototype;["backgroundImage","background"].forEach(function(p){var d=Object.getOwnPropertyDescriptor(cs,p);' +
  'if(d&&d.set){Object.defineProperty(cs,p,{configurable:true,enumerable:d.enumerable,get:d.get,set:function(v){d.set.call(this,rwt(v));}});}});' +
  'var sp=cs.setProperty;cs.setProperty=function(n,v,pr){if(/background|image/i.test(n)&&typeof v==="string")v=rwt(v);return sp.call(this,n,v,pr);};}catch(e){}' +
  'if(navigator.sendBeacon){var sb=navigator.sendBeacon;navigator.sendBeacon=function(u,d){return sb.call(navigator,rw(String(u)),d);};}' +
  '}catch(e){}})();';

function fixHtml(body) {
  body = body.replace(/<meta[^>]+http-equiv=["']?content-security-policy["']?[^>]*>/ig, '')
             .replace(/\sintegrity=("[^"]*"|'[^']*')/ig, '');
  var inj = '<script>' + CLIENT_PATCH.replace('__DOMS__', JSON.stringify(cfg.domains || [])) + '</script>';
  if (/<head[^>]*>/i.test(body)) return body.replace(/<head[^>]*>/i, function (m) { return m + inj; });
  return inj + body;
}

function webError(res, code, msg) {
  if (res.headersSent) { try { res.end(); } catch (e) {} return; }
  res.writeHead(code, { 'Content-Type': 'text/html; charset=utf-8' });
  res.end('<meta charset="utf-8"><body style="font:28px sans-serif;background:#12203a;color:#fff;padding:40px">' + msg + '</body>');
}

function handleWeb(req, res) {
  var hostport = req.headers.host || ('127.0.0.1:' + (ports.web || cfg.webPort || 8095));
  var base = 'http://' + hostport;
  if (!cfg.server || !cfg.uuid) { webError(res, 503, '<h2>VPN не настроен</h2><p>Откройте на телефоне http://IP_ТВ:' + (ports.setup || cfg.setupPort || 8090) + ' и вставьте ссылку vless://</p>'); return; }
  var host = 'www.youtube.com';
  var path = req.url;
  var m = req.url.match(/^\/__h\/([^\/?#]+)(.*)$/);
  if (m) { host = m[1].toLowerCase(); path = m[2] || '/'; if (path.charAt(0) !== '/') path = '/' + path; }
  else if (req.url === '/' || req.url === '') { res.writeHead(302, { Location: '/tv' }); res.end(); return; }
  if (!matches(host)) { webError(res, 403, 'blocked: ' + host); return; }

  var h = {};
  for (var k in req.headers) { if (HOP[k] || k === 'host' || k === 'accept-encoding') continue; h[k] = req.headers[k]; }
  h.host = host;
  h['accept-encoding'] = 'identity';
  if (h.origin) h.origin = toUpstream(h.origin, base);
  if (h.referer) h.referer = toUpstream(h.referer, base);

  var ckey = (req.method === 'GET' && /^\/(s|yts)\//.test(path)) ? host + path : null;
  if (ckey && wcache[ckey]) {
    var c = wcache[ckey];
    res.writeHead(c.status, c.headers);
    res.end(c.body);
    return;
  }

  var up = https.request({
    host: '127.0.0.1', port: ports.relay || cfg.sniPort || 8443, servername: host, method: req.method, path: path,
    headers: h, agent: agentFor(host), rejectUnauthorized: !cfg.upstreamInsecure
  }, function (ur) {
    log('web', req.method, ur.statusCode, host + path.slice(0, 70));
    var rh = {};
    for (var k2 in ur.headers) { if (!HOP[k2]) rh[k2] = ur.headers[k2]; }
    delete rh['content-security-policy']; delete rh['content-security-policy-report-only'];
    delete rh['x-frame-options']; delete rh['strict-transport-security']; delete rh['alt-svc'];
    delete rh['report-to']; delete rh['nel'];
    if (rh.location) rh.location = fixLocation(rh.location, host, hostport);
    if (rh['set-cookie']) rh['set-cookie'] = [].concat(rh['set-cookie']).map(fixCookie);
    var ct = String(ur.headers['content-type'] || '');
    var enc = String(ur.headers['content-encoding'] || '').toLowerCase();
    var plainEnc = (!enc || enc === 'identity' || enc === 'gzip' || enc === 'deflate');
    if (!TEXT_RE.test(ct) || !plainEnc || ur.statusCode === 206 || ur.statusCode === 204 || ur.statusCode === 304) {
      res.writeHead(ur.statusCode, rh);
      ur.pipe(res);
      return;
    }
    var src = ur;
    if (enc === 'gzip') src = ur.pipe(zlib.createGunzip());
    else if (enc === 'deflate') src = ur.pipe(zlib.createInflate());
    var chunks = [];
    src.on('data', function (d) { chunks.push(d); });
    src.on('error', function () { webError(res, 502, 'decode error'); });
    src.on('end', function () {
      var text = Buffer.concat(chunks).toString('utf8');
      try {
        if (ur.statusCode >= 400) log('web BODY', ur.statusCode, path.slice(0, 40), text.slice(0, 400).replace(/\s+/g, ' '));
        if (/^\/youtubei\/v1\/player/.test(path)) {
          var ps = text.match(/"playabilityStatus"\s*:\s*\{\s*"status"\s*:\s*"([A-Z_]+)"(?:[^}]*?"reason"\s*:\s*"([^"]*)")?/);
          log('web PLAYER', ps ? ps[1] + (ps[2] ? ' | ' + ps[2] : '') : 'no playabilityStatus', '| streamingData=' + (/"streamingData"/.test(text) ? 'yes' : 'no'), '| len=' + text.length);
        }
      } catch (e) {}
      text = rewriteText(text, hostport);
      if (/text\/html/i.test(ct)) text = fixHtml(text);
      var out = bFromStr(text, 'utf8');
      delete rh['content-encoding']; delete rh['content-length'];
      rh['content-length'] = out.length;
      res.writeHead(ur.statusCode, rh);
      res.end(out);
      if (ckey && ur.statusCode === 200 && out.length < 6 * 1024 * 1024) {
        wcache[ckey] = { status: 200, headers: rh, body: out };
        wcacheKeys.push(ckey);
        if (wcacheKeys.length > 30) delete wcache[wcacheKeys.shift()];
      }
    });
  });
  up.setTimeout(45000, function () { up.abort(); });
  up.on('error', function (e) { log('web upstream error:', host, e.message); webError(res, 502, 'Нет связи с ' + host + ' через VPN: ' + e.message); });
  res.on('close', function () { try { up.abort(); } catch (e) {} });
  if (req.method === 'POST' && /^\/o\/oauth2\/device\/code/.test(path)) {
    var rb = '';
    req.on('data', function (d) { if (rb.length < 400) rb += d.toString('utf8'); });
    req.on('end', function () { log('web REQBODY device/code', rb.slice(0, 400)); });
  }
  req.pipe(up);
}

function startWeb() {
  listenScan(function () { return http.createServer(handleWeb); }, cfg.webPort || 8095, '127.0.0.1', 'web', function (port) {
    ports.web = port;
    status.webPort = port;
    status.web = 'ok';
    log('web proxy on 127.0.0.1:' + port);
  }, function (e) { status.web = e.code || e.message; log('web error:', e.message); });
}

// ---- lifecycle ----
function safe(name, fn) { try { fn(); } catch (e) { log(name + ' failed:', e.message); if (status[name] === 'starting') status[name] = 'error: ' + e.message; } }

function start() {
  if (started) return;
  started = true;
  safe('config', loadCfg);
  safe('setup', startSetup);
  // Relay goes first: web needs to know which port the relay really got.
  var webStarted = false;
  function webOnce() { if (webStarted) return; webStarted = true; safe('web', startWeb); }
  try {
    startSni(cfg.sniPort || 8443, 'tls', '127.0.0.1', 'relay', true, function (p) { ports.relay = p; }, webOnce);
  } catch (e) {
    status.relay = 'error: ' + e.message;
    log('relay failed:', e.message);
    webOnce();
  }
  if (cfg.lan || cfg.privileged) {
    safe('dns', startDns);
    safe('https', function () { startSni(cfg.httpsPort || 443, 'tls', null, null, false); });
    safe('http', function () { startSni(cfg.httpPort || 80, 'http', null, null, false); });
  }
}

function stop() {
  for (var i = 0; i < handles.length; i++) { try { handles[i].close(); } catch (e) {} }
  handles = [];
  ports = { setup: 0, relay: 0, web: 0 };
  started = false;
}

if (typeof module !== 'undefined' && module && module.exports) {
  module.exports.onStart = start;
  module.exports.onStop = stop;
}
if (!ENV.TV_VLESS_NOAUTOSTART) start();
