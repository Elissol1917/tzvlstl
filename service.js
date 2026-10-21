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
  domains: ['youtube.com', 'youtu.be', 'youtube-nocookie.com', 'googlevideo.com', 'ytimg.com', 'ggpht.com',
    'googleapis.com', 'gstatic.com', 'google.com', 'googleusercontent.com'],
  upstreamDns: ['8.8.8.8', '1.1.1.1']
};
var status = { dns: 'starting', https: 'starting', http: 'starting', proxy: 'starting', setup: 'starting', vpn: 'not configured', saved: '-' };
var handles = [];
var started = false;

function log() {
  try { if (typeof console !== 'undefined') console.log.apply(console, ['[tizenvless]'].concat([].slice.call(arguments))); } catch (e) {}
}
function merge(a, b) { for (var k in b) { if (Object.prototype.hasOwnProperty.call(b, k)) a[k] = b[k]; } return a; }

// ---- Buffer helpers (work on old Node too) ----
function bAlloc(n) { if (Buffer.alloc) return Buffer.alloc(n); var b = new Buffer(n); b.fill(0); return b; }
function bFromArr(a) { return (Buffer.from && Buffer.from !== Uint8Array.from) ? Buffer.from(a) : new Buffer(a); }
function bFromStr(s, enc) { return (Buffer.from && Buffer.from !== Uint8Array.from) ? Buffer.from(s, enc) : new Buffer(s, enc); }

// ---- config ----
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
      '<p>Диагностика (ok = порт занят успешно):</p><pre>' + JSON.stringify(status, null, 1) + '</pre>' +
      '<form method="POST" action="/save"><p>Вставьте ссылку vless:// (ws + tls):</p>' +
      '<textarea name="link" rows="6" style="width:100%"></textarea><p><button style="font-size:20px;padding:8px 20px">Сохранить</button></p></form>';
  }
  var srv = http.createServer(function (req, res) {
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
  });
  srv.on('error', function (e) { status.setup = e.code || e.message; log('setup error:', e.message); });
  srv.listen(cfg.setupPort || 8090, '0.0.0.0', function () { status.setup = 'ok'; log('setup page on port ' + (cfg.setupPort || 8090)); });
  handles.push(srv);
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

function startSni(port, kind) {
  var key = kind === 'tls' ? 'https' : 'http';
  var srv = net.createServer(function (client) {
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
      if (!host) { client.destroy(); return; }
      log(kind, host);
      tunnel(host, kind === 'tls' ? 443 : 80, client, buf, null);
    }
    client.on('data', onData);
  });
  srv.on('error', function (e) { status[key] = e.code || e.message; log(key + ' bind error:', e.message); });
  srv.listen(port, '127.0.0.1', function () { status[key] = 'ok'; log(key + ' listening on ' + port); });
  handles.push(srv);
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
          var ans = bFromArr([0xC0, 0x0C, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 127, 0, 0, 1]);
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
  sock.bind(cfg.dnsPort || 53, '127.0.0.1', function () { status.dns = 'ok'; log('dns listening on ' + (cfg.dnsPort || 53)); });
  handles.push(sock);
}

// ---- lifecycle ----
function safe(name, fn) { try { fn(); } catch (e) { log(name + ' failed:', e.message); if (status[name] === 'starting') status[name] = 'error: ' + e.message; } }

function start() {
  if (started) return;
  started = true;
  safe('config', loadCfg);
  safe('proxy', startProxy);
  safe('setup', startSetup);
  safe('dns', startDns);
  safe('https', function () { startSni(cfg.httpsPort || 443, 'tls'); });
  safe('http', function () { startSni(cfg.httpPort || 80, 'http'); });
}

function stop() {
  for (var i = 0; i < handles.length; i++) { try { handles[i].close(); } catch (e) {} }
  handles = [];
  started = false;
}

if (typeof module !== 'undefined' && module && module.exports) {
  module.exports.onStart = start;
  module.exports.onStop = stop;
}
if (!ENV.TV_VLESS_NOAUTOSTART) start();
