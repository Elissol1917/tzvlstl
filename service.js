'use strict';
// Local HTTP/CONNECT proxy -> VLESS over WebSocket (optionally TLS).
// Only Node built-ins, no npm dependencies.
const net = require('net');
const tls = require('tls');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');

let cfg = null;
let server = null;

function log() {
  try { console.log.apply(console, ['[tizenvless]'].concat([].slice.call(arguments))); } catch (e) {}
}

function secretPaths() {
  if (process.env.TV_VLESS_SECRET) return [process.env.TV_VLESS_SECRET];
  return [path.join(__dirname, 'vpn.json'), path.join(require('os').tmpdir(), 'tizenvless-vpn.json')];
}

function loadCfg() {
  const p = process.env.TV_VLESS_CONFIG || path.join(__dirname, 'config.json');
  cfg = JSON.parse(fs.readFileSync(p, 'utf8'));
  const ps = secretPaths();
  for (let i = 0; i < ps.length; i++) {
    try {
      Object.assign(cfg, JSON.parse(fs.readFileSync(ps[i], 'utf8')));
      status.saved = ps[i];
      break;
    } catch (e) {}
  }
  status.vpn = (cfg.server && cfg.uuid) ? 'configured' : 'not configured';
}

function saveVpn(v) {
  Object.assign(cfg, v);
  const ps = secretPaths();
  let saved = null;
  for (let i = 0; i < ps.length && !saved; i++) {
    try { fs.writeFileSync(ps[i], JSON.stringify(v)); saved = ps[i]; } catch (e) {}
  }
  status.saved = saved || 'memory only (re-enter after restart)';
  status.vpn = 'configured';
}

function parseVless(link) {
  const m = String(link || '').trim().match(/^vless:\/\/([0-9a-fA-F-]{32,36})@([^:\/?#]+):(\d+)\/?(?:\?([^#]*))?(?:#.*)?$/);
  if (!m) return { error: 'Не похоже на ссылку vless://UUID@сервер:порт?...' };
  const q = require('querystring').parse(m[4] || '');
  const type = q.type || 'tcp';
  const sec = q.security || 'none';
  if (sec === 'reality') return { error: 'Reality не поддерживается. Нужен транспорт ws (WebSocket) с tls.' };
  if (type !== 'ws') return { error: 'Поддерживается только type=ws (WebSocket). В ссылке: type=' + type };
  return { cfg: {
    server: m[2], port: parseInt(m[3], 10), uuid: m[1],
    tls: sec === 'tls', sni: q.sni || q.host || m[2], host: q.host || m[2],
    path: q.path || '/', allowInsecure: q.allowInsecure === '1' || q.allowInsecure === 'true'
  } };
}

// ---------- WebSocket (client side, minimal) ----------
function wsFrame(op, data) {
  const len = data.length;
  let head;
  if (len < 126) { head = Buffer.alloc(2); head[1] = 0x80 | len; }
  else if (len < 65536) { head = Buffer.alloc(4); head[1] = 0x80 | 126; head.writeUInt16BE(len, 2); }
  else { head = Buffer.alloc(10); head[1] = 0x80 | 127; head.writeUInt32BE(0, 2); head.writeUInt32BE(len, 6); }
  head[0] = 0x80 | op;
  const mask = crypto.randomBytes(4);
  const out = Buffer.alloc(len);
  for (let i = 0; i < len; i++) out[i] = data[i] ^ mask[i & 3];
  return Buffer.concat([head, mask, out]);
}

function wsConnect(onOpen, onMessage, onClose) {
  if (!cfg.server || !cfg.uuid) { log('VPN not configured'); setTimeout(onClose, 0); return; }
  const key = crypto.randomBytes(16).toString('base64');
  const opts = { host: cfg.serverIp || cfg.server, port: cfg.port };
  let sock;
  if (cfg.tls) {
    opts.servername = cfg.sni || cfg.server;
    opts.rejectUnauthorized = !cfg.allowInsecure;
    sock = tls.connect(opts);
  } else {
    sock = net.connect(opts);
  }
  let buf = Buffer.alloc(0);
  let upgraded = false;
  let closed = false;
  const api = {
    send: function (d) { if (!closed) sock.write(wsFrame(0x2, d)); },
    close: function () { if (!closed) { closed = true; try { sock.destroy(); } catch (e) {} } }
  };
  function fail() { const was = closed; api.close(); if (!was) onClose(); }

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
      const op = buf[0] & 0x0f;
      let len = buf[1] & 0x7f;
      let off = 2;
      if (len === 126) { if (buf.length < 4) return; len = buf.readUInt16BE(2); off = 4; }
      else if (len === 127) { if (buf.length < 10) return; len = buf.readUInt32BE(2) * 4294967296 + buf.readUInt32BE(6); off = 10; }
      const masked = (buf[1] & 0x80) !== 0;
      let mask = null;
      if (masked) { if (buf.length < off + 4) return; mask = buf.slice(off, off + 4); off += 4; }
      if (buf.length < off + len) return;
      let payload = buf.slice(off, off + len);
      if (masked) { const p = Buffer.alloc(len); for (let i = 0; i < len; i++) p[i] = payload[i] ^ mask[i & 3]; payload = p; }
      buf = buf.slice(off + len);
      if (op === 0x8) { fail(); return; }
      else if (op === 0x9) { sock.write(wsFrame(0xA, payload)); }
      else if (op === 0x0 || op === 0x1 || op === 0x2) { onMessage(payload); }
    }
  }

  sock.on('data', function (chunk) {
    buf = Buffer.concat([buf, chunk]);
    if (!upgraded) {
      const i = buf.indexOf('\r\n\r\n');
      if (i < 0) return;
      const head = buf.slice(0, i).toString();
      if (!/^HTTP\/1\.[01] 101/.test(head)) { log('ws handshake failed:', head.split('\r\n')[0]); fail(); return; }
      upgraded = true;
      buf = buf.slice(i + 4);
      onOpen(api);
    }
    parse();
  });
}

// ---------- VLESS ----------
function vlessHeader(host, port) {
  const uuid = Buffer.from(cfg.uuid.replace(/-/g, ''), 'hex');
  let atype, addr;
  if (net.isIPv4(host)) { atype = 1; addr = Buffer.from(host.split('.').map(Number)); }
  else { atype = 2; const h = Buffer.from(host); addr = Buffer.concat([Buffer.from([h.length]), h]); }
  const p = Buffer.alloc(2); p.writeUInt16BE(port, 0);
  // version, uuid, addons len, command (1=tcp), port, addr type, addr
  return Buffer.concat([Buffer.from([0]), uuid, Buffer.from([0, 1]), p, Buffer.from([atype]), addr]);
}

function tunnel(host, port, client, first, onReady) {
  let gotResp = false;
  let pend = Buffer.alloc(0);
  client.pause();
  wsConnect(function (ws) {
    const hdr = vlessHeader(host, port);
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
      const need = 2 + pend[1];
      if (pend.length < need) return;
      msg = pend.slice(need);
      gotResp = true;
      pend = null;
      if (!msg.length) return;
    }
    if (!client.destroyed) client.write(msg);
  }, function () { client.destroy(); });
}

// ---------- local proxy ----------
function startProxy() {
  server = net.createServer(function (client) {
    client.on('error', function () {});
    client.once('data', function (chunk) {
      const s = chunk.toString('latin1');
      const lineEnd = s.indexOf('\r\n');
      const m = s.slice(0, lineEnd).match(/^(\w+) (\S+) HTTP\/(1\.[01])/);
      if (!m) { client.destroy(); return; }
      if (m[1] === 'CONNECT') {
        const i = m[2].lastIndexOf(':');
        const host = i > 0 ? m[2].slice(0, i) : m[2];
        const port = i > 0 ? parseInt(m[2].slice(i + 1), 10) : 443;
        const he = chunk.indexOf('\r\n\r\n');
        const rest = he >= 0 ? chunk.slice(he + 4) : Buffer.alloc(0);
        log('CONNECT', host + ':' + port);
        tunnel(host, port, client, rest, function () {
          client.write('HTTP/1.1 200 Connection Established\r\n\r\n');
        });
      } else if (m[2].charAt(0) === '/') {
        const body = JSON.stringify(status);
        client.end('HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nAccess-Control-Allow-Origin: *\r\nConnection: close\r\nContent-Length: ' + Buffer.byteLength(body) + '\r\n\r\n' + body);
      } else {
        let u;
        try { u = new URL(m[2]); } catch (e) { client.destroy(); return; }
        const port = parseInt(u.port || '80', 10);
        const line = m[1] + ' ' + (u.pathname || '/') + u.search + ' HTTP/' + m[3];
        const rest = Buffer.from(line + s.slice(lineEnd), 'latin1');
        log(m[1], u.hostname + ':' + port);
        tunnel(u.hostname, port, client, rest, null);
      }
    });
  });
  server.on('error', function (e) { status.proxy = e.code || e.message; log('proxy error:', e.message); });
  server.listen(cfg.listen || 8080, '127.0.0.1', function () {
    status.proxy = 'ok';
    log('listening on 127.0.0.1:' + (cfg.listen || 8080));
  });
}


// ---------- status ----------
var status = { dns: 'starting', https: 'starting', http: 'starting', proxy: 'starting', setup: 'starting', vpn: 'not configured', saved: '-' };

function matches(name) {
  if (name === cfg.server || name === cfg.sni || name === cfg.host) return false;
  const d = cfg.domains || [];
  for (let i = 0; i < d.length; i++) {
    if (d[i] === '*') return true;
    if (name === d[i] || name.endsWith('.' + d[i])) return true;
  }
  return false;
}

// ---------- SNI / Host proxies ----------
function parseSNI(buf) {
  // returns hostname, null (no SNI / not TLS) or undefined (need more data)
  if (buf.length < 5 || buf[0] !== 0x16) return buf.length >= 1 ? null : undefined;
  const recLen = buf.readUInt16BE(3);
  if (buf.length < 5 + recLen) return undefined;
  try {
    let p = 5 + 4 + 2 + 32;
    p += 1 + buf[p];
    p += 2 + buf.readUInt16BE(p);
    p += 1 + buf[p];
    const extEnd = p + 2 + buf.readUInt16BE(p);
    p += 2;
    while (p + 4 <= extEnd && p + 4 <= buf.length) {
      const t = buf.readUInt16BE(p), l = buf.readUInt16BE(p + 2);
      p += 4;
      if (t === 0) { const nl = buf.readUInt16BE(p + 3); return buf.slice(p + 5, p + 5 + nl).toString(); }
      p += l;
    }
  } catch (e) {}
  return null;
}

function startSni(port, kind) {
  const key = kind === 'tls' ? 'https' : 'http';
  const srv = net.createServer(function (client) {
    client.on('error', function () {});
    let buf = Buffer.alloc(0);
    function onData(chunk) {
      buf = Buffer.concat([buf, chunk]);
      let host = null;
      if (kind === 'tls') {
        const r = parseSNI(buf);
        if (r === undefined && buf.length < 16384) return;
        host = r;
      } else {
        const he = buf.indexOf('\r\n\r\n');
        if (he < 0 && buf.length < 16384) return;
        const mm = buf.toString('latin1').match(/\r\nHost:\s*([^\r\n:]+)/i);
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
}

// ---------- DNS ----------
function startDns() {
  const dgram = require('dgram');
  const sock = dgram.createSocket('udp4');
  sock.on('error', function (e) { status.dns = e.code || e.message; log('dns error:', e.message); });
  sock.on('message', function (msg, rinfo) {
    try {
      if (msg.length < 17) return;
      let p = 12;
      const labels = [];
      while (msg[p] !== 0) {
        if (msg[p] >= 0xC0 || p >= msg.length) return;
        labels.push(msg.slice(p + 1, p + 1 + msg[p]).toString());
        p += 1 + msg[p];
      }
      const qEnd = p + 1 + 4;
      if (qEnd > msg.length) return;
      const qtype = msg.readUInt16BE(p + 1);
      const name = labels.join('.').toLowerCase();
      if (matches(name)) {
        const hdr = Buffer.alloc(12);
        msg.copy(hdr, 0, 0, 2);
        hdr.writeUInt16BE(0x8180, 2);
        hdr.writeUInt16BE(1, 4);
        const q = msg.slice(12, qEnd);
        if (qtype === 1) {
          hdr.writeUInt16BE(1, 6);
          const ans = Buffer.from([0xC0, 0x0C, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 127, 0, 0, 1]);
          sock.send(Buffer.concat([hdr, q, ans]), rinfo.port, rinfo.address);
        } else {
          sock.send(Buffer.concat([hdr, q]), rinfo.port, rinfo.address); // AAAA/HTTPS: empty answer -> IPv4 only
        }
        return;
      }
      const ups = cfg.upstreamDns || ['8.8.8.8'];
      const f = dgram.createSocket('udp4');
      const t = setTimeout(function () { try { f.close(); } catch (e) {} }, 4000);
      f.on('message', function (r) { clearTimeout(t); sock.send(r, rinfo.port, rinfo.address); try { f.close(); } catch (e) {} });
      f.on('error', function () { clearTimeout(t); try { f.close(); } catch (e) {} });
      ups.forEach(function (u) {
        const a = String(u).split(':');
        f.send(msg, parseInt(a[1] || '53', 10), a[0], function () {});
      });
    } catch (e) { log('dns handler error:', e.message); }
  });
  sock.bind(cfg.dnsPort || 53, '127.0.0.1', function () { status.dns = 'ok'; log('dns listening on ' + (cfg.dnsPort || 53)); });
}


// ---------- setup page (paste vless:// link from phone) ----------
function startSetup() {
  const http = require('http');
  const qs = require('querystring');
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
  const srv = http.createServer(function (req, res) {
    if (req.method === 'POST' && req.url === '/save') {
      let body = '';
      req.on('data', function (d) { body += d; if (body.length > 8192) req.destroy(); });
      req.on('end', function () {
        const r = parseVless(qs.parse(body).link);
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
}

module.exports.onStart = function () {
  try {
    loadCfg();
    startProxy();
    startSetup();
    startDns();
    startSni(cfg.httpsPort || 443, 'tls');
    startSni(cfg.httpPort || 80, 'http');
  } catch (e) { log('start failed:', e.message); }
};
module.exports.onStop = function () {
  try { if (server) server.close(); } catch (e) {}
};

if (require.main === module) module.exports.onStart();
