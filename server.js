'use strict';
/*
  Glowmoor multiplayer server.
  No dependencies: plain Node (18+). Serves the game page and a WebSocket endpoint at /ws.
  Players join a room with /?room=NAME (default "public"). Each room holds up to MAX_PLAYERS.
  The server only relays presence (position, facing, name) and which doors are open.
  The world itself is generated in each browser from a fixed seed, so it is identical for everyone.
*/
const http = require('http');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');

const PORT = parseInt(process.env.PORT, 10) || 3000;
const MAX_PLAYERS = parseInt(process.env.MAX_PLAYERS, 10) || 16;
const MAX_ROOMS = parseInt(process.env.MAX_ROOMS, 10) || 200;
const TICK_MS = 100;
const GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
const WORLD_LIMIT = 700;
const MAX_DOOR_INDEX = 4000;

const INDEX_PATH = path.join(__dirname, 'public', 'index.html');
let indexCache = null;
function loadIndex() {
  if (!indexCache) indexCache = fs.readFileSync(INDEX_PATH);
  return indexCache;
}

/* ---------- rooms ---------- */
const rooms = new Map();
let nextId = 1;

function cleanRoomName(raw) {
  const n = String(raw || 'public').replace(/[^\w-]/g, '').slice(0, 24);
  return n || 'public';
}
function cleanName(raw, id) {
  const n = String(raw || '').replace(/[\u0000-\u001f\u007f<>]/g, '').trim().slice(0, 16);
  return n || 'Walker ' + id;
}
function getRoom(name) {
  let r = rooms.get(name);
  if (!r) {
    if (rooms.size >= MAX_ROOMS) return null;
    r = { name, players: new Map(), doors: new Set(), dirty: false };
    rooms.set(name, r);
  }
  return r;
}
function num(v, lim) {
  v = Number(v);
  if (!Number.isFinite(v)) return null;
  return Math.max(-lim, Math.min(lim, v));
}
function r2(v) { return Math.round(v * 100) / 100; }

/* ---------- minimal WebSocket (RFC 6455) ---------- */
function encodeFrame(opcode, payload) {
  const len = payload.length;
  let head;
  if (len < 126) {
    head = Buffer.from([0x80 | opcode, len]);
  } else if (len < 65536) {
    head = Buffer.alloc(4);
    head[0] = 0x80 | opcode; head[1] = 126; head.writeUInt16BE(len, 2);
  } else {
    head = Buffer.alloc(10);
    head[0] = 0x80 | opcode; head[1] = 127; head.writeBigUInt64BE(BigInt(len), 2);
  }
  return Buffer.concat([head, payload]);
}

class Client {
  constructor(socket, room, name) {
    this.socket = socket;
    this.room = room;
    this.id = nextId++;
    this.name = cleanName(name, this.id);
    this.hue = (this.id * 67) % 360;
    this.x = 0; this.y = 0; this.z = 6; this.yaw = 0;
    this.buf = Buffer.alloc(0);
    this.frag = null;
    this.alive = true;
    this.lastPong = Date.now();
    this.lastPos = 0;
    this.closed = false;

    socket.on('data', (d) => this.onData(d));
    socket.on('close', () => this.cleanup());
    socket.on('error', () => this.cleanup());
    socket.setTimeout(0);
  }

  sendRaw(buf) {
    if (this.closed || this.socket.destroyed) return;
    if (this.socket.writableLength > 1e6) { this.close(1013); return; }
    this.socket.write(buf);
  }
  send(obj) { this.sendRaw(encodeFrame(0x1, Buffer.from(JSON.stringify(obj)))); }
  ping() { this.sendRaw(encodeFrame(0x9, Buffer.alloc(0))); }
  close(code) {
    if (this.closed) return;
    const p = Buffer.alloc(2); p.writeUInt16BE(code || 1000, 0);
    try { this.socket.write(encodeFrame(0x8, p)); } catch (e) { /* socket already gone */ }
    this.socket.end();
    setTimeout(() => { if (!this.socket.destroyed) this.socket.destroy(); }, 1000).unref();
    this.cleanup();
  }

  onData(chunk) {
    this.buf = Buffer.concat([this.buf, chunk]);
    if (this.buf.length > 70000) { this.close(1009); return; }
    for (;;) {
      const b = this.buf;
      if (b.length < 2) return;
      const fin = (b[0] & 0x80) !== 0;
      const op = b[0] & 0x0f;
      const masked = (b[1] & 0x80) !== 0;
      let len = b[1] & 0x7f;
      let off = 2;
      if (len === 126) {
        if (b.length < 4) return;
        len = b.readUInt16BE(2); off = 4;
      } else if (len === 127) {
        if (b.length < 10) return;
        const big = b.readBigUInt64BE(2);
        if (big > 65536n) { this.close(1009); return; }
        len = Number(big); off = 10;
      }
      if (!masked) { this.close(1002); return; }
      if (b.length < off + 4 + len) return;
      const mask = b.subarray(off, off + 4);
      const data = Buffer.from(b.subarray(off + 4, off + 4 + len));
      for (let i = 0; i < data.length; i++) data[i] ^= mask[i & 3];
      this.buf = b.subarray(off + 4 + len);
      this.onFrame(fin, op, data);
      if (this.closed) return;
    }
  }

  onFrame(fin, op, data) {
    if (op === 0x8) { this.close(1000); return; }
    if (op === 0x9) { this.sendRaw(encodeFrame(0xA, data)); return; }
    if (op === 0xA) { this.lastPong = Date.now(); return; }
    if (op === 0x1 || op === 0x0) {
      if (op === 0x1) this.frag = [];
      if (!this.frag) { this.close(1002); return; }
      this.frag.push(data);
      if (!fin) return;
      const msg = Buffer.concat(this.frag).toString('utf8');
      this.frag = null;
      if (msg.length > 2048) { this.close(1009); return; }
      this.onMessage(msg);
      return;
    }
    if (op !== 0x2) this.close(1002);
  }

  onMessage(text) {
    let m;
    try { m = JSON.parse(text); } catch (e) { return; }
    if (!m || typeof m !== 'object') return;
    const room = this.room;
    if (m.t === 'pos') {
      const now = Date.now();
      if (now - this.lastPos < 20) return;
      this.lastPos = now;
      const x = num(m.x, WORLD_LIMIT), y = num(m.y, 200), z = num(m.z, WORLD_LIMIT), yaw = num(m.yaw, 1000);
      if (x === null || y === null || z === null || yaw === null) return;
      this.x = r2(x); this.y = r2(y); this.z = r2(z); this.yaw = r2(yaw);
      room.dirty = true;
    } else if (m.t === 'door') {
      const i = m.i;
      if (!Number.isInteger(i) || i < 0 || i > MAX_DOOR_INDEX) return;
      const open = m.o ? 1 : 0;
      if (open) room.doors.add(i); else room.doors.delete(i);
      broadcast(room, { t: 'door', i, o: open }, this);
    }
  }

  cleanup() {
    if (this.closed) return;
    this.closed = true;
    const room = this.room;
    if (room.players.get(this.id) === this) {
      room.players.delete(this.id);
      broadcast(room, { t: 'leave', id: this.id }, null);
      if (room.players.size === 0) rooms.delete(room.name);
    }
  }
}

function broadcast(room, obj, except) {
  const buf = encodeFrame(0x1, Buffer.from(JSON.stringify(obj)));
  for (const p of room.players.values()) if (p !== except) p.sendRaw(buf);
}
function publicPlayer(p) {
  return { id: p.id, name: p.name, hue: p.hue, x: p.x, y: p.y, z: p.z, yaw: p.yaw };
}

/* ---------- HTTP ---------- */
const server = http.createServer((req, res) => {
  const url = new URL(req.url, 'http://localhost');
  if (url.pathname === '/health') {
    let players = 0;
    for (const r of rooms.values()) players += r.players.size;
    res.writeHead(200, { 'Content-Type': 'application/json', 'Cache-Control': 'no-store' });
    res.end(JSON.stringify({ ok: true, rooms: rooms.size, players }));
    return;
  }
  if (url.pathname === '/' || url.pathname === '/index.html') {
    try {
      const html = loadIndex();
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache' });
      res.end(html);
    } catch (e) {
      res.writeHead(500, { 'Content-Type': 'text/plain' });
      res.end('public/index.html is missing');
    }
    return;
  }
  res.writeHead(404, { 'Content-Type': 'text/plain' });
  res.end('Not found');
});

server.on('upgrade', (req, socket) => {
  const url = new URL(req.url, 'http://localhost');
  const key = req.headers['sec-websocket-key'];
  if (url.pathname !== '/ws' || !key || String(req.headers.upgrade).toLowerCase() !== 'websocket') {
    socket.destroy();
    return;
  }
  const accept = crypto.createHash('sha1').update(key + GUID).digest('base64');
  socket.write(
    'HTTP/1.1 101 Switching Protocols\r\n' +
    'Upgrade: websocket\r\nConnection: Upgrade\r\n' +
    'Sec-WebSocket-Accept: ' + accept + '\r\n\r\n'
  );
  socket.setNoDelay(true);

  const roomName = cleanRoomName(url.searchParams.get('room'));
  const room = getRoom(roomName);
  const client = room ? new Client(socket, room, url.searchParams.get('name')) : null;
  if (!room) {
    socket.write(encodeFrame(0x1, Buffer.from(JSON.stringify({ t: 'full', why: 'rooms' }))));
    socket.end();
    return;
  }
  if (room.players.size >= MAX_PLAYERS) {
    client.send({ t: 'full', why: 'room', max: MAX_PLAYERS });
    client.closed = true;
    socket.end();
    return;
  }
  room.players.set(client.id, client);
  client.send({
    t: 'welcome',
    id: client.id,
    name: client.name,
    hue: client.hue,
    room: room.name,
    max: MAX_PLAYERS,
    players: [...room.players.values()].filter((p) => p !== client).map(publicPlayer),
    doors: [...room.doors]
  });
  broadcast(room, { t: 'join', p: publicPlayer(client) }, client);
});

/* ---------- loops ---------- */
setInterval(() => {
  for (const room of rooms.values()) {
    if (!room.dirty) continue;
    room.dirty = false;
    const s = [];
    for (const p of room.players.values()) s.push([p.id, p.x, p.y, p.z, p.yaw]);
    broadcast(room, { t: 'state', s }, null);
  }
}, TICK_MS);

/* keep idle connections alive through Render's proxy and drop dead ones */
setInterval(() => {
  const now = Date.now();
  for (const room of rooms.values()) {
    for (const p of [...room.players.values()]) {
      if (now - p.lastPong > 70000) { p.close(1001); continue; }
      p.ping();
    }
  }
}, 20000);

function shutdown() {
  for (const room of rooms.values()) for (const p of room.players.values()) p.close(1001);
  server.close(() => process.exit(0));
  setTimeout(() => process.exit(0), 3000).unref();
}
process.on('SIGTERM', shutdown);
process.on('SIGINT', shutdown);
process.on('uncaughtException', (e) => console.error('uncaught', e));

if (require.main === module) {
  server.listen(PORT, '0.0.0.0', () => console.log('Glowmoor server listening on ' + PORT));
}
module.exports = { server, rooms };
