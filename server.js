'use strict';
/*
  Blauwdruk: server
  - serveert de website (staat onderaan dit bestand)
  - accounts met e-mailadres, wachtwoord en gebruikersnaam
  - games opslaan en tonen
  - AI-bouwer via de Anthropic API (streaming)
  - multiplayer via WebSocket
  Instellingen: instellingen.txt naast dit bestand.
  Opslag: een JSON-bestand in DATA_DIR. Dat is bedoeld voor een klein tot middelgroot platform.
*/
const http = require('node:http');
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const { promisify } = require('node:util');
const { WebSocketServer } = require('ws');
const scrypt = promisify(crypto.scrypt);

/* ---------- instellingen ---------- */
(function loadEnv() {
  for (const name of ['instellingen.txt', '.env']) {
    try {
      const text = fs.readFileSync(path.join(__dirname, name), 'utf8');
      for (const raw of text.split(/\r?\n/)) {
        const line = raw.trim();
        if (!line || line[0] === '#') continue;
        const i = line.indexOf('=');
        if (i < 1) continue;
        const k = line.slice(0, i).trim();
        let v = line.slice(i + 1).trim();
        if ((v[0] === '"' && v.endsWith('"')) || (v[0] === "'" && v.endsWith("'"))) v = v.slice(1, -1);
        if (!(k in process.env)) process.env[k] = v;
      }
    } catch (e) { /* bestand bestaat niet, prima */ }
  }
})();

const env = (k, d) => (process.env[k] !== undefined && process.env[k] !== '' ? process.env[k] : d);
const PORT = Number(env('PORT', 3000));
const SITE_NAME = env('SITE_NAME', 'Blauwdruk');
const API_KEY = env('ANTHROPIC_API_KEY', '');
const MODEL = env('ANTHROPIC_MODEL', 'claude-sonnet-5-5');
const API_BASE = env('ANTHROPIC_BASE_URL', 'https://api.anthropic.com');
const AI_PER_HOUR = Number(env('AI_PER_HOUR', 15));
const MAX_GAMES = Number(env('MAX_GAMES_PER_USER', 20));
const TRUST_PROXY = env('TRUST_PROXY', '0') === '1';
const ADMINS = env('ADMIN_USERNAMES', '').toLowerCase().split(',').map(s => s.trim()).filter(Boolean);
const DATA_DIR = path.resolve(__dirname, env('DATA_DIR', 'data'));
const MAX_HTML = 80000;
const SESSION_MS = 30 * 24 * 3600 * 1000;
const COOKIE = 'bp_session';

/* ---------- opslag ---------- */
fs.mkdirSync(DATA_DIR, { recursive: true });
const DB_FILE = path.join(DATA_DIR, 'db.json');
let db = { users: {}, games: {}, sessions: {} };
try {
  db = Object.assign(db, JSON.parse(fs.readFileSync(DB_FILE, 'utf8')));
} catch (e) {
  if (e.code !== 'ENOENT') { console.error('db.json kan niet worden gelezen:', e.message); process.exit(1); }
}
let saveTimer = null;
function flush() {
  if (saveTimer) { clearTimeout(saveTimer); saveTimer = null; }
  const tmp = DB_FILE + '.tmp';
  fs.writeFileSync(tmp, JSON.stringify(db));
  fs.renameSync(tmp, DB_FILE);
}
function save() { if (!saveTimer) saveTimer = setTimeout(flush, 150); }
for (const sig of ['SIGINT', 'SIGTERM']) process.on(sig, () => { try { flush(); } finally { process.exit(0); } });

/* ---------- hulpjes ---------- */
const now = () => Date.now();
const sha = s => crypto.createHash('sha256').update(s).digest('hex');
const httpErr = (status, message, extra) => Object.assign(new Error(message), { status, extra });
const str = v => (typeof v === 'string' ? v : '');
const isAdmin = u => !!u && ADMINS.includes(u.username);
const pubUser = u => (u ? { username: u.username, admin: isAdmin(u) } : null);

function json(res, status, obj) {
  const body = JSON.stringify(obj);
  res.writeHead(status, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' });
  res.end(body);
}
function readJson(req, limit) {
  return new Promise((resolve, reject) => {
    if (!(req.headers['content-type'] || '').includes('application/json')) return reject(httpErr(415, 'Ongeldig verzoek.'));
    let size = 0; const chunks = [];
    req.on('data', c => {
      size += c.length;
      if (size > limit) { reject(httpErr(413, 'Het verzoek is te groot.')); req.destroy(); return; }
      chunks.push(c);
    });
    req.on('end', () => {
      try {
        const v = JSON.parse(Buffer.concat(chunks).toString('utf8'));
        if (!v || typeof v !== 'object' || Array.isArray(v)) throw new Error('x');
        resolve(v);
      } catch (e) { reject(httpErr(400, 'Ongeldig verzoek.')); }
    });
    req.on('error', reject);
  });
}
function clientIp(req) {
  if (TRUST_PROXY) {
    const f = req.headers['x-forwarded-for'];
    if (f) return String(f).split(',')[0].trim();
  }
  return req.socket.remoteAddress || 'onbekend';
}
const hits = new Map();
function limit(key, max, windowMs) {
  const t = now();
  let e = hits.get(key);
  if (!e || e.reset < t) { e = { n: 0, reset: t + windowMs }; hits.set(key, e); }
  e.n++;
  return e.n <= max;
}
function checkOrigin(req) {
  const o = req.headers.origin;
  if (!o) return;
  let host = '';
  try { host = new URL(o).host; } catch (e) { /* hieronder geweigerd */ }
  if (host !== req.headers.host) throw httpErr(403, 'Dit verzoek is niet toegestaan.');
}
function parseCookies(req) {
  const out = {};
  for (const part of String(req.headers.cookie || '').split(';')) {
    const i = part.indexOf('=');
    if (i > 0) out[part.slice(0, i).trim()] = part.slice(i + 1).trim();
  }
  return out;
}
const isHttps = req => !!req.socket.encrypted || (TRUST_PROXY && req.headers['x-forwarded-proto'] === 'https');

/* ---------- sessies ---------- */
function getUser(req) {
  const tok = parseCookies(req)[COOKIE];
  if (!tok) return null;
  const s = db.sessions[sha(tok)];
  if (!s || s.exp < now()) return null;
  const u = db.users[s.uid];
  return u && u.verified ? u : null;
}
function startSession(req, res, user) {
  const tok = crypto.randomBytes(32).toString('base64url');
  db.sessions[sha(tok)] = { uid: user.id, exp: now() + SESSION_MS };
  save();
  const flags = ['HttpOnly', 'SameSite=Lax', 'Path=/', 'Max-Age=' + Math.floor(SESSION_MS / 1000)];
  if (isHttps(req)) flags.push('Secure');
  res.setHeader('Set-Cookie', COOKIE + '=' + tok + '; ' + flags.join('; '));
}
function endSession(req, res) {
  const tok = parseCookies(req)[COOKIE];
  if (tok) { delete db.sessions[sha(tok)]; save(); }
  res.setHeader('Set-Cookie', COOKIE + '=; HttpOnly; SameSite=Lax; Path=/; Max-Age=0');
}

/* ---------- wachtwoorden en codes ---------- */
async function makePassword(pw) {
  const salt = crypto.randomBytes(16);
  const hash = await scrypt(pw, salt, 64);
  return { salt: salt.toString('base64'), hash: hash.toString('base64') };
}
async function checkPassword(user, pw) {
  const salt = Buffer.from(user ? user.salt : DUMMY.salt, 'base64');
  const want = Buffer.from(user ? user.hash : DUMMY.hash, 'base64');
  const got = await scrypt(pw, salt, 64);
  return !!user && crypto.timingSafeEqual(got, want);
}
let DUMMY = { salt: crypto.randomBytes(16).toString('base64'), hash: crypto.randomBytes(64).toString('base64') };

function findUser(login) {
  const l = str(login).trim().toLowerCase();
  if (!l) return null;
  const byEmail = l.includes('@');
  for (const id in db.users) {
    const u = db.users[id];
    if (byEmail ? u.email === l : u.username === l) return u;
  }
  return null;
}
/* ---------- accounts ---------- */
const EMAIL_RE = /^[^\s@]+@[^\s@]+\.[^\s@]{2,}$/;
const USER_RE = /^[a-z0-9_]{3,20}$/;

async function signup(req, res) {
  const ip = clientIp(req);
  if (!limit('signup:' + ip, 8, 3600e3)) throw httpErr(429, 'Te veel pogingen. Probeer het later opnieuw.');
  const b = await readJson(req, 4000);
  const email = str(b.email).trim().toLowerCase();
  const username = str(b.username).trim().toLowerCase();
  const password = str(b.password);
  if (!EMAIL_RE.test(email) || email.length > 120) throw httpErr(400, 'Vul een geldig e-mailadres in.');
  if (password.length < 8 || password.length > 200) throw httpErr(400, 'Kies een wachtwoord van minstens 8 tekens.');
  if (!USER_RE.test(username)) throw httpErr(400, 'Een gebruikersnaam heeft 3 tot 20 letters, cijfers of underscores.');
  for (const id in db.users) {
    const u = db.users[id];
    if (u.email === email) throw httpErr(409, 'Er bestaat al een account met dit e-mailadres. Log in.');
    if (u.username === username) throw httpErr(409, 'Die gebruikersnaam is al bezet. Kies een andere.');
  }
  const pw = await makePassword(password);
  const user = Object.assign({ id: 'u' + crypto.randomBytes(8).toString('hex'), email, username, verified: true, created: now() }, pw);
  db.users[user.id] = user;
  save();
  startSession(req, res, user);
  json(res, 200, { user: pubUser(user) });
}
async function loginPassword(req, res) {
  const ip = clientIp(req);
  const b = await readJson(req, 2000);
  const login = str(b.login).trim().toLowerCase();
  if (!limit('login:' + ip, 20, 600e3) || !limit('login:' + login, 10, 600e3)) throw httpErr(429, 'Te veel pogingen. Wacht een paar minuten.');
  const user = findUser(login);
  const ok = await checkPassword(user, str(b.password));
  if (!ok) throw httpErr(401, 'E-mailadres, gebruikersnaam of wachtwoord klopt niet.');
  startSession(req, res, user);
  json(res, 200, { user: pubUser(user) });
}

/* ---------- games ---------- */
function listGames(req, res) {
  const me = getUser(req);
  const list = Object.values(db.games).sort((a, b) => b.at - a.at).map(g => ({
    id: g.id, title: g.title, desc: g.desc, multi: !!g.multi, author: g.author, at: g.at,
    canDelete: !!me && (me.id === g.uid || isAdmin(me))
  }));
  json(res, 200, { games: list });
}
async function publishGame(req, res, user) {
  const b = await readJson(req, 200000);
  if (b.finished !== true) throw httpErr(400, 'Je kunt alleen publiceren als je game af is.');
  const title = str(b.title).trim(), desc = str(b.desc).trim(), html = str(b.html);
  if (title.length < 2 || title.length > 40) throw httpErr(400, 'Geef je game een naam van 2 tot 40 tekens.');
  if (desc.length > 120) throw httpErr(400, 'De uitleg mag maximaal 120 tekens zijn.');
  if (html.indexOf('<') < 0 || Buffer.byteLength(html) < 100) throw httpErr(400, 'Er staat nog geen game in.');
  if (Buffer.byteLength(html) > MAX_HTML) throw httpErr(400, 'Je game is te groot (maximaal 80 KB).');
  if (!limit('pub:' + user.id, 10, 3600e3)) throw httpErr(429, 'Je publiceert te snel. Probeer het later opnieuw.');
  const mine = Object.values(db.games).filter(g => g.uid === user.id).length;
  if (mine >= MAX_GAMES) throw httpErr(400, 'Je hebt al ' + MAX_GAMES + ' games gepubliceerd. Verwijder er eerst een.');
  const g = { id: crypto.randomBytes(5).toString('hex'), uid: user.id, author: user.username, title, desc, multi: b.multi === true, html, at: now() };
  db.games[g.id] = g;
  save();
  json(res, 201, { id: g.id });
}
function deleteGame(req, res, user, id) {
  const g = db.games[id];
  if (!g) throw httpErr(404, 'Deze game bestaat niet meer.');
  if (g.uid !== user.id && !isAdmin(user)) throw httpErr(403, 'Dit is niet jouw game.');
  delete db.games[id];
  save();
  json(res, 200, { ok: true });
}

/* ---------- speelvenster ---------- */
const BRIDGE = [
  '(function(){var L=[],P=[],peers=[];',
  'var M=window.Multiplayer={myId:null,',
  'send:function(d){parent.postMessage({bd:"send",data:d},"*")},',
  'onMessage:function(f){L.push(f)},',
  'onPeers:function(f){P.push(f);if(peers.length)f(peers)}};',
  'addEventListener("message",function(e){if(e.source!==parent)return;var m=e.data;if(!m||typeof m!=="object")return;',
  'if(m.bd==="msg"){L.forEach(function(f){try{f(m.data,m.from,!!m.isMe)}catch(x){}})}',
  'else if(m.bd==="peers"){M.myId=m.me;peers=m.peers||[];P.forEach(function(f){try{f(peers)}catch(x){}})}});',
  'parent.postMessage({bd:"ready"},"*");})();'
].join('');
function injectBridge(html) {
  const tag = '<script>' + BRIDGE + '</script>';
  let m = html.match(/<head[^>]*>/i);
  if (m) return html.replace(m[0], () => m[0] + tag);
  m = html.match(/<html[^>]*>/i);
  if (m) return html.replace(m[0], () => m[0] + '<head>' + tag + '</head>');
  return tag + html;
}
const previews = new Map();
async function makePreview(req, res, user) {
  const b = await readJson(req, 200000);
  const html = str(b.html);
  if (html.indexOf('<') < 0 || Buffer.byteLength(html) > MAX_HTML) throw httpErr(400, 'De game is leeg of te groot (maximaal 80 KB).');
  if (!limit('prev:' + user.id, 60, 600e3)) throw httpErr(429, 'Je test te snel. Wacht even.');
  if (previews.size > 500) throw httpErr(503, 'De server is druk. Probeer het zo opnieuw.');
  const token = crypto.randomBytes(16).toString('hex');
  previews.set(token, { html, exp: now() + 15 * 60 * 1000 });
  json(res, 200, { token });
}
/* Games draaien in een afgesloten venster: geen toegang tot je account en geen internet. */
function serveFrame(req, res, html) {
  res.writeHead(200, {
    'Content-Type': 'text/html; charset=utf-8',
    'Cache-Control': 'no-store',
    'X-Content-Type-Options': 'nosniff',
    'Referrer-Policy': 'no-referrer',
    'Content-Security-Policy': "sandbox allow-scripts; default-src 'none'; script-src 'unsafe-inline'; style-src 'unsafe-inline'; img-src data: blob:; media-src data: blob:; font-src data:; frame-ancestors 'self'"
  });
  res.end(req.method === 'HEAD' ? undefined : injectBridge(html));
}
function frameRoute(req, res, p) {
  let html = null;
  let m = p.match(/^\/play\/([a-f0-9]{10})$/);
  if (m && db.games[m[1]]) html = db.games[m[1]].html;
  m = p.match(/^\/preview\/([a-f0-9]{32})$/);
  if (m) { const pv = previews.get(m[1]); if (pv && pv.exp > now()) html = pv.html; }
  if (html === null) return json(res, 404, { error: 'Niet gevonden.' });
  serveFrame(req, res, html);
}

/* ---------- AI-bouwer ---------- */
const AI_RULES = [
  'Je bent een ervaren gamebouwer. Schrijf een speelbare game als een enkel, compleet HTML-bestand met alle HTML, CSS en JavaScript erin.',
  'Regels:',
  '- Geen externe bestanden, libraries, lettertypen of afbeeldingen. Gebruik canvas, CSS, inline SVG of emoji. Geen fetch, geen netwerk, geen localStorage.',
  '- Maximaal ongeveer 25000 tekens.',
  '- Werkt op een telefoon (aanraking) en met toetsenbord. Schaal mee met het scherm (viewport meta, gebruik innerWidth en innerHeight).',
  '- Alle tekst in het Nederlands. Maak een startscherm met titel en startknop, laat score of doel zien en bied een manier om opnieuw te spelen.',
  '- Geen alert, confirm of prompt.',
  '- Geschikt voor alle leeftijden.'
];
const AI_MULTI = 'Multiplayer: de pagina krijgt een globaal object Multiplayer. Multiplayer.send(obj) stuurt een klein JSON-object (maximaal 3 KB, hooguit 15 keer per seconde) naar alle spelers in dezelfde kamer, ook naar jezelf. Multiplayer.onMessage(function(data, fromId, isMe){...}) ontvangt berichten, negeer je eigen berichten met isMe. Multiplayer.onPeers(function(list){...}) krijgt de lijst spelers als [{id, name, isMe}] telkens als iemand binnenkomt of weggaat. Multiplayer.myId is je eigen id. Sorteer de id waardes om een host of speler 1 en 2 te kiezen. De game moet werken voor 2 of meer spelers, laat Wachten op spelers zien als je alleen bent en synchroniseer de toestand met send. Gebruik geen andere netwerkmethode.';
const AI_KEEP_MULTI = 'De game gebruikt het globale object Multiplayer (send, onMessage, onPeers, myId). Houd dat werkend.';
const AI_FORMAT = 'Geef alleen het HTML-bestand terug in een enkel codeblok met ```html, zonder uitleg.';
const aiBusy = new Set();

async function aiRoute(req, res, user) {
  if (!API_KEY) throw httpErr(503, 'De AI-bouwer is nog niet ingesteld op deze site.');
  const b = await readJson(req, 200000);
  const prompt = str(b.prompt).trim();
  const current = str(b.current);
  if (prompt.length < 3 || prompt.length > 2000) throw httpErr(400, 'Beschrijf je game in 3 tot 2000 tekens.');
  if (current.length > MAX_HTML) throw httpErr(400, 'De game is te groot om aan te passen.');
  if (aiBusy.has(user.id)) throw httpErr(429, 'Er wordt al een game voor je gebouwd.');
  if (!limit('ai:' + user.id, AI_PER_HOUR, 3600e3)) throw httpErr(429, 'Je hebt het maximum aantal AI-aanvragen van dit uur bereikt. Probeer het later opnieuw.');

  const rules = AI_RULES.slice();
  if (current) { if (/Multiplayer\./.test(current)) rules.push(AI_KEEP_MULTI); }
  else if (b.multi === true) rules.push(AI_MULTI);
  rules.push(AI_FORMAT);
  const content = current
    ? 'Hier is de huidige game:\n```html\n' + current + '\n```\n\nPas de game aan volgens deze wens en geef het volledige bijgewerkte bestand terug:\n' + prompt
    : 'De game die de gebruiker wil:\n' + prompt;

  aiBusy.add(user.id);
  res.writeHead(200, { 'Content-Type': 'application/x-ndjson; charset=utf-8', 'Cache-Control': 'no-store', 'X-Accel-Buffering': 'no' });
  const write = o => { if (!res.writableEnded) res.write(JSON.stringify(o) + '\n'); };
  const ac = new AbortController();
  res.on('close', () => { if (!res.writableEnded) ac.abort(); });
  try {
    const r = await fetch(API_BASE + '/v1/messages', {
      method: 'POST',
      headers: { 'content-type': 'application/json', 'x-api-key': API_KEY, 'anthropic-version': '2023-06-01' },
      body: JSON.stringify({ model: MODEL, max_tokens: 16000, stream: true, system: rules.join('\n'), messages: [{ role: 'user', content }] }),
      signal: ac.signal
    });
    if (!r.ok) {
      const t = await r.text().catch(() => '');
      console.error('Anthropic API fout', r.status, t.slice(0, 300));
      write({ error: r.status === 429 || r.status === 529 ? 'De AI is nu druk bezet. Probeer het over een minuut opnieuw.' : 'De AI-bouwer werkt nu niet. Probeer het later opnieuw.' });
      return;
    }
    const dec = new TextDecoder();
    let buf = '', stop = '';
    for await (const chunk of r.body) {
      buf += dec.decode(chunk, { stream: true });
      let i;
      while ((i = buf.indexOf('\n')) >= 0) {
        const line = buf.slice(0, i).trimEnd();
        buf = buf.slice(i + 1);
        if (!line.startsWith('data:')) continue;
        let ev;
        try { ev = JSON.parse(line.slice(5).trim()); } catch (e) { continue; }
        if (ev.type === 'content_block_delta' && ev.delta && ev.delta.type === 'text_delta') write({ d: ev.delta.text });
        else if (ev.type === 'message_delta' && ev.delta && ev.delta.stop_reason) stop = ev.delta.stop_reason;
        else if (ev.type === 'error') { console.error('Anthropic stream fout', JSON.stringify(ev.error)); write({ error: 'De AI stopte onverwacht. Probeer het opnieuw.' }); return; }
      }
    }
    write({ done: true, truncated: stop === 'max_tokens' });
  } catch (e) {
    if (e.name !== 'AbortError') { console.error('AI fout:', e.message); write({ error: 'De verbinding met de AI is verbroken. Probeer het opnieuw.' }); }
  } finally {
    aiBusy.delete(user.id);
    if (!res.writableEnded) res.end();
  }
}

/* ---------- API-routes ---------- */
async function apiRoute(req, res, p) {
  const m = req.method;
  if (m !== 'GET' && m !== 'HEAD') checkOrigin(req);
  const user = getUser(req);
  const needUser = () => { if (!user) throw httpErr(401, 'Log eerst in.'); return user; };
  if (p === '/api/me' && m === 'GET') return json(res, 200, { user: pubUser(user), ai: !!API_KEY });
  if (p === '/api/games' && m === 'GET') return listGames(req, res);
  if (p === '/api/games' && m === 'POST') return publishGame(req, res, needUser());
  let g = p.match(/^\/api\/games\/([a-f0-9]{10})$/);
  if (g && m === 'DELETE') return deleteGame(req, res, needUser(), g[1]);
  if (p === '/api/signup' && m === 'POST') return signup(req, res);
  if (p === '/api/login' && m === 'POST') return loginPassword(req, res);
  if (p === '/api/logout' && m === 'POST') { endSession(req, res); return json(res, 200, { ok: true }); }
  if (p === '/api/preview' && m === 'POST') return makePreview(req, res, needUser());
  if (p === '/api/ai' && m === 'POST') return aiRoute(req, res, needUser());
  throw httpErr(404, 'Niet gevonden.');
}

/* ---------- statische bestanden ---------- */
const MIME = {
  '.html': 'text/html; charset=utf-8', '.css': 'text/css; charset=utf-8', '.js': 'text/javascript; charset=utf-8',
  '.svg': 'image/svg+xml', '.png': 'image/png', '.jpg': 'image/jpeg', '.ico': 'image/x-icon',
  '.json': 'application/json; charset=utf-8', '.txt': 'text/plain; charset=utf-8', '.webmanifest': 'application/manifest+json'
};
const PAGE_CSP = "default-src 'self'; script-src 'self'; style-src 'self' 'unsafe-inline'; img-src 'self' data:; font-src 'self'; connect-src 'self' ws: wss:; frame-src 'self'; frame-ancestors 'none'; base-uri 'none'; form-action 'self'; object-src 'none'";
function serveStatic(req, res, pathname) {
  let key = pathname === '/' ? '/index.html' : pathname;
  if (!Object.prototype.hasOwnProperty.call(WEBSITE, key)) {
    if (path.extname(key)) return json(res, 404, { error: 'Niet gevonden.' });
    key = '/index.html';
  }
  res.writeHead(200, {
    'Content-Type': MIME[path.extname(key)] || 'application/octet-stream',
    'Cache-Control': 'no-cache',
    'Content-Security-Policy': PAGE_CSP,
    'X-Content-Type-Options': 'nosniff',
    'Referrer-Policy': 'same-origin'
  });
  res.end(req.method === 'HEAD' ? undefined : WEBSITE[key]);
}

const server = http.createServer(async (req, res) => {
  try {
    const p = new URL(req.url, 'http://x').pathname;
    if (p.startsWith('/api/')) return await apiRoute(req, res, p);
    if (req.method !== 'GET' && req.method !== 'HEAD') throw httpErr(405, 'Niet toegestaan.');
    if (p.startsWith('/play/') || p.startsWith('/preview/')) return frameRoute(req, res, p);
    serveStatic(req, res, p);
  } catch (e) {
    if (res.headersSent) { if (!res.writableEnded) res.end(); return; }
    if (e && e.status) return json(res, e.status, Object.assign({ error: e.message }, e.extra || {}));
    console.error(e);
    json(res, 500, { error: 'Er ging iets mis op de server.' });
  }
});

/* ---------- multiplayer ---------- */
const wss = new WebSocketServer({ noServer: true, maxPayload: 8192 });
const rooms = new Map();
const ROOM_RE = /^[a-z0-9_.-]{1,40}$/;
const MAX_ROOM = 16;
const wsSend = (ws, o) => { if (ws.readyState === 1) ws.send(JSON.stringify(o)); };

server.on('upgrade', (req, socket, head) => {
  const deny = code => { socket.write('HTTP/1.1 ' + code + '\r\nConnection: close\r\n\r\n'); socket.destroy(); };
  let p = '';
  try { p = new URL(req.url, 'http://x').pathname; } catch (e) { return deny('400 Bad Request'); }
  if (p !== '/ws') return deny('404 Not Found');
  try { checkOrigin(req); } catch (e) { return deny('403 Forbidden'); }
  if (!req.headers.origin) return deny('403 Forbidden');
  const user = getUser(req);
  if (!user) return deny('401 Unauthorized');
  wss.handleUpgrade(req, socket, head, ws => { ws.user = user; wss.emit('connection', ws); });
});
function leaveRoom(ws) {
  const name = ws.room;
  if (!name) return;
  ws.room = null;
  const set = rooms.get(name);
  if (!set) return;
  set.delete(ws);
  if (!set.size) rooms.delete(name); else sendPeers(name);
}
function sendPeers(name) {
  const set = rooms.get(name);
  if (!set) return;
  const list = [...set].map(c => ({ id: c.pid, name: c.user.username }));
  for (const c of set) wsSend(c, { t: 'peers', me: c.pid, peers: list.map(x => ({ id: x.id, name: x.name, isMe: x.id === c.pid })) });
}
wss.on('connection', ws => {
  ws.alive = true; ws.room = null; ws.count = 0; ws.tick = now();
  ws.on('pong', () => { ws.alive = true; });
  ws.on('message', raw => {
    let m;
    try { m = JSON.parse(raw.toString()); } catch (e) { return; }
    if (!m || typeof m !== 'object') return;
    if (m.t === 'join') {
      const name = str(m.room);
      if (!ROOM_RE.test(name)) return;
      leaveRoom(ws);
      const set = rooms.get(name) || new Set();
      if (set.size >= MAX_ROOM) return wsSend(ws, { t: 'full' });
      ws.pid = crypto.randomBytes(4).toString('hex');
      set.add(ws); rooms.set(name, set); ws.room = name;
      sendPeers(name);
    } else if (m.t === 'msg' && ws.room) {
      const t = now();
      if (t - ws.tick > 1000) { ws.tick = t; ws.count = 0; }
      if (++ws.count > 60) return;
      let s;
      try { s = JSON.stringify(m.data); } catch (e) { return; }
      if (s === undefined || s.length > 4000) return;
      const set = rooms.get(ws.room);
      if (!set) return;
      const out = JSON.stringify({ t: 'msg', from: ws.pid, data: m.data });
      for (const c of set) if (c.readyState === 1) c.send(out);
    }
  });
  ws.on('close', () => leaveRoom(ws));
  ws.on('error', () => {});
});

/* ---------- opruimen ---------- */
setInterval(() => {
  const t = now();
  for (const k in db.sessions) if (db.sessions[k].exp < t) delete db.sessions[k];
  for (const [k, v] of previews) if (v.exp < t) previews.delete(k);
  for (const [k, v] of hits) if (v.reset < t) hits.delete(k);
  for (const c of wss.clients) { if (!c.alive) { c.terminate(); continue; } c.alive = false; try { c.ping(); } catch (e) { /* gesloten */ } }
  save();
}, 30000).unref();

server.listen(PORT, () => {
  console.log(SITE_NAME + ' draait op http://localhost:' + PORT);
  if (!API_KEY) console.log('LET OP: ANTHROPIC_API_KEY ontbreekt. De AI-bouwer staat uit.');
});

/* ---------------------------------------------------------------------------
   DE WEBSITE
   Hieronder staan de pagina (index.html), de opmaak (style.css) en het script
   (app.js) van de website. Je hoeft hier niets aan te doen.
   --------------------------------------------------------------------------- */
const WEBSITE = {
  "/index.html": "<!doctype html>\n<html lang=\"nl\">\n<head>\n<meta charset=\"utf-8\">\n<meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">\n<title>Blauwdruk</title>\n<meta name=\"description\" content=\"Speel games van anderen, bouw je eigen game met AI en publiceer hem op Blauwdruk.\">\n<meta name=\"theme-color\" content=\"#1d4fff\">\n<link rel=\"icon\" href=\"data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 32 32'%3E%3Crect width='32' height='32' rx='7' fill='%231d4fff'/%3E%3Crect x='7' y='7' width='18' height='18' rx='2' fill='none' stroke='white' stroke-width='2'/%3E%3Cpath d='M7 13h18M13 7v18' stroke='%236fe3ff' stroke-width='1.6'/%3E%3C/svg%3E\">\n<link rel=\"stylesheet\" href=\"/style.css\">\n<script src=\"/app.js\" defer></script>\n</head>\n<body>\n\n<header class=\"top\">\n  <div class=\"wrap\">\n    <div class=\"bar\">\n      <button class=\"brand\" id=\"brand\" type=\"button\" aria-label=\"Blauwdruk, naar alle games\">\n        <svg width=\"28\" height=\"28\" viewBox=\"0 0 28 28\" fill=\"none\" aria-hidden=\"true\"><rect x=\"3\" y=\"3\" width=\"22\" height=\"22\" rx=\"3\" stroke=\"#fff\" stroke-width=\"2\"/><path d=\"M3 10h22M10 3v22\" stroke=\"#6fe3ff\" stroke-width=\"1.6\"/><circle cx=\"17.5\" cy=\"17.5\" r=\"3\" fill=\"#fff\"/></svg>\n        Blauwdruk\n      </button>\n      <div class=\"right\">\n        <span class=\"who\" id=\"who\" hidden></span>\n        <div class=\"plus-wrap\">\n          <button class=\"plus\" id=\"plus\" type=\"button\" aria-label=\"Account maken of game bouwen\" aria-haspopup=\"true\" aria-expanded=\"false\">\n            <svg width=\"24\" height=\"24\" viewBox=\"0 0 24 24\" fill=\"none\" aria-hidden=\"true\"><path d=\"M12 4v16M4 12h16\" stroke=\"currentColor\" stroke-width=\"3\" stroke-linecap=\"round\"/></svg>\n          </button>\n          <div class=\"menu\" id=\"menu\" role=\"menu\" hidden>\n            <button type=\"button\" role=\"menuitem\" id=\"m-ai\">Game laten maken door AI</button>\n            <button type=\"button\" role=\"menuitem\" id=\"m-code\">Zelf een game maken</button>\n            <hr>\n            <button type=\"button\" role=\"menuitem\" id=\"m-out\">Uitloggen</button>\n          </div>\n        </div>\n      </div>\n    </div>\n    <div class=\"hero\">\n      <h1>Speel games van anderen. Bouw je eigen.</h1>\n      <p>Klik op het plusje rechtsboven, maak een account en vertel de AI welke game je wilt maken.</p>\n    </div>\n  </div>\n</header>\n\n<main>\n  <div id=\"view-home\" class=\"wrap section\">\n    <div class=\"sec-head\"><h2>Games</h2><span class=\"mono\" id=\"count\"></span></div>\n    <div id=\"feed\"></div>\n  </div>\n\n  <section id=\"view-studio\" class=\"wrap studio\" hidden>\n    <div class=\"studio-head\">\n      <button class=\"btn small\" id=\"st-back\" type=\"button\">Terug naar games</button>\n      <h2>Nieuwe game</h2>\n    </div>\n    <div class=\"studio-grid\">\n      <div class=\"panel\">\n        <div class=\"tabs\" role=\"tablist\" aria-label=\"Hoe wil je bouwen\">\n          <button type=\"button\" role=\"tab\" id=\"tab-ai\" aria-selected=\"true\">Met AI</button>\n          <button type=\"button\" role=\"tab\" id=\"tab-code\" aria-selected=\"false\">Zelf met code</button>\n        </div>\n        <div id=\"pane-ai\">\n          <label for=\"ai-prompt\" id=\"ai-label\">Wat voor game wil je maken?</label>\n          <textarea class=\"in\" id=\"ai-prompt\" rows=\"4\" maxlength=\"2000\" placeholder=\"Bijvoorbeeld: een snelle snake-game met levels\"></textarea>\n          <div class=\"chips\" id=\"ai-chips\"></div>\n          <label class=\"check\" id=\"ai-multi-wrap\"><input type=\"checkbox\" id=\"ai-multi\"><span>Multiplayer: meerdere spelers tegelijk in dezelfde game</span></label>\n          <div class=\"row\">\n            <button class=\"btn primary\" id=\"ai-go\" type=\"button\">Bouw mijn game</button>\n            <button class=\"btn ghost\" id=\"ai-stop\" type=\"button\" hidden>Stop</button>\n            <button class=\"btn ghost\" id=\"ai-reset\" type=\"button\" hidden>Nieuwe game starten</button>\n          </div>\n          <p class=\"note gap\" id=\"ai-status\" role=\"status\"></p>\n        </div>\n        <div id=\"pane-code\" hidden>\n          <label for=\"code-area\">HTML van je game (alles in een bestand)</label>\n          <textarea class=\"in code\" id=\"code-area\" spellcheck=\"false\" autocapitalize=\"off\" autocorrect=\"off\"></textarea>\n          <div class=\"row gap\"><button class=\"btn primary\" id=\"code-run\" type=\"button\">Test mijn game</button></div>\n          <p class=\"note gap\" id=\"code-status\" role=\"status\"></p>\n        </div>\n      </div>\n      <div class=\"panel\">\n        <div class=\"stage-bar\"><span class=\"mono\">Testvenster</span><button class=\"btn small ghost\" id=\"st-reload\" type=\"button\" hidden>Opnieuw starten</button></div>\n        <div class=\"frame-box\" id=\"stage-box\">\n          <div class=\"empty\" id=\"stage-empty\"><p>Je game verschijnt hier zodra hij klaar is. Daarna kun je hem testen.</p></div>\n        </div>\n      </div>\n    </div>\n    <div class=\"panel publish\">\n      <h3>Publiceren</h3>\n      <div class=\"pub-grid\">\n        <div class=\"field\"><label for=\"pub-title\">Naam van je game</label><input class=\"in\" id=\"pub-title\" maxlength=\"40\" autocomplete=\"off\"></div>\n        <div class=\"field\"><label for=\"pub-desc\">Korte uitleg</label><input class=\"in\" id=\"pub-desc\" maxlength=\"120\" autocomplete=\"off\"></div>\n      </div>\n      <label class=\"check first\"><input type=\"checkbox\" id=\"pub-multi\"><span>Deze game is multiplayer</span></label>\n      <label class=\"check\"><input type=\"checkbox\" id=\"pub-done\" disabled><span>Mijn game is af en ik heb hem getest</span></label>\n      <div class=\"row\"><button class=\"btn primary\" id=\"pub-go\" type=\"button\" disabled>Publiceer</button></div>\n      <p class=\"note gap\" id=\"pub-note\" role=\"status\">Bouw of schrijf eerst een game.</p>\n    </div>\n  </section>\n</main>\n\n<div class=\"overlay\" id=\"auth\" hidden>\n  <div class=\"modal\" role=\"dialog\" aria-modal=\"true\" aria-labelledby=\"auth-title\">\n    <button class=\"x\" id=\"auth-x\" type=\"button\" aria-label=\"Sluiten\">&times;</button>\n    <h2 id=\"auth-title\"></h2>\n    <p class=\"lead\" id=\"auth-lead\"></p>\n    <form id=\"auth-form\" novalidate>\n      <div class=\"field\" id=\"f-email\"><label for=\"a-email\">E-mailadres</label><input class=\"in\" id=\"a-email\" type=\"email\" autocomplete=\"email\" inputmode=\"email\" maxlength=\"120\"></div>\n      <div class=\"field\" id=\"f-login\"><label for=\"a-login\">E-mailadres of gebruikersnaam</label><input class=\"in\" id=\"a-login\" type=\"text\" autocomplete=\"username\" autocapitalize=\"off\" spellcheck=\"false\" maxlength=\"120\"></div>\n      <div class=\"field\" id=\"f-pass\"><label for=\"a-pass\" id=\"l-pass\">Wachtwoord</label><input class=\"in\" id=\"a-pass\" type=\"password\" autocomplete=\"new-password\" maxlength=\"200\"></div>\n      <div class=\"field\" id=\"f-user\"><label for=\"a-user\">Gebruikersnaam</label><input class=\"in\" id=\"a-user\" maxlength=\"20\" autocomplete=\"off\" autocapitalize=\"off\" spellcheck=\"false\"></div>\n      <p class=\"err\" id=\"auth-err\" role=\"alert\"></p>\n      <button class=\"btn primary wide\" id=\"auth-go\" type=\"submit\">Verder</button>\n    </form>\n    <div class=\"alt\" id=\"auth-alt\"></div>\n  </div>\n</div>\n\n<div class=\"play\" id=\"play\" hidden>\n  <div class=\"play-bar\">\n    <div class=\"wrap\">\n      <button class=\"btn small\" id=\"play-x\" type=\"button\">Sluiten</button>\n      <div class=\"play-title\"><span id=\"play-title\"></span><small id=\"play-author\"></small></div>\n      <span class=\"grow\"></span>\n      <span class=\"mono\" id=\"play-count\" hidden></span>\n      <form class=\"room\" id=\"room-form\" hidden>\n        <label for=\"room-code\" class=\"mono nomargin\">Kamer</label>\n        <input class=\"in\" id=\"room-code\" value=\"open\" maxlength=\"12\" autocomplete=\"off\" autocapitalize=\"off\">\n        <button class=\"btn small\" type=\"submit\">Ga</button>\n      </form>\n    </div>\n  </div>\n  <div class=\"play-box\" id=\"play-box\"></div>\n</div>\n\n<div class=\"toast\" id=\"toast\" role=\"status\" hidden></div>\n<noscript><p class=\"wrap\">Blauwdruk heeft JavaScript nodig. Zet JavaScript aan in je browser.</p></noscript>\n</body>\n</html>\n",
  "/style.css": "/* Blauwdruk: blauwe kop met blauwdruk-raster, rooster met gamekaarten, studio en speelvenster. */\n:root{\n  --bg:#eaf0ff; --surface:#ffffff; --surface-2:#f3f6ff; --ink:#0a1a45; --muted:#475892; --line:#c6d4fa;\n  --blue:#1d4fff; --blue-hover:#1240e0; --on-blue:#ffffff;\n  --head:#1d4fff; --head-2:#1236c4; --grid:rgba(255,255,255,.16);\n  --ok:#0b7a46; --err:#c4202e; --focus:#0a1a45;\n  --shadow:0 1px 2px rgba(10,26,69,.08),0 10px 28px rgba(10,26,69,.08);\n  --f-display:\"Avenir Next\",\"Segoe UI\",\"Helvetica Neue\",system-ui,sans-serif;\n  --f-body:system-ui,-apple-system,\"Segoe UI\",Roboto,sans-serif;\n  --f-mono:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;\n  color-scheme:light;\n}\n@media (prefers-color-scheme: dark){\n  :root{\n    --bg:#071029; --surface:#0e1a44; --surface-2:#0a1438; --ink:#e8eeff; --muted:#a3b4ea; --line:#24367a;\n    --blue:#3d6bff; --blue-hover:#5a82ff; --head:#0f2a9c; --head-2:#0a1c6e; --grid:rgba(255,255,255,.1);\n    --ok:#3ddc97; --err:#ff8791; --focus:#e8eeff; --shadow:0 1px 2px rgba(0,0,0,.4),0 10px 28px rgba(0,0,0,.35);\n    color-scheme:dark;\n  }\n}\n*{box-sizing:border-box}\n[hidden]{display:none!important}\nhtml,body{margin:0}\nbody{background:var(--bg);color:var(--ink);font:16px/1.5 var(--f-body);min-height:100vh}\nbutton,input,textarea{font:inherit}\n:focus-visible{outline:3px solid var(--focus);outline-offset:2px}\nh1,h2,h3{margin:0;text-wrap:balance}\n.wrap{max-width:1100px;margin:0 auto;padding-left:max(16px,env(safe-area-inset-left,0px));padding-right:max(16px,env(safe-area-inset-right,0px))}\n.mono{font-family:var(--f-mono);font-size:12px;letter-spacing:.08em;text-transform:uppercase}\n.nomargin{margin:0}\n.gap{margin-top:12px}\n\n/* kop */\n.top{position:relative;background:linear-gradient(180deg,var(--head),var(--head-2));color:#fff}\n.top::before{content:\"\";position:absolute;inset:0;pointer-events:none;\n  background-image:linear-gradient(var(--grid) 1px,transparent 1px),linear-gradient(90deg,var(--grid) 1px,transparent 1px);\n  background-size:28px 28px;-webkit-mask-image:linear-gradient(180deg,#000 35%,transparent);mask-image:linear-gradient(180deg,#000 35%,transparent)}\n.bar{position:relative;display:flex;align-items:center;justify-content:space-between;gap:12px;padding-block:14px}\n.brand{display:flex;align-items:center;gap:10px;background:none;border:0;color:#fff;cursor:pointer;padding:6px 0;\n  font-family:var(--f-display);font-weight:800;font-size:19px;letter-spacing:-.01em}\n.right{display:flex;align-items:center;gap:12px;min-width:0}\n.who{font-family:var(--f-mono);font-size:13px;background:rgba(255,255,255,.16);padding:6px 10px;border-radius:999px;max-width:40vw;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}\n.plus-wrap{position:relative}\n.plus{width:48px;height:48px;border-radius:50%;border:0;background:#fff;color:#1d4fff;display:grid;place-items:center;cursor:pointer;box-shadow:0 3px 0 rgba(0,0,0,.18)}\n.plus svg{transition:transform .2s ease}\n.plus[aria-expanded=\"true\"] svg{transform:rotate(45deg)}\n.plus:focus-visible{outline-color:#fff}\n.menu{position:absolute;right:0;top:58px;z-index:20;min-width:240px;background:var(--surface);color:var(--ink);border:1.5px solid var(--line);border-radius:14px;box-shadow:var(--shadow);padding:6px;display:flex;flex-direction:column}\n.menu button{background:none;border:0;text-align:left;padding:12px;border-radius:9px;cursor:pointer;color:var(--ink);font-weight:600}\n.menu button:hover{background:var(--surface-2)}\n.menu hr{border:0;border-top:1px solid var(--line);margin:4px 0;width:100%}\n.hero{position:relative;padding-block:14px 40px}\n.hero h1{font-family:var(--f-display);font-weight:800;font-size:clamp(26px,5.6vw,44px);line-height:1.1;letter-spacing:-.02em;max-width:20ch}\n.hero p{margin:14px 0 0;max-width:50ch;color:rgba(255,255,255,.92);font-size:17px}\n\n/* secties */\n.section{padding-block:28px 64px}\n.sec-head{display:flex;align-items:baseline;justify-content:space-between;gap:12px;margin-bottom:16px}\n.sec-head h2{font-family:var(--f-display);font-weight:700;font-size:21px}\n.sec-head .mono{color:var(--muted)}\n.note{margin:0;color:var(--muted);font-size:14px}\n.note.ok{color:var(--ok)}\n.note.bad,.err{color:var(--err)}\n.err{margin:0 0 10px;font-size:14px;min-height:1.4em}\n\n/* knoppen en velden */\n.btn{font-weight:600;font-size:15px;line-height:1;padding:13px 18px;border-radius:10px;border:1.5px solid var(--line);background:var(--surface);color:var(--ink);cursor:pointer;min-height:46px}\n.btn:hover:not(:disabled){border-color:var(--blue)}\n.btn.primary{background:var(--blue);border-color:var(--blue);color:var(--on-blue)}\n.btn.primary:hover:not(:disabled){background:var(--blue-hover);border-color:var(--blue-hover)}\n.btn.ghost{background:transparent}\n.btn.small{padding:9px 13px;min-height:38px;font-size:14px}\n.btn.wide{width:100%}\n.btn:disabled{opacity:.5;cursor:not-allowed}\n.link{background:none;border:0;padding:6px 0;color:var(--blue);font-weight:600;cursor:pointer;text-decoration:underline;text-underline-offset:3px}\n.link:disabled{color:var(--muted);cursor:default;text-decoration:none}\n.in{width:100%;color:var(--ink);background:var(--surface-2);border:1.5px solid var(--line);border-radius:10px;padding:12px}\ntextarea.in{resize:vertical;min-height:96px}\ntextarea.code{font-family:var(--f-mono);font-size:13px;line-height:1.5;min-height:300px;white-space:pre;overflow:auto}\n.codebox{font-family:var(--f-mono);font-size:24px;letter-spacing:.3em;text-align:center}\nlabel{display:block;font-weight:600;font-size:14px;margin:0 0 6px}\n.field{margin-bottom:14px}\n.check{display:flex;gap:10px;align-items:flex-start;font-weight:500;margin:14px 0}\n.check.first{margin-top:0}\n.check input{width:20px;height:20px;margin:2px 0 0;accent-color:var(--blue);flex:none}\n.row{display:flex;gap:10px;flex-wrap:wrap;align-items:center}\n.chips{display:flex;flex-wrap:wrap;gap:8px;margin-top:10px}\n.chip{border:1.5px solid var(--line);background:var(--surface);color:var(--ink);border-radius:999px;padding:8px 12px;font-size:14px;cursor:pointer}\n.chip:hover{border-color:var(--blue)}\n.badge{display:inline-block;font-family:var(--f-mono);font-size:11px;letter-spacing:.06em;text-transform:uppercase;padding:3px 7px;border-radius:6px;background:var(--blue);color:var(--on-blue);margin-left:8px;vertical-align:middle}\n\n/* kaarten */\n.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(min(100%,230px),1fr));gap:16px}\n.card{display:flex;flex-direction:column;min-width:0;background:var(--surface);border:1.5px solid var(--line);border-radius:14px;overflow:hidden}\n.cover{position:relative;aspect-ratio:16/10;display:grid;place-items:center;overflow:hidden;\n  background:radial-gradient(circle at var(--x) var(--y),hsl(var(--h) 100% 72% / .6),transparent 46%),linear-gradient(var(--a),hsl(var(--h) 92% 48%),hsl(calc(var(--h) + 14) 86% 26%))}\n.cover::after{content:\"\";position:absolute;inset:0;background-image:linear-gradient(rgba(255,255,255,.14) 1px,transparent 1px),linear-gradient(90deg,rgba(255,255,255,.14) 1px,transparent 1px);background-size:22px 22px}\n.ini{position:relative;z-index:1;font-family:var(--f-display);font-weight:800;font-size:54px;color:#fff;text-shadow:0 3px 0 rgba(0,0,0,.2)}\n.cbody{padding:14px;display:flex;flex-direction:column;gap:6px;flex:1;min-width:0}\n.ctitle{font-weight:700;font-size:17px;overflow-wrap:anywhere}\n.cmeta{font-size:13px;color:var(--muted);overflow-wrap:anywhere}\n.cdesc{margin:0;font-size:14px;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden;overflow-wrap:anywhere}\n.cact{display:flex;gap:8px;margin-top:auto;padding-top:10px}\n.empty{border:2px dashed var(--line);border-radius:16px;padding:32px 20px;text-align:center;background:var(--surface);display:flex;flex-direction:column;align-items:center;gap:10px}\n.empty h3{font-family:var(--f-display);font-weight:700;font-size:20px}\n.empty p{margin:0;max-width:44ch;color:var(--muted)}\n\n/* studio */\n.studio{padding-block:24px 64px}\n.studio-head{display:flex;align-items:center;gap:12px;margin-bottom:16px;flex-wrap:wrap}\n.studio-head h2{font-family:var(--f-display);font-weight:700;font-size:21px}\n.studio-grid{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1.25fr);gap:16px;align-items:start}\n@media (max-width:820px){.studio-grid{grid-template-columns:minmax(0,1fr)}}\n.panel{background:var(--surface);border:1.5px solid var(--line);border-radius:14px;padding:18px;min-width:0}\n.publish{margin-top:16px}\n.panel h3{font-family:var(--f-display);font-weight:700;font-size:17px;margin-bottom:12px}\n.tabs{display:flex;gap:6px;background:var(--surface-2);padding:5px;border-radius:12px;margin-bottom:16px}\n.tabs [role=\"tab\"]{flex:1;border:0;background:transparent;color:var(--ink);font-weight:600;padding:10px;border-radius:8px;cursor:pointer}\n.tabs [role=\"tab\"][aria-selected=\"true\"]{background:var(--blue);color:var(--on-blue)}\n.stage-bar{display:flex;justify-content:space-between;align-items:center;gap:8px;margin-bottom:10px}\n.stage-bar .mono{color:var(--muted)}\n.frame-box{position:relative;background:var(--surface-2);border:1.5px solid var(--line);border-radius:10px;overflow:hidden;min-height:260px}\n.frame-box iframe{display:block;width:100%;height:min(66vh,520px);border:0;background:#fff}\n.frame-box .empty{border:0;background:transparent;min-height:260px;justify-content:center}\n.frame-box .note{padding:12px}\n.pub-grid{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1fr);gap:14px}\n@media (max-width:600px){.pub-grid{grid-template-columns:minmax(0,1fr)}}\n\n/* overlays */\n.overlay{position:fixed;inset:0;z-index:60;background:rgba(5,12,38,.6);display:flex;align-items:center;justify-content:center;\n  padding:16px max(16px,env(safe-area-inset-right,0px)) max(16px,env(safe-area-inset-bottom,0px)) max(16px,env(safe-area-inset-left,0px))}\n.modal{position:relative;width:100%;max-width:420px;max-height:100%;overflow:auto;background:var(--surface);border:1.5px solid var(--line);border-radius:18px;padding:24px;box-shadow:var(--shadow)}\n.modal h2{font-family:var(--f-display);font-weight:700;font-size:22px;padding-right:36px}\n.modal .lead{margin:8px 0 18px;color:var(--muted)}\n.alt{display:flex;flex-direction:column;align-items:flex-start;gap:2px;margin-top:14px}\n.x{position:absolute;top:12px;right:12px;width:40px;height:40px;border-radius:50%;border:0;background:var(--surface-2);color:var(--ink);font-size:22px;line-height:1;cursor:pointer}\n.play{position:fixed;inset:0;z-index:50;background:var(--bg);display:flex;flex-direction:column;\n  padding-top:env(safe-area-inset-top,0px);padding-bottom:env(safe-area-inset-bottom,0px)}\n.play-bar{padding-block:10px;background:var(--surface);border-bottom:1.5px solid var(--line)}\n.play-bar .wrap{display:flex;align-items:center;gap:10px;flex-wrap:wrap;width:100%;max-width:none}\n.play-title{font-weight:700;min-width:0;overflow-wrap:anywhere}\n.play-title small{display:block;font-weight:400;color:var(--muted);font-size:13px}\n.grow{flex:1}\n.room{display:flex;align-items:center;gap:6px}\n.room .in{width:110px;padding:8px 10px}\n.play-box{flex:1;min-height:0;position:relative;background:#050b22}\n.play-box iframe{position:absolute;inset:0;width:100%;height:100%;border:0;background:#fff}\n.play-box .note{position:absolute;inset:0;display:grid;place-items:center;color:#cfe0ff;padding:20px;text-align:center}\n.toast{position:fixed;left:50%;transform:translateX(-50%);bottom:max(20px,env(safe-area-inset-bottom,0px));z-index:80;background:var(--ink);color:var(--bg);padding:12px 18px;border-radius:12px;font-weight:600;max-width:calc(100% - 32px);box-shadow:var(--shadow)}\n@media (prefers-reduced-motion:reduce){*{transition:none!important;animation:none!important}}\n",
  "/app.js": "(function () {\n'use strict';\n\n/* ---------- hulpjes ---------- */\nconst $ = (s, r) => (r || document).querySelector(s);\nfunction h(tag, props) {\n  const el = document.createElement(tag);\n  if (props) for (const k in props) {\n    const v = props[k];\n    if (k === 'class') el.className = v;\n    else if (k.slice(0, 2) === 'on') el.addEventListener(k.slice(2), v);\n    else if (v === true) el.setAttribute(k, '');\n    else if (v !== false && v != null) el.setAttribute(k, v);\n  }\n  for (let i = 2; i < arguments.length; i++) {\n    [].concat(arguments[i]).forEach(c => { if (c != null && c !== false) el.append(c.nodeType ? c : document.createTextNode(String(c))); });\n  }\n  return el;\n}\nfunction hashStr(s) { let x = 0; for (let i = 0; i < s.length; i++) x = (x * 31 + s.charCodeAt(i)) | 0; return Math.abs(x); }\nlet toastTimer;\nfunction toast(msg) {\n  const t = $('#toast'); t.textContent = msg; t.hidden = false;\n  clearTimeout(toastTimer); toastTimer = setTimeout(() => { t.hidden = true; }, 4000);\n}\nconst ls = {\n  get(k) { try { return localStorage.getItem(k); } catch (e) { return null; } },\n  set(k, v) { try { if (v === null) localStorage.removeItem(k); else localStorage.setItem(k, v); } catch (e) { /* opslag uit */ } }\n};\n\n/* ---------- staat ---------- */\nconst S = {\n  me: null, ai: false,\n  games: [], gamesState: 'loading',\n  auth: { mode: 'signup', login: '', hint: '', until: 0, busy: false, lead: '' },\n  studio: { tab: 'ai', html: '', tested: false, finished: false, title: '', desc: '', multi: false, busy: false, ctl: null, seq: 0 },\n  play: null\n};\n\nasync function api(path, opt) {\n  opt = opt || {};\n  const r = await fetch('/api' + path, {\n    method: opt.method || 'GET',\n    headers: opt.body ? { 'Content-Type': 'application/json' } : {},\n    body: opt.body ? JSON.stringify(opt.body) : undefined,\n    credentials: 'same-origin',\n    signal: opt.signal\n  });\n  let data = null;\n  try { data = await r.json(); } catch (e) { /* geen json */ }\n  if (!r.ok) throw Object.assign(new Error((data && data.error) || 'Er ging iets mis. Probeer het opnieuw.'), { status: r.status, data: data || {} });\n  return data;\n}\n\n/* ---------- spelvenster (iframe) ---------- */\nconst frames = [];\nfunction postTo(f, msg) { try { f.frame.contentWindow.postMessage(msg, '*'); } catch (e) { /* venster weg */ } }\nfunction unmountIn(box) {\n  for (let i = frames.length - 1; i >= 0; i--) {\n    const f = frames[i];\n    if (f.box !== box) continue;\n    clearTimeout(f.timer);\n    if (f.cleanup) f.cleanup();\n    f.frame.remove();\n    if (f.note) f.note.remove();\n    frames.splice(i, 1);\n  }\n}\nfunction mountFrame(box, src, ctx) {\n  unmountIn(box);\n  const fr = document.createElement('iframe');\n  fr.setAttribute('sandbox', 'allow-scripts');\n  fr.setAttribute('title', ctx.title || 'Game');\n  const f = Object.assign({ frame: fr, box: box, ready: false }, ctx);\n  frames.push(f);\n  fr.src = src;\n  box.append(fr);\n  f.timer = setTimeout(() => {\n    if (f.ready) return;\n    f.note = h('p', { class: 'note' }, 'De game start niet. Controleer je verbinding en probeer opnieuw.');\n    box.append(f.note);\n  }, 7000);\n  return f;\n}\nwindow.addEventListener('message', ev => {\n  const f = frames.find(x => x.frame.contentWindow === ev.source);\n  const m = ev.data;\n  if (!f || !m || typeof m !== 'object') return;\n  if (m.bd === 'ready') {\n    f.ready = true; clearTimeout(f.timer);\n    if (f.note) { f.note.remove(); f.note = null; }\n    if (f.onReady) f.onReady(f);\n  } else if (m.bd === 'send' && f.onSend) {\n    f.onSend(f, m.data);\n  }\n});\nfunction soloMode(f) {\n  f.onSend = (ff, d) => postTo(ff, { bd: 'msg', data: d, from: 'jij', isMe: true });\n  postTo(f, { bd: 'peers', me: 'jij', peers: [{ id: 'jij', name: S.me ? S.me.username : 'jij', isMe: true }] });\n}\n\n/* ---------- accounts ---------- */\nfunction renderWho() {\n  const who = $('#who');\n  if (S.me) { who.textContent = '@' + S.me.username; who.hidden = false; } else who.hidden = true;\n  $('#m-out').hidden = !S.me;\n}\nfunction afterLogin(user, isNew) {\n  S.me = user; renderWho(); closeAuth(); loadGames();\n  if (isNew) { toast('Je account is gemaakt. Welkom, @' + user.username + '!'); openStudio('ai'); }\n  else toast('Ingelogd als @' + user.username);\n}\nconst AUTH = {\n  signup: { title: 'Maak een account', lead: 'Kies een e-mailadres, een wachtwoord en een gebruikersnaam. Meer is niet nodig.', show: ['f-email', 'f-pass', 'f-user'], btn: 'Account maken', pass: 'new-password' },\n  login: { title: 'Inloggen', lead: 'Log in met je e-mailadres of gebruikersnaam en je wachtwoord.', show: ['f-login', 'f-pass'], btn: 'Inloggen', pass: 'current-password' }\n};\nfunction setAuth(mode, opts) {\n  const a = S.auth; a.mode = mode;\n  if (opts) Object.assign(a, opts);\n  const c = AUTH[mode];\n  $('#auth-title').textContent = c.title;\n  $('#auth-lead').textContent = a.lead || c.lead;\n  ['f-email', 'f-login', 'f-pass', 'f-user'].forEach(id => { $('#' + id).hidden = c.show.indexOf(id) < 0; });\n  $('#a-pass').setAttribute('autocomplete', c.pass);\n  $('#auth-go').textContent = c.btn;\n  $('#auth-err').textContent = '';\n  const alt = $('#auth-alt'); alt.textContent = '';\n  const link = (t, fn) => h('button', { class: 'link', type: 'button', onclick: fn }, t);\n  if (mode === 'signup') alt.append(link('Ik heb al een account', () => setAuth('login', { lead: '' })));\n  else alt.append(link('Nog geen account? Maak er een', () => setAuth('signup', { lead: '' })));\n  $('#auth').hidden = false;\n  setTimeout(() => {\n    const el = $(mode === 'signup' ? '#a-email' : '#a-login');\n    if (el) el.focus();\n  }, 30);\n}\nfunction openAuth(mode, lead) { setAuth(mode, { lead: lead || '' }); }\nfunction closeAuth() { $('#auth').hidden = true; $('#a-pass').value = ''; }\nasync function onAuthSubmit(e) {\n  e.preventDefault();\n  const a = S.auth;\n  if (a.busy) return;\n  const err = m => { $('#auth-err').textContent = m; };\n  err('');\n  a.busy = true; $('#auth-go').disabled = true;\n  try {\n    if (a.mode === 'signup') {\n      const email = $('#a-email').value.trim(), pw = $('#a-pass').value, user = $('#a-user').value.trim().toLowerCase();\n      if (!/^[^\\s@]+@[^\\s@]+\\.[^\\s@]{2,}$/.test(email)) return err('Vul een geldig e-mailadres in.');\n      if (pw.length < 8) return err('Kies een wachtwoord van minstens 8 tekens.');\n      if (!/^[a-z0-9_]{3,20}$/.test(user)) return err('Een gebruikersnaam heeft 3 tot 20 letters, cijfers of underscores.');\n      const d = await api('/signup', { method: 'POST', body: { email: email, password: pw, username: user } });\n      afterLogin(d.user, true);\n    } else {\n      const login = $('#a-login').value.trim(), pw = $('#a-pass').value;\n      if (!login) return err('Vul je e-mailadres of gebruikersnaam in.');\n      if (!pw) return err('Vul je wachtwoord in.');\n      const d = await api('/login', { method: 'POST', body: { login: login, password: pw } });\n      afterLogin(d.user, false);\n    }\n  } catch (ex) {\n    err(ex.message);\n  } finally {\n    a.busy = false; $('#auth-go').disabled = false;\n  }\n}\n\n/* ---------- plus-knop en menu ---------- */\nfunction toggleMenu(force) {\n  const m = $('#menu');\n  const open = force === undefined ? m.hidden : force;\n  m.hidden = !open;\n  $('#plus').setAttribute('aria-expanded', String(open));\n}\nfunction onPlus() {\n  if (!S.me) return openAuth('signup');\n  toggleMenu();\n}\n\n/* ---------- lijst met games ---------- */\nfunction emptyBox(title, text, btn) {\n  return h('div', { class: 'empty' }, h('h3', null, title), h('p', null, text), btn || null);\n}\nasync function loadGames() {\n  try {\n    const d = await api('/games');\n    S.games = d.games; S.gamesState = 'ready';\n  } catch (e) {\n    if (S.gamesState !== 'ready') S.gamesState = 'error';\n  }\n  renderFeed();\n}\nfunction renderFeed() {\n  const box = $('#feed');\n  box.textContent = '';\n  const n = S.games.length;\n  $('#count').textContent = n + (n === 1 ? ' game' : ' games');\n  if (S.gamesState === 'loading') return box.append(h('p', { class: 'note' }, 'Games laden...'));\n  if (S.gamesState === 'error') return box.append(emptyBox('De games laden niet', 'Controleer je verbinding en probeer het opnieuw.', h('button', { class: 'btn primary', type: 'button', onclick: loadGames }, 'Opnieuw proberen')));\n  if (!n) return box.append(emptyBox('Nog geen games', 'Blauwdruk is nieuw. Maak een account, laat de AI jouw game bouwen en wees de eerste op het platform.',\n    h('button', { class: 'btn primary', type: 'button', onclick: onPlus }, S.me ? 'Bouw een game' : 'Account maken')));\n  const grid = h('div', { class: 'grid' });\n  S.games.forEach(g => grid.append(card(g)));\n  box.append(grid);\n}\nfunction card(g) {\n  const n = hashStr(g.id);\n  const cover = h('div', { class: 'cover', 'aria-hidden': 'true' }, h('span', { class: 'ini' }, (g.title || '?').trim().charAt(0).toUpperCase()));\n  cover.style.setProperty('--h', String(208 + (n % 34)));\n  cover.style.setProperty('--a', String((n >> 3) % 180) + 'deg');\n  cover.style.setProperty('--x', String(15 + (n % 70)) + '%');\n  cover.style.setProperty('--y', String(15 + ((n >> 5) % 60)) + '%');\n  return h('article', { class: 'card' }, cover,\n    h('div', { class: 'cbody' },\n      h('div', { class: 'ctitle' }, g.title, g.multi ? h('span', { class: 'badge' }, 'Multiplayer') : null),\n      h('div', { class: 'cmeta' }, 'door @' + g.author),\n      g.desc ? h('p', { class: 'cdesc' }, g.desc) : null,\n      h('div', { class: 'cact' },\n        h('button', { class: 'btn primary small', type: 'button', onclick: () => openPlay(g) }, 'Speel'),\n        g.canDelete ? h('button', { class: 'btn small ghost', type: 'button', onclick: ev => confirmDelete(ev.currentTarget, g) }, 'Verwijder') : null)));\n}\nfunction confirmDelete(btn, g) {\n  if (btn.dataset.sure) return doDelete(g);\n  btn.dataset.sure = '1'; btn.textContent = 'Zeker weten?';\n  setTimeout(() => { if (btn.isConnected) { delete btn.dataset.sure; btn.textContent = 'Verwijder'; } }, 3000);\n}\nasync function doDelete(g) {\n  try { await api('/games/' + g.id, { method: 'DELETE' }); toast('Game verwijderd.'); loadGames(); }\n  catch (e) { toast(e.message); }\n}\n\n/* ---------- speelvenster ---------- */\nfunction setPlayCount(n) {\n  const el = $('#play-count');\n  if (n == null) { el.hidden = true; return; }\n  el.hidden = false; el.textContent = n + (n === 1 ? ' speler' : ' spelers');\n}\nfunction connectRoom(f) {\n  const g = S.play.g;\n  const room = (g.id + '-' + S.play.code).toLowerCase();\n  let ws;\n  try { ws = new WebSocket((location.protocol === 'https:' ? 'wss://' : 'ws://') + location.host + '/ws'); }\n  catch (e) { soloMode(f); setPlayCount(1); toast('Multiplayer kon niet starten. Je speelt alleen.'); return; }\n  let opened = false;\n  ws.onopen = () => { opened = true; ws.send(JSON.stringify({ t: 'join', room: room })); };\n  ws.onmessage = ev => {\n    let m; try { m = JSON.parse(ev.data); } catch (e) { return; }\n    if (m.t === 'peers') { f.me = m.me; postTo(f, { bd: 'peers', me: m.me, peers: m.peers }); setPlayCount(m.peers.length); }\n    else if (m.t === 'msg') postTo(f, { bd: 'msg', data: m.data, from: m.from, isMe: m.from === f.me });\n    else if (m.t === 'full') toast('Deze kamer zit vol. Kies een andere kamer.');\n  };\n  ws.onclose = () => {\n    if (!frames.includes(f)) return;\n    if (!opened) { soloMode(f); setPlayCount(1); toast('Multiplayer kon niet verbinden. Je speelt alleen.'); }\n    else toast('De verbinding met de kamer is verbroken. Start de game opnieuw.');\n  };\n  f.onSend = (ff, d) => { if (ws.readyState === 1) ws.send(JSON.stringify({ t: 'msg', data: d })); };\n  f.cleanup = () => { ws.onclose = null; try { ws.close(); } catch (e) { /* al dicht */ } };\n}\nfunction startPlay() {\n  const g = S.play.g;\n  setPlayCount(null);\n  mountFrame($('#play-box'), '/play/' + g.id, { title: g.title, onReady: g.multi ? connectRoom : null });\n}\nfunction openPlay(g) {\n  if (g.multi && !S.me) return openAuth('login', 'Log in om multiplayer te spelen. Heb je nog geen account? Kies hieronder Maak er een.');\n  S.play = { g: g, code: 'open' };\n  $('#play-title').textContent = g.title;\n  $('#play-author').textContent = 'door @' + g.author;\n  $('#room-form').hidden = !g.multi;\n  $('#room-code').value = 'open';\n  $('#play').hidden = false;\n  startPlay();\n}\nfunction closePlay() {\n  unmountIn($('#play-box'));\n  $('#play').hidden = true;\n  S.play = null;\n}\n\n/* ---------- studio ---------- */\nconst STARTER = [\n  '<!doctype html>',\n  '<html lang=\"nl\"><head><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">',\n  '<style>',\n  'html,body{margin:0;height:100%;background:#0a1a45;color:#fff;font-family:system-ui,sans-serif;overflow:hidden;touch-action:manipulation}',\n  '#hud{position:absolute;top:14px;left:0;right:0;text-align:center;font-size:20px}',\n  '#dot{position:absolute;width:64px;height:64px;border-radius:50%;background:#6fe3ff;border:0;cursor:pointer}',\n  '</style></head><body>',\n  '<div id=\"hud\">Tik de stip! Score: <b id=\"s\">0</b> &middot; Tijd: <b id=\"t\">15</b></div>',\n  '<button id=\"dot\" aria-label=\"stip\"></button>',\n  '<scr' + 'ipt>',\n  'var s=0,t=15,dot=document.getElementById(\"dot\");',\n  'function move(){dot.style.left=Math.random()*(innerWidth-64)+\"px\";dot.style.top=70+Math.random()*(innerHeight-140)+\"px\"}',\n  'dot.onclick=function(){if(t>0){s++;document.getElementById(\"s\").textContent=s;move()}};',\n  'move();',\n  'var iv=setInterval(function(){t--;document.getElementById(\"t\").textContent=t;if(t<=0){clearInterval(iv);dot.style.display=\"none\";document.getElementById(\"hud\").textContent=\"Klaar! Score: \"+s}},1000);',\n  '</scr' + 'ipt></body></html>'\n].join('\\n');\nconst IDEAS = [\n  ['Snake met levels', false],\n  ['Memory met dieren', false],\n  ['Ontwijk de vallende blokken', false],\n  ['Vier op een rij voor twee spelers', true],\n  ['Wie tikt het snelst? Race tegen elkaar', true]\n];\n\nfunction setTab(t) {\n  S.studio.tab = t;\n  $('#tab-ai').setAttribute('aria-selected', String(t === 'ai'));\n  $('#tab-code').setAttribute('aria-selected', String(t === 'code'));\n  $('#pane-ai').hidden = t !== 'ai';\n  $('#pane-code').hidden = t !== 'code';\n  if (t === 'code' && !$('#code-area').value) $('#code-area').value = STARTER;\n}\nfunction updateAiUi() {\n  const st = S.studio, has = !!st.html;\n  $('#ai-label').textContent = has ? 'Wat wil je aanpassen?' : 'Wat voor game wil je maken?';\n  $('#ai-prompt').placeholder = has ? 'Bijvoorbeeld: maak hem sneller en voeg een score toe' : 'Bijvoorbeeld: een snelle snake-game met levels';\n  $('#ai-go').textContent = has ? 'Pas aan' : 'Bouw mijn game';\n  $('#ai-chips').hidden = has;\n  $('#ai-multi-wrap').hidden = has;\n  $('#ai-reset').hidden = !has || st.busy;\n  $('#ai-go').disabled = st.busy || !S.ai;\n  $('#ai-stop').hidden = !st.busy;\n  if (!S.ai) $('#ai-status').textContent = 'De AI-bouwer staat op deze site nog uit. Je kunt wel zelf een game schrijven.';\n}\nfunction refreshPublish() {\n  const st = S.studio;\n  const done = $('#pub-done');\n  done.disabled = !st.tested;\n  if (!st.tested) { done.checked = false; st.finished = false; }\n  const ok = !!st.html && st.tested && st.finished && st.title.trim().length >= 2;\n  $('#pub-go').disabled = !ok;\n  let msg = 'Klaar om te publiceren.';\n  if (!st.html) msg = 'Bouw of schrijf eerst een game.';\n  else if (!st.tested) msg = 'Test je game eerst in het testvenster.';\n  else if (!st.finished) msg = 'Je kunt pas publiceren als je game af is. Vink dat hierboven aan.';\n  else if (st.title.trim().length < 2) msg = 'Geef je game een naam.';\n  const n = $('#pub-note');\n  n.textContent = msg;\n  n.className = 'note gap' + (ok ? ' ok' : '');\n}\nasync function mountPreview() {\n  const st = S.studio;\n  const seq = ++st.seq;\n  $('#stage-empty').hidden = true;\n  $('#st-reload').hidden = false;\n  try {\n    const d = await api('/preview', { method: 'POST', body: { html: st.html } });\n    if (seq !== st.seq) return;\n    mountFrame($('#stage-box'), '/preview/' + d.token, {\n      title: 'Testvenster',\n      onReady: f => { st.tested = true; soloMode(f); refreshPublish(); }\n    });\n  } catch (e) {\n    if (seq !== st.seq) return;\n    if (e.status === 401) { S.me = null; renderWho(); openAuth('login', 'Je bent uitgelogd. Log opnieuw in om verder te gaan.'); }\n    else toast(e.message);\n  }\n}\nfunction saveDraft() {\n  const st = S.studio;\n  if (!st.html) return;\n  ls.set('bp-draft', JSON.stringify({ html: st.html, title: st.title, desc: st.desc, multi: st.multi }));\n}\nfunction setHtml(html) {\n  const st = S.studio;\n  st.html = html; st.tested = false; st.finished = false;\n  $('#pub-done').checked = false;\n  $('#code-area').value = html;\n  if (/Multiplayer\\./.test(html)) { $('#pub-multi').checked = true; st.multi = true; }\n  mountPreview();\n  refreshPublish(); updateAiUi(); saveDraft();\n}\nfunction resetStudio() {\n  const st = S.studio;\n  if (st.ctl) st.ctl.abort();\n  st.seq++;\n  Object.assign(st, { html: '', tested: false, finished: false, title: '', desc: '', multi: false, busy: false, ctl: null });\n  unmountIn($('#stage-box'));\n  $('#stage-empty').hidden = false; $('#st-reload').hidden = true;\n  ['#ai-prompt', '#pub-title', '#pub-desc', '#code-area'].forEach(s => { $(s).value = ''; });\n  $('#pub-multi').checked = false; $('#ai-multi').checked = false; $('#pub-done').checked = false;\n  $('#ai-status').textContent = ''; $('#code-status').textContent = '';\n  ls.set('bp-draft', null);\n  setTab(st.tab);\n  refreshPublish(); updateAiUi();\n}\nfunction openStudio(tab) {\n  toggleMenu(false);\n  if (!S.me) return openAuth('signup');\n  $('#view-home').hidden = true;\n  $('#view-studio').hidden = false;\n  setTab(tab || 'ai');\n  updateAiUi(); refreshPublish();\n  window.scrollTo(0, 0);\n}\nfunction goHome() {\n  $('#view-studio').hidden = true;\n  $('#view-home').hidden = false;\n  toggleMenu(false);\n  window.scrollTo(0, 0);\n}\n\n/* ---------- AI bouwt de game ---------- */\nfunction extractHtml(t) {\n  const m = t.match(/```(?:html)?[ \\t]*\\n([\\s\\S]*?)```/i);\n  let s = m ? m[1] : ((t.match(/```(?:html)?[ \\t]*\\n([\\s\\S]*)$/i) || [])[1] || t);\n  s = s.trim();\n  const i = s.search(/<!doctype|<html/i);\n  if (i > 0) s = s.slice(i);\n  return s;\n}\nasync function buildAI() {\n  const st = S.studio;\n  const status = $('#ai-status');\n  if (!S.ai || st.busy) return;\n  const idea = $('#ai-prompt').value.trim();\n  if (idea.length < 3) { status.textContent = 'Vertel eerst welke game je wilt maken.'; return; }\n  const editing = !!st.html;\n  const ctl = new AbortController();\n  st.busy = true; st.ctl = ctl;\n  updateAiUi();\n  status.textContent = 'De AI denkt na...';\n  let text = '', truncated = false;\n  try {\n    const r = await fetch('/api/ai', {\n      method: 'POST', credentials: 'same-origin', signal: ctl.signal,\n      headers: { 'Content-Type': 'application/json' },\n      body: JSON.stringify({ prompt: idea, multi: $('#ai-multi').checked, current: editing ? st.html : '' })\n    });\n    if (!r.ok) {\n      let d = null; try { d = await r.json(); } catch (e) { /* geen json */ }\n      if (r.status === 401) { S.me = null; renderWho(); openAuth('login', 'Je bent uitgelogd. Log opnieuw in om verder te gaan.'); }\n      throw new Error((d && d.error) || 'Er ging iets mis bij het bouwen. Probeer het opnieuw.');\n    }\n    const reader = r.body.getReader(), dec = new TextDecoder();\n    let buf = '';\n    for (;;) {\n      const x = await reader.read();\n      if (x.done) break;\n      buf += dec.decode(x.value, { stream: true });\n      let i;\n      while ((i = buf.indexOf('\\n')) >= 0) {\n        const line = buf.slice(0, i); buf = buf.slice(i + 1);\n        if (!line.trim()) continue;\n        let m; try { m = JSON.parse(line); } catch (e) { continue; }\n        if (m.d) { text += m.d; status.textContent = 'Bezig met bouwen... ' + Math.max(1, Math.round(text.length / 1000)) + 'k tekens'; }\n        else if (m.error) throw new Error(m.error);\n        else if (m.done) truncated = !!m.truncated;\n      }\n    }\n    const html = extractHtml(text);\n    if (html.length < 200 || html.indexOf('<') < 0) throw new Error('De AI gaf geen bruikbare game terug. Probeer het opnieuw of beschrijf het anders.');\n    if (!editing) {\n      st.multi = $('#ai-multi').checked || /Multiplayer\\./.test(html);\n      $('#pub-multi').checked = st.multi;\n      if (!$('#pub-title').value) { st.title = idea.slice(0, 40); $('#pub-title').value = st.title; }\n    }\n    setHtml(html);\n    $('#ai-prompt').value = '';\n    status.textContent = truncated ? 'De game is afgekapt. Vraag om een eenvoudigere versie.' : 'Klaar. Test je game en vraag aanpassingen als je wilt.';\n  } catch (e) {\n    status.textContent = e.name === 'AbortError' ? 'Gestopt.' : e.message;\n  } finally {\n    st.busy = false; st.ctl = null; updateAiUi();\n  }\n}\n\n/* ---------- publiceren ---------- */\nasync function publish() {\n  const st = S.studio;\n  const note = $('#pub-note');\n  if ($('#pub-go').disabled) return;\n  $('#pub-go').disabled = true;\n  try {\n    await api('/games', { method: 'POST', body: { title: st.title.trim(), desc: st.desc.trim(), multi: !!st.multi, html: st.html, finished: st.finished === true } });\n    resetStudio(); goHome(); loadGames();\n    toast('Gepubliceerd! Je game staat nu op Blauwdruk.');\n  } catch (e) {\n    if (e.status === 401) { S.me = null; renderWho(); openAuth('login', 'Je bent uitgelogd. Log opnieuw in en publiceer dan nog een keer.'); }\n    note.textContent = e.message; note.className = 'note gap bad';\n  } finally {\n    if (!$('#view-studio').hidden) { $('#pub-go').disabled = false; refreshPublishKeepError(); }\n  }\n}\nfunction refreshPublishKeepError() {\n  const n = $('#pub-note');\n  if (n.classList.contains('bad')) { const msg = n.textContent; refreshPublish(); n.textContent = msg; n.className = 'note gap bad'; }\n  else refreshPublish();\n}\n\n/* ---------- koppelingen ---------- */\nfunction bind() {\n  $('#brand').addEventListener('click', () => { goHome(); });\n  $('#plus').addEventListener('click', onPlus);\n  $('#m-ai').addEventListener('click', () => openStudio('ai'));\n  $('#m-code').addEventListener('click', () => openStudio('code'));\n  $('#m-out').addEventListener('click', async () => {\n    try { await api('/logout', { method: 'POST', body: {} }); } catch (e) { /* toch uitloggen in de pagina */ }\n    S.me = null; renderWho(); toggleMenu(false); goHome(); loadGames(); toast('Je bent uitgelogd.');\n  });\n  document.addEventListener('click', ev => { if (!$('#menu').hidden && !ev.target.closest('#menu,#plus')) toggleMenu(false); });\n  document.addEventListener('keydown', ev => {\n    if (ev.key !== 'Escape') return;\n    if (!$('#auth').hidden) closeAuth(); else if (!$('#play').hidden) closePlay(); else toggleMenu(false);\n  });\n  $('#auth-x').addEventListener('click', closeAuth);\n  $('#auth').addEventListener('click', ev => { if (ev.target === $('#auth')) closeAuth(); });\n  $('#auth-form').addEventListener('submit', onAuthSubmit);\n  $('#play-x').addEventListener('click', closePlay);\n  $('#room-form').addEventListener('submit', ev => {\n    ev.preventDefault();\n    S.play.code = ($('#room-code').value.toLowerCase().replace(/[^a-z0-9]/g, '').slice(0, 12)) || 'open';\n    $('#room-code').value = S.play.code;\n    startPlay();\n  });\n  $('#st-back').addEventListener('click', goHome);\n  $('#tab-ai').addEventListener('click', () => setTab('ai'));\n  $('#tab-code').addEventListener('click', () => setTab('code'));\n  const chips = $('#ai-chips');\n  IDEAS.forEach(i => chips.append(h('button', { class: 'chip', type: 'button', onclick: () => { $('#ai-prompt').value = i[0]; $('#ai-multi').checked = i[1]; $('#ai-prompt').focus(); } }, i[0])));\n  $('#ai-go').addEventListener('click', buildAI);\n  $('#ai-stop').addEventListener('click', () => { if (S.studio.ctl) S.studio.ctl.abort(); });\n  $('#ai-reset').addEventListener('click', resetStudio);\n  $('#code-run').addEventListener('click', () => {\n    const v = $('#code-area').value.trim();\n    if (v.length < 20 || v.indexOf('<') < 0) { $('#code-status').textContent = 'Schrijf eerst de HTML van je game.'; return; }\n    if (v.length > 80000) { $('#code-status').textContent = 'Je game is te groot. Maak hem kleiner dan 80.000 tekens.'; return; }\n    $('#code-status').textContent = 'Je game draait in het testvenster.';\n    setHtml(v);\n  });\n  $('#code-area').addEventListener('input', () => {\n    const st = S.studio;\n    if ($('#code-area').value === st.html) return;\n    st.tested = false; st.finished = false; $('#pub-done').checked = false;\n    $('#code-status').textContent = 'Je code is veranderd. Test hem opnieuw.';\n    refreshPublish();\n  });\n  $('#st-reload').addEventListener('click', () => { if (S.studio.html) mountPreview(); });\n  $('#pub-title').addEventListener('input', e => { S.studio.title = e.target.value; refreshPublish(); });\n  $('#pub-desc').addEventListener('input', e => { S.studio.desc = e.target.value; });\n  $('#pub-title').addEventListener('change', saveDraft);\n  $('#pub-desc').addEventListener('change', saveDraft);\n  $('#pub-multi').addEventListener('change', e => { S.studio.multi = e.target.checked; saveDraft(); });\n  $('#pub-done').addEventListener('change', e => { S.studio.finished = e.target.checked; refreshPublish(); });\n  $('#pub-go').addEventListener('click', publish);\n}\n\nasync function init() {\n  bind();\n  renderWho();\n  try {\n    const d = await api('/me');\n    S.me = d.user; S.ai = !!d.ai;\n  } catch (e) { /* offline: je blijft uitgelogd */ }\n  renderWho();\n  try {\n    const x = JSON.parse(ls.get('bp-draft') || 'null');\n    if (x && typeof x.html === 'string' && x.html) {\n      Object.assign(S.studio, { html: x.html, title: String(x.title || ''), desc: String(x.desc || ''), multi: !!x.multi });\n      $('#pub-title').value = S.studio.title; $('#pub-desc').value = S.studio.desc; $('#pub-multi').checked = S.studio.multi;\n      $('#code-area').value = x.html;\n      $('#ai-status').textContent = 'Je vorige concept is teruggezet. Klik op Opnieuw starten in het testvenster om hem te testen.';\n      $('#stage-empty').hidden = true; $('#st-reload').hidden = false;\n    }\n  } catch (e) { /* geen concept */ }\n  refreshPublish(); updateAiUi();\n  loadGames();\n  setInterval(() => { if (!document.hidden && !$('#view-home').hidden) loadGames(); }, 60000);\n}\ninit();\n})();\n"
};
