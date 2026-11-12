// Generated from prompts/cli/accounts-cloud.prompt.md (sha256: 3e45ecb26ee5662d5067b0cf4a37c0b1407eb901d508e5c03071b8a3612d24bc).
// The PDD login server client: share, accept, leave, groups, the server audit log, the list rows, the copy desk
// and the access-only run home. The gh token stays in request headers only; a login text never reaches a message.
import { spawnSync } from 'node:child_process';
import { createHash, randomBytes } from 'node:crypto';
import { chmodSync, closeSync, constants, existsSync, fsyncSync, lstatSync, mkdirSync, openSync, readdirSync, readFileSync, realpathSync, renameSync, unlinkSync, writeFileSync } from 'node:fs';
import { homedir, hostname as osHostname } from 'node:os';
import { isAbsolute, join, relative, sep } from 'node:path';
import { redactSecrets, rememberSecrets } from './secret-redaction.mjs';

const VERSION = JSON.parse(readFileSync(new URL('../package.json', import.meta.url), 'utf8')).version;
export const LOCAL_MODE_TEXT = 'This needs the PDD login server. It is not set up on this machine.';
const ENV_URL_TEXT = 'PDD_ACCOUNTS_URL must be an HTTPS address, for example https://accounts.example.';
const POOL_URL_TEXT = 'The server address in accounts.json must be an HTTPS address, for example https://accounts.example.';
const AUTH_TEXT = 'The PDD login server did not accept your GitHub login (HTTP 401). Run gh auth login, then run the command again.';
const ME_TEXT = 'pdd could not read your GitHub login (gh api user). Run gh auth status.';
const CLAUDE_TEXT = 'Claude logins stay on this machine. The PDD login server does not hold them.';
const UPLOAD_TEXT = 'pdd accounts upload is not ready yet. Use --local.';
const NAME = /^[a-z0-9][a-z0-9._-]{0,31}$/;
const GH_LOGIN = /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$/;
const TEAM = /^[A-Za-z0-9._-]{1,100}$/;
const ID = /^[A-Za-z0-9_-]{1,128}$/;
const MACHINE_ID = /^m_[0-9a-f]{16}$/;
const MACHINE_NAME = /^[A-Za-z0-9._-]{1,63}$/;
const MAX_REPLY = 1024 * 1024;
const MAX_AUTH = 64 * 1024;
const MARKER = '.pdd-copy-home';
const STORE_LINE = 'cli_auth_credentials_store = "file"\n';
const SERVER_CODES = new Set(['not_found', 'forbidden', 'conflict', 'invalid', 'needs_sign_in', 'all_out', 'unavailable']);
const EXIT = { local: 2, input: 2, 'sign-in': 5, unavailable: 3, bad_reply: 3 };
const UNREACHABLE = { ENOTFOUND: 'the address was not found', EAI_AGAIN: 'the address was not found', ECONNREFUSED: 'the connection was refused',
  ECONNRESET: 'the connection was reset', EHOSTUNREACH: 'there is no network route to it', ENETUNREACH: 'there is no network route to it',
  UND_ERR_CONNECT_TIMEOUT: 'the connection timed out' };

const isObject = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const fail = (code, message) => ({ ok: false, code, exitCode: EXIT[code] ?? 1, message });
const sha256 = text => createHash('sha256').update(text).digest('hex');

// Safe text: known secrets first, then the shared redaction, one line, at most 300 characters.
function safe(value, secrets = []) {
  let text = String(value ?? '');
  for (const secret of secrets) if (secret) text = text.split(secret).join('[secret]');
  return redactSecrets(text, secrets).replace(/\s+/g, ' ').trim().slice(0, 300);
}
const shown = value => safe(typeof value === 'string' ? value : JSON.stringify(value) ?? String(value)).slice(0, 60) || '(empty)';
// Every string of a server value as a safe text; numbers, booleans and null stay.
function clean(value, secrets) {
  if (typeof value === 'string') return safe(value, secrets);
  if (Array.isArray(value)) return value.map(item => clean(item, secrets));
  if (isObject(value)) return Object.fromEntries(Object.entries(value).map(([key, item]) => [safe(key, secrets), clean(item, secrets)]));
  return value;
}

// ---------- the server address ----------

function checkedBase(raw, fromEnv) {
  let url = null;
  try { url = typeof raw === 'string' ? new URL(raw) : null; } catch { url = null; }
  const loopback = url && ['127.0.0.1', 'localhost', '[::1]'].includes(url.hostname);
  if (!url || !(url.protocol === 'https:' || (url.protocol === 'http:' && loopback)) || url.username || url.password
    || url.search || url.hash || raw.includes('?') || raw.includes('#'))
    throw Object.assign(new Error(fromEnv ? ENV_URL_TEXT : POOL_URL_TEXT), { exitCode: 2, code: 'input' });
  return url.href.endsWith('/') ? url.href : `${url.href}/`;
}
const envUrlSet = env => typeof env?.PDD_ACCOUNTS_URL === 'string' && env.PDD_ACCOUNTS_URL !== '';

export function cloudUrl(env = process.env, pool) {
  if (envUrlSet(env)) return checkedBase(env.PDD_ACCOUNTS_URL, true);
  const server = pool?.server;
  if (server === undefined || server === null) return null;
  return checkedBase(isObject(server) ? server.url : undefined, false);
}

// ---------- folders and the machine id (DESIGN 2) ----------

function folders(env) {
  const home = env.HOME || homedir();
  const configDir = isAbsolute(env.XDG_CONFIG_HOME ?? '') ? join(env.XDG_CONFIG_HOME, 'pdd') : join(home, '.config', 'pdd');
  const stateDir = isAbsolute(env.XDG_STATE_HOME ?? '') ? join(env.XDG_STATE_HOME, 'pdd', 'accounts') : join(home, '.local', 'state', 'pdd', 'accounts');
  return { home, configDir, stateDir, machineFile: join(configDir, 'machine.json') };
}
const shortHost = value => String(value ?? '').split('.')[0].replace(/[^A-Za-z0-9_-]/g, '').slice(0, 63) || 'machine';

function machineIdentity(ctx) {
  if (ctx.machine) return ctx.machine;
  const { configDir, machineFile } = folders(ctx.env);
  const fresh = () => ({ id: `m_${ctx.ports.randomHex(8)}`, name: shortHost(ctx.ports.hostname()) });
  const read = () => {
    try {
      const value = JSON.parse(readFileSync(machineFile, 'utf8'));
      return isObject(value) && MACHINE_ID.test(value.id ?? '') && MACHINE_NAME.test(value.name ?? '') ? { id: value.id, name: value.name } : 'bad';
    } catch (error) { return error?.code === 'ENOENT' ? null : 'bad'; }
  };
  let found = read();
  if (found === null) {
    const made = fresh();
    try {
      mkdirSync(configDir, { recursive: true, mode: 0o700 });
      const fd = openSync(machineFile, constants.O_WRONLY | constants.O_CREAT | constants.O_EXCL, 0o600);
      try { writeFileSync(fd, `${JSON.stringify(made, null, 2)}\n`); fsyncSync(fd); } finally { closeSync(fd); }
      found = made;
    } catch (error) { found = error?.code === 'EEXIST' ? read() : 'bad'; }
  }
  // A bad file is never overwritten: this request sends an id that lives in memory only.
  ctx.machine = found === null || found === 'bad' || !MACHINE_ID.test(found.id) ? fresh() : found;
  if (!MACHINE_ID.test(ctx.machine.id)) ctx.machine = { id: `m_${randomBytes(8).toString('hex')}`, name: ctx.machine.name };
  return ctx.machine;
}

// ---------- gh: the token and who I am ----------

// The first gh on PATH that is a file or link and not a PDD Try launcher, as src/runtime-client.mjs finds it.
function ghProgram(env) {
  for (const path of (env.PATH || process.env.PATH || '').split(':').filter(Boolean).map(folder => join(folder, 'gh'))) {
    try {
      const stat = lstatSync(path);
      if (!stat.isFile() && !stat.isSymbolicLink()) continue;
      if (readFileSync(path).subarray(0, 64).toString().includes('PDD Try launcher v1')) continue;
      return realpathSync(path);
    } catch { /* the next PATH folder */ }
  }
  return null;
}
const DEFAULT_GH = Symbol('default gh');
const identities = new Map();

function readToken(ctx) {
  let reply;
  try { reply = ctx.ports.gh(['auth', 'token']); } catch { reply = null; }
  if (reply?.error?.code === 'ENOENT') return fail('sign-in', 'Install the GitHub CLI, then run gh auth login.');
  const token = reply?.status === 0 ? String(reply.stdout ?? '').trim() : '';
  if (!token) return fail('sign-in', 'Run gh auth login.');
  rememberSecrets(token);
  ctx.token = token;
  ctx.secrets = [token];
  return null;
}

function readMe(ctx) {
  const key = `${sha256(ctx.token)}`;
  let cache = identities.get(ctx.ghKey);
  if (!cache) identities.set(ctx.ghKey, cache = new Map());
  if (cache.has(key)) { ctx.me = cache.get(key); return null; }
  let reply;
  try { reply = ctx.ports.gh(['api', 'user', '--jq', '.login + " " + (.id|tostring)']); } catch { reply = null; }
  const words = reply?.status === 0 ? String(reply.stdout ?? '').trim().split(/\s+/) : [];
  if (words.length !== 2 || !GH_LOGIN.test(words[0]) || !/^\d{1,20}$/.test(words[1])) return fail('sign-in', ME_TEXT);
  ctx.me = { login: words[0], id: words[1] };
  cache.set(key, ctx.me);
  return null;
}
const signIn = (ctx, needMe) => readToken(ctx) ?? (needMe ? readMe(ctx) : null);

// ---------- context ----------

async function loadPool(input, env, ports) {
  if (input.pool !== undefined || envUrlSet(env)) return input.pool ?? null;
  if (typeof ports.readPool === 'function') return ports.readPool({ env });
  // Only a missing store file means "no pool"; a store that fails to load is an error.
  const file = new URL('./accounts-store.mjs', import.meta.url);
  if (!existsSync(file)) return null;
  const store = await import(file.href);
  return typeof store.readPool === 'function' ? store.readPool({ env }) : null;
}

async function connect(input, given) {
  const env = input.env ?? process.env;
  const ports = {
    fetch: given.fetch ?? globalThis.fetch,
    gh: given.gh ?? (args => {
      const program = ghProgram(env);
      return program ? spawnSync(program, args, { encoding: 'utf8', env, stdio: ['ignore', 'pipe', 'pipe'], timeout: 60_000 }) : { status: null, error: { code: 'ENOENT' } };
    }),
    hostname: given.hostname ?? osHostname,
    randomHex: given.randomHex ?? (bytes => randomBytes(bytes).toString('hex')),
    timeZone: given.timeZone,
    timeoutMs: given.timeoutMs ?? 15_000,
  };
  let pool;
  try { pool = await loadPool(input, env, given); } catch (error) { return { failure: fail('input', safe(error?.message) || 'pdd could not read accounts.json.') }; }
  let base;
  try { base = cloudUrl(env, pool); } catch (error) { return { failure: fail('input', error.message) }; }
  if (!base) return { failure: fail('local', LOCAL_MODE_TEXT) };
  return { env, pool, base, host: new URL(base).host, ports, given, ghKey: given.gh ?? DEFAULT_GH, secrets: [] };
}

// ---------- HTTP ----------

async function readBody(response) {
  if (response.body && typeof response.body.getReader === 'function') {
    const reader = response.body.getReader(), chunks = [];
    let size = 0;
    for (;;) {
      const { done, value } = await reader.read();
      if (done) break;
      size += value.byteLength;
      if (size > MAX_REPLY) { await reader.cancel().catch(() => {}); return null; }
      chunks.push(Buffer.from(value));
    }
    return Buffer.concat(chunks).toString('utf8');
  }
  const text = typeof response.text === 'function' ? String(await response.text()) : '';
  return Buffer.byteLength(text) > MAX_REPLY ? null : text;
}

function lost(ctx, error) {
  const raw = String(error?.cause?.code ?? error?.code ?? ''), code = raw.replace(/[^A-Z0-9_]/g, '').slice(0, 40);
  const reason = error?.name === 'AbortError' || error?.name === 'TimeoutError' ? 'no answer in time'
    : UNREACHABLE[code] ?? (/CERT|SELF_SIGNED|UNABLE_TO_VERIFY|ERR_TLS/.test(code) ? 'its TLS certificate was not accepted' : code ? `connection failed: ${code}` : 'connection failed');
  return fail('unavailable', `pdd could not reach the PDD login server at ${ctx.host} (${reason}). Check your network and PDD_ACCOUNTS_URL.`);
}

async function call(ctx, method, path, body) {
  const machine = machineIdentity(ctx);
  const headers = { Authorization: `Bearer ${ctx.token}`, Accept: 'application/json', 'User-Agent': `pdd/${VERSION}`,
    'X-PDD-Machine': machine.id, 'X-PDD-Machine-Name': machine.name };
  if (body !== undefined) headers['Content-Type'] = 'application/json';
  const controller = new AbortController(), timer = setTimeout(() => controller.abort(), ctx.ports.timeoutMs);
  let response, text;
  try {
    response = await ctx.ports.fetch(new URL(path, ctx.base), { method, headers, body: body === undefined ? undefined : JSON.stringify(body), redirect: 'manual', signal: controller.signal });
    text = await readBody(response);
  } catch (error) { return { failure: lost(ctx, error) }; } finally { clearTimeout(timer); }
  const status = Number(response?.status);
  if (status === 0 || (status >= 300 && status < 400))
    return { failure: fail('bad_reply', `The PDD login server at ${ctx.host} sent a redirect. pdd does not follow it with your GitHub login. Check PDD_ACCOUNTS_URL.`) };
  if (status === 401) return { failure: fail('sign-in', AUTH_TEXT) };
  let json = null;
  try { json = text === null ? null : JSON.parse(text); } catch { json = null; }
  if (status >= 200 && status < 300) {
    if (!isObject(json)) return { failure: fail('bad_reply', `The PDD login server sent a reply that pdd can not read (HTTP ${status}). Nothing was saved.`) };
    return { json, status };
  }
  const error = isObject(json?.error) ? json.error : {};
  const serverCode = typeof error.code === 'string' && SERVER_CODES.has(error.code) ? error.code : null;
  const busy = status >= 500 || status === 408 || status === 429;
  const code = serverCode === 'all_out' ? 'all_out' : busy ? 'unavailable' : serverCode ?? 'refused';
  const said = typeof error.message === 'string' ? safe(error.message, ctx.secrets) : '';
  const shownCode = typeof error.code === 'string' ? safe(error.code, ctx.secrets).slice(0, 40) : 'no code';
  const message = said || (code === 'unavailable' ? `The PDD login server is not available now (HTTP ${status}). Try again later.`
    : `The PDD login server refused this (HTTP ${status}, ${shownCode}).`);
  return { failure: fail(code, message), json, status };
}

const enc = id => encodeURIComponent(id);
const validRow = row => isObject(row) && typeof row.id === 'string' && ID.test(row.id) && typeof row.name === 'string' && NAME.test(row.name)
  && isObject(row.owner) && typeof row.owner.login === 'string' && GH_LOGIN.test(row.owner.login);

async function listing(ctx) {
  if (ctx.listing) return ctx.listing;
  const reply = await call(ctx, 'GET', 'v1/accounts');
  if (reply.failure) return reply;
  const json = reply.json;
  const good = ['logins', 'invites', 'order', 'groups'].every(key => Array.isArray(json[key])) && json.logins.every(validRow) && json.invites.every(validRow)
    && json.order.every(id => typeof id === 'string') && json.groups.every(isObject);
  if (!good) return { failure: fail('bad_reply', `The PDD login server sent a reply that pdd can not read (HTTP ${reply.status}). Nothing was saved.`) };
  ctx.listing = { json };
  return ctx.listing;
}

// ---------- names ----------

function parseName(value) {
  if (typeof value !== 'string') return null;
  const parts = value.split('/');
  if (parts.length === 1 && NAME.test(parts[0])) return { owner: null, name: parts[0] };
  if (parts.length === 2 && GH_LOGIN.test(parts[0]) && NAME.test(parts[1])) return { owner: parts[0], name: parts[1] };
  return null;
}
const badName = value => fail('input', `${shown(value)} is not a login name. Use lower-case letters, digits, dots, dashes or underscores (at most 32), or OWNER/NAME.`);
const sameLogin = (a, b) => String(a).toLowerCase() === String(b).toLowerCase();
const isOwn = (row, me) => row.owner.id !== undefined && row.owner.id !== null ? String(row.owner.id) === me.id : sameLogin(row.owner.login, me.login);
const displayOf = (row, me) => me && isOwn(row, me) ? row.name : `${row.owner.login}/${row.name}`;
const matches = (row, wanted) => row.name === wanted.name && (!wanted.owner || sameLogin(row.owner.login, wanted.owner));

function userList(value) {
  const items = Array.isArray(value) ? value : value === undefined || value === null ? [] : [value];
  if (!items.every(item => typeof item === 'string')) return { failure: fail('input', 'The --with list must name GitHub users.') };
  const list = [], seen = new Set();
  for (const item of items.flatMap(text => text.split(','))) {
    const user = item.trim();
    if (!user) continue;
    if (!GH_LOGIN.test(user)) return { failure: fail('input', `${shown(user)} is not a GitHub user name.`) };
    if (!seen.has(user.toLowerCase())) { seen.add(user.toLowerCase()); list.push(user); }
  }
  return { list };
}
const absent = value => value === undefined || value === null || value === '';

async function ownLogin(ctx, wanted) {
  const found = await listing(ctx);
  if (found.failure) return found;
  const label = wanted.owner ? `${wanted.owner}/${wanted.name}` : wanted.name;
  const row = !wanted.owner || sameLogin(wanted.owner, ctx.me.login) ? found.json.logins.find(item => isOwn(item, ctx.me) && item.name === wanted.name) : null;
  return row ? { row } : { failure: fail('not_found', `You have no login named ${label} on the PDD login server. Run pdd accounts list.`) };
}

function pickOne(items, wanted, label) {
  const hits = items.filter(item => matches(item, wanted));
  if (hits.length > 1) return { failure: fail('input', `Two people share a login named ${label} with you. Use OWNER/NAME: ${hits.map(item => `${item.owner.login}/${item.name}`).join(', ')}.`) };
  return hits.length ? { row: hits[0] } : null;
}

// ---------- time ----------

function timeMs(value) {
  const ms = typeof value === 'number' ? value : typeof value === 'string' ? Date.parse(value) : NaN;
  return Number.isFinite(ms) ? ms : null;
}
function timeParts(ms, timeZone) {
  try {
    const parts = new Intl.DateTimeFormat('en-US', { timeZone, month: 'short', day: 'numeric', hour: '2-digit', minute: '2-digit', hourCycle: 'h23', timeZoneName: 'short' })
      .formatToParts(new Date(ms));
    const get = type => parts.find(part => part.type === type)?.value ?? '';
    return { text: `${get('month')} ${get('day')} ${get('hour')}:${get('minute')}`, zone: get('timeZoneName') };
  } catch { return null; }
}
function timeText(value, timeZone, withZone = false) {
  const ms = timeMs(value), parts = ms === null ? null : timeParts(ms, timeZone);
  return parts ? `${parts.text}${withZone ? ` ${parts.zone}` : ''}` : null;
}

// ---------- actions ----------

async function share(ctx, input) {
  const wanted = parseName(input.name);
  if (!wanted) return badName(input.name);
  const users = userList(input.with);
  if (users.failure) return users.failure;
  const group = absent(input.group) ? null : input.group;
  if (group !== null && (typeof group !== 'string' || !NAME.test(group))) return fail('input', `${shown(group)} is not a group name.`);
  if (!users.list.length && !group) return fail('input', 'Name the people to share with: --with USER,...');
  const failed = signIn(ctx, true);
  if (failed) return failed;
  const own = await ownLogin(ctx, wanted);
  if (own.failure) return own.failure;
  const reply = await call(ctx, 'POST', `v1/accounts/${enc(own.row.id)}/share`, { with: users.list, ...(group ? { group } : {}) });
  if (reply.failure) return reply.failure;
  const who = [users.list.length ? users.list.join(', ') : null, group ? `group ${group}` : null].filter(Boolean).join(' and ');
  const next = users.list.length ? ` Each person accepts it with: pdd accounts accept ${own.row.name}` : ' Each member accepts it once.';
  return { ok: true, exitCode: 0, message: `Shared ${own.row.name} with ${who}.${next}` };
}

async function unshare(ctx, input) {
  const wanted = parseName(input.name);
  if (!wanted) return badName(input.name);
  const users = userList(input.with);
  if (users.failure) return users.failure;
  if (!users.list.length) return fail('input', 'Name the people to stop sharing with: --with USER,...');
  const failed = signIn(ctx, true);
  if (failed) return failed;
  const own = await ownLogin(ctx, wanted);
  if (own.failure) return own.failure;
  const reply = await call(ctx, 'POST', `v1/accounts/${enc(own.row.id)}/unshare`, { with: users.list });
  if (reply.failure) return reply.failure;
  const ends = timeText(reply.json.accessExpiresAt, ctx.ports.timeZone, true);
  return { ok: true, exitCode: 0, message: `${users.list.join(', ')} ${users.list.length === 1 ? 'gets' : 'get'} no new copies of ${own.row.name}. `
    + `A copy that is already on a machine works until its access ends${ends ? ` (${ends})` : ''}.` };
}

async function accept(ctx, input) {
  const wanted = parseName(input.name);
  if (!wanted) return badName(input.name);
  const failed = signIn(ctx, false);
  if (failed) return failed;
  const found = await listing(ctx);
  if (found.failure) return found.failure;
  const hit = pickOne(found.json.invites, wanted, input.name);
  if (!hit) return fail('not_found', `No invite for ${input.name}. Run pdd accounts list.`);
  if (hit.failure) return hit.failure;
  const reply = await call(ctx, 'POST', `v1/accounts/${enc(hit.row.id)}/accept`);
  if (reply.failure) return reply.failure;
  return { ok: true, exitCode: 0, message: `You accepted ${hit.row.owner.login}/${hit.row.name}. Your steps use it after your own logins.` };
}

async function leave(ctx, input) {
  const wanted = parseName(input.name);
  if (!wanted) return badName(input.name);
  const failed = signIn(ctx, true);
  if (failed) return failed;
  const found = await listing(ctx);
  if (found.failure) return found.failure;
  const hit = pickOne(found.json.logins.filter(row => !isOwn(row, ctx.me)), wanted, input.name) ?? pickOne(found.json.invites, wanted, input.name);
  if (!hit) return fail('not_found', `You have no shared login named ${input.name}. Run pdd accounts list.`);
  if (hit.failure) return hit.failure;
  const reply = await call(ctx, 'POST', `v1/accounts/${enc(hit.row.id)}/leave`);
  if (reply.failure) return reply.failure;
  return { ok: true, exitCode: 0, message: `You left ${hit.row.owner.login}/${hit.row.name}. You get no new copies of it.` };
}

async function groupCreate(ctx, input) {
  if (typeof input.name !== 'string' || !NAME.test(input.name)) return fail('input', `${shown(input.name)} is not a group name. Use lower-case letters, digits, dots, dashes or underscores (at most 32).`);
  const users = userList(input.with);
  if (users.failure) return users.failure;
  const github = absent(input.github) ? null : input.github;
  if (users.list.length && github !== null || !users.list.length && github === null) return fail('input', 'Use one of --with USER,... or --github ORG[/TEAM].');
  if (github !== null) {
    const parts = typeof github === 'string' ? github.split('/') : [];
    if (!(parts.length === 1 || parts.length === 2) || !GH_LOGIN.test(parts[0]) || (parts.length === 2 && !TEAM.test(parts[1])))
      return fail('input', `${shown(github)} is not a GitHub org or ORG/TEAM.`);
  }
  const failed = signIn(ctx, false);
  if (failed) return failed;
  const reply = await call(ctx, 'POST', 'v1/groups', github === null ? { name: input.name, with: users.list } : { name: input.name, github });
  if (reply.failure) return reply.failure;
  if (github === null) return { ok: true, exitCode: 0, message: `Made group ${input.name} with ${users.list.join(', ')}. Each member accepts it once.` };
  return { ok: true, exitCode: 0, message: `Made group ${input.name}. It follows GitHub ${github.includes('/') ? 'team' : 'org'} ${github}. Each member accepts it once.` };
}

const AUDIT = ['at', 'action', 'login', 'actor', 'machine', 'detail'];
function auditCell(value, secrets) {
  if (typeof value === 'number' && Number.isFinite(value)) return String(value);
  return typeof value === 'string' && value.trim() ? safe(value, secrets) : '-';
}

async function serverLog(ctx, input) {
  const wanted = absent(input.name) ? null : parseName(input.name);
  if (!absent(input.name) && !wanted) return badName(input.name);
  const failed = signIn(ctx, true);
  if (failed) return failed;
  let rows;
  if (wanted) {
    const own = await ownLogin(ctx, wanted);
    if (own.failure) return own.failure;
    rows = [own.row];
  } else {
    const found = await listing(ctx);
    if (found.failure) return found.failure;
    rows = found.json.logins.filter(row => isOwn(row, ctx.me));
  }
  const all = [];
  for (const row of rows) {
    const reply = await call(ctx, 'GET', `v1/accounts/${enc(row.id)}/log`);
    if (reply.failure) return reply.failure;
    if (!Array.isArray(reply.json.rows) || !reply.json.rows.every(isObject))
      return fail('bad_reply', `The PDD login server sent a reply that pdd can not read (HTTP ${reply.status}). Nothing was saved.`);
    for (const item of reply.json.rows) all.push({ item, name: row.name });
  }
  const sorted = all.map((entry, index) => ({ ...entry, index, ms: timeMs(entry.item.at) ?? Infinity }))
    .sort((a, b) => a.ms - b.ms || a.index - b.index);
  const label = wanted ? input.name : 'your logins';
  if (input.json) {
    const out = sorted.map(({ item, name }) => Object.fromEntries(AUDIT.map(key => {
      const value = key === 'login' && absent(item.login) ? name : item[key];
      return [key, typeof value === 'string' ? safe(value, ctx.secrets) : typeof value === 'number' && Number.isFinite(value) ? value : null];
    })));
    return { ok: true, exitCode: 0, message: JSON.stringify({ rows: out }, null, 2) };
  }
  if (!sorted.length) return { ok: true, exitCode: 0, message: `No server log rows for ${label}.` };
  const zone = timeParts(sorted.find(entry => Number.isFinite(entry.ms))?.ms ?? Date.now(), ctx.ports.timeZone)?.zone ?? 'local time';
  const table = [['TIME', 'ACTION', 'LOGIN', 'BY', 'MACHINE', 'DETAIL'], ...sorted.map(({ item, name }) => [
    timeText(item.at, ctx.ports.timeZone) ?? '-', auditCell(item.action, ctx.secrets), auditCell(absent(item.login) ? name : item.login, ctx.secrets),
    auditCell(item.actor, ctx.secrets), auditCell(item.machine, ctx.secrets), auditCell(item.detail, ctx.secrets)])];
  const widths = table[0].map((_, column) => Math.max(...table.map(cells => cells[column].length)));
  const lines = table.map(cells => cells.map((cell, column) => cell.padEnd(widths[column])).join('  ').trimEnd());
  return { ok: true, exitCode: 0, message: [`Server log for ${label} (newest last). Times in ${zone}.`, '', ...lines].join('\n') };
}

const HANDLERS = { share, unshare, accept, leave, 'group-create': groupCreate, log: serverLog, upload: async () => fail('input', UPLOAD_TEXT) };

export async function runCloudAccounts(action, input = {}, ports = {}) {
  let result;
  if (!Object.hasOwn(HANDLERS, action)) result = fail('input', `Unknown pdd accounts server action: ${shown(action)}.`);
  else {
    const ctx = await connect(input ?? {}, ports ?? {});
    result = ctx.failure ?? await HANDLERS[action](ctx, input ?? {});
  }
  return { exitCode: result.exitCode, message: result.message };
}

// ---------- list ----------

const GROUP_FIELDS = ['id', 'name', 'owner', 'members', 'github'];
const ROW_FIELDS = ['id', 'name', 'owner', 'provider', 'plan', 'reset', 'stop', 'paused', 'state', 'week', 'fiveHour', 'accessExpiresAt', 'refreshOkAt', 'sharedWith', 'group'];
const pickRow = (row, secrets) => Object.fromEntries(ROW_FIELDS.filter(key => Object.hasOwn(row, key)).map(key => [key, clean(row[key], secrets)]));

export async function cloudList(input = {}, ports = {}) {
  input = input ?? {};
  const ctx = await connect(input, ports ?? {});
  if (ctx.failure) return ctx.failure;
  const failed = signIn(ctx, true);
  if (failed) return failed;
  const found = await listing(ctx);
  if (found.failure) return found.failure;
  const { json } = found, me = ctx.me;
  const logins = json.logins.map(row => {
    const shared = !isOwn(row, me);
    return { ...pickRow(row, ctx.secrets), display: displayOf(row, me), shared, kind: shared ? `shared by ${row.owner.login}` : 'cloud login' };
  });
  const invites = json.invites.map(row => ({ ...clean({ id: row.id, name: row.name, owner: { login: row.owner.login }, ...(Object.hasOwn(row, 'via') ? { via: row.via } : {}) }, ctx.secrets),
    display: `${row.owner.login}/${row.name}` }));
  const groups = json.groups.map(group => clean(Object.fromEntries(GROUP_FIELDS.filter(key => Object.hasOwn(group, key)).map(key => [key, group[key]])), ctx.secrets));
  const inviteLines = json.invites.map(row => {
    const twin = json.invites.filter(other => other.name === row.name).length > 1;
    const via = typeof row.via === 'string' && row.via.startsWith('group:') ? ` (group ${safe(row.via.slice(6), ctx.secrets).slice(0, 40)})` : '';
    return `${row.owner.login} shares ${row.name} with you${via}. Accept it with: pdd accounts accept ${twin ? `${row.owner.login}/${row.name}` : row.name}`;
  });
  const byId = new Map(json.logins.map(row => [row.id, displayOf(row, me)]));
  const order = json.order.filter(id => byId.has(id)).map(id => byId.get(id));
  return { ok: true, url: ctx.base, me: { ...me }, logins, invites, order, groups, inviteLines };
}

// ---------- the copy desk and the run home ----------

export async function cloudCopy(input = {}, ports = {}) {
  input = input ?? {};
  const ctx = await connect(input, ports ?? {});
  if (ctx.failure) return ctx.failure;
  const provider = input.provider ?? 'codex';
  if (provider === 'claude') return fail('input', CLAUDE_TEXT);
  if (provider !== 'codex') return fail('input', `pdd can not ask the PDD login server for a ${shown(provider)} login.`);
  const skip = input.skip ?? [];
  if (!Array.isArray(skip) || !skip.every(id => typeof id === 'string' && ID.test(id))) return fail('input', 'skip must list server login ids.');
  if (!absent(input.pin) && !(typeof input.pin === 'string' && ID.test(input.pin))) return fail('input', 'pin must be a server login id.');
  const failed = signIn(ctx, true);
  if (failed) return failed;
  const reply = await call(ctx, 'POST', 'v1/copy', { provider, ...(skip.length ? { skip } : {}), ...(absent(input.pin) ? {} : { pin: input.pin }) });
  if (reply.failure) {
    if (reply.failure.code !== 'all_out') return reply.failure;
    const raw = isObject(reply.json?.error?.earliest) ? reply.json.error.earliest : isObject(reply.json?.earliest) ? reply.json.earliest : null;
    let earliest = null;
    if (raw && typeof raw.id === 'string' && ID.test(raw.id)) {
      const found = await listing(ctx), row = found.failure ? null : found.json.logins.find(item => item.id === raw.id);
      earliest = { id: raw.id, name: row ? displayOf(row, ctx.me) : null, at: timeMs(raw.at) };
    }
    const when = earliest?.at === null || earliest?.at === undefined ? null : timeText(earliest.at, ctx.ports.timeZone, true);
    const next = !when ? '' : earliest.name ? ` Next free: ${earliest.name} at ${when}.` : ` Next free at ${when}.`;
    return { ...fail('all_out', `No login on the PDD login server has quota now.${next}`), earliest };
  }
  const { login, auth, expiresAt, copyId } = reply.json;
  if (!validRow(login) || typeof auth !== 'string')
    return fail('bad_reply', `The PDD login server sent a reply that pdd can not read (HTTP ${reply.status}). Nothing was saved.`);
  const name = displayOf(login, ctx.me);
  const home = writeCopyHome({ env: ctx.env, name, auth }, ports);
  if (!home.ok) return home;
  return { ok: true, name, login: pickRow(login, ctx.secrets), home: home.home,
    expiresAt: timeMs(expiresAt), copyId: typeof copyId === 'string' && ID.test(copyId) ? copyId : null };
}

// A key named refresh_token anywhere, with a value other than "", null or absent, could renew the login.
function canRenew(root) {
  const stack = [root];
  while (stack.length) {
    const value = stack.pop();
    if (Array.isArray(value)) stack.push(...value);
    else if (isObject(value)) for (const [key, item] of Object.entries(value)) {
      if (key === 'refresh_token' && item !== '' && item !== null && item !== undefined) return true;
      stack.push(item);
    }
  }
  return false;
}

// Make the folder (0700) when it is missing; false for a link or a file. The caller sets 0700 after its own checks.
const absentKey = value => value === undefined || value === null;

function realFolder(path) {
  try { mkdirSync(path, { mode: 0o700 }); } catch (error) { if (error?.code !== 'EEXIST') throw error; }
  const stat = lstatSync(path);
  return !stat.isSymbolicLink() && stat.isDirectory();
}

function atomicWrite(path, text) {
  const temporary = `${path}.${process.pid}.${randomBytes(6).toString('hex')}.tmp`;
  let fd = null;
  try {
    fd = openSync(temporary, constants.O_WRONLY | constants.O_CREAT | constants.O_EXCL, 0o600);
    writeFileSync(fd, text); fsyncSync(fd); closeSync(fd); fd = null;
    chmodSync(temporary, 0o600);
    renameSync(temporary, path);
    chmodSync(path, 0o600);
  } catch (error) {
    if (fd !== null) try { closeSync(fd); } catch { /* already closed */ }
    try { unlinkSync(temporary); } catch { /* not made or already moved */ }
    throw error;
  }
}

function hasFileStore(path) {
  try {
    if (!lstatSync(path).isFile()) return false;
    const topLevel = readFileSync(path, 'utf8').split(/^\s*\[/m)[0];
    return /^\s*cli_auth_credentials_store\s*=\s*"file"\s*(?:#.*)?$/m.test(topLevel);
  } catch { return false; }
}

const tilde = (path, home) => { const rel = relative(home, path); return rel && !rel.startsWith('..') && !isAbsolute(rel) ? `~${sep}${rel}` : path; };

export function writeCopyHome(input = {}, ports = {}) {
  const { env = process.env, name, auth } = input ?? {};
  const wanted = parseName(name);
  if (!wanted) return badName(name);
  const label = wanted.owner ? `${wanted.owner}/${wanted.name}` : wanted.name;
  let parsed = null;
  try { parsed = typeof auth === 'string' && Buffer.byteLength(auth) <= MAX_AUTH ? JSON.parse(auth) : null; } catch { parsed = null; }
  if (isObject(parsed) && canRenew(parsed)) return fail('unsafe_copy', `The login server sent a copy of ${label} that can renew itself. pdd did not save it. Tell the server owner.`);
  if (isObject(parsed) && !absentKey(parsed.OPENAI_API_KEY)) return fail('unsafe_copy', `The login server sent a copy of ${label} with an API key. pdd did not save it. Tell the server owner.`);
  const tokens = isObject(parsed) ? parsed.tokens : null;
  if (!isObject(tokens) || typeof tokens.access_token !== 'string' || !tokens.access_token || tokens.refresh_token !== '')
    return fail('bad_copy', `The login server sent a copy of ${label} that pdd can not read. pdd did not save it.`);
  const { home, stateDir } = folders(env), homes = join(stateDir, 'homes');
  const chain = wanted.owner ? [homes, join(homes, `@${wanted.owner.toLowerCase()}`)] : [homes];
  const folder = join(chain.at(-1), wanted.name);
  const refuse = path => fail('not_copy_home', `${tilde(path, home)} is not a folder that pdd made for copies. pdd did not write there.`);
  try {
    mkdirSync(stateDir, { recursive: true, mode: 0o700 });
    for (const path of chain) { if (!realFolder(path)) return refuse(path); chmodSync(path, 0o700); }
    if (!realFolder(folder)) return refuse(folder);
    const entries = readdirSync(folder);
    if (!entries.includes(MARKER)) {
      if (entries.length) return refuse(folder);
      // Another step may make the same new folder at the same time; its marker is as good as this one.
      let fd = null;
      try { fd = openSync(join(folder, MARKER), constants.O_WRONLY | constants.O_CREAT | constants.O_EXCL, 0o600); } catch (error) { if (error?.code !== 'EEXIST') throw error; }
      if (fd !== null) try { writeFileSync(fd, 'pdd copy home v1\n'); } finally { closeSync(fd); }
    }
    chmodSync(folder, 0o700);
    const config = join(folder, 'config.toml');
    if (!hasFileStore(config)) atomicWrite(config, STORE_LINE);
    atomicWrite(join(folder, 'auth.json'), `${JSON.stringify(parsed, null, 2)}\n`);
  } catch (error) {
    return fail('home_error', `pdd could not write the copy of ${label} (${String(error?.code ?? 'file error').replace(/[^A-Z0-9_]/g, '').slice(0, 20) || 'file error'}).`);
  }
  return { ok: true, home: folder };
}
