// Generated from prompts/cli/accounts-store.prompt.md (sha256: 0449d63226008f67669a04c1ba54dacc7042ab2726b29fb481dd03eefb93e598).
import * as nodeFs from 'node:fs/promises';
import { randomBytes } from 'node:crypto';
import { userInfo } from 'node:os';
import { basename, dirname, isAbsolute, join } from 'node:path';

export class PoolError extends Error {
  constructor(code, message) { super(message); this.name = 'PoolError'; this.code = code; }
}

const NAME = /^[a-z0-9][a-z0-9._-]{0,31}$/;
const SHARED = /^[A-Za-z0-9][A-Za-z0-9-]{0,38}\/[a-z0-9][a-z0-9._-]{0,31}$/;
const ACTION = /^[a-z][a-z-]{0,31}$/;
const LOCK_STALE_MS = 30_000, LOCK_WAIT_MS = 5_000, LOCK_STEP_MS = 50;
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const emptyPool = () => ({ version: 1, order: [], logins: [], server: null });
const tools = ports => ({
  fs: ports.fs ?? nodeFs,
  now: ports.now ?? Date.now,
  sleep: ports.sleep ?? (ms => new Promise(resolve => setTimeout(resolve, ms))),
});

function homeFolder(env, ports) {
  if (isAbsolute(env.HOME ?? '')) return env.HOME;
  try {
    const value = (ports.userInfo ?? userInfo)().homedir;
    if (typeof value === 'string' && isAbsolute(value)) return value;
  } catch { /* No account home: the caller gets one clear line. */ }
  throw new PoolError('no-home', 'pdd accounts needs an absolute home folder; set HOME to an absolute path.');
}

export function poolPaths(env = process.env, ports = {}) {
  const config = isAbsolute(env.XDG_CONFIG_HOME ?? '') ? env.XDG_CONFIG_HOME : null;
  const state = isAbsolute(env.XDG_STATE_HOME ?? '') ? env.XDG_STATE_HOME : null;
  const home = config && state ? null : homeFolder(env, ports);
  const configDir = join(config ?? join(home, '.config'), 'pdd');
  const stateDir = join(state ?? join(home, '.local', 'state'), 'pdd', 'accounts');
  return { configDir, stateDir, poolFile: join(configDir, 'accounts.json'), logFile: join(stateDir, 'log.jsonl'),
    usageFile: join(stateDir, 'usage.json'), machineFile: join(configDir, 'machine.json') };
}

const percent = value => typeof value === 'number' && Number.isFinite(value) && value >= 1 && value <= 100;

// Returns the pool with defaults filled in, or the first broken rule in a few words.
function checkPool(value) {
  if (!object(value)) return { problem: 'it is not a JSON object' };
  if (value.version !== 1) return { problem: 'its version is not 1' };
  const order = value.order ?? [];
  if (!Array.isArray(order) || order.some(name => typeof name !== 'string' || !name)) return { problem: 'order is not a list of names' };
  const server = value.server ?? null;
  if (server !== null && !(object(server) && typeof server.url === 'string' && server.url)) return { problem: 'server is not null or an object with a url' };
  if (value.homesDir !== undefined && !(typeof value.homesDir === 'string' && isAbsolute(value.homesDir))) return { problem: 'homesDir is not an absolute path' };
  if (!Array.isArray(value.logins ?? [])) return { problem: 'logins is not a list' };
  const names = new Set(), logins = [];
  for (const [index, row] of (value.logins ?? []).entries()) {
    const at = `login ${index + 1}`;
    if (!object(row)) return { problem: `${at} is not an object` };
    if (typeof row.name !== 'string' || !NAME.test(row.name)) return { problem: `${at} has no valid name` };
    const name = row.name;
    if (names.has(name)) return { problem: `the name ${name} is used twice` };
    names.add(name);
    if (!['codex', 'claude'].includes(row.provider)) return { problem: `${name} has no valid provider` };
    if (typeof row.home !== 'string' || !isAbsolute(row.home)) return { problem: `${name} has no absolute home` };
    const next = { ...row, source: row.source ?? 'import', mode: row.mode ?? 'local', paused: row.paused ?? false, reset: row.reset ?? 'never' };
    if (!['import', 'add'].includes(next.source)) return { problem: `${name} has no valid source` };
    if (!['local', 'cloud'].includes(next.mode)) return { problem: `${name} has no valid mode` };
    if (typeof next.paused !== 'boolean') return { problem: `${name} has no valid paused value` };
    if (!['never', 'ask', 'auto'].includes(next.reset)) return { problem: `${name} has no valid reset setting` };
    if (row.stop !== undefined && !object(row.stop)) return { problem: `${name} has no valid stop lines` };
    const stop = { ...(row.stop ?? {}), week: row.stop?.week ?? 97, fiveHour: row.stop?.fiveHour ?? 97 };
    if (!percent(stop.week) || !percent(stop.fiveHour)) return { problem: `${name} has a stop line outside 1 to 100` };
    next.stop = stop;
    if (row.addedAt !== undefined && (typeof row.addedAt !== 'string' || Number.isNaN(Date.parse(row.addedAt)))) return { problem: `${name} has no valid addedAt time` };
    logins.push(next);
  }
  return { pool: { ...value, version: 1, order: [...order], logins, server } };
}

const invalidFile = (path, problem) => new PoolError('invalid',
  `The pool file ${path} is not valid: ${problem}. pdd did not change it. Fix or move the file, then try again.`);

async function readChecked(path, fs) {
  let text;
  try { text = await fs.readFile(path, 'utf8'); }
  catch (error) { if (error?.code === 'ENOENT') return emptyPool(); throw error; }
  let value;
  try { value = JSON.parse(text); } catch { throw invalidFile(path, 'it is not valid JSON'); }
  const checked = checkPool(value);
  if (checked.problem) throw invalidFile(path, checked.problem);
  return checked.pool;
}

export async function readPool({ env = process.env } = {}, ports = {}) {
  return readChecked(poolPaths(env, ports).poolFile, tools(ports).fs);
}

async function takeLock(lock, { fs, now, sleep }) {
  const token = randomBytes(8).toString('hex'), started = now();
  for (;;) {
    try {
      const handle = await fs.open(lock, 'wx', 0o600);
      try { await handle.writeFile(`${JSON.stringify({ pid: process.pid, token, at: new Date(now()).toISOString() })}\n`); }
      finally { await handle.close(); }
      return token;
    } catch (error) { if (error?.code !== 'EEXIST') throw error; }
    try {
      const info = await fs.stat(lock);
      // A crashed process leaves its lock behind; after 30 s nobody still works under it.
      if (now() - info.mtimeMs > LOCK_STALE_MS) { await fs.unlink(lock).catch(() => {}); continue; }
    } catch (error) { if (error?.code === 'ENOENT') continue; throw error; }
    if (now() - started >= LOCK_WAIT_MS) throw new PoolError('busy', `Another pdd process is changing the pool (${lock}). Try again.`);
    await sleep(LOCK_STEP_MS);
  }
}

async function releaseLock(lock, token, fs) {
  try {
    const text = await fs.readFile(lock, 'utf8');
    if (JSON.parse(text).token === token) await fs.unlink(lock);
  } catch { /* A lock that another process took over after it went stale is not ours to remove. */ }
}

async function writeAtomic(path, text, fs) {
  const temp = join(dirname(path), `.${basename(path)}.${process.pid}.${randomBytes(6).toString('hex')}.tmp`);
  let handle;
  try {
    handle = await fs.open(temp, 'wx', 0o600);
    await handle.writeFile(text);
    await handle.sync();
    await handle.close(); handle = null;
    await fs.rename(temp, path);
  } catch (error) {
    if (handle) await handle.close().catch(() => {});
    await fs.unlink(temp).catch(() => {});
    throw error;
  }
}

export async function updatePool({ env = process.env } = {}, change, ports = {}) {
  const tool = tools(ports), { configDir, poolFile } = poolPaths(env, ports), lock = `${poolFile}.lock`;
  await tool.fs.mkdir(configDir, { recursive: true, mode: 0o700 });
  const token = await takeLock(lock, tool);
  try {
    const pool = await readChecked(poolFile, tool.fs);
    const checked = checkPool(await change(pool));
    if (checked.problem) throw new PoolError('invalid-change', `pdd did not save the pool: ${checked.problem}.`);
    await writeAtomic(poolFile, `${JSON.stringify(checked.pool, null, 2)}\n`, tool.fs);
    return checked.pool;
  } finally { await releaseLock(lock, token, tool.fs); }
}

export function orderedLogins(pool) {
  const logins = pool?.logins ?? [], byName = new Map(logins.map(row => [row.name, row])), placed = new Set(), result = [];
  for (const name of pool?.order ?? []) {
    if (!byName.has(name) || placed.has(name)) continue;
    placed.add(name); result.push(byName.get(name));
  }
  const time = row => typeof row.addedAt === 'string' && !Number.isNaN(Date.parse(row.addedAt)) ? Date.parse(row.addedAt) : Infinity;
  const rest = logins.filter(row => !placed.has(row.name)).map((row, index) => ({ row, index }))
    .sort((a, b) => time(a.row) - time(b.row) || a.index - b.index).map(item => item.row);
  return [...result, ...rest].map((row, index) => ({ ...row, position: index + 1 }));
}

// Email-like and JWT-like text never reaches the log, even when a caller passes it by mistake.
const scrub = text => text.replace(/[^\s@]+@[^\s@]+\.[^\s@]+/g, '[removed]')
  .replace(/eyJ[A-Za-z0-9_-]*\.[A-Za-z0-9_-]+\.[A-Za-z0-9_-]*/g, '[removed]');

export async function appendLog({ env = process.env } = {}, row = {}, ports = {}) {
  const tool = tools(ports), { stateDir, logFile } = poolPaths(env, ports);
  if (typeof row.action !== 'string' || !ACTION.test(row.action)) throw new PoolError('invalid-log', 'A log row needs a short action word.');
  const login = row.login ?? null;
  if (login !== null && !(typeof login === 'string' && (NAME.test(login) || SHARED.test(login)))) throw new PoolError('invalid-log', 'A log row needs a valid login name or null.');
  const saved = { at: row.at ?? new Date(tool.now()).toISOString(), action: row.action, login,
    detail: scrub(String(row.detail ?? '').replace(/[\r\n]+/g, ' ')).slice(0, 300) };
  await tool.fs.mkdir(stateDir, { recursive: true, mode: 0o700 });
  await tool.fs.appendFile(logFile, `${JSON.stringify(saved)}\n`, { mode: 0o600 });
  return saved;
}

export async function readLog({ env = process.env, name, limit = 100 } = {}, ports = {}) {
  let text;
  try { text = await tools(ports).fs.readFile(poolPaths(env, ports).logFile, 'utf8'); }
  catch (error) { if (error?.code === 'ENOENT') return []; throw error; }
  const rows = [];
  for (const line of text.split('\n')) {
    if (!line.trim()) continue;
    let row; try { row = JSON.parse(line); } catch { continue; }
    if (!object(row) || typeof row.action !== 'string' || typeof row.at !== 'string') continue;
    if (name !== undefined && name !== null && row.login !== name) continue;
    rows.push({ at: row.at, action: row.action, login: row.login ?? null, detail: typeof row.detail === 'string' ? row.detail : '' });
  }
  return limit > 0 ? rows.slice(-limit) : [];
}
