// Generated from prompts/cli/accounts-usage.prompt.md (sha256: de4d01f42f1812ba4009adc02250ba4f037ac51c3610b8a13303a72a0f74621b).
import * as realFs from 'node:fs/promises';
import { constants } from 'node:fs';
import { homedir } from 'node:os';
import { dirname, isAbsolute, join } from 'node:path';
import { codexLoginFacts, withAccessOnlyHome } from './accounts-login.mjs';
import { readCodexRateLimitsReply } from './codex-limits.mjs';

const ACCESS_MARGIN_MS = 10 * 60 * 1000;
const STATES = new Set(['ok', 'expired', 'no-login', 'needs-sign-in', 'unknown']);
const REASONS = new Set(['limit', 'credits']);
const CREDIT_TYPES = new Set(['workspace_owner_credits_depleted', 'workspace_member_credits_depleted']);
const CLIENT = { name: 'pdd_accounts', title: 'PDD accounts', version: '1' };
const TRANSPORT_NOTES = {
  spawn: 'codex did not start',
  exit: 'codex app-server ended early',
  timeout: 'usage read timed out',
  output: 'codex app-server sent too much output',
  protocol: 'bad reply from codex app-server',
  error: 'codex app-server refused the read',
};
const MAX_CACHE_BYTES = 1024 * 1024;
const READ_NO_BLOCK = constants.O_RDONLY | constants.O_NONBLOCK;

const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const finite = value => typeof value === 'number' && Number.isFinite(value);
const clock = now => typeof now === 'function' ? now : finite(now) ? () => now : Date.now;

function row(state, fields = {}) {
  return { state, plan: null, week: null, fiveHour: null, accessExpiresAt: null, readAt: null,
    limitedUntil: null, limitReason: null, resets: null, note: '', ...fields };
}

// The facts checks, shared by the first look and the copied file.
function factsRow(facts, nowMs) {
  if (facts.state === 'none') return row('no-login', { note: 'no Codex login in this folder' });
  if (facts.state === 'unreadable') return row('unknown', { note: 'login file is unreadable' });
  if (facts.accessExpiresAt == null) return row('unknown', { note: 'access end is unknown; not read' });
  if (facts.accessExpiresAt <= nowMs + ACCESS_MARGIN_MS)
    return row('expired', { accessExpiresAt: facts.accessExpiresAt, note: 'access ended; this read never refreshes' });
  return null;
}

const validWindow = w => object(w) && finite(w.usedPercent) && w.usedPercent >= 0
  && (w.resetsAt == null || finite(w.resetsAt) && w.resetsAt >= 0 && w.resetsAt <= 8.64e12);
const ms = seconds => seconds == null ? null : seconds * 1000;

function usageFromReply(reply) {
  if (!object(reply)) return row('unknown', { note: 'bad usage reply' });
  const bucket = reply.rateLimitsByLimitId?.codex ?? reply.rateLimits;
  if (!object(bucket)) return row('unknown', { note: 'bad usage reply' });
  const windows = [bucket.primary, bucket.secondary].filter(w => w != null);
  if (!windows.every(validWindow)) return row('unknown', { note: 'bad usage reply' });
  const reached = typeof bucket.rateLimitReachedType === 'string' && bucket.rateLimitReachedType.trim() !== '';
  if (!windows.length && !reached) return row('unknown', { note: 'no usage windows in reply' });
  const pick = mins => {
    const found = windows.filter(w => w.windowDurationMins === mins);
    if (!found.length) return null;
    const best = found.reduce((a, b) => b.usedPercent > a.usedPercent ? b : a);
    return { usedPercent: best.usedPercent, resetsAt: ms(best.resetsAt) };
  };
  const blocked = windows.filter(w => w.usedPercent >= 100);
  const limited = blocked.length > 0 || reached || reply.ordinaryUsageAllowed === false;
  const ends = blocked.length ? blocked : windows;
  return row('ok', {
    plan: typeof bucket.planType === 'string' && bucket.planType !== '' ? bucket.planType : null,
    week: pick(10080), fiveHour: pick(300),
    limitedUntil: limited && ends.length && ends.every(w => w.resetsAt != null) ? Math.max(...ends.map(w => w.resetsAt * 1000)) : null,
    limitReason: limited ? (reached && CREDIT_TYPES.has(bucket.rateLimitReachedType) ? 'credits' : 'limit') : null,
    resets: null,
  });
}

function childEnv(env, tempHome) {
  const next = { ...env, CODEX_HOME: tempHome };
  for (const key of ['OPENAI_API_KEY', 'CODEX_API_KEY', 'CODEX_ACCESS_TOKEN']) delete next[key];
  return next;
}

async function readCodex(login, { env, now, command }, ports) {
  if (login.provider !== 'codex') return row('unknown', { note: 'usage read is only for codex logins' });
  if (typeof login.home !== 'string' || login.home === '' || !isAbsolute(login.home))
    return row('unknown', { note: 'login folder is not an absolute path' });
  const loginPorts = { fs: ports.fs, tmpdir: ports.tmpdir };
  const early = factsRow(await codexLoginFacts(login.home, loginPorts), now());
  if (early) return early;
  try {
    return await withAccessOnlyHome(login.home, async (tempHome, copied) => {
      const late = factsRow(copied, now());
      if (late) return late;
      const read = await readCodexRateLimitsReply({ command, cwd: tempHome, env: childEnv(env, tempHome), clientInfo: CLIENT },
        { spawn: ports.spawn });
      const result = read.ok ? usageFromReply(read.reply) : row('unknown', { note: TRANSPORT_NOTES[read.reason] ?? 'usage read failed' });
      return { ...result, accessExpiresAt: copied.accessExpiresAt };
    }, loginPorts);
  } catch (error) {
    if (error?.code === 'PDD_NO_LOGIN') return factsRow({ state: error.state, accessExpiresAt: null }, now()) ?? row('unknown', { note: 'login file is unreadable' });
    if (error?.code === 'PDD_TEMP_HOME_LEFT') return row('unknown', { note: `temporary login folder not removed: ${error.path}` });
    return row('unknown', { note: 'temporary login folder failed' });
  }
}

export async function readLoginUsage(login, { env = process.env, now, command = 'codex' } = {}, ports = {}) {
  const time = clock(now);
  let result;
  try {
    result = object(login) ? await readCodex(login, { env, now: time, command }, ports) : row('unknown', { note: 'usage read failed' });
  } catch {
    result = row('unknown', { note: 'usage read failed' });
  }
  return { ...result, readAt: time() };
}

export async function readAllUsage(logins, { env = process.env, now, command = 'codex', save = true } = {}, ports = {}) {
  if (!Array.isArray(logins) || !logins.every(login => object(login) && typeof login.name === 'string' && login.name !== ''))
    throw new TypeError('logins must be an array of pool logins.');
  const results = new Array(logins.length);
  let next = 0;
  const worker = async () => {
    while (next < logins.length) {
      const index = next++;
      results[index] = await readLoginUsage(logins[index], { env, now, command }, ports);
    }
  };
  await Promise.all(Array.from({ length: Math.min(4, logins.length) }, worker));
  // fromEntries makes own keys, so a name such as __proto__ stays data.
  const rows = Object.fromEntries(logins.map((login, index) => [login.name, results[index]]));
  return save ? saveUsage({ env }, rows, ports) : rows;
}

// ---- cache

function statePaths(env) {
  const home = typeof env.HOME === 'string' && isAbsolute(env.HOME) ? env.HOME : homedir();
  const stateDir = typeof env.XDG_STATE_HOME === 'string' && isAbsolute(env.XDG_STATE_HOME)
    ? join(env.XDG_STATE_HOME, 'pdd', 'accounts') : join(home, '.local', 'state', 'pdd', 'accounts');
  const usageFile = join(stateDir, 'usage.json');
  return { stateDir, usageFile, lockFile: `${usageFile}.lock` };
}

const time = value => finite(value) ? value : null;
const windowOf = value => object(value) && finite(value.usedPercent) ? { usedPercent: value.usedPercent, resetsAt: time(value.resetsAt) } : null;
function cleanRow(value) {
  const r = object(value) ? value : {};
  return {
    state: STATES.has(r.state) ? r.state : 'unknown',
    plan: typeof r.plan === 'string' ? r.plan : null,
    week: windowOf(r.week), fiveHour: windowOf(r.fiveHour),
    accessExpiresAt: time(r.accessExpiresAt), readAt: time(r.readAt), limitedUntil: time(r.limitedUntil),
    limitReason: REASONS.has(r.limitReason) ? r.limitReason : null,
    resets: object(r.resets) && Number.isInteger(r.resets.left) && r.resets.left >= 0 ? { left: r.resets.left, expiresAt: time(r.resets.expiresAt) } : null,
    note: typeof r.note === 'string' ? r.note : '',
  };
}

// The cache rows by name, as a Map: a login name never meets an inherited member.
async function readCache(file, fs) {
  let text;
  try {
    const handle = await fs.open(file, READ_NO_BLOCK);
    try {
      const stat = await handle.stat();
      if (!stat.isFile() || stat.size > MAX_CACHE_BYTES) return new Map();
      text = await handle.readFile('utf8');
    } finally { await handle.close().catch(() => {}); }
  } catch { return new Map(); }
  if (Buffer.byteLength(text) > MAX_CACHE_BYTES) return new Map();
  let doc;
  try { doc = JSON.parse(text); } catch { return new Map(); }
  if (!object(doc) || doc.version !== 1 || !object(doc.rows)) return new Map();
  return new Map(Object.entries(doc.rows).filter(([, value]) => object(value)).map(([name, value]) => [name, cleanRow(value)]));
}

export async function loadUsage({ env = process.env } = {}, ports = {}) {
  return Object.fromEntries(await readCache(statePaths(env).usageFile, { ...realFs, ...ports.fs }));
}

async function updateCache(env, change, ports) {
  const fs = { ...realFs, ...ports.fs };
  const sleep = ports.sleep ?? (wait => new Promise(resolve => setTimeout(resolve, wait)));
  const { stateDir, usageFile, lockFile } = statePaths(env);
  await fs.mkdir(stateDir, { recursive: true, mode: 0o700 });
  await fs.chmod(stateDir, 0o700);
  let locked = false;
  for (let attempt = 0; attempt < 100 && !locked; attempt++) {
    try {
      await (await fs.open(lockFile, 'wx', 0o600)).close();
      locked = true;
    } catch (error) {
      if (error?.code !== 'EEXIST') throw error;
      const stat = await fs.stat(lockFile).catch(() => null);
      if (stat && Date.now() - stat.mtimeMs > 30_000) { await fs.rm(lockFile, { force: true }); continue; }
      await sleep(50);
    }
  }
  if (!locked) throw Object.assign(new Error('The usage cache is locked by another pdd process.'), { code: 'PDD_USAGE_LOCKED' });
  try {
    const rows = await readCache(usageFile, fs);
    const result = change(rows);
    const temp = join(dirname(usageFile), `.usage.json.${process.pid}.${Date.now()}.tmp`);
    try {
      const handle = await fs.open(temp, 'wx', 0o600);
      try {
        await handle.writeFile(JSON.stringify({ version: 1, rows: Object.fromEntries(rows) }, null, 2) + '\n');
        await handle.sync();
      } finally { await handle.close(); }
      await fs.rename(temp, usageFile);
    } catch (error) {
      await fs.rm(temp, { force: true }).catch(() => {});
      throw error;
    }
    return result;
  } finally {
    await fs.rm(lockFile, { force: true }).catch(() => {});
  }
}

const activeLimit = (old, next) => old && old.limitReason != null
  && (old.limitedUntil == null || next.readAt == null || old.limitedUntil > next.readAt);

export async function saveUsage({ env = process.env } = {}, rows, ports = {}) {
  if (!object(rows)) throw new TypeError('rows must be an object of usage rows by login name.');
  return updateCache(env, cached => {
    const saved = [];
    for (const [name, value] of Object.entries(rows)) {
      const next = cleanRow(value), old = cached.get(name);
      if (next.state !== 'ok' && activeLimit(old, next)) { next.limitedUntil = old.limitedUntil; next.limitReason = old.limitReason; }
      cached.set(name, next); saved.push([name, { ...next }]);
    }
    return Object.fromEntries(saved);
  }, ports);
}

export async function markLimited({ env = process.env } = {}, name, untilMs, reason, ports = {}) {
  if (typeof name !== 'string' || name === '') throw new TypeError('name must be a login name.');
  if (untilMs !== null && !(finite(untilMs) && untilMs >= 0)) throw new TypeError('untilMs must be epoch milliseconds or null.');
  if (!REASONS.has(reason)) throw new TypeError('reason must be limit or credits.');
  return updateCache(env, cached => {
    const next = cached.get(name) ?? row('unknown', { note: 'not read yet' });
    next.limitedUntil = untilMs; next.limitReason = reason;
    cached.set(name, next);
    return { ...next };
  }, ports);
}
