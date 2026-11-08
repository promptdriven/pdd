// Generated from prompts/cli/interpreter-queue.prompt.md (sha256: ef7206e3d86babe317e73bc46f6ef6d9090181c9409c6ca4081446e3e8e1ea99).
import * as files from 'node:fs';
import { join, isAbsolute, resolve } from 'node:path';
import { randomUUID } from 'node:crypto';

const alive = pid => { try { process.kill(pid, 0); return true; } catch (error) { return error.code !== 'ESRCH'; } };
const problem = error => Object.assign(new Error(`Machine interpreter queue unavailable: ${error.message}`), { code: 'local-state-unavailable' });
function portsFor(env = process.env, ports = {}) {
  const root = env.PDD_INTERPRETER_QUEUE ?? `/tmp/pdd-interpreter-${process.getuid?.() ?? 'user'}`;
  if (!isAbsolute(root)) throw Error('The interpreter queue needs an absolute path.');
  const p = { fs: files, now: Date.now, sleep: ms => new Promise(done => setTimeout(done, ms)), alive, pid: process.pid,
    uuid: randomUUID, interrupted: () => false, say: () => {}, ...ports, root };
  const raw = env.PDD_INTERPRETER_CONCURRENCY;
  p.limit = raw === undefined ? 2 : /^[1-9][0-9]*$/.test(String(raw)) && Number.isSafeInteger(Number(raw)) ? Number(raw) : 2;
  if (raw !== undefined && p.limit === 2 && String(raw) !== '2') p.say('Warning: PDD_INTERPRETER_CONCURRENCY must be a positive safe integer; using 2.');
  return p;
}
export function interpreterQueueEnvironment(env = process.env) {
  const p = portsFor(env);
  return { PDD_INTERPRETER_QUEUE: p.root, PDD_INTERPRETER_CONCURRENCY: String(p.limit) };
}
function read(p, path) {
  const stat = p.fs.lstatSync(path);
  if (!stat.isFile() || stat.isSymbolicLink()) throw Error('Queue record is not a regular file.');
  return JSON.parse(p.fs.readFileSync(path, 'utf8'));
}
function save(p, name, row) {
  const path = join(p.root, name), temporary = `${path}.${p.uuid()}.tmp`;
  try { p.fs.writeFileSync(temporary, JSON.stringify(row), { mode: 0o600, flag: 'wx' }); p.fs.renameSync(temporary, path); }
  finally { try { p.fs.unlinkSync(temporary); } catch {} }
}
function records(p) {
  let names;
  try {
    const rootStat = p.fs.lstatSync(p.root);
    if (!rootStat.isDirectory() || rootStat.isSymbolicLink()) throw Error('Queue root is not a directory.');
    names = p.fs.readdirSync(p.root);
  } catch (error) { if (error.code === 'ENOENT') return []; throw error; }
  return names.filter(name => /^ticket-.*\.json$/.test(name)).map(name => {
    const row = read(p, join(p.root, name));
    if (!Number.isSafeInteger(row.ticket) || row.ticket < 1 || name !== `ticket-${row.ticket}.json`
      || !Number.isSafeInteger(row.pid) || row.pid <= 0 || typeof row.cwd !== 'string' || !isAbsolute(row.cwd)
      || typeof row.origin !== 'string' || typeof row.requestId !== 'string' || !['lint', 'check'].includes(row.kind)
      || !['waiting', 'running', 'finished'].includes(row.state) || !Number.isFinite(row.queuedAt)
      || row.startedAt !== null && !Number.isFinite(row.startedAt) || row.endedAt !== null && !Number.isFinite(row.endedAt)
      || ![null, 'verdict', 'unknown', 'busy', 'refused', 'not_sent'].includes(row.outcome)
      || typeof row.dispatched !== 'boolean'
      || ![row.activeAtStart, row.activeAtEnd].every(n => n === null || Number.isSafeInteger(n) && n >= 0)) throw Error('Unreadable interpreter queue ownership.');
    // A dead owner proves only that a still-waiting ticket was not dispatched.
    if ((row.state === 'waiting' || row.state === 'running' && !row.dispatched) && !p.alive(row.pid)) return { ...row, state: 'finished',
      endedAt: p.fs.lstatSync(join(p.root, name)).mtimeMs, outcome: 'not_sent' };
    return row;
  }).sort((a, b) => a.ticket - b.ticket);
}
function capacity(p) {
  let row;
  try { row = read(p, join(p.root, 'capacity.json')); } catch (error) { if (error.code === 'ENOENT') return { limit: p.limit, until: 0, blockedUntil: 0 }; throw error; }
  if (!Number.isSafeInteger(row.limit) || row.limit < 1 || !Number.isFinite(row.until) || !Number.isFinite(row.blockedUntil)) throw Error('Unreadable interpreter capacity.');
  return row;
}
async function locked(p, action, ended = () => false, settling = false) {
  const acquire = p.acquireLock ?? (await import('./workflow-runner.mjs')).acquireRunLock;
  const stopAt = Math.min(p.now() + 5000, p.deadline ?? Infinity);
  let retrying = false;
  const stopped = () => {
    if (!settling && ended()) return true;
    if (ended() || p.now() >= stopAt) throw Error('Admission lock wait stopped.');
    return false;
  };
  while (settling || !ended()) {
    if (retrying && stopped()) return null;
    let release;
    try { release = acquire(p.root, 'interpreter-admission.lock'); }
    catch (error) {
      if (error.code !== 'run_busy') throw error;
      if (error.cause) throw error.cause;
      // acquireRunLock deliberately combines live contention with unverifiable
      // ownership. Only a verified live PID/token authorizes a queue wait.
      const path = join(p.root, 'interpreter-admission.lock');
      let owner;
      try {
        if (p.fs.lstatSync(path).size > 4096) throw Error('Oversized admission lock.');
        owner = read(p, path);
        if (!owner || Object.keys(owner).some(key => !['pid', 'token'].includes(key))
          || !Number.isSafeInteger(owner.pid) || owner.pid <= 0
          || typeof owner.token !== 'string' || !/^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i.test(owner.token ?? '')
          || !p.alive(owner.pid)) throw Error('Unverifiable admission lock ownership.');
      } catch (error) {
        // A live holder can release between the failed acquire and this read.
        if (error.code !== 'ENOENT') throw error;
        const root = p.fs.lstatSync(p.root);
        if (!root.isDirectory() || root.isSymbolicLink()) throw Error('Queue root is not a directory.');
      }
      if (stopped()) return null;
      retrying = true;
      await p.sleep(Math.min(100, Math.max(0, stopAt - p.now()))); continue;
    }
    try { return !settling && ended() ? null : action(); } finally { release(); }
  }
  return null;
}
const place = (all, row) => all.filter(other => other.state === 'waiting' && other.ticket <= row.ticket).length;
export async function acquireInterpreterSlot({ cwd, origin, requestId, kind, env = process.env, deadline = Infinity }, ports = {}) {
  let p, row;
  try {
    p = portsFor(env, { ...ports, deadline });
    if (!['lint', 'check'].includes(kind)) throw Error('Invalid interpreter request kind.');
    p.fs.mkdirSync(p.root, { recursive: true, mode: 0o700 });
    if (!p.fs.lstatSync(p.root).isDirectory() || p.fs.lstatSync(p.root).isSymbolicLink()) throw Error('Queue root is not a directory.');
    const ended = () => p.interrupted() || p.now() >= deadline;
    row = await locked(p, () => {
      const all = records(p);
      if (all.some(other => other.origin === origin && other.requestId === requestId)) throw Error('Interpreter request already has a ticket.');
      const ticket = (all.at(-1)?.ticket ?? 0) + 1;
      if (!Number.isSafeInteger(ticket)) throw Error('Interpreter ticket range exhausted.');
      const next = { ticket, pid: p.pid, cwd: resolve(cwd), origin, requestId, kind, state: 'waiting', queuedAt: p.now(),
        startedAt: null, endedAt: null, outcome: null, activeAtStart: null, activeAtEnd: null, dispatched: false };
      save(p, `ticket-${ticket}.json`, next); return next;
    }, ended);
    if (!row) return null;
    let last;
    while (!ended()) {
      const position = await locked(p, () => {
        const all = records(p), position = place(all, row), active = all.filter(other => other.state === 'running').length, cap = capacity(p);
        if (position === 1 && active < Math.min(p.limit, cap.limit) && p.now() >= cap.blockedUntil) {
          row.state = 'running'; row.startedAt = p.now(); row.activeAtStart = active + 1;
          save(p, `ticket-${row.ticket}.json`, row); return 0;
        }
        return position;
      }, ended);
      if (position === 0) return { root: p.root, ticket: row.ticket };
      if (position === null) break;
      if (position !== last) { p.say(`waiting for an interpreter slot (position ${position})`); last = position; }
      await p.sleep(Math.min(250, Math.max(0, deadline - p.now())));
    }
    await observeInterpreterRequest({ env, origin, requestId, outcome: 'not_sent', terminal: true }, ports);
    return null;
  } catch (error) {
    if (row && !row.dispatched) {
      row.state = 'finished'; row.endedAt = p.now(); row.outcome = 'not_sent';
      try { save(p, `ticket-${row.ticket}.json`, row); } catch {}
    }
    throw problem(error);
  }
}
export async function markInterpreterDispatch({ root, ticket }, ports = {}) {
  const p = portsFor({ PDD_INTERPRETER_QUEUE: root }, ports);
  try {
    await locked(p, () => {
      if (p.interrupted() || p.now() >= (p.deadline ?? Infinity)) throw Error('Dispatch marking stopped.');
      const row = read(p, join(root, `ticket-${ticket}.json`));
      if (row.pid !== p.pid || row.state !== 'running' || row.dispatched) throw Error('Interpreter dispatch ownership changed.');
      row.dispatched = true; save(p, `ticket-${ticket}.json`, row);
    }, () => p.interrupted(), true);
  } catch (error) { throw problem(error); }
}
export async function observeInterpreterRequest({ env = process.env, origin, requestId, outcome, terminal = false, busy = false, waitMs = 5000 }, ports = {}) {
  const p = portsFor(env, ports);
  try {
    // Read-only recovery of an old batch must not create a machine queue.
    if (!p.fs.existsSync(p.root)) return;
    await locked(p, () => {
      const all = records(p), row = all.find(row => row.origin === origin && row.requestId === requestId);
      if (!row || row.state === 'finished') return;
      const active = all.filter(other => other.state === 'running').length;
      row.outcome = outcome; row.endedAt = p.now(); row.activeAtEnd = active;
      if (terminal) row.state = 'finished';
      save(p, `ticket-${row.ticket}.json`, row);
      const cap = capacity(p);
      if (busy || outcome === 'busy') {
        cap.limit = Math.max(1, Math.floor(Math.min(cap.limit, p.limit) / 2)); cap.until = p.now() + 60_000;
        cap.blockedUntil = Math.max(cap.blockedUntil, p.now() + Math.min(60_000, Math.max(1000, Number.isFinite(waitMs) ? waitMs : 5000)));
      } else if (outcome === 'verdict' && terminal && p.now() >= cap.until) cap.limit = Math.min(p.limit, cap.limit + 1);
      save(p, 'capacity.json', cap);
    }, () => p.interrupted(), true);
  } catch (error) { throw problem(error); }
}
export function readInterpreterProgress({ cwd, since = 0, env = process.env }, ports = {}) {
  try {
    const p = portsFor(env, ports), all = records(p), own = all.filter(row => row.cwd === resolve(cwd));
    if (!own.length) return null;
    const row = own.find(row => row.state === 'waiting') ?? own.find(row => row.state !== 'finished') ?? own.at(-1);
    const intervals = own.map(row => [Math.max(since, row.queuedAt), Math.min(p.now(), row.startedAt ?? row.endedAt ?? p.now())])
      .filter(([start, end]) => end > start).sort((a, b) => a[0] - b[0]);
    let pausedMs = 0, end = -Infinity;
    for (const [start, stop] of intervals) { pausedMs += Math.max(0, stop - Math.max(start, end)); end = Math.max(end, stop); }
    return { state: row.state, position: row.state === 'waiting' ? place(all, row) : null, pausedMs, requests: own };
  } catch (error) { return { state: 'unavailable', reason: error.message, pausedMs: 0, requests: [] }; }
}
export function interpreterStatusWords(progress) {
  return progress.state === 'waiting' ? `waiting for an interpreter slot (position ${progress.position})`
    : progress.state === 'unavailable' ? `interpreter queue unavailable: ${progress.reason}`
    : progress.state === 'running' ? 'running an interpreter request' : 'interpreter requests finished';
}
