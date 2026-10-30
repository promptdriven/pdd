// Generated from prompts/cli/runtime-slots.prompt.md (sha256: 7d1812c0ce5beb24cfbbab993681c889a1606f98be9ca7089d8c7bb410a8361a).
import { chmodSync, closeSync, lstatSync, mkdirSync, linkSync, openSync, readFileSync, readdirSync, renameSync, unlinkSync, writeFileSync, fsyncSync } from 'node:fs';
import { randomUUID } from 'node:crypto';
import { homedir } from 'node:os';
import { join, resolve } from 'node:path';
import { runtimeOrigin } from './runtime-client.mjs';

const unavailable = error => Object.assign(new Error(`Local runtime state unavailable: ${String(error?.message ?? error).split('\n')[0]}`), { code: 'local-state-unavailable' });
const alive = pid => { try { process.kill(pid, 0); return true; } catch (error) { return error.code !== 'ESRCH'; } };
const order = (a, b) => a.started_at - b.started_at || (a.id < b.id ? -1 : a.id > b.id ? 1 : 0);
const directoryFor = ({ stateDir, origin }) => join(stateDir, 'slots', encodeURIComponent(new URL(origin).host));
function ensure(directory) { mkdirSync(directory, { recursive: true, mode: 0o700 }); chmodSync(directory, 0o700); }
function readRecord(path) {
  if (!lstatSync(path).isFile() || lstatSync(path).isSymbolicLink()) throw new Error('Slot record is not a regular file');
  return JSON.parse(readFileSync(path, 'utf8'));
}
const heldClaims = new Map();
function publishExclusive(path, record) {
  const temporary = `${path}.${randomUUID()}.tmp`, fd = openSync(temporary, 'wx', 0o600);
  try { writeFileSync(fd, `${JSON.stringify(record)}\n`); fsyncSync(fd); } finally { closeSync(fd); }
  try { try { linkSync(temporary, path); return true; } catch (error) { if (error.code === 'EEXIST') return false; throw error; } }
  finally { unlinkSync(temporary); }
}
// Bakery claims have never-reused paths. A dead claimant can be removed without
// deleting a successor's lock, even when several processes notice its death.
function claimNative(path, record) {
  const directory = resolve(path, '..'), id = randomUUID(), mine = join(directory, `.claim-${id}.lock`);
  const contenders = () => {
    const live = [];
    for (const name of readdirSync(directory).filter(name => /^\.claim-.*\.lock$/.test(name))) {
      const file = join(directory, name); let row;
      try { row = readRecord(file); } catch (error) { if (error.code === 'ENOENT') continue; throw error; }
      if (typeof row.id !== 'string' || !Number.isSafeInteger(row.pid) || row.pid < 1 || typeof row.choosing !== 'boolean'
        || !row.choosing && (!Number.isSafeInteger(row.number) || row.number < 1)) throw new Error('Invalid runtime claim');
      if (!alive(row.pid)) { try { unlinkSync(file); } catch (error) { if (error.code !== 'ENOENT') throw error; } }
      else live.push(row);
    }
    return live;
  };
  publishExclusive(mine, { id, pid: record.pid, choosing: true });
  let held = false;
  try {
    const prior = contenders().filter(row => row.id !== id);
    if (prior.some(row => row.choosing)) return false;
    const number = 1 + Math.max(0, ...prior.map(row => row.number));
    nativeFiles.writeAtomic(mine, { id, pid: record.pid, number, choosing: false });
    const others = contenders().filter(row => row.id !== id);
    if (others.some(row => row.choosing || row.number < number || row.number === number && row.id < id)) return false;
    heldClaims.set(path, mine); held = true; return true;
  } finally { if (!held) unlinkSync(mine); }
}
const nativeFiles = {
  listRecords({ directory }) {
    let names;
    try { names = readdirSync(directory); } catch (error) { if (error.code === 'ENOENT') return { jobs: [] }; throw error; }
    const jobs = [];
    for (const name of names.filter(name => name.endsWith('.json') && name !== 'claim.json')) {
      let row;
      try { row = readRecord(join(directory, name)); } catch (error) { if (error.code === 'ENOENT') continue; throw error; }
      if (typeof row.id !== 'string' || name !== `${row.id}.json` || !['active', 'waiting'].includes(row.state)
        || !Number.isSafeInteger(row.pid) || row.pid < 1 || !['check', 'lint', 'try'].includes(row.kind)
        || !Number.isSafeInteger(row.started_at) || row.started_at < 0 || !Array.isArray(row.request_ids) || row.request_ids.some(id => typeof id !== 'string')) throw new Error('Invalid slot record');
      jobs.push({ id: row.id, state: row.state, pid: row.pid, kind: row.kind, started_at: row.started_at, request_ids: row.request_ids });
    }
    return { jobs };
  },
  exclusiveCreate(path, record) {
    ensure(resolve(path, '..'));
    if (path.endsWith('/claim.json')) return claimNative(path, record);
    return publishExclusive(path, record);
  },
  writeAtomic(path, record) {
    const temporary = `${path}.${randomUUID()}.tmp`;
    const fd = openSync(temporary, 'wx', 0o600);
    try { writeFileSync(fd, `${JSON.stringify(record)}\n`); fsyncSync(fd); } finally { closeSync(fd); }
    renameSync(temporary, path);
  },
  unlink(path) { if (path.endsWith('/claim.json')) { const held = heldClaims.get(path); if (!held) return; heldClaims.delete(path); path = held; } try { unlinkSync(path); } catch (error) { if (error.code !== 'ENOENT') throw error; } },
};
const defaults = ports => ({ files: nativeFiles, pid: process.pid, isAlive: alive, now: Date.now, randomUUID,
  sleep: ms => new Promise(done => setTimeout(done, ms)), interrupted: () => false, readRun: async () => 'unknown', say: () => {}, ...ports });
const rows = async (files, directory) => { try { return (await files.listRecords({ directory })).jobs; } catch (error) { throw unavailable(error); } };
async function locked(directory, ports, action) {
  const path = join(directory, 'claim.json');
  if (!await ports.files.exclusiveCreate(path, { pid: ports.pid })) return { claimed: false };
  try { return { claimed: true, value: await action() }; } finally { await ports.files.unlink(path); }
}

export async function acquireRuntimeSlot({ stateDir, origin, limit = 4, kind, deadline = null }, given = {}) {
  const ports = defaults(given), directory = directoryFor({ stateDir, origin }), id = ports.randomUUID();
  const ticket = { id, state: 'waiting', pid: ports.pid, kind, started_at: ports.now(), request_ids: [] };
  const path = join(directory, `${id}.json`), ended = () => ports.interrupted() || deadline !== null && ports.now() >= deadline;
  if (ended()) return null;
  if (!await ports.files.exclusiveCreate(path, ticket)) throw unavailable(new Error('Duplicate slot identity'));
  let acquired = false, last = '';
  try {
    while (!ended()) {
      const attempt = await locked(directory, ports, async () => {
        let jobs = await rows(ports.files, directory);
        for (const row of jobs) {
          if (ports.isAlive(row.pid)) continue;
          let reclaim = row.state === 'waiting' || !row.request_ids.length || ports.now() - row.started_at >= 1_800_000;
          if (!reclaim) {
            const states = await Promise.all(row.request_ids.map(async requestId => { try { return await ports.readRun(requestId); } catch { return 'unknown'; } }));
            reclaim = states.every(state => state === 'ended');
          }
          if (reclaim) { await ports.files.unlink(join(directory, `${row.id}.json`)); jobs = jobs.filter(item => item.id !== row.id); }
        }
        const active = jobs.filter(row => row.state === 'active'), waiting = jobs.filter(row => row.state === 'waiting').sort(order);
        if (!ended() && active.length < limit && waiting[0]?.id === id) {
          await ports.files.writeAtomic(path, { ...ticket, state: 'active', started_at: ports.now() });
          return true;
        }
        const message = `Waiting for a local slot: ${active.length} of ${limit} busy, ${Math.max(0, waiting.findIndex(row => row.id === id))} ahead of you. (Set PDD_MAX_JOBS to change the limit.)`;
        if (message !== last) { ports.say(message); last = message; }
        return false;
      });
      if (attempt.value) { acquired = true; return { id, directory }; }
      if (!ended()) await ports.sleep(Math.min(100, deadline === null ? 100 : Math.max(0, deadline - ports.now())));
    }
    return null;
  } finally { if (!acquired) await ports.files.unlink(path); }
}

export async function recordRuntimeRequest(reservation, requestId, given = {}) {
  const ports = defaults(given);
  for (;;) {
    if (ports.interrupted() || ports.deadline !== undefined && ports.now() >= ports.deadline) return false;
    const result = await locked(reservation.directory, ports, async () => {
      if (ports.interrupted() || ports.deadline !== undefined && ports.now() >= ports.deadline) return false;
      const row = (await rows(ports.files, reservation.directory)).find(row => row.id === reservation.id);
      if (!row || row.state !== 'active') throw unavailable(new Error('Missing runtime reservation'));
      if (!row.request_ids.includes(requestId)) await ports.files.writeAtomic(join(reservation.directory, `${row.id}.json`), { ...row, request_ids: [...row.request_ids, requestId] });
    });
    if (result.claimed) return result.value !== false;
    await ports.sleep(10);
  }
}
export async function releaseRuntimeSlot(reservation, { ended }, given = {}) {
  if (reservation && ended) await defaults(given).files.unlink(join(reservation.directory, `${reservation.id}.json`));
}
export async function listRuntimeJobs(options, ports = {}) {
  const jobs = await rows(ports.files ?? nativeFiles, directoryFor(options));
  return { jobs: [...jobs].sort((a, b) => (a.state === 'active' ? 0 : 1) - (b.state === 'active' ? 0 : 1) || order(a, b)) };
}
export async function runJobs({ env = process.env } = {}, { stdout = process.stdout, stderr = process.stderr, files, now = Date.now } = {}) {
  try {
    const stateDir = resolve(env.PDD_STATE_DIR || join(env.HOME || homedir(), '.pdd', 'runtime'));
    const { jobs } = await listRuntimeJobs({ stateDir, origin: runtimeOrigin(env) }, { files });
    if (!jobs.length) stdout.write('No local runtime jobs.\n');
    for (const row of jobs) stdout.write(`${row.state} ${row.kind} · PID ${row.pid} · ${Math.max(0, Math.floor((now() - row.started_at) / 1000))} s · ${row.id} · ${row.request_ids.join(', ') || 'no request yet'}\n`);
    return 0;
  } catch (error) { stderr.write(`${String(error.message).split('\n')[0]}\n`); return 5; }
}
