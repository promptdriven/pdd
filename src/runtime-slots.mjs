// Generated from prompts/cli/runtime-slots.prompt.md (sha256: 147c1ce2915c2369030716c75f3de0e288e90a79057d5484023b41a68b640974).
import { chmodSync, closeSync, lstatSync, mkdirSync, linkSync, openSync, readFileSync, readdirSync, renameSync, unlinkSync, writeFileSync, fsyncSync, utimesSync } from 'node:fs';
import { randomUUID } from 'node:crypto';
import { homedir } from 'node:os';
import { join, resolve } from 'node:path';
import { runtimeOrigin } from './runtime-client.mjs';

const HEARTBEAT_MS = 5000, EXPIRED_MS = 60_000, LEASE_MS = 1_800_000, PROBE_MS = 15_000;
const unavailable = error => Object.assign(new Error(`Local runtime state unavailable: ${String(error?.message ?? error).split('\n')[0]}`), { code: 'local-state-unavailable' });
const alive = pid => { try { process.kill(pid, 0); return true; } catch (error) { return error.code !== 'ESRCH'; } };
const order = (a, b) => a.started_at - b.started_at || (a.id < b.id ? -1 : a.id > b.id ? 1 : 0);
const snapshotKey = row => JSON.stringify([row.id, row.pid, row.state, row.kind, row.started_at, row.request_ids]);
const nativeSnapshotKey = row => row.state === undefined ? JSON.stringify([row.id, row.pid, row.choosing, row.number]) : snapshotKey(row);
const rememberNativeOwnership = Symbol('rememberNativeOwnership');
const directoryFor = ({ stateDir, origin }) => join(stateDir, 'slots', encodeURIComponent(new URL(origin).host));
const nativeInterrupt = handler => {
  const signals = ['SIGINT', 'SIGHUP', 'SIGTERM'];
  for (const signal of signals) process.on(signal, handler);
  return () => { for (const signal of signals) process.off(signal, handler); };
};
function ensure(directory) { mkdirSync(directory, { recursive: true, mode: 0o700 }); chmodSync(directory, 0o700); }
function readRecord(path) {
  const stat = lstatSync(path);
  if (!stat.isFile() || stat.isSymbolicLink()) throw new Error('Slot record is not a regular file');
  return JSON.parse(readFileSync(path, 'utf8'));
}
function publishExclusive(path, record) {
  const temporary = `${path}.${randomUUID()}.tmp`, fd = openSync(temporary, 'wx', 0o600);
  try { writeFileSync(fd, `${JSON.stringify(record)}\n`); fsyncSync(fd); } finally { closeSync(fd); }
  try { try { linkSync(temporary, path); return true; } catch (error) { if (error.code === 'EEXIST') return false; throw error; } }
  finally { unlinkSync(temporary); }
}
let claimSequence = 0;
// Each claimant has its own never-reused path. Removing an abandoned claimant
// cannot unlink a successor, unlike deleting and recreating a shared lock path.
function nativeFilePort(ports) {
  const heldClaims = new Map(), owned = new Map();
  const remember = (path, record) => owned.set(path, nativeSnapshotKey(record));
  const actual = path => path.endsWith('/claim.json') ? heldClaims.get(path) : path;
  const files = {
    [rememberNativeOwnership]: (path, record) => owned.set(path, nativeSnapshotKey(record)),
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
      if (!path.endsWith('/claim.json')) { const created = publishExclusive(path, record); if (created) { remember(path, record); files.touch(path); } return created; }
      const directory = resolve(path, '..'), id = `${record.pid}-${ports.randomUUID()}-${++claimSequence}`, mine = join(directory, `.claim-${id}.lock`);
      const contenders = () => {
        const live = [];
        for (const name of readdirSync(directory).filter(name => /^\.claim-.*\.lock$/.test(name))) {
          const file = join(directory, name); let row, modified;
          try { row = readRecord(file); modified = files.modifiedAt(file); } catch (error) { if (error.code === 'ENOENT') continue; throw error; }
          if (typeof row.id !== 'string' || !Number.isSafeInteger(row.pid) || row.pid < 1 || typeof row.choosing !== 'boolean'
            || !row.choosing && (!Number.isSafeInteger(row.number) || row.number < 1)) throw new Error('Invalid runtime claim');
          if (!ports.isAlive(row.pid) || modified === null || ports.now() - modified >= EXPIRED_MS) files.unlink(file);
          else live.push(row);
        }
        return live;
      };
      const choosing = { id, pid: record.pid, choosing: true };
      publishExclusive(mine, choosing); remember(mine, choosing); files.touch(mine);
      let held = false;
      try {
        const number = 1 + Math.max(0, ...contenders().filter(row => row.id !== id).map(row => row.number || 0));
        files.writeAtomic(mine, { id, pid: record.pid, number, choosing: false });
        if (contenders().some(row => row.id !== id && (row.choosing || row.number < number || row.number === number && row.id < id))) return false;
        heldClaims.set(path, mine); held = true; return true;
      } finally { if (!held) files.unlink(mine); }
    },
    writeAtomic(path, record) {
      const temporary = `${path}.${randomUUID()}.tmp`, fd = openSync(temporary, 'wx', 0o600);
      try { writeFileSync(fd, `${JSON.stringify(record)}\n`); fsyncSync(fd); } finally { closeSync(fd); }
      renameSync(temporary, path); remember(path, record); files.touch(path);
    },
    modifiedAt(path) {
      const claim = path.endsWith('/claim.json');
      path = actual(path); if (!path) return null;
      try { const stat = lstatSync(path); if (!stat.isFile() || stat.isSymbolicLink()) throw new Error('Slot record is not a regular file');
        if (claim && nativeSnapshotKey(readRecord(path)) !== owned.get(path)) return null;
        return stat.mtimeMs; }
      catch (error) { if (error.code === 'ENOENT') return null; throw error; }
    },
    touch(path) {
      path = actual(path); if (!path) return false;
      try { const stat = lstatSync(path); if (!stat.isFile() || stat.isSymbolicLink()) throw new Error('Slot record is not a regular file'); const identity = owned.get(path), record = readRecord(path);
        if (identity === undefined || nativeSnapshotKey(record) !== identity) return false;
        const time = new Date(ports.now()); utimesSync(path, time, time); return true; }
      catch (error) { if (error.code === 'ENOENT') return false; throw error; }
    },
    unlink(path) {
      const resolved = actual(path); if (!resolved) return;
      if (path.endsWith('/claim.json')) heldClaims.delete(path);
      const identity = owned.get(resolved);
      owned.delete(resolved);
      try {
        if (resolved.endsWith('.lock') && identity !== undefined && nativeSnapshotKey(readRecord(resolved)) !== identity) return;
        unlinkSync(resolved);
      } catch (error) { if (error.code !== 'ENOENT') throw error; }
    },
  };
  return files;
}
function defaults(given = {}) {
  const ports = { pid: process.pid, isAlive: alive, now: Date.now, randomUUID, random: Math.random,
    timers: { setInterval, clearInterval }, onInterrupt: nativeInterrupt,
    sleep: ms => new Promise(done => setTimeout(done, ms)), interrupted: () => false, readRun: async () => 'unknown', say: () => {}, ...given };
  ports.files = given.files ?? nativeFilePort(ports);
  return ports;
}
const nativeFiles = nativeFilePort({ now: Date.now, randomUUID, isAlive: alive });
const owners = new Map(), reservationOwners = new WeakMap(), probes = new Map();
let claimSections = 0;
const claimWaiters = new Set();
function leaveClaim() { if (--claimSections === 0) { for (const done of claimWaiters) done(); claimWaiters.clear(); } }
async function outsideRead(ports, id) {
  while (claimSections) await new Promise(done => claimWaiters.add(done));
  return ports.readRun(id);
}
const rows = async (files, directory) => { try { return (await files.listRecords({ directory })).jobs; } catch (error) { throw unavailable(error); } };
const freshness = async (ports, path) => ports.files.modifiedAt ? await ports.files.modifiedAt(path) : owners.has(path) ? ports.now() : null;
const expired = (ports, row, modified) => !ports.isAlive(row.pid) || modified === null || ports.now() - modified >= EXPIRED_MS;
function heartbeat(path, ports, interrupted, retainInterrupt = false) {
  let stopped = false, pending = Promise.resolve(), unsubscribe = () => {};
  const pause = () => { if (!stopped) { stopped = true; ports.timers.clearInterval(timer); } };
  const stop = () => { pause(); unsubscribe(); };
  const missing = () => { if (retainInterrupt) pause(); else stop(); };
  const timer = ports.timers.setInterval(() => {
    pending = pending.then(async () => {
      if (stopped) return;
      if (!ports.files.touch || await ports.files.touch(path) === false) missing();
    }).catch(missing);
  }, HEARTBEAT_MS);
  timer?.unref?.();
  unsubscribe = ports.onInterrupt(() => { stop(); interrupted?.(); });
  if (stopped) unsubscribe();
  return { stop, pause, pending: () => pending };
}
async function locked(directory, ports, action) {
  const path = join(directory, 'claim.json');
  claimSections++;
  let claimed;
  try { claimed = await ports.files.exclusiveCreate(path, { pid: ports.pid }); } catch (error) { leaveClaim(); throw error; }
  if (!claimed) { leaveClaim(); return { claimed: false }; }
  let cancelled = false;
  const pulse = heartbeat(path, ports, () => { cancelled = true; void ports.files.unlink(path); });
  const ownsClaim = async () => {
    if (cancelled || ports.interrupted()) return false;
    if (!ports.files.modifiedAt) return true;
    const modified = await freshness(ports, path);
    return modified !== null && ports.now() - modified < EXPIRED_MS;
  };
  try { return { claimed: true, value: await ownsClaim() ? await action(ownsClaim) : false }; }
  finally { pulse.stop(); try { await pulse.pending(); await ports.files.unlink(path); } finally { leaveClaim(); } }
}
function retryDelay(ports, failures, follower, remaining) {
  const base = follower ? 8 : Math.min(4, 2 * 2 ** Math.min(failures, 1));
  return Math.min(remaining, base + Math.floor(ports.random() * base));
}
async function observe(result, ports, ended, deadline, stopWaiting) {
  let timer, off = () => {};
  try {
    return await Promise.race([result, new Promise(done => {
      const stop = () => { stopWaiting(); done('unknown'); };
      off = ports.onInterrupt(stop);
      if (ended()) { stop(); return; }
      const waitForDeadline = () => {
        if (timer !== undefined) { ports.timers.clearInterval(timer); timer = undefined; }
        if (ended()) { stop(); return; }
        // Native timers overflow on far-future absolute deadlines. Each chunk
        // only wakes this observer to recheck its own deadline and interruption.
        timer = ports.timers.setInterval(waitForDeadline, Math.max(1, Math.min(60_000, deadline - ports.now())));
      };
      if (deadline !== null) waitForDeadline();
    })]);
  } finally {
    if (timer !== undefined) ports.timers.clearInterval(timer);
    off();
  }
}
async function inspect(directory, origin, ports, ended, deadline, stopWaiting, waitingTicket) {
  const snapshots = [];
  for (const row of await rows(ports.files, directory)) {
    if (ended()) break;
    // This acquisition still owns its original ticket even if wall time jumps
    // before the next heartbeat. Other owners retain ordinary expiry rules.
    if (snapshotKey(row) === snapshotKey(waitingTicket)) continue;
    const path = join(directory, `${row.id}.json`), modified = await freshness(ports, path);
    if (!expired(ports, row, modified)) continue;
    let reclaim = row.state === 'waiting' || !row.request_ids.length || ports.now() - row.started_at >= LEASE_MS;
    if (!reclaim) {
      const states = [];
      for (const id of row.request_ids) {
        if (ended()) break;
        const key = JSON.stringify([origin, row.kind, id]), cached = probes.get(key), now = ports.now();
        let observation = cached && (cached.pending || now >= cached.at && now - cached.at < PROBE_MS) ? cached : null;
        const shared = !!observation;
        if (!observation) {
          observation = { at: now, pending: true };
          observation.result = Promise.resolve().then(() => outsideRead(ports, id)).catch(() => 'unknown').then(state => { observation.pending = false; observation.at = ports.now(); return state; });
          probes.set(key, observation);
        }
        // The cached GET can belong to a caller with a longer wait. Ending this
        // observer must leave that shared read and its eventual cache intact.
        // The initiating readRun already owns this acquisition's transport
        // deadline. Only observers borrowing that read need a separate timer.
        states.push(await (shared ? observe(observation.result, ports, ended, deadline, stopWaiting) : observation.result));
      }
      reclaim = states.length === row.request_ids.length && states.every(state => state === 'ended');
    }
    if (reclaim) snapshots.push({ row, modified, key: snapshotKey(row) });
  }
  return snapshots;
}

export async function acquireRuntimeSlot({ stateDir, origin, limit = 4, kind, deadline = null }, given = {}) {
  const ports = defaults(given), directory = directoryFor({ stateDir, origin }), id = ports.randomUUID();
  const ticket = { id, state: 'waiting', pid: ports.pid, kind, started_at: ports.now(), request_ids: [] };
  const path = join(directory, `${id}.json`);
  let cancelled = false;
  const ended = () => cancelled || ports.interrupted() || deadline !== null && ports.now() >= deadline;
  if (ended()) return null;
  if (!await ports.files.exclusiveCreate(path, ticket)) throw unavailable(new Error('Duplicate slot identity'));
  let acquired = false, activeTicket = null, last = '', failures = 0;
  const owner = { posted: false, pulse: null, snapshot: snapshotKey(ticket), [rememberNativeOwnership]: ports.files[rememberNativeOwnership] };
  const interruptOwner = () => {
    cancelled = true;
    if (!owner.posted) void removeUnsent();
  };
  const ownWaiting = row => row && snapshotKey(row) === snapshotKey(ticket);
  const removeUnsent = async () => {
    const current = (await rows(ports.files, directory)).find(row => row.id === id);
    if (ownWaiting(current) || activeTicket && current && snapshotKey(current) === snapshotKey(activeTicket)) await ports.files.unlink(path);
  };
  // Cancellation outlives an absent-file refresh while this wait is pending.
  owner.pulse = heartbeat(path, ports, interruptOwner, true);
  owners.set(path, owner);
  try {
    while (!ended()) {
      // Probes can block on HTTP. Nothing in this process holds exclusion here.
      const snapshots = await inspect(directory, origin, ports, ended, deadline, () => { cancelled = true; }, ticket);
      if (ended()) break;
      // Dead waiters are safe to remove by immutable ticket path without a claim.
      for (const item of snapshots.filter(item => item.row.state === 'waiting')) {
        const current = (await rows(ports.files, directory)).find(row => row.id === item.row.id);
        if (current && snapshotKey(current) === item.key && await freshness(ports, join(directory, `${current.id}.json`)) === item.modified)
          await ports.files.unlink(join(directory, `${current.id}.json`));
      }
      let jobs = await rows(ports.files, directory);
      if (ended()) break;
      if (!jobs.some(row => row.id === id)) {
        // Only the pending acquisition may restore its immutable waiting ticket.
        // An absent-file heartbeat may already have stopped; retire it before
        // restoring so an old in-flight pulse cannot stop the new lifecycle.
        owner.pulse.pause(); await owner.pulse.pending();
        if (ended()) break;
        if (await ports.files.exclusiveCreate(path, ticket)) {
          const pulse = heartbeat(path, ports, interruptOwner, true);
          owner.pulse.stop(); owner.pulse = pulse;
        }
        if (ended()) break;
        jobs = await rows(ports.files, directory);
      }
      const waiting = jobs.filter(row => row.state === 'waiting').sort(order), active = jobs.filter(row => row.state === 'active');
      const message = `Waiting for a local slot: ${active.length} of ${limit} busy, ${Math.max(0, waiting.findIndex(row => row.id === id))} ahead of you. (Set PDD_MAX_JOBS to change the limit.)`;
      if (ownWaiting(waiting[0])) {
        const attempt = await locked(directory, ports, async ownsClaim => {
          let currentJobs = await rows(ports.files, directory);
          if (!await ownsClaim()) return false;
          for (const item of snapshots.filter(item => item.row.state === 'active')) {
            if (ended()) return false;
            const row = currentJobs.find(row => row.id === item.row.id), file = join(directory, `${item.row.id}.json`);
            const modified = await freshness(ports, file);
            if (row && snapshotKey(row) === item.key && modified === item.modified && expired(ports, row, modified) && await ownsClaim()) {
              await ports.files.unlink(file); currentJobs = currentJobs.filter(other => other.id !== row.id);
            }
          }
          if (!ended() && await ownsClaim() && currentJobs.filter(row => row.state === 'active').length < limit
            && ownWaiting(currentJobs.filter(row => row.state === 'waiting').sort(order)[0])) {
            activeTicket = { ...ticket, state: 'active', started_at: ports.now() };
            await ports.files.writeAtomic(path, activeTicket);
            owner.snapshot = snapshotKey(activeTicket);
            return true;
          }
          return false;
        });
        if (attempt.value) { acquired = true; const reservation = { id, directory }; reservationOwners.set(reservation, owner); return reservation; }
        failures++;
      }
      if (message !== last) { ports.say(message); last = message; }
      if (!ended()) await ports.sleep(retryDelay(ports, failures, waiting[0]?.id !== id, deadline === null ? Infinity : Math.max(0, deadline - ports.now())));
    }
    return null;
  } finally {
    if (!acquired) { owner.pulse.stop(); await owner.pulse.pending(); owners.delete(path); await removeUnsent(); }
  }
}

export async function recordRuntimeRequest(reservation, requestId, given = {}) {
  const ports = defaults(given), path = join(reservation.directory, `${reservation.id}.json`);
  let failures = 0, cancelled = false;
  const off = ports.onInterrupt(() => { cancelled = true; });
  const ended = () => cancelled || ports.interrupted() || ports.deadline !== undefined && ports.now() >= ports.deadline;
  try {
    for (;;) {
      if (ended()) return false;
      const result = await locked(reservation.directory, ports, async ownsClaim => {
        if (ended()) return false;
        const row = (await rows(ports.files, reservation.directory)).find(row => row.id === reservation.id);
        if (ended() || !await ownsClaim()) return false;
        const owner = reservationOwners.get(reservation) ?? owners.get(path);
        if (owner && (!row || snapshotKey(row) !== owner.snapshot)) {
          owner.pulse.stop();
          throw unavailable(new Error('Runtime reservation ownership changed'));
        }
        if (!row || row.state !== 'active') throw unavailable(new Error('Missing runtime reservation'));
        if (!row.request_ids.includes(requestId)) {
          const next = { ...row, request_ids: [...row.request_ids, requestId] };
          await ports.files.writeAtomic(path, next);
          if (owner) { owner.snapshot = snapshotKey(next); owner[rememberNativeOwnership]?.(path, next); }
        }
        if (owner) owner.posted = true;
      });
      if (result.claimed) return result.value !== false;
      const remaining = ports.deadline === undefined ? Infinity : Math.max(0, ports.deadline - ports.now());
      await ports.sleep(Math.min(remaining, Math.max(10, retryDelay(ports, ++failures, false, remaining))));
    }
  } finally { off(); }
}
export async function releaseRuntimeSlot(reservation, { ended }, given = {}) {
  if (!reservation) return;
  const path = join(reservation.directory, `${reservation.id}.json`), owner = reservationOwners.get(reservation) ?? owners.get(path);
  if (owner) { owner.pulse.stop(); await owner.pulse.pending(); if (owners.get(path) === owner) owners.delete(path); }
  if (ended) {
    const ports = defaults(given);
    if (owner) {
      const row = (await rows(ports.files, reservation.directory)).find(row => row.id === reservation.id);
      if (!row || snapshotKey(row) !== owner.snapshot) return;
    }
    await ports.files.unlink(path);
  }
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
