// Owned by prompts/cli/test-suite-queue.prompt.md.
import * as files from 'node:fs';
import { join, isAbsolute, resolve } from 'node:path';
import { randomUUID } from 'node:crypto';
import { spawn } from 'node:child_process';

const CAPACITY = 3;
const delay = ms => new Promise(done => setTimeout(done, ms));
const alive = pid => {
  try { process.kill(pid, 0); return true; }
  catch (error) { return error.code !== 'ESRCH'; }
};
export function suiteQueueRoot(env = process.env) {
  const root = env.PDD_SUITE_QUEUE ?? (env.PDD_VM_SUITE_LOCK ? `${env.PDD_VM_SUITE_LOCK}.queue` : `/tmp/pdd-full-suite-${process.getuid?.() ?? 'user'}`);
  if (!isAbsolute(root)) throw Error('The shared suite queue needs an absolute path.');
  return root;
}
function portsFor(env, ports) {
  return { fs: files, now: Date.now, sleep: delay, alive, pid: process.pid, say: text => process.stdout.write(`${text}\n`),
    execute: executeSuite, uuid: randomUUID, ...ports, root: ports.queueRoot ?? suiteQueueRoot(env) };
}
function save(p, record) {
  const target = join(p.root, `ticket-${record.ticket}.json`), temp = `${target}.${p.uuid()}.tmp`;
  try { p.fs.writeFileSync(temp, JSON.stringify(record), { mode: 0o600 }); p.fs.renameSync(temp, target); }
  finally { try { p.fs.unlinkSync(temp); } catch {} }
}
function records(p) {
  let names;
  try { names = p.fs.readdirSync(p.root); } catch (error) { if (error.code === 'ENOENT') return []; throw error; }
  return names.filter(name => /^ticket-.*\.json$/.test(name)).map(name => {
    const row = JSON.parse(p.fs.readFileSync(join(p.root, name), 'utf8'));
    if (!Number.isSafeInteger(row.ticket) || !Number.isSafeInteger(row.pid) || row.pid <= 0 || typeof row.cwd !== 'string'
      || !['waiting', 'running', 'finished'].includes(row.state) || !Number.isFinite(row.queuedAt)
      || row.startedAt !== null && !Number.isFinite(row.startedAt) || row.finishedAt !== null && !Number.isFinite(row.finishedAt)) {
      throw Error('Unreadable shared suite queue ownership.');
    }
    // A dead runner does not make its live or uncertain child safe to reclaim.
    if (row.state !== 'finished' && !p.alive(row.pid)
      && (row.state === 'waiting' || row.childPid && !p.alive(-row.childPid))) {
      return { ...row, state: 'finished', finishedAt: p.fs.statSync(join(p.root, name)).mtimeMs,
        reason: 'Test suite runner ended before reporting a result.' };
    }
    if (row.state !== 'finished' && !p.alive(row.pid)) return { ...row,
      reason: 'Test suite runner ended; suite descendants are still live or their ownership is unknown.' };
    return row;
  }).sort((a, b) => a.ticket - b.ticket);
}
async function underLock(p, action) {
  const lock = p.acquireLock ?? (await import('./workflow-runner.mjs')).acquireRunLock;
  for (;;) {
    let release;
    try { release = lock(p.root, 'suite-admission.lock'); }
    catch (error) { if (error.code !== 'run_busy') throw error; await p.sleep(100); continue; }
    try { return action(); } finally { release(); }
  }
}
const positionOf = (all, row) => all.filter(other => other.state === 'waiting' && other.ticket <= row.ticket).length;
function pausedTime(all, since, now) {
  const intervals = all.map(row => [Math.max(since, row.queuedAt), Math.min(now, row.finishedAt ?? now)])
    .filter(([start, end]) => end > start).sort((a, b) => a[0] - b[0]);
  let total = 0, end = -Infinity;
  for (const [start, stop] of intervals) { total += Math.max(0, stop - Math.max(start, end)); end = Math.max(end, stop); }
  return total;
}
export function readSuiteProgress({ cwd, since = 0, env = process.env }, ports = {}) {
  let p, all;
  try { p = portsFor(env, ports); all = records(p); }
  catch (error) { return { state: 'unavailable', reason: error.message, pausedMs: 0 }; }
  const own = all.filter(row => row.cwd === resolve(cwd));
  if (!own.length) return null;
  const row = own.findLast(row => row.state !== 'finished') ?? own.at(-1);
  return { ticket: row.ticket, state: row.state, position: row.state === 'waiting' ? positionOf(all, row) : null,
    queuedAt: row.queuedAt, startedAt: row.startedAt, finishedAt: row.finishedAt, reason: row.reason,
    pausedMs: pausedTime(own, since, p.now()) };
}
export function suiteStatusWords(suite) {
  return suite.state === 'unavailable' ? `full test suite queue unavailable: ${suite.reason}`
    : suite.reason ? `full test suite failed: ${suite.reason}`
    : suite.state === 'waiting' ? `waiting for a test slot (position ${suite.position})`
    : suite.state === 'running' ? 'running the full test suite'
    : 'full test suite finished';
}
export async function runTestSuite({ cwd, command, timeout = 30, env = process.env }, ports = {}) {
  if (typeof command !== 'string' || !command.trim() || !Number.isInteger(timeout) || timeout < 1 || timeout > 120)
    return { exitCode: 2, message: 'Supply a suite command and a timeout of 1 to 120 minutes.' };
  let p, row;
  try {
    p = portsFor(env, ports);
    p.fs.mkdirSync(p.root, { recursive: true, mode: 0o700 });
    row = await underLock(p, () => {
      const all = records(p), ticket = (all.at(-1)?.ticket ?? 0) + 1;
      const record = { ticket, pid: p.pid, childPid: null, cwd: resolve(cwd), state: 'waiting', queuedAt: p.now(), startedAt: null, finishedAt: null, reason: null };
      save(p, record); return record;
    });
    let lastPosition;
    for (;;) {
      const position = await underLock(p, () => {
        const all = records(p), place = positionOf(all, row);
        if (place === 1 && all.filter(other => other.state === 'running').length < CAPACITY) {
          row.state = 'running'; row.startedAt = p.now(); save(p, row); return 0;
        }
        return place;
      });
      if (!position) break;
      if (position !== lastPosition) { p.say(`waiting for a test slot (position ${position})`); lastPosition = position; }
      await p.sleep(250);
    }
    p.say('running the full test suite');
    const result = await p.execute(command, { cwd, env, timeoutMs: Number(timeout) * 60_000,
      onChild: pid => { row.childPid = pid; save(p, row); } });
    row.state = 'finished'; row.finishedAt = p.now(); row.reason = result.reason ?? (result.exitCode ? `Test suite exited with status ${result.exitCode}.` : null);
    save(p, row);
    return { exitCode: result.exitCode, message: row.reason ?? 'Full test suite finished.' };
  } catch (error) {
    // An execution port must stop descendants before rejecting. A native child is
    // never released on an uncertain save or execution failure.
    if (p && row && (row.state === 'waiting' || row.childPid && !p.alive(-row.childPid))) {
      row.state = 'finished'; row.finishedAt = p.now(); row.reason = `Test suite failed: ${error.code ?? error.message}`;
      try { save(p, row); } catch {}
    }
    return { exitCode: 1, message: `Shared test suite queue failed: ${error.code ?? error.message}` };
  }
}
export async function executeSuite(command, { cwd, env, timeoutMs, onChild }) {
  return new Promise(done => {
    const child = spawn('/bin/bash', ['-c', command], { cwd, env, detached: true, stdio: ['ignore', 'inherit', 'inherit'] });
    let reason = null, forcedCode = null, escalation;
    const killGroup = signal => { if (child.pid) { try { process.kill(-child.pid, signal); } catch (error) { if (error.code !== 'ESRCH') throw error; } } };
    const stop = (code, why) => {
      if (forcedCode !== null) return;
      forcedCode = code; reason = why; killGroup('SIGTERM');
      escalation = setTimeout(() => killGroup('SIGKILL'), 2000);
    };
    const interrupt = () => stop(130, 'Test suite interrupted (SIGINT).');
    const terminate = () => stop(143, 'Test suite interrupted (SIGTERM).');
    process.on('SIGINT', interrupt); process.on('SIGTERM', terminate);
    const timer = setTimeout(() => stop(124, `Test suite execution timeout after ${timeoutMs / 60_000} minutes.`), timeoutMs);
    const cleanup = () => { clearTimeout(timer); clearTimeout(escalation); process.off('SIGINT', interrupt); process.off('SIGTERM', terminate); killGroup('SIGKILL'); };
    child.once('error', error => { cleanup(); done({exitCode:1, reason:`Test suite could not start: ${error.code ?? error.message}`}); });
    child.once('close', (code, signal) => { cleanup(); done({ exitCode: forcedCode ?? code ?? 1, reason: reason ?? (signal ? `Test suite ended by ${signal}.` : null) }); });
    try { if (child.pid) onChild(child.pid); }
    catch (error) { stop(1, `Test suite could not save its child ownership: ${error.code ?? error.message}`); }
  });
}
