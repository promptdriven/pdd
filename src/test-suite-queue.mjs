// Owned by prompts/cli/test-suite-queue.prompt.md.
import * as files from 'node:fs';
import { join, isAbsolute, resolve } from 'node:path';
import { randomUUID } from 'node:crypto';
import { spawn } from 'node:child_process';
import { availableParallelism, freemem, loadavg } from 'node:os';

function nativeCores() {
  if (process.platform === 'linux') {
    let list;
    try { list = /^Cpus_allowed_list:\s*(.+)$/m.exec(files.readFileSync('/proc/self/status', 'utf8'))?.[1]; } catch { /* Use available parallelism without procfs. */ }
    if (list) return list.split(',').flatMap(part => {
      const [first, last = first] = part.split('-').map(Number);
      return Array.from({length:last - first + 1}, (_, index) => first + index);
    });
  }
  return Array.from({length:availableParallelism()}, (_, index) => index);
}
function nativeBattery() {
  if (process.platform !== 'linux') return false;
  let names;
  try { names = files.readdirSync('/sys/class/power_supply'); } catch (error) { if (error.code === 'ENOENT') return false; throw error; }
  return names.some(name => files.readFileSync(join('/sys/class/power_supply', name, 'type'), 'utf8').trim() === 'Battery');
}
function nativeTaskset(env) {
  if (process.platform !== 'linux') return null;
  for (const folder of (env.PATH ?? '').split(':').filter(isAbsolute)) {
    const path = join(folder, 'taskset');
    try { files.accessSync(path, files.constants.X_OK); if (files.statSync(path).isFile()) return path; } catch {}
  }
  return null;
}
export function calculateCheckCapacity({checks, runs} = {}, ports = {}) {
  const cpuIds = (ports.cores ?? nativeCores)(), freeMemory = (ports.memory ?? freemem)(),
    load = (ports.load ?? (() => loadavg()[0]))(), platform = ports.platform ?? process.platform;
  const battery = platform === 'linux' ? (ports.battery ?? nativeBattery)() : false;
  const personal = platform === 'darwin' || platform === 'linux' && battery;
  const taskset = platform === 'linux' ? (ports.taskset ?? (() => nativeTaskset(ports.env ?? process.env)))() : null;
  if (typeof platform !== 'string' || typeof battery !== 'boolean' || !Array.isArray(cpuIds) || !cpuIds.length || cpuIds.some(id => !Number.isSafeInteger(id) || id < 0)
    || new Set(cpuIds).size !== cpuIds.length || !Number.isFinite(freeMemory) || freeMemory < 0
    || !Number.isFinite(load) || load < 0 || taskset !== null && (typeof taskset !== 'string' || !isAbsolute(taskset))
    || [checks,runs].some(value => value !== undefined && (!Number.isSafeInteger(value) || value < 1))) throw Error('Machine check capacity is unavailable or invalid.');
  const usable = cpuIds.slice(0, personal ? Math.max(1, Math.floor(cpuIds.length / 2)) : cpuIds.length);
  const affinity = platform === 'linux' && taskset !== null;
  const calculatedChecks = Math.max(1, Math.min(Math.floor(usable.length / 12), Math.floor(freeMemory / (4 * 1024 ** 3)), affinity ? Infinity : 1));
  const selected = checks ?? calculatedChecks, calculatedRuns = Math.min(Number.MAX_SAFE_INTEGER, selected * 2);
  return {cores:cpuIds.length, usableCores:usable.length, cpuIds:usable, freeMemory, load, personal, affinity, taskset,
    calculatedChecks, checks:selected, calculatedRuns, runs:runs ?? calculatedRuns,
    coresPerCheck:Math.max(1, Math.floor(usable.length / selected)), busy:load > usable.length};
}
const CAPACITY_LIFETIME = 31 * 60_000;
export async function configureCheckCapacity({env = process.env, checks, runs, owner = null}, ports = {}) {
  const p = portsFor(env, ports), observedAt = p.now();
  if (owner !== null && (typeof owner !== 'string' || !owner)) throw Error('Invalid check capacity owner.');
  const capacity = {...calculateCheckCapacity({checks,runs}, {...p,env}), owner, observedAt, expiresAt:observedAt + CAPACITY_LIFETIME};
  p.fs.mkdirSync(p.root, {recursive:true,mode:0o700});
  await underLock(p, () => {
    const path = join(p.root, 'capacity.json'), temp = `${path}.${p.uuid()}.tmp`;
    try { p.fs.writeFileSync(temp, JSON.stringify(capacity), {mode:0o600}); p.fs.renameSync(temp,path); }
    finally { try { p.fs.unlinkSync(temp); } catch {} }
  });
  return capacity;
}
export async function releaseCheckCapacity({env = process.env, owner}, ports = {}) {
  if (typeof owner !== 'string' || !owner) throw Error('Invalid check capacity owner.');
  const p = portsFor(env, ports), path = join(p.root,'capacity.json');
  try { p.fs.accessSync(path); } catch (error) { if (error.code === 'ENOENT') return false; throw error; }
  return underLock(p, () => {
    let value;
    try { value = JSON.parse(p.fs.readFileSync(path,'utf8')); } catch (error) { if (error.code === 'ENOENT') return false; throw error; }
    if (value.owner !== owner) return false;
    p.fs.unlinkSync(path); return true;
  });
}
function admissionCapacity(p, env) {
  let value;
  try { value = JSON.parse(p.fs.readFileSync(join(p.root,'capacity.json'),'utf8')); }
  catch (error) { if (error.code === 'ENOENT') return calculateCheckCapacity({}, {...p,env}); throw error; }
  if (!value || typeof value.personal !== 'boolean' || typeof value.affinity !== 'boolean'
    || value.owner !== null && (typeof value.owner !== 'string' || !value.owner)
    || !Number.isFinite(value.observedAt) || value.expiresAt !== value.observedAt + CAPACITY_LIFETIME
    || typeof value.busy !== 'boolean' || !Number.isSafeInteger(value.cores) || value.cores < 1
    || !Number.isSafeInteger(value.checks) || value.checks < 1 || !Number.isSafeInteger(value.runs) || value.runs < 1
    || value.usableCores !== (value.personal ? Math.max(1,Math.floor(value.cores/2)) : value.cores)
    || value.affinity !== (typeof value.taskset === 'string' && isAbsolute(value.taskset))
    || !value.affinity && value.taskset !== null) throw Error('Invalid saved machine check capacity.');
  // Revalidate saved observations, including the derived values, before using them.
  const result = calculateCheckCapacity({checks:value.checks,runs:value.runs}, {
    cores:()=>value.cpuIds, memory:()=>value.freeMemory, load:()=>value.load, platform:value.affinity?'linux':'other',
    battery:()=>false, taskset:()=>value.taskset,
  });
  if (result.usableCores !== value.usableCores || result.coresPerCheck !== value.coresPerCheck
    || result.busy !== value.busy || result.calculatedChecks !== value.calculatedChecks
    || result.calculatedRuns !== value.calculatedRuns) throw Error('Invalid saved machine check capacity.');
  if (p.now() >= value.expiresAt) return calculateCheckCapacity({}, {...p,env});
  return {...result, affinity:value.affinity, taskset:value.taskset};
}
export function readCheckStatus({env = process.env, checks, runs}, ports = {}) {
  const p = portsFor(env, ports), capacity = calculateCheckCapacity({checks,runs}, {...p,env}), all = records(p);
  return {...capacity, busyChecks:all.filter(row=>row.state==='running').length, waitingChecks:all.filter(row=>row.state==='waiting').length};
}
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
    execute: (command, options) => executeSuite(command, options, ports), uuid: randomUUID, ...ports, root: ports.queueRoot ?? suiteQueueRoot(env) };
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
      || row.cpuIds !== undefined && (!Array.isArray(row.cpuIds) || row.cpuIds.some(id=>!Number.isSafeInteger(id) || id<0) || new Set(row.cpuIds).size !== row.cpuIds.length)
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
    : suite.state === 'waiting' ? `waiting for a check slot (position ${suite.position})`
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
        const all = records(p), place = positionOf(all, row), capacity = admissionCapacity(p, env);
        const running = all.filter(other => other.state === 'running');
        const occupied = new Set(running.flatMap(other => other.cpuIds ?? []));
        const available = capacity.cpuIds.filter(id => !occupied.has(id));
        if (place === 1 && !capacity.busy && running.length < capacity.checks
          && (!capacity.affinity || running.every(other=>Array.isArray(other.cpuIds) && other.cpuIds.length) && available.length >= capacity.coresPerCheck)) {
          row.cpuIds = capacity.affinity ? available.slice(0, capacity.coresPerCheck) : [];
          row.coresPerCheck = capacity.coresPerCheck; row.taskset = capacity.affinity ? capacity.taskset : null;
          row.state = 'running'; row.startedAt = p.now(); save(p, row); return 0;
        }
        return place;
      });
      if (!position) break;
      if (position !== lastPosition) { p.say(`waiting for a check slot (position ${position})`); lastPosition = position; }
      await p.sleep(250);
    }
    p.say('running the full test suite');
    const result = await p.execute(command, { cwd, env:{...env,PDD_CHECK_CPUS:String(row.coresPerCheck)}, cpuIds:row.cpuIds, taskset:row.taskset, timeoutMs: Number(timeout) * 60_000,
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
export async function executeSuite(command, { cwd, env, timeoutMs, onChild, cpuIds = [], taskset = null }, ports = {}) {
  return new Promise(done => {
    const child = (ports.spawn ?? spawn)(taskset ?? '/bin/bash', taskset ? ['--cpu-list',cpuIds.join(','),'/bin/bash','-c',command] : ['-c', command], { cwd, env, detached: true, stdio: ['ignore', 'inherit', 'inherit'] });
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
