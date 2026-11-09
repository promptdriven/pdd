// Generated from prompts/cli/test-suite-queue.prompt.md (sha256: b1e53593c12693d9f4394249e176c5e5aa93c22d6adda8960d7b35a30c4ff516).
import {knownSecretValues, rememberSecrets} from './secret-redaction.mjs';
import * as files from 'node:fs';
import {serializeValidationReceipt, safeEvidenceText} from './validation-evidence.mjs';
import { join, isAbsolute, resolve } from 'node:path';
import { createHash, hash as contentDigest, randomUUID } from 'node:crypto';
import { spawn, spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { machineCheckPorts } from './machine-resources.mjs';

export function calculateCheckCapacity({checks, runs} = {}, ports = {}) {
  const native = machineCheckPorts(ports.env ?? process.env, ports);
  ports = {...ports};
  for (const [name, value] of Object.entries(native)) ports[name] ??= value;
  const cpuIds = ports.cores(), freeMemory = ports.memory(),
    load = ports.load(), platform = ports.platform ?? process.platform;
  const battery = platform === 'linux' ? ports.battery() : false;
  const virtualized = platform === 'linux' ? ports.virtualized() : false;
  const personal = platform === 'darwin' || platform === 'linux' && (battery || !virtualized);
  const taskset = platform === 'linux' ? ports.taskset() : null;
  if (typeof platform !== 'string' || typeof battery !== 'boolean' || typeof virtualized !== 'boolean' || !Array.isArray(cpuIds) || !cpuIds.length || cpuIds.some(id => !Number.isSafeInteger(id) || id < 0)
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
export async function configureCheckCapacity({env = process.env, checks, runs, owner = null, resources}, ports = {}) {
  const p = portsFor(env, ports), observedAt = p.now();
  if (owner !== null && (typeof owner !== 'string' || !owner)) throw Error('Invalid check capacity owner.');
  const shared = resources ? {
    memory:()=>resources.memory?.available, load:()=>resources.load,
    ...(resources.check ? {cores:()=>resources.check.cpuIds, platform:resources.check.platform,
      battery:()=>resources.check.battery, virtualized:()=>resources.check.virtualized, taskset:()=>resources.check.taskset} : {}),
  } : {};
  const capacity = {...calculateCheckCapacity({checks,runs}, {...p,env,...shared}), owner, observedAt, expiresAt:observedAt + CAPACITY_LIFETIME};
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
    battery:()=>false, virtualized:()=>true, taskset:()=>value.taskset,
  });
  if (result.usableCores !== value.usableCores || result.coresPerCheck !== value.coresPerCheck
    || result.busy !== value.busy || result.calculatedChecks !== value.calculatedChecks
    || result.calculatedRuns !== value.calculatedRuns) throw Error('Invalid saved machine check capacity.');
  if (p.now() >= value.expiresAt) return calculateCheckCapacity({}, {...p,env});
  return {...result, cores:value.cores, personal:value.personal, affinity:value.affinity, taskset:value.taskset};
}
export function readCheckStatus({env = process.env, checks, runs}, ports = {}) {
  const p = portsFor(env, ports), capacity = admissionCapacity(p, env), all = records(p);
  return {...capacity, busyChecks:all.filter(row=>row.state==='running').length, waitingChecks:all.filter(row=>row.state==='waiting').length};
}
const delay = ms => new Promise(done => setTimeout(done, ms));
const alive = pid => {
  if (pid < 0) return groupAlive(-pid) !== false;
  try { process.kill(pid, 0); return true; }
  catch (error) { return error.code !== 'ESRCH'; }
};
function groupAlive(pgid) {
  try { process.kill(-pgid,0); } catch (error) { return error.code === 'ESRCH' ? false : null; }
  if (process.platform !== 'linux') return true;
  // Orphaned zombies cannot execute or hold resources for a validation command.
  // A permission or parse error is uncertainty, never evidence of termination.
  try {
    for (const name of files.readdirSync('/proc').filter(name=>/^\d+$/.test(name))) {
      let stat;
      try { stat = files.readFileSync(`/proc/${name}/stat`,'utf8'); }
      catch (error) { if (error.code === 'ENOENT' || error.code === 'ESRCH') continue; return null; }
      const fields = stat.slice(stat.lastIndexOf(') ')+2).split(' ');
      if (fields.length < 3) return null;
      if (Number(fields[2]) === pgid && !['Z','X'].includes(fields[0])) return true;
    }
    return false;
  } catch { return null; }
}
export function suiteQueueRoot(env = process.env) {
  const root = env.PDD_SUITE_QUEUE ?? (env.PDD_VM_SUITE_LOCK ? `${env.PDD_VM_SUITE_LOCK}.queue` : `/tmp/pdd-full-suite-${process.getuid?.() ?? 'user'}`);
  if (!isAbsolute(root)) throw Error('The shared suite queue needs an absolute path.');
  return root;
}
function processIdentity(pid) {
  try { return files.readFileSync(`/proc/${pid}/stat`, 'utf8').split(') ').at(-1).split(' ')[19]; }
  catch { return null; }
}
function sourceIdentity(cwd, p) {
  const source = {head:null, fingerprint:null, runId:null, issue:null, error:null};
  let gitCwd = cwd;
  const git = args => {
    const result = p.git(args, gitCwd);
    if (result.status !== 0) throw Error('Git source identity unavailable.');
    return result.stdout;
  };
  try {
    source.head = git(['rev-parse','HEAD']).trim();
    gitCwd = git(['rev-parse','--show-toplevel']).trim();
    const hash = createHash('sha256').update(git(['diff','--binary','HEAD','--']));
    for (const path of git(['ls-files','--others','--exclude-standard','-z']).split('\0').filter(Boolean).sort()) {
      hash.update(path).update('\0');
      const full = join(gitCwd,path);
      hash.update(p.fs.lstatSync(full).isSymbolicLink() ? p.fs.readlinkSync(full) : p.fs.readFileSync(full));
      hash.update('\0');
    }
    source.fingerprint = hash.digest('hex');
    const root = resolve(gitCwd,git(['rev-parse','--git-common-dir']).trim(),'pdd/runs');
    if (p.fs.existsSync(root)) for (const name of p.fs.readdirSync(root)) {
      const path = join(root,name,'status.json');
      if (!p.fs.existsSync(path)) continue;
      const run = JSON.parse(p.fs.readFileSync(path,'utf8'));
      if (run.root === resolve(gitCwd)) { source.runId = run.runId ?? null; source.issue = run.number ?? null; break; }
    }
  } catch (error) { source.error = error.code ?? error.message; }
  return source;
}
function portsFor(env, ports) {
  return { fs: files, now: Date.now, sleep: delay, alive, pid: process.pid, say: text => process.stdout.write(`${text}\n`),
    execute: (command, options) => ports.spawn ? executeSuite(command, options, ports) : executeRecordedSuite(command, options, ports),
    processIdentity, git:(args,cwd) => spawnSync('git',args,{cwd,encoding:'utf8',maxBuffer:64*1024*1024,timeout:5000,env:{PATH:env.PATH ?? '/usr/bin:/bin',HOME:env.HOME,LC_ALL:env.LC_ALL ?? 'C',GIT_CONFIG_NOSYSTEM:'1',GIT_CONFIG_GLOBAL:'/dev/null'}}), uuid: randomUUID, ...ports, root: ports.queueRoot ?? suiteQueueRoot(env) };
}
function save(p, record) {
  const target = join(p.root, `ticket-${record.ticket}.json`), temp = `${target}.${p.uuid()}.tmp`;
  try { p.fs.writeFileSync(temp, serializeValidationReceipt(record), { mode: 0o600 }); p.fs.renameSync(temp, target); }
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
    const recorderLive = row.recorderPid && p.alive(row.recorderPid)
      && (!row.recorderIdentity || p.processIdentity(row.recorderPid) === row.recorderIdentity);
    if (row.state !== 'finished' && !recorderLive && !p.alive(row.pid)
      && (row.state === 'waiting' || row.childPid && !p.alive(-row.childPid))) {
      return { ...row, state: 'finished', finishedAt: p.fs.statSync(join(p.root, name)).mtimeMs,
        outcome:'unknown', exitCode:null, counts:null,
        reason: 'Test suite runner ended before reporting a result.' };
    }
    if (row.state !== 'finished' && !recorderLive && !p.alive(row.pid)) return { ...row,
      outcome:'unknown', exitCode:null, counts:null,
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
  catch (error) { return { state: 'unavailable', reason: safeEvidenceText(error.message), pausedMs: 0 }; }
  const own = all.filter(row => row.cwd === resolve(cwd));
  if (!own.length) return null;
  const row = own.findLast(row => row.state !== 'finished') ?? own.at(-1);
  return { ticket: row.ticket, state: row.state, position: row.state === 'waiting' ? positionOf(all, row) : null,
    queuedAt: row.queuedAt, startedAt: row.startedAt, finishedAt: row.finishedAt, reason: row.reason,
    pausedMs: pausedTime(own, since, p.now()),
    ...Object.fromEntries(['command','commandFingerprint','evidence','source','logPath','receiptPath','recorderPid','recorderIdentity','childPid','exitCode','signal','counts','outcome'].map(key=>[key,row[key] ?? null])) };
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
  rememberSecrets(...knownSecretValues(env));
  let p, row, environmentRoot, executionStarted = false, keepEnvironment = false;
  try {
    p = portsFor(env, ports);
    p.fs.mkdirSync(p.root, { recursive: true, mode: 0o700 });
    row = await underLock(p, () => {
      const all = records(p), ticket = (all.at(-1)?.ticket ?? 0) + 1;
      const record = { ticket, pid: p.pid, childPid: null, cwd: resolve(cwd), state: 'waiting', queuedAt: p.now(), startedAt: null, finishedAt: null, reason: null, environmentPolicy: 'clean-v1' };
      const logFolder = join(env.PDD_STATE_DIR ?? join(env.HOME || process.env.HOME,'.local','state','pdd'), 'validation', createHash('sha256').update(p.root).digest('hex').slice(0,20));
      // Content identity for a validation attempt; never used to verify a password.
      Object.assign(record, {command:'[redacted]', commandFingerprint:contentDigest('sha256', command, 'hex'), source:ports.source ? ports.source(cwd) : sourceIdentity(cwd,p),
        logPath:null, receiptPath:join(p.root,`ticket-${ticket}.json`),
        recorderPid:null, recorderIdentity:null, exitCode:null, signal:null, counts:null, outcome:'running'});
      for (;;) {
        record.logPath = join(logFolder, `validation-${ticket}-${p.uuid()}.log`);
        // Validate each candidate before creating even an empty log.
        serializeValidationReceipt(record);
        p.fs.mkdirSync(logFolder, {recursive:true,mode:0o700});
        try { p.fs.writeFileSync(record.logPath, '', {mode:0o600,flag:'wx'}); break; }
        catch (error) { if (error.code !== 'EEXIST') throw error; }
      }
      try { save(p, record); }
      catch (error) { try { p.fs.unlinkSync(record.logPath); } catch {} throw error; }
      return record;
    });
    if (ports.announceReceipt !== false) p.say(`Validation receipt: ${row.receiptPath}; output evidence: ${row.logPath}`);
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
          row.source = ports.source ? ports.source(cwd) : sourceIdentity(cwd,p);
          row.state = 'running'; row.startedAt = p.now(); save(p, row); return 0;
        }
        return place;
      });
      if (!position) break;
      if (position !== lastPosition) { p.say(`waiting for a check slot (position ${position})`); lastPosition = position; }
      await p.sleep(250);
    }
    p.say('running the full test suite');
    environmentRoot = p.fs.mkdtempSync(join(p.root, 'suite-env-'));
    const childEnv = Object.fromEntries(Object.entries(env).filter(([key, value]) =>
      typeof value === 'string' && /^(?:PATH|LANG|LANGUAGE|LC_[A-Z_]+|TZ|TERM|CI|SystemRoot|WINDIR)$/.test(key)));
    childEnv.PATH ??= '/usr/bin:/bin';
    childEnv.POCKET_BROWSER_BIN = env.POCKET_BROWSER_BIN ?? '/usr/bin/google-chrome';
    for (const [folder, names] of [
      ['home', ['HOME', 'USERPROFILE']], ['state', ['PDD_STATE_DIR']],
      ['config', ['XDG_CONFIG_HOME']], ['tmp', ['TMPDIR', 'TMP', 'TEMP']],
      ['interpreter-queue', ['PDD_INTERPRETER_QUEUE']],
    ]) {
      const path = join(environmentRoot, folder);
      p.fs.mkdirSync(path, {mode:0o700});
      for (const name of names) childEnv[name] = path;
    }
    childEnv.PDD_CHECK_CPUS = String(row.coresPerCheck);
    executionStarted = true;
    const result = await p.execute(command, { cwd, env:childEnv, cpuIds:row.cpuIds, taskset:row.taskset, timeoutMs: Number(timeout) * 60_000,
      record:row, environmentRoot, secrets:knownSecretValues(env),
      onRecorder: pid => { row.recorderPid = pid; row.recorderIdentity = p.processIdentity(pid); save(p,row); keepEnvironment = true; },
      onChild: pid => { row.childPid = pid; save(p, row); } });
    if (result.record) row = result.record;
    else {
      const confirmed = result.ownershipConfirmed !== false;
      if (!confirmed) keepEnvironment = true;
      row.exitCode = confirmed ? result.exitCode : null; row.signal = result.signal ?? null;
      row.outcome = confirmed ? 'completed' : 'unknown';
      row.state = confirmed ? 'finished' : 'running'; row.finishedAt = confirmed ? p.now() : null;
      row.reason = result.reason == null ? (!confirmed ? 'Test suite descendant ownership is unknown.' : result.exitCode ? `Test suite exited with status ${result.exitCode}.` : null) : safeEvidenceText(result.reason);
      save(p, row);
    }
    if (ports.announceReceipt !== false) p.say(`Validation receipt: ${row.receiptPath}; output evidence: ${row.logPath}`);
    return { exitCode: result.ownershipConfirmed === false ? 1 : result.exitCode, message: row.reason ? safeEvidenceText(row.reason) : 'Full test suite finished.' };
  } catch (error) {
    // Setup cannot have a child. Once execution starts, keep the reservation
    // unless the reported child group is confirmed dead.
    if (p && row && (!executionStarted || row.state === 'waiting' || row.childPid && !p.alive(-row.childPid))) {
      row.state = 'finished'; row.finishedAt = p.now(); row.exitCode = 1; row.outcome = 'completed'; row.reason = safeEvidenceText(`Test suite failed: ${error.code ?? error.message}`);
      try { save(p, row); } catch {}
    }
    return { exitCode: 1, message: safeEvidenceText(`Shared test suite queue failed: ${error.code ?? error.message}`) };
  } finally {
    if (environmentRoot && !keepEnvironment) p.fs.rmSync(environmentRoot, {recursive:true, force:true});
  }
}
export async function executeSuite(command, { cwd, env, timeoutMs, onChild, onOutput, startGate = false, cpuIds = [], taskset = null }, ports = {}) {
  return new Promise(done => {
    const file = taskset ?? '/bin/bash', args = taskset ? ['--cpu-list',cpuIds.join(','),'/bin/bash','-c',command] : ['-c',command];
    const child = (ports.spawn ?? spawn)(startGate ? '/bin/bash' : file,
      startGate ? ['-c','read -r _pdd_gate; exec "$@" </dev/null','pdd-suite-gate',file,...args] : args,
      {cwd,env,detached:true,stdio:[startGate ? 'pipe' : 'ignore',onOutput ? 'pipe' : 'inherit',onOutput ? 'pipe' : 'inherit']});
    if (onOutput) for (const stream of ['stdout','stderr']) child[stream]?.on('data', bytes => {
      try { onOutput(stream,bytes); } catch (error) { stop(1, `Test suite output could not be saved: ${error.code ?? error.message}`); }
    });
    child.stdin?.on('error', () => {});
    let reason = null, forcedCode = null, escalation;
    const killGroup = signal => { if (child.pid) { try { (ports.kill ?? process.kill)(-child.pid, signal); } catch (error) { if (error.code !== 'ESRCH') throw error; } } };
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
    let settled = false;
    const finish = async result => {
      if (settled) return;
      settled = true; cleanup();
      let ownershipConfirmed = !child.pid;
      if (child.pid) for (let attempt=0;attempt<=100;attempt++) {
        let live;
        try { live = (ports.groupAlive ?? groupAlive)(child.pid); } catch { live = null; }
        if (live === false) { ownershipConfirmed = true; break; }
        if (attempt < 100) await (ports.sleep ?? delay)(20);
      }
      done(ownershipConfirmed ? {...result,...(result.reason == null ? {} : {reason:safeEvidenceText(result.reason)}),ownershipConfirmed:true} : {exitCode:1,signal:result.signal ?? null,
        reason:'Test suite descendants could not be confirmed stopped.',ownershipConfirmed:false});
    };
    child.once('error', error => { void finish({exitCode:1, reason:`Test suite could not start: ${error.code ?? error.message}`}); });
    child.once('close', (code, signal) => { void finish({ signal, exitCode: forcedCode ?? code ?? 1, reason: reason ?? (signal ? `Test suite ended by ${signal}.` : null) }); });
    try { if (child.pid) onChild(child.pid); if (startGate) child.stdin.end('\n'); }
    catch (error) { stop(1, `Test suite could not save its child ownership: ${error.code ?? error.message}`); }
  });
}

// The recorder starts no command until its caller has saved its custody.
async function executeRecordedSuite(command, options, ports) {
  return new Promise((done, reject) => {
    const child = spawn(process.execPath, [fileURLToPath(new URL('./test-suite-recorder.mjs',import.meta.url))],
      {cwd:options.cwd,env:options.env,detached:true,stdio:['ignore','ignore','ignore','ipc']});
    let terminal = false;
    const cancel = signal => { if (child.connected) child.send({cancel:signal},()=>{}); };
    const interrupt = () => cancel('SIGINT'), terminate = () => cancel('SIGTERM');
    process.on('SIGINT',interrupt); process.on('SIGTERM',terminate);
    const cleanup = () => { process.off('SIGINT',interrupt); process.off('SIGTERM',terminate); };
    child.once('error', error => { cleanup(); reject(error); });
    child.once('exit', () => { cleanup(); if (!terminal) reject(Error('Validation recorder ended without a terminal receipt.')); });
    child.on('message', message => {
      if (message.stream) {
        const output = ports[message.stream] ?? process[message.stream];
        // Output is already durable. A closed terminal cannot undo that write.
        try { output.write(Buffer.from(message.bytes,'base64')); } catch {}
      }
      if (message.result) { terminal = true; done(message.result); }
    });
    child.once('spawn', () => {
      try {
        options.onRecorder(child.pid);
        const {cwd,env,timeoutMs,cpuIds,taskset,record,environmentRoot,secrets} = options;
        child.send({start:{command,cwd,env,timeoutMs,cpuIds,taskset,record,environmentRoot,secrets}},()=>{});
      } catch (error) { child.disconnect(); reject(error); }
    });
  });
}
