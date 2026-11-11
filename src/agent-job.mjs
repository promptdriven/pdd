// Generated from prompts/cli/agent-job.prompt.md (sha256: a8146af7cfae6e4173db9c318b9b391026a551bd3d99dd2269035061957b7410).
import { execFile, spawn, spawnSync } from 'node:child_process';
import { accessSync, closeSync, constants, openSync, readFileSync, renameSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { setPriority } from 'node:os';
import { join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const self = fileURLToPath(import.meta.url), GRACE_MS = 2000;
const SESSION_KEYS = /^(?:CLAUDECODE$|CLAUDE_CODE_|CLAUDE_PID$|CODEX_THREAD_ID$|CODEX_SANDBOX|HERDR_|PDD_AGENT_SESSION$|PDD_AUTOPILOT_CONTEXT$)/;
const readJson = file => { try { return JSON.parse(readFileSync(file, 'utf8')); } catch (error) { if (error.code === 'ENOENT') return undefined; return 'invalid'; } };
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
function writeAtomic(file, text) {
  const temp = `${file}.${process.pid}.tmp`;
  writeFileSync(temp, text, { mode: 0o600 }); renameSync(temp, file);
}

export function agentCommand(agent, { model } = {}) {
  const extra = model ? ['--model', model] : [];
  if (agent?.kind === 'codex') return { command: agent.command ?? 'codex', args: ['exec', '--json', '--dangerously-bypass-approvals-and-sandbox', '-c', 'features.multi_agent=false', ...extra, '-'] };
  // Claude streams its events (stream-json) so that its log grows while it works; the core reads the result file.
  if (agent?.kind === 'claude') return { command: agent.command ?? 'claude', args: ['-p', '--output-format', 'stream-json', '--verbose', '--permission-mode', 'bypassPermissions', ...extra] };
  throw Error('Autopilot core jobs need codex or claude');
}

export function jobEnvironment(env = {}) {
  return Object.fromEntries(Object.entries(env).filter(([key, value]) => typeof value === 'string' && !SESSION_KEYS.test(key)));
}

export function startAgentJob({ id, dir, cwd, command, args = [], input = '', env = {}, priority = null, pddCheck = null }, ports = {}) {
  if (!/^[A-Za-z0-9._-]+$/.test(String(id))) throw Error('Invalid job id');
  const base = join(resolve(dir), id), now = ports.now ?? Date.now;
  const job = { id, token: `${base}.spec.json`, log: `${base}.log`, exit: `${base}.exit.json`, result: `${base}.result.json`, input: `${base}.input` };
  writeFileSync(job.input, input, { mode: 0o600 });
  writeAtomic(job.token, JSON.stringify({ command, args, cwd, input: job.input, log: job.log, exit: job.exit, ...(priority ? { priority } : {}), ...(pddCheck ? { pddCheck } : {}) }));
  const child = (ports.spawn ?? spawn)(process.execPath, [self, '--wrapper', job.token], { cwd, env, detached: true, stdio: 'ignore' });
  // A spawn that fails later (a cwd that is gone, EAGAIN, ENOMEM) is an exit with code 127, never an uncaught error.
  child.on?.('error', error => { try { writeAtomic(job.exit, JSON.stringify({ code: 127, signal: null, at: now(), error: String(error.code ?? error.message) })); } catch { /* The job reads as dead. */ } });
  child.unref?.();
  return { ...job, pid: child.pid, started: now() };
}

function nativeAlive(pid, token) {
  try { process.kill(pid, 0); } catch (error) { if (error.code !== 'EPERM') return false; }
  const row = spawnSync('ps', ['-o', 'command=', '-p', String(pid)], { encoding: 'utf8', timeout: 5000 });
  return row.status === 0 && String(row.stdout).includes(token);
}

export function readAgentJob(job, ports = {}) {
  if (!object(job)) return { state: 'dead', exit: null, result: null, log: null };
  const alive = Number.isSafeInteger(job?.pid) && job.pid > 0 && (ports.alive ?? nativeAlive)(job.pid, job.token);
  const exit = readJson(job.exit), result = readJson(job.result);
  // The log's size and change time show progress while the job runs.
  let log = null;
  try { const stat = statSync(job.log); log = { size: stat.size, mtime: stat.mtimeMs }; } catch { /* No log yet. */ }
  return { state: alive ? 'running' : object(exit) ? 'exited' : 'dead', exit: object(exit) ? exit : null,
    result: result === undefined ? null : object(result) ? result : 'invalid', log };
}

// CPU seconds of each process under the job, by pid, without the wrapper and its direct child (the agent CLI or the
// suite runner). A child that starts its own process group still counts: the tree follows parent pids. null when the
// process table cannot be read.
const cpuSeconds = text => {
  const [days, clock] = String(text).includes('-') ? String(text).split('-') : ['0', String(text)];
  return clock.split(':').reduce((sum, part) => sum * 60 + Number(part), 0) + Number(days) * 86400;
};
export function agentJobCpu(job, ports = {}) {
  if (!(Number.isSafeInteger(job?.pid) && job.pid > 0)) return null;
  const table = (ports.spawnSync ?? spawnSync)('ps', ['-A', '-o', 'pid=,ppid=,time='], { encoding: 'utf8', timeout: 5000 });
  if (table.status !== 0) return null;
  const rows = String(table.stdout).split('\n').map(line => line.trim().split(/\s+/)).filter(row => row.length === 3).map(([pid, ppid, time]) => ({ pid: Number(pid), ppid: Number(ppid), cpu: cpuSeconds(time) }));
  const children = new Map();
  for (const row of rows) children.set(row.ppid, [...(children.get(row.ppid) ?? []), row]);
  const found = {}, queue = (children.get(job.pid) ?? []).flatMap(cli => children.get(cli.pid) ?? []);
  for (let i = 0; i < queue.length && i < 2000; i++) {
    const row = queue[i];
    if (Number.isFinite(row.cpu)) found[row.pid] = row.cpu;
    queue.push(...(children.get(row.pid) ?? []));
  }
  return found;
}

export function stopAgentJob(job, ports = {}) {
  if (!(Number.isSafeInteger(job?.pid) && job.pid > 0 && (ports.alive ?? nativeAlive)(job.pid, job.token))) return false;
  try { (ports.kill ?? process.kill)(-job.pid, 'SIGTERM'); } catch { try { (ports.kill ?? process.kill)(job.pid, 'SIGTERM'); } catch { return false; } }
  return true;
}

// The lowest priority for every job (#3231), for the child, not for the wrapper: the wrapper only waits, and it must
// answer a stop at once on a busy machine. `nice -n 19` (nice and taskpolicy and taskset run the command in the same
// process, so the CPU watch sees the same tree), then macOS utility QoS (it also lowers disk I/O; no extra disk
// throttle, which kept stopped jobs alive on a busy disk) or a Linux CPU list (taskset) for Autopilot's share.
const TASKPOLICY = '/usr/sbin/taskpolicy', NICE = '/usr/bin/nice';
const executable = file => { try { accessSync(file, constants.X_OK); return true; } catch { return false; } };
const niceOf = spec => Number.isSafeInteger(spec?.priority?.nice) ? spec.priority.nice : 19;
export function jobCommand(spec, platform = process.platform, ports = {}) {
  const p = spec?.priority ?? {}, can = ports.executable ?? executable, qos = p.qos === undefined ? 'utility' : p.qos;
  let run = { command: spec.command, args: spec.args ?? [] };
  if (platform === 'darwin' && qos && can(TASKPOLICY)) run = { command: TASKPOLICY, args: ['-c', qos, run.command, ...run.args] };
  else if (platform === 'linux' && typeof p.cpus === 'string' && /^[0-9,-]+$/.test(p.cpus) && typeof p.taskset === 'string' && p.taskset.startsWith('/'))
    run = { command: p.taskset, args: ['--cpu-list', p.cpus, run.command, ...run.args] };
  return niceOf(spec) > 0 && can(NICE) ? { command: NICE, args: ['-n', String(niceOf(spec)), run.command, ...run.args] } : run;
}
// #3177: the pdd that the agent's own login shell finds (Codex runs each command in one, and a profile can put an older
// pdd first on PATH). When it is not the engine's version, one line goes to the job log and to ID.pdd-check.json, for
// the status; the agent uses "$PDD_CLI" either way. A failed check writes nothing.
export const pddCheckFile = log => String(log).replace(/\.log$/, '') + '.pdd-check.json';
export function pddCheckLine({ found, path, version, engine, cli }) {
  if (found && version === engine) return null;
  return `pdd check: the agent shell finds ${found ? `pdd ${version ?? '(unknown version)'} at ${path}` : 'no pdd on PATH'}; the engine is ${engine}; using PDD_CLI (${cli})`;
}
export function checkShellPdd(spec, out, ports = {}) {
  const shell = process.env.SHELL && process.env.SHELL.startsWith('/') ? process.env.SHELL : '/bin/sh';
  // A marker line separates the two answers from anything that a profile prints.
  const script = 'echo "@pdd-path $(command -v pdd || true)"; echo "@pdd-version $(pdd --version 2>/dev/null | head -n 5 | tr "\\n" " ")"';
  (ports.execFile ?? execFile)(shell, ['-lc', script], { cwd: spec.cwd, env: process.env, timeout: 20000, encoding: 'utf8' }, (error, stdout) => {
    const text = String(stdout ?? ''), answer = name => new RegExp(`^@pdd-${name} ?(.*)$`, 'm').exec(text)?.[1]?.trim() ?? null;
    if (answer('path') === null) return;
    const path = answer('path') || null, version = path ? /\b(\d+\.\d+\.\d+)\b/.exec(answer('version') ?? '')?.[1] ?? null : null;
    const record = { at: Date.now(), found: Boolean(path), path, version, engine: spec.pddCheck.version ?? null, cli: spec.pddCheck.cli ?? null };
    record.line = pddCheckLine(record);
    try { writeAtomic(pddCheckFile(spec.log), JSON.stringify(record)); if (record.line) writeSync(out, `${record.line}\n`); } catch { /* The check is a note only. */ }
  });
}
// The skills that the agent's tools load by default (pddCheck.skills.read, for example ~/.agents/skills) against the
// engine's own skills: another version gives one line in the job log and ID.skills-check.json; the agent reads
// "$PDD_SKILLS" either way. Missing or unreadable folders write nothing.
export const skillsCheckFile = log => String(log).replace(/\.log$/, '') + '.skills-check.json';
const skillVersion = folder => { try { return /^\s*pdd-skills:\s*(\d+\.\d+\.\d+)\s*$/m.exec(readFileSync(join(folder, 'pdd-feature', 'SKILL.md'), 'utf8'))?.[1] ?? null; } catch { return null; } };
export function checkSkills(spec, out) {
  const skills = spec.pddCheck?.skills;
  if (!skills?.version || !Array.isArray(skills.read)) return null;
  const found = skills.read.map(folder => ({ folder, version: skillVersion(folder) })).filter(row => row.version), other = found.filter(row => row.version !== skills.version);
  const record = { at: Date.now(), found, engine: skills.version, dir: skills.dir ?? null,
    line: other.length ? `pdd check: installed skills are ${other.map(row => `${row.version} at ${row.folder}`).join(' and ')}, the engine is ${skills.version}; jobs use PDD_SKILLS (${skills.dir})` : null };
  try { writeAtomic(skillsCheckFile(spec.log), JSON.stringify(record)); if (record.line) writeSync(out, `${record.line}\n`); } catch { /* The check is a note only. */ }
  return record;
}
// With no nice program, the wrapper lowers its own nice value instead (every child inherits it).
function lowerPriority(spec) {
  if (executable(NICE)) return;
  try { setPriority(0, niceOf(spec)); } catch { /* A lower priority is best effort. */ }
}
// The detached wrapper: it owns the agent process and records how it ended.
function wrap(specFile) {
  const spec = JSON.parse(readFileSync(specFile, 'utf8'));
  lowerPriority(spec);
  const stdin = openSync(spec.input, 'r'), out = openSync(spec.log, 'a', 0o600);
  let finished = false, stopping = null, ended = null, child;
  const finish = (code, signal, group = false) => {
    if (finished) return; finished = true;
    try {
      try { writeAtomic(spec.exit, JSON.stringify({ code, signal: signal ?? null, at: Date.now() })); }
      finally { for (const fd of [stdin, out]) try { closeSync(fd); } catch { /* Already closed. */ } }
    } catch { /* The exit record is best effort; the job then reads as dead. */ }
    finally {
      // A stop ends the whole group (this wrapper leads it), also after a failed write: no process that waits after the
      // first SIGTERM survives.
      if (group) try { process.kill(-process.pid, 'SIGKILL'); } catch { /* Only this wrapper is left. */ }
      process.exit(0);
    }
  };
  const stop = signal => {
    if (stopping) return; stopping = signal;
    try { process.kill(-process.pid, 'SIGTERM'); } catch { try { child?.kill('SIGTERM'); } catch { /* The child may already be gone. */ } }
    // A kept timer: the wrapper waits the grace time also when its direct child exits at once (sh does).
    setTimeout(() => finish(ended?.code ?? null, ended?.signal ?? signal, true), GRACE_MS);
  };
  for (const signal of ['SIGTERM', 'SIGINT', 'SIGHUP']) process.on(signal, () => stop(signal));
  const run = jobCommand(spec);
  try { child = spawn(run.command, run.args, { cwd: spec.cwd, env: process.env, stdio: [stdin, out, out] }); }
  catch (error) { writeFileSync(out, `agent-job: ${error.message}\n`); finish(127, null); return; }
  child.on('error', error => { try { writeFileSync(out, `agent-job: ${error.message}\n`); } catch {} finish(127, null); });
  // A group stop can reach the child before the wrapper's own handler runs: a child killed by a stop signal is that
  // stop, so the whole group still ends after the grace time (no process that ignores SIGTERM is left behind).
  child.on('exit', (code, signal) => { if (stopping) ended = { code, signal }; else if (['SIGTERM', 'SIGINT', 'SIGHUP'].includes(signal)) { ended = { code, signal }; stop(signal); } else finish(code, signal); });
  if (spec.pddCheck) { checkSkills(spec, out); checkShellPdd(spec, out); }
}

if (process.argv[1] && resolve(process.argv[1]) === self && process.argv[2] === '--wrapper') wrap(process.argv[3]);
