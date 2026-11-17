// Generated from prompts/cli/autopilot-logs.prompt.md.
import * as files from 'node:fs';
import { dirname, basename, join, resolve } from 'node:path';
import { setTimeout as sleep } from 'node:timers/promises';
import { stripVTControlCharacters } from 'node:util';
import { inspectAgentJob } from './agent-job.mjs';
import { readSuiteProgress } from './test-suite-queue.mjs';

const LIMIT = 64 * 1024;
const safe = text => stripVTControlCharacters(String(text)).replace(/[\x00-\x1f\x7f-\x9f\u202a-\u202e\u2066-\u2069]/g, ' ');
const time = value => Number.isFinite(value) && Math.abs(value) <= 8.64e15 ? new Date(value).toISOString() : 'unknown';
const newest = (...values) => Math.max(...values.filter(Number.isFinite));
const withLine = (name, value) => value ? `\n  ${name}: ${safe(value)}` : '';

export function describeWorkerProcess({ role, processState, exitCode, signal, queueState, position, lastActivity, log, evidence }) {
  const wrapper = processState === 'running' ? 'wrapper running'
    : processState === 'dead' ? 'wrapper not running (no exit record)'
    : `wrapper exited${Number.isInteger(exitCode) ? ` (status ${exitCode})` : signal ? ` (${safe(signal)})` : ''}`;
  const queue = {
    waiting: `waiting for a check slot${Number.isSafeInteger(position) ? ` (position ${position})` : ''}`,
    starting: 'tests have not started', running: 'tests running', finished: 'test receipt finished',
    stale: 'no live test process confirmed (stale or uncertain receipt)', unavailable: 'test queue evidence unavailable',
  }[queueState];
  return `${safe(role)}: ${wrapper}${queue ? `; ${queue}` : ''}; last activity ${safe(lastActivity)}`
    + withLine('Log', log) + withLine('Evidence', evidence);
}

function stat(fs, file) {
  try { const item = fs.lstatSync(file); if (item.isFile()) return item; } catch {}
  return null;
}

function readWorkers(fs, root) {
  const dir = join(root, 'jobs');
  let names;
  try { names = fs.readdirSync(dir); } catch (error) { if (error.code === 'ENOENT') return []; throw error; }
  return names.filter(name => /^[1-9]\d*\.json$/.test(name)).flatMap(name => {
    const file = join(dir, name), saved = stat(fs, file);
    if (!saved) return [];
    try {
      const job = JSON.parse(fs.readFileSync(file, 'utf8'));
      return job?.issue === Number(basename(name, '.json')) && Number.isSafeInteger(job.issue) ? [{ job, savedAt: saved.mtimeMs }] : [];
    } catch { return []; }
  }).sort((left, right) => left.job.issue - right.job.issue);
}

const hasIssue = (job, issue) => Array.isArray(job.issues) && job.issues.includes(issue);
const choose = (workers, issue) => workers.find(({ job }) => job.issue === issue) ?? workers.find(({ job }) => hasIssue(job, issue));

function groupAlive(pid) {
  try { process.kill(-pid, 0); return true; } catch { return false; }
}

function checkProgress(role, part, job, seen, env, ports) {
  if (!['suite', 'replay'].includes(role) || typeof part.cwd !== 'string') return { state: 'none' };
  const live = seen.state === 'running', since = part.agent.started;
  const receipt = ports.queue.read({ cwd: part.cwd, since, env });
  if (!receipt) return { state: live ? 'starting' : 'none' };
  if (receipt.state === 'unavailable') return receipt;
  const head = job.head ?? part.head;
  if (!Number.isFinite(since) || receipt.queuedAt < since || (part.head && part.head !== head)
    || (head && receipt.source?.head && receipt.source.head !== head)) return { state: 'stale' };
  const child = receipt.childPid;
  const state = receipt.outcome === 'unknown' ? 'stale'
    : receipt.state === 'finished' ? 'finished'
    : !live ? 'stale'
    : receipt.state === 'waiting' ? 'waiting'
    : child == null ? 'starting'
    : Number.isSafeInteger(child) && child > 0 && ports.process.groupAlive(child) ? 'running' : 'stale';
  return { ...receipt, state };
}

function processView(role, part, job, logDir, env, ports) {
  const agent = part.agent, { fs } = ports;
  const local = (path, suffix) => typeof path === 'string' && dirname(path) === logDir
    && basename(path).startsWith(`${job.issue}-`) && path.endsWith(suffix) ? path : null;
  const regular = (path, suffix) => { const owned = local(path, suffix); return stat(fs, owned) ? owned : null; };
  const log = local(agent.log, '.log'), exit = regular(agent.exit, '.exit.json'), result = regular(agent.result, '.result.json');
  const seen = ports.jobs.inspect({ ...agent, token: local(agent.token, '.spec.json'), exit, log: regular(log, '.log') });
  const check = checkProgress(role, part, job, seen, env, ports);
  const last = newest(agent.started, seen.log?.mtime, seen.exit?.at, stat(fs, result)?.mtimeMs,
    check.queuedAt, check.startedAt, check.finishedAt, stat(fs, check.logPath)?.mtimeMs);
  const fields = { role, processState: seen.state, exitCode: seen.exit?.code, signal: seen.exit?.signal, queueState: check.state,
    position: check.position, log: seen.log ? log : null, evidence: stat(fs, check.receiptPath) ? check.receiptPath : null };
  const notes = withLine('Test log', stat(fs, check.logPath) ? check.logPath : null)
    + withLine('Result', result) + withLine('Exit', exit) + withLine('Check', check.reason);
  return { log, role, last, display: describeWorkerProcess({ ...fields, lastActivity: time(last) }) + notes,
    signature: JSON.stringify(fields) + notes };
}

function workerView({ job, savedAt }, root, env, ports) {
  const companions = Array.isArray(job.issues) ? job.issues.filter(issue => Number.isSafeInteger(issue) && issue !== job.issue) : [];
  const stage = job.phase === 'pr' ? 'PR checks' : job.phase === 'running' ? job.role ?? 'worker' : job.phase ?? 'unknown';
  const title = `#${job.issue}${companions.length ? ` (also ${companions.map(issue => `#${issue}`).join(', ')})` : ''} — ${safe(stage)}`
    + (Number.isSafeInteger(job.pr) ? ` · PR #${job.pr}` : '');
  const stop = job.stepStop, runtime = job.runtimeWait;
  const blockers = [
    stop && !stop.resumed && (stop.held || stop.until > ports.clock.now()) ? `Waiting: ${safe(stop.text ?? 'retry')}${stop.until ? ` (retry after ${time(stop.until)})` : ''}` : null,
    runtime?.state === 'waiting' && runtime.head === (job.agentHead ?? job.head) ? `Waiting for Runtime maintenance${runtime.until ? ` until ${time(runtime.until)}` : ''}` : null,
    job.lane?.state === 'waiting' ? `Waiting for the merge lane${job.lane.holder ? ` (PR #${safe(job.lane.holder)})` : ''}` : null,
    job.end?.cause?.text ? `Ending: ${safe(job.end.cause.text)}` : null,
    job.lastError ? `Last error: ${safe(job.lastError)}` : null,
  ].filter(Boolean);
  const parts = [[job.role ?? 'worker', job], ['review', job.review], ['replay', job.vectors], ['suite', job.suite], ['Runtime', runtime]]
    .filter(([, part]) => part?.agent && typeof part.agent === 'object')
    .map(([role, part]) => processView(role, part, job, join(root, 'logs'), env, ports));
  const last = newest(savedAt, job.started, job.progress?.at, ...parts.map(part => part.last));
  const display = [`${title} · last activity ${time(last)}`, ...blockers,
    ...(parts.length ? parts.map(part => part.display) : ['No worker process recorded.'])].join('\n');
  return { display, signature: JSON.stringify([title, blockers, ...parts.map(part => part.signature)]), parts };
}

function readable(text) {
  let event;
  if (text.startsWith('{')) try { event = JSON.parse(text); } catch {}
  if (event?.item?.text && typeof event.item.text === 'string') text = event.item.text;
  else if (event?.item?.command && typeof event.item.command === 'string') {
    text = `$ ${event.item.command}${Number.isInteger(event.item.exit_code) ? ` (status ${event.item.exit_code})` : ''}`;
  } else if (event?.type === 'assistant' && Array.isArray(event.message?.content)) {
    text = event.message.content.map(part => part?.text ?? (part?.name ? `Tool: ${part.name}` : '')).filter(Boolean).join(' ');
  } else if (typeof event?.message === 'string') text = event.message;
  else if (typeof event?.type === 'string') text = event.item?.type ? `${event.type}: ${event.item.type}` : event.type;
  const clean = safe(text).trimEnd();
  return clean.length > 1000 ? `${clean.slice(0, 1000)}…` : clean;
}

function logLines(fs, cursor, final) {
  const output = [], show = text => { const message = readable(text); if (message) output.push(`[${safe(cursor.role)}] ${message}`); };
  let fd, bytes = Buffer.alloc(0);
  try {
    fd = fs.openSync(cursor.log, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK);
    const info = fs.fstatSync(fd), identity = `${info.dev}:${info.ino}`;
    if (info.isFile()) {
      if (cursor.identity !== identity || cursor.offset > info.size) Object.assign(cursor, { identity, offset: 0, pending: null, skip: false });
      if (info.size - cursor.offset > LIMIT) {
        cursor.offset = info.size - LIMIT; cursor.pending = null; cursor.skip = true;
        show('(earlier log bytes omitted)');
      }
      const buffer = Buffer.alloc(Math.max(0, info.size - cursor.offset));
      const length = buffer.length ? fs.readSync(fd, buffer, 0, buffer.length, cursor.offset) : 0;
      cursor.offset += length;
      bytes = buffer.subarray(0, length);
    }
  } catch {}
  finally { if (fd !== undefined) fs.closeSync(fd); }
  if (cursor.pending) bytes = Buffer.concat([cursor.pending, bytes]);
  let from = 0, newline;
  while ((newline = bytes.indexOf(10, from)) !== -1) {
    if (!cursor.skip) show(bytes.subarray(from, newline).toString('utf8'));
    cursor.skip = false;
    from = newline + 1;
  }
  cursor.pending = null;
  if (final) {
    if (!cursor.skip && from < bytes.length) show(bytes.subarray(from).toString('utf8'));
  } else if (!cursor.skip && bytes.length - from > LIMIT) {
    cursor.skip = true;
    show('(oversized log line omitted)');
  } else if (!cursor.skip && from < bytes.length) cursor.pending = bytes.subarray(from);
  return output;
}

export async function runAutopilotLogs({ root, issue, follow = false, env }, overrides = {}) {
  const ports = { fs: files, jobs: { inspect: inspectAgentJob }, queue: { read: readSuiteProgress },
    process: { groupAlive }, clock: { now: Date.now, sleep }, ...overrides };
  const fs = ports.fs, core = resolve(root), read = () => readWorkers(fs, core);
  const workers = read(), view = worker => workerView(worker, core, env, ports);
  if (issue === undefined) return { exitCode: 0, message: workers.length
    ? workers.map(worker => view(worker).display).join('\n\n') + '\n\nFollow a worker with pdd autopilot logs --issue N --follow.'
    : 'No current Autopilot workers in this repository.' };
  const selected = choose(workers, issue);
  if (!selected) return { exitCode: 1, message: `No current Autopilot worker for #${issue}. Run pdd autopilot logs to list current workers.` };
  const issueNumber = selected.job.issue;
  let current = selected, cursors = new Map(), lastSignature;
  for (;;) {
    const observed = current ? view(current) : null;
    const next = new Map(), text = [];
    for (const part of observed?.parts ?? []) {
      if (part.log) next.set(part.log, cursors.get(part.log) ?? { role: part.role, log: part.log, offset: 0 });
    }
    for (const [path, cursor] of cursors) if (!next.has(path)) text.push(...logLines(fs, cursor, true));
    if (observed && lastSignature !== observed.signature) text.push(observed.display);
    for (const cursor of next.values()) text.push(...logLines(fs, cursor, !follow));
    if (!follow) return { exitCode: 0, message: text.join('\n') };
    if (text.length) await ports.emit(text.join('\n'));
    if (!observed) return { exitCode: 0, message: `Autopilot worker #${issueNumber} is no longer current.` };
    lastSignature = observed.signature;
    cursors = next;
    await ports.clock.sleep(1000);
    current = read().find(({ job }) => job.issue === issueNumber && job.started === selected.job.started && job.branch === selected.job.branch);
  }
}
