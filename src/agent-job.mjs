// Generated from prompts/cli/agent-job.prompt.md (sha256: 2ddeed3e9d83d1bc3b21d89376364ae517f24cd62930b9a15f682c72deefd5dc).
import { execFile, spawn, spawnSync } from 'node:child_process';
import { accessSync, closeSync, constants, fstatSync, openSync, readFileSync, readlinkSync, readSync, realpathSync, renameSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { setPriority } from 'node:os';
import { basename, dirname, join, resolve, sep } from 'node:path';
import { fileURLToPath } from 'node:url';
import { descendants, parseProcessTable, sameProcess, terminateCaptured } from './process-lifecycle.mjs';

const self = fileURLToPath(import.meta.url), GRACE_MS = 2000;
const SESSION_KEYS = /^(?:ANTIGRAVITY_(?!APP_DATA_DIR$)|CLAUDECODE$|CLAUDE_CODE_|CLAUDE_PID$|CODEX_THREAD_ID$|CODEX_SANDBOX|HERDR_|PDD_AGENT_SESSION$|PDD_AUTOPILOT_CONTEXT$)/;
const readJson = file => { try { return JSON.parse(readFileSync(file, 'utf8')); } catch (error) { if (error.code === 'ENOENT') return undefined; return 'invalid'; } };
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const startIdentity = value => typeof value === 'string' && /^(?:(?:Mon|Tue|Wed|Thu|Fri|Sat|Sun) [A-Z][a-z]{2} (?: [1-9]|[12]\d|3[01]) \d{2}:\d{2}:\d{2} \d{4}|@\S+)$/.test(value);
const processIdentity = row => Number.isSafeInteger(row?.pid) && row.pid > 0 && startIdentity(row.start) && typeof row.args === 'string' && row.args.trim().length > 0;
const sameIdentity = (saved, current) => saved?.pid === current?.pid && saved?.start === current?.start;
const processManifest = rows => Array.isArray(rows) && rows.length > 0 && rows.every(processIdentity);
function writeAtomic(file, text) {
  const temp = `${file}.${process.pid}.tmp`;
  writeFileSync(temp, text, { mode: 0o600 }); renameSync(temp, file);
}

export function agentCommand(agent, { model } = {}) {
  const extra = model ? ['--model', model] : [];
  if (agent?.kind === 'codex') return { command: agent.command ?? 'codex', args: ['exec', '--json', '--dangerously-bypass-approvals-and-sandbox', '-c', 'features.multi_agent=false', ...extra, '-'] };
  // Claude streams its events (stream-json) so that its log grows while it works; the core reads the result file.
  if (agent?.kind === 'claude') return { command: agent.command ?? 'claude', args: ['-p', '--output-format', 'stream-json', '--verbose', '--permission-mode', 'bypassPermissions', ...extra] };
  if (agent?.kind === 'agy') return { command: agent.command ?? 'agy', args: ['--input-format', 'text', '--output-format', 'stream-json', '--dangerously-skip-permissions', ...extra] };
  throw Error('Autopilot core jobs need codex, claude or agy');
}

export function jobEnvironment(env = {}) {
  return Object.fromEntries(Object.entries(env).filter(([key, value]) => typeof value === 'string' && !SESSION_KEYS.test(key)));
}

// The hung-command watch settings: after (ms of log silence), every (ms between rounds), cpu (seconds of growth).
const hungSettings = value => object(value) && [value.after, value.every].every(n => Number.isFinite(n) && n > 0) && Number.isFinite(value.cpu) && value.cpu >= 0
  ? { after: value.after, every: value.every, cpu: value.cpu } : null;
export function startAgentJob({ id, dir, cwd, command, args = [], input = '', env = {}, priority = null, pddCheck = null, hung = null, custodyRoot = null }, ports = {}) {
  if (!/^[A-Za-z0-9._-]+$/.test(String(id))) throw Error('Invalid job id');
  const base = join(resolve(dir), id), now = ports.now ?? Date.now, watch = hungSettings(hung), custody = typeof custodyRoot === 'string' && custodyRoot ? resolve(custodyRoot) : null;
  const job = { id, token: `${base}.spec.json`, log: `${base}.log`, exit: `${base}.exit.json`, result: `${base}.result.json`, input: `${base}.input`, hangs: `${base}.hangs.json` };
  writeFileSync(job.input, input, { mode: 0o600 });
  // This boundary precedes the spec and wrapper spawn. `started`, sampled after
  // spawn, would not safely exclude an already-running descendant.
  const custodyBoundary = custody ? now() : null;
  writeAtomic(job.token, JSON.stringify({ command, args, cwd, input: job.input, log: job.log, exit: job.exit, hangs: job.hangs, ...(priority ? { priority } : {}), ...(pddCheck ? { pddCheck } : {}), ...(watch ? { hung: watch } : {}), ...(custody ? { custodyRoot: custody, custodyBoundary } : {}) }));
  const child = (ports.spawn ?? spawn)(process.execPath, [self, '--wrapper', job.token], { cwd, env, detached: true, stdio: 'ignore' });
  // A spawn that fails later (a cwd that is gone, EAGAIN, ENOMEM) is an exit with code 127, never an uncaught error.
  child.on?.('error', error => { try { writeAtomic(job.exit, JSON.stringify({ code: 127, signal: null, at: now(), error: String(error.code ?? error.message) })); } catch { /* The job reads as dead. */ } });
  child.unref?.();
  return { ...job, pid: child.pid, started: now(), ...(custodyBoundary !== null ? { custodyBoundary } : {}) };
}

function nativeAlive(pid, token) {
  try { process.kill(pid, 0); } catch (error) { if (error.code !== 'EPERM') return false; }
  const row = spawnSync('ps', ['-ww', '-o', 'command=', '-p', String(pid)], { encoding: 'utf8', timeout: 5000, env: { ...process.env, LC_ALL: 'C', LANG: 'C' } });
  return row.status === 0 && String(row.stdout).includes(token);
}

export function readAgentJob(job, ports = {}) {
  if (!object(job)) return { state: 'dead', exit: null, result: null, log: null };
  const alive = Number.isSafeInteger(job?.pid) && job.pid > 0 && (ports.alive ?? nativeAlive)(job.pid, job.token);
  if (alive) snapshotAgentJob(job, ports);
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

// The commands that the wrapper's hung-command watch stopped, oldest first.
export function agentJobHangs(job) {
  const value = typeof job?.hangs === 'string' ? readJson(job.hangs) : undefined;
  return Array.isArray(value) ? value.filter(object) : [];
}

export function stopAgentJob(job, ports = {}) {
  if (!(Number.isSafeInteger(job?.pid) && job.pid > 0 && (ports.alive ?? nativeAlive)(job.pid, job.token))) return false;
  try { (ports.kill ?? process.kill)(-job.pid, 'SIGTERM'); } catch { try { (ports.kill ?? process.kill)(job.pid, 'SIGTERM'); } catch { return false; } }
  return true;
}

function lifecycleRows(ports = {}, withUid = false) {
  if (withUid && ports.list) {
    let rows; try { rows = ports.list(ports); } catch { return null; }
    return Array.isArray(rows) && rows.some(row => row.pid === process.pid)
      && rows.every(row => processIdentity(row) && Number.isSafeInteger(row.uid)) ? rows : null;
  }
  if (withUid) {
    const owned = (ports.spawnSync ?? spawnSync)('ps', ['-A', '-ww', '-o', 'pid=', '-o', 'ppid=', '-o', 'pgid=', '-o', 'rss=', '-o', 'uid=', '-o', 'state=', '-o', 'lstart=', '-o', 'command='],
      { encoding: 'utf8', timeout: 5000, maxBuffer: 64 * 1024 * 1024, env: { ...process.env, LC_ALL: 'C' } });
    if (owned?.status !== 0) return null;
    const matches = String(owned.stdout).split('\n').filter(line => line.trim()).map(line => /^\s*(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(-?\d+)\s+(\S+)\s+((?:(?:Mon|Tue|Wed|Thu|Fri|Sat|Sun) .{20})|@\S+)\s+(.*)$/.exec(line));
    if (matches.some(match => !match)) return null;
    const rows = matches.map(match => ({ pid: Number(match[1]), ppid: Number(match[2]), pgid: Number(match[3]), rss: Number(match[4]), uid: Number(match[5]), state: match[6], start: match[7].trim(), args: match[8] }));
    return rows.some(row => row.pid === process.pid) && rows.every(row => processIdentity(row) && Number.isSafeInteger(row.uid)) ? rows : null;
  }
  const table = (ports.spawnSync ?? spawnSync)('ps', ['-A', '-ww', '-o', 'pid=', '-o', 'ppid=', '-o', 'pgid=', '-o', 'rss=', '-o', 'lstart=', '-o', 'command='],
    { encoding: 'utf8', timeout: 5000, env: { ...process.env, LC_ALL: 'C' } });
  return table?.status === 0 ? parseProcessTable(table.stdout) : null;
}

function markProcessUncertain(job, reason) {
  job.processesUncertain = true;
  try { writeFileSync(`${job.token}.processes.error`, `${reason}\n`, { mode: 0o600 }); } catch {}
  return null;
}

const cleanupSnapshotFile = token => `${token}.processes.cleanup-snapshot.json`;
const validCleanupSnapshotRecord = value => object(value) && value.schema === 1 && Number.isSafeInteger(value.pid) && value.pid > 0
  && typeof value.token === 'string' && Array.isArray(value.attempts) && value.attempts.length > 0
  && value.attempts.every(row => object(row) && Number.isFinite(row.at) && typeof row.reason === 'string'
    && (row.wrapper === null || processIdentity(row.wrapper) && row.wrapper.pid === value.pid))
  && Array.isArray(value.resolutions) && value.resolutions.every(row => object(row) && Number.isFinite(row.at)
    && Number.isSafeInteger(row.attempt) && row.attempt > 0 && row.attempt <= value.attempts.length
    && (row.wrapper === null || processIdentity(row.wrapper) && row.wrapper.pid === value.pid));
const resolvedCleanupAttempts = record => Math.max(0, ...record.resolutions.map(row => row.attempt));
const cleanupSnapshotPending = record => record.attempts.length > resolvedCleanupAttempts(record);

function cleanupSnapshotRecord(job) {
  const value = readJson(cleanupSnapshotFile(job.token));
  if (value === undefined) return { record: null, valid: true };
  return validCleanupSnapshotRecord(value) && value.pid === job.pid && value.token === job.token
    ? { record: value, valid: true } : { record: null, valid: false };
}

function recordCleanupSnapshotFailure(job, reason, wrapper = null) {
  const file = cleanupSnapshotFile(job.token), previous = readJson(file);
  if (previous !== undefined && (!validCleanupSnapshotRecord(previous) || previous.pid !== job.pid || previous.token !== job.token))
    return markProcessUncertain(job, 'cleanup snapshot history invalid');
  const record = previous ?? { schema: 1, pid: job.pid, token: job.token, attempts: [], resolutions: [] };
  const known = wrapper && processIdentity(wrapper) && wrapper.pid === job.pid ? { pid: wrapper.pid, start: wrapper.start, args: wrapper.args } : null;
  record.attempts.push({ at: Date.now(), reason, wrapper: known });
  try { writeAtomic(file, JSON.stringify(record)); }
  catch { return markProcessUncertain(job, 'cleanup snapshot history write failed'); }
  return null;
}

function cleanupSnapshotMatches(record, wrapper) {
  return record.attempts.slice(resolvedCleanupAttempts(record)).every(attempt => !attempt.wrapper || sameIdentity(attempt.wrapper, wrapper));
}

function resolveCleanupSnapshot(job, record, wrapper) {
  const resolved = { ...record, resolutions: [...record.resolutions,
    { at: Date.now(), attempt: record.attempts.length, wrapper: { pid: wrapper.pid, start: wrapper.start, args: wrapper.args } }] };
  try { writeAtomic(cleanupSnapshotFile(job.token), JSON.stringify(resolved)); } catch { return null; }
  return resolved;
}

const custodyFile = token => `${token}.processes.custody.json`;
const validCustodyRecord = value => object(value) && value.schema === 1 && typeof value.root === 'string'
  && Array.isArray(value.observations) && value.observations.length > 0
  && value.observations.every(row => object(row) && typeof row.reason === 'string' && processManifest(row.identities))
  && (value.resolution === null || object(value.resolution)) && (value.legacy === undefined || value.legacy === true);
function markCustodyUncertain(job, finding, legacy = false) {
  if (!finding || !Array.isArray(finding.identities) || !processManifest(finding.identities)) return markProcessUncertain(job, finding?.reason ?? 'custody identity unavailable');
  const file = custodyFile(job.token), previous = readJson(file);
  if (previous !== undefined && !validCustodyRecord(previous)) return markProcessUncertain(job, 'custody record invalid');
  const record = previous ?? { schema: 1, root: finding.root, observations: [], resolution: null, ...(legacy ? { legacy: true } : {}) };
  if (record.root !== finding.root) return markProcessUncertain(job, 'custody root changed');
  if (legacy && record.legacy !== true) return markProcessUncertain(job, 'custody record mode changed');
  const byIdentity = new Map();
  for (const row of finding.identities) byIdentity.set(`${row.pid}:${row.start}`, byIdentity.get(`${row.pid}:${row.start}`) ?? row);
  record.observations.push({ at: Date.now(), reason: finding.reason, identities: [...byIdentity.values()] });
  record.resolution = null;
  try { writeAtomic(file, JSON.stringify(record)); } catch { return markProcessUncertain(job, 'custody record write failed'); }
  return record;
}

function worktreeCwds(rows, uid, ports = {}) {
  const platform = ports.platform ?? process.platform;
  if (typeof ports.cwd === 'function') {
    const found = new Map();
    for (const row of rows) try {
      const path = ports.cwd(row.pid, uid, row);
      if (typeof path === 'string') found.set(row.pid, path);
    } catch { /* Re-read this identity below. */ }
    return found;
  }
  if (platform === 'linux') {
    const found = new Map();
    for (const row of rows) try { found.set(row.pid, readlinkSync(`/proc/${row.pid}/cwd`)); } catch { /* Re-read this identity below. */ }
    return found;
  }
  if (platform !== 'darwin') return null;
  const listed = (ports.spawnSync ?? spawnSync)('lsof', ['-n', '-a', '-u', String(uid), '-d', 'cwd', '-Fpn'], { encoding: 'utf8', timeout: 5000, maxBuffer: 64 * 1024 * 1024 });
  if (listed.status !== 0) return null;
  const found = new Map(); let pid = null;
  for (const line of String(listed.stdout).split('\n')) {
    const process = /^p(\d+)$/.exec(line);
    if (process) { pid = Number(process[1]); continue; }
    if (pid && line.startsWith('n')) found.set(pid, line.slice(1));
  }
  return found;
}

// A process can retain a deleted directory as cwd. Resolve the nearest existing
// parent too, so a macOS /tmp alias still compares with its physical path.
function canonicalCwd(path) {
  const suffix = [];
  for (let current = path, depth = 0; depth < 100; depth++) {
    try { return join(realpathSync(current), ...suffix); } catch { /* Try its parent. */ }
    const parent = dirname(current);
    if (parent === current) return null;
    suffix.unshift(basename(current)); current = parent;
  }
  return null;
}

// `ps lstart` has whole-second precision. A candidate is definitely older only
// when its start second is before the boundary's second; equal seconds stay
// conservative. Unknown or synthetic starts never prove this relationship.
function startsBeforeBoundary(row, boundary) {
  if (!Number.isFinite(boundary) || !/^\w{3} \w{3} (?: [1-9]|[12]\d|3[01]) \d{2}:\d{2}:\d{2} \d{4}$/.test(String(row?.start))) return false;
  const start = Date.parse(row.start);
  return Number.isFinite(start) && Math.floor(start / 1000) < Math.floor(boundary / 1000);
}

function ancestorPids(rows, seeds) {
  const byPid = new Map(rows.map(row => [row.pid, row])), seen = new Set();
  for (let pid of seeds) {
    for (let depth = 0; Number.isSafeInteger(pid) && pid > 0 && !seen.has(pid) && depth < 64; depth++) {
      seen.add(pid);
      pid = byPid.get(pid)?.ppid;
    }
  }
  return seen;
}

// The wrapper is detached into a new non-root POSIX session. A candidate outside
// the wrapper's group and session whose session leader predates the boundary, or
// is privilege-separated under root (such as Linux sshd), or is systemd's (sd-pam)
// inside systemd --user's own session, cannot descend from the wrapper.
function inOutsideLinuxSession(row, job, boundary, latest, ports = {}) {
  const platform = ports.platform ?? process.platform;
  if (platform !== 'linux' || row.pgid === job.pid) return false;
  const read = pid => {
    const result = (ports.spawnSync ?? spawnSync)('ps', ['-ww', '-p', String(pid), '-o', 'pid=,sid=,uid=,state=,lstart='],
      { encoding: 'utf8', timeout: 2000, env: { ...process.env, LC_ALL: 'C' } });
    if (result?.status !== 0) return null;
    const match = /^\s*(\d+)\s+(\d+)\s+(-?\d+)\s+(\S+)\s+((?:Mon|Tue|Wed|Thu|Fri|Sat|Sun) .{20})\s*$/.exec(String(result.stdout));
    return match ? { pid: Number(match[1]), sid: Number(match[2]), uid: Number(match[3]), state: match[4], start: match[5].trim() } : null;
  };
  const current = read(row.pid);
  if (!current || current.pid !== row.pid || current.uid !== row.uid || current.start !== row.start
      || String(current.state).startsWith('Z') || !Number.isSafeInteger(current.sid) || current.sid <= 0 || current.sid === job.pid) return false;
  const leader = read(current.sid);
  if (!leader || leader.pid !== current.sid || leader.sid !== current.sid) return false;
  if (Number.isFinite(boundary) && startsBeforeBoundary(leader, boundary)) return true;
  if (row.uid > 0 && leader.uid === 0) return true;
  if (current.pid !== current.sid && row.args === '(sd-pam)' && leader.uid === row.uid) return true;
  if (row.uid > 0 && Number.isSafeInteger(row.ppid) && row.ppid > 1 && Array.isArray(latest)) {
    const ancestors = ancestorPids(latest, [process.pid, job.pid]);
    if (!ancestors.has(row.ppid)) {
      const parent = read(row.ppid);
      if (parent && parent.pid === row.ppid && parent.uid === 0 && !String(parent.state).startsWith('Z')) return true;
    }
  }
  return false;
}

// An explicit custody-root match can only retain the disposable worktree. It never
// proves ownership and is never used to send a signal. The direct child has exited,
// so an unsaved matching process is the late detached-helper case that the periodic
// descendant snapshots can miss.
function worktreeCustody(job, custodyRoot, ports = {}, retained = [], legacy = false, boundary = null) {
  const platform = ports.platform ?? process.platform;
  if (!['darwin', 'linux'].includes(platform)) return { reason: 'cwd custody is unsupported', root: null, identities: null };
  const manifest = readJson(`${job.token}.processes.json`);
  if (legacy ? manifest !== undefined : !processManifest(manifest)) return { reason: 'manifest invalid', root: null, identities: null };
  const saved = legacy ? [] : manifest;
  const requested = resolve(custodyRoot);
  let root; try { root = realpathSync(requested); } catch { return { reason: 'worktree unavailable', root: null, identities: null }; }
  const uid = typeof process.getuid === 'function' ? process.getuid() : null;
  if (!Number.isSafeInteger(uid) || uid < 0) return { reason: 'current-user identity unavailable', root, identities: null };
  const rows = lifecycleRows(ports, true);
  if (!Array.isArray(rows)) return { reason: 'worktree inventory unavailable', root, identities: null };
  if (legacy) {
    const wrapper = rows.find(row => row.pid === job.pid && !String(row.state ?? '').startsWith('Z') && String(row.args).includes(job.token));
    if (wrapper) return { reason: 'legacy wrapper still runs this spec', root, identities: [wrapper] };
  }
  const observed = [...saved, ...retained];
  const stillKnown = observed.filter(known => rows.some(row => sameIdentity(known, row) && !String(row.state ?? '').startsWith('Z')));
  const group = legacy ? rows.filter(row => row.pgid === job.pid && !String(row.state ?? '').startsWith('Z')) : [];
  // A wrapper PID can be reused. Exclude only a saved PID/start identity; an
  // observed identity remains held below even when its command text changed.
  const candidates = rows.filter(row => row.uid === uid && !String(row.state ?? '').startsWith('Z') && !observed.some(known => sameIdentity(known, row)));
  const cwds = worktreeCwds(candidates, uid, ports);
  if (!(cwds instanceof Map)) return { reason: 'worktree cwd evidence unavailable', root, identities: null };
  let latest = null, reason = null; const identities = [];
  for (const row of candidates) {
    const current = cwds.get(row.pid);
    if (current === undefined) {
      latest ??= lifecycleRows(ports, true);
      if (!Array.isArray(latest)) return { reason: 'worktree inventory unavailable', root, identities: null };
      const current = latest.find(now => sameIdentity(row, now));
      if (current && !String(current.state ?? '').startsWith('Z') && !startsBeforeBoundary(row, boundary)
          && !inOutsideLinuxSession(row, job, boundary, latest, ports)) {
        identities.push(row); reason ??= 'cwd evidence unavailable for a live process';
      }
      continue;
    }
    const deleted = / \(deleted\)$/.test(String(current)), path = String(current).replace(/ \(deleted\)$/, ''), actual = canonicalCwd(path);
    if (actual && (actual === root || actual.startsWith(root + sep))) { identities.push(row); reason ??= 'unsaved process uses worktree'; }
    else if (!actual && deleted && (path === requested || path.startsWith(requested + sep))) { identities.push(row); reason ??= 'deleted process cwd uses worktree'; }
    else if (!actual && deleted) return { reason: 'worktree cwd could not be canonicalized', root, identities: null };
  }
  for (const row of group) if (!identities.some(known => sameIdentity(known, row))) { identities.push(row); reason ??= 'legacy wrapper process group remains'; }
  for (const row of stillKnown) if (!identities.some(known => sameIdentity(known, row))) { identities.push(row); reason ??= 'a recorded custody process remains'; }
  return identities.length ? { reason, root, identities } : null;
}

const validExitRecord = value => object(value) && (Number.isSafeInteger(value.code) || value.code === null)
  && (value.signal === null || typeof value.signal === 'string') && Number.isFinite(value.at);
function legacyCleanupResult() {
  return { confirmed: true, stopped: 0, killed: 0, remaining: 0,
    legacy: 'No 0.1.28 descendant manifest was available; a complete checkout and old-group scan found no live process.' };
}
function cleanupLegacyAgentJob(job, ports, manifest, errorFile, custodyPath) {
  const rootPath = ports.legacyCustodyRoot;
  if (!(Number.isSafeInteger(job?.pid) && job.pid > 0) || typeof rootPath !== 'string' || !rootPath
      || manifest !== undefined || job.processes !== undefined && job.processes !== null) return null;
  const spec = readJson(job.token);
  if (!object(spec) || Object.hasOwn(spec, 'custodyRoot') || typeof spec.cwd !== 'string'
      || typeof spec.exit !== 'string' || typeof job.exit !== 'string' || spec.exit !== job.exit
      || !Array.isArray(spec.args) || typeof spec.command !== 'string' || !validExitRecord(readJson(spec.exit))) return null;
  let root;
  try {
    root = realpathSync(rootPath);
    if (realpathSync(spec.cwd) !== root) return null;
  } catch { return null; }
  const custody = readJson(custodyPath);
  if (custody !== undefined && (!validCustodyRecord(custody) || custody.legacy !== true || custody.root !== root)) return null;
  const retained = custody?.observations.flatMap(row => row.identities) ?? [];
  // Core supplies this only when it saved a job-level time before every part
  // spawn. A part's post-spawn `started` time is not a safe boundary.
  const boundary = Number.isFinite(ports.legacyCustodyBoundary) ? ports.legacyCustodyBoundary : null;
  const finding = worktreeCustody(job, root, ports, retained, true, boundary);
  if (!finding) {
    if (custody) {
      const resolved = { ...custody, resolution: { at: Date.now(), completeProcessTable: true, completeCwdInventory: true,
        recordedIdentitiesGone: true, unsavedProcessesInRoot: 0, manifestConfirmed: false, legacyGroupScanned: true } };
      try { writeAtomic(custodyPath, JSON.stringify(resolved)); } catch { return null; }
    }
    // A missing old manifest limits what can be proven. The caller may finish local
    // removal only with this explicit bounded result; it never authorizes a signal.
    return legacyCleanupResult();
  }
  if (Array.isArray(finding.identities) && processManifest(finding.identities)) {
    const record = markCustodyUncertain(job, finding, true);
    if (record && !readJson(errorFile)) return { confirmed: false, stopped: 0, killed: 0, remaining: finding.identities.length };
  }
  return null;
}

// Save the tree while its parent links still exist. A later stop can then find a
// helper that reparented itself after its direct agent exited.
export function snapshotAgentJob(job, ports = {}, { requireWrapper = false, cleanupSnapshot = false } = {}) {
  if (!(Number.isSafeInteger(job?.pid) && job.pid > 0)) return null;
  const manifestFile = `${job.token}.processes.json`;
  const retryable = new Set(['inventory unavailable', 'live wrapper identity unavailable', 'incomplete inventory', 'process identity invalid']);
  const savedManifest = readJson(manifestFile);
  if ((savedManifest !== undefined && !processManifest(savedManifest)) || (Array.isArray(job.processes) && !processManifest(job.processes))) return markProcessUncertain(job, 'manifest invalid');
  const saved = [...(savedManifest ?? []), ...(Array.isArray(job.processes) ? job.processes : [])];
  if (saved.length && !processManifest(saved)) return markProcessUncertain(job, 'manifest invalid');
  const previousRoot = saved.find(row => row.pid === job.pid && String(row.args).includes(job.token)) ?? null;
  const uncertain = (reason, wrapper = previousRoot) => cleanupSnapshot && retryable.has(reason)
    ? recordCleanupSnapshotFailure(job, reason, wrapper) : markProcessUncertain(job, reason);
  let rows; try { rows = (ports.list ?? lifecycleRows)(ports); } catch { return uncertain('inventory unavailable'); }
  if (!Array.isArray(rows)) return uncertain('inventory unavailable');
  const root = rows.find(row => row.pid === job.pid && String(row.args).includes(job.token));
  if (!root) {
    if (requireWrapper) return uncertain('live wrapper identity unavailable');
    if (saved.length) { job.processes = saved; return saved; }
    return uncertain('wrapper identity unavailable');
  }
  const current = descendants(rows, [root]);
  if (current.incomplete) return uncertain('incomplete inventory', root);
  if (!current.every(processIdentity)) return uncertain('process identity invalid', root);
  const byIdentity = new Map();
  for (const row of [...saved, ...current]) if (processIdentity(row)) byIdentity.set(`${row.pid}:${row.start}`, byIdentity.get(`${row.pid}:${row.start}`) ?? row);
  job.processes = [...byIdentity.values()];
  try { writeAtomic(manifestFile, JSON.stringify(job.processes)); }
  catch { uncertain('manifest write failed'); }
  return job.processes;
}

export async function cleanupAgentJob(job, ports = {}) {
  const manifestFile = typeof job?.token === 'string' ? `${job.token}.processes.json` : null;
  const errorFile = typeof job?.token === 'string' ? `${job.token}.processes.error` : null;
  const custodyPath = typeof job?.token === 'string' ? custodyFile(job.token) : null;
  const manifest = manifestFile ? readJson(manifestFile) : null;
  if (manifest !== undefined && !processManifest(manifest)) {
    try { writeFileSync(errorFile, 'manifest invalid\n', { mode: 0o600 }); } catch {}
    return { confirmed: false, stopped: 0, killed: 0, remaining: 0 };
  }
  if (job?.processesUncertain || errorFile && (() => { try { readFileSync(errorFile); return true; } catch { return false; } })()) return { confirmed: false, stopped: 0, killed: 0, remaining: 0 };
  const custody = custodyPath ? readJson(custodyPath) : undefined;
  if (custody !== undefined && !validCustodyRecord(custody)) return { confirmed: false, stopped: 0, killed: 0, remaining: 0 };
  const snapshotState = typeof job?.token === 'string' && Number.isSafeInteger(job?.pid)
    ? cleanupSnapshotRecord(job) : { record: null, valid: true };
  if (!snapshotState.valid) {
    markProcessUncertain(job, 'cleanup snapshot history invalid');
    return { confirmed: false, stopped: 0, killed: 0, remaining: 0 };
  }
  const retryRecord = snapshotState.record;
  const retryPending = retryRecord && cleanupSnapshotPending(retryRecord);
  let saved = Array.isArray(job?.processes) ? job.processes : Array.isArray(manifest) ? manifest : null;
  const live = (ports.alive ?? nativeAlive)(job.pid, job.token);
  if (retryPending && !live) return { confirmed: false, stopped: 0, killed: 0, remaining: saved?.length ?? 1 };
  if (live) {
    const fresh = snapshotAgentJob(job, ports, { requireWrapper: true, cleanupSnapshot: true });
    const error = errorFile && (() => { try { readFileSync(errorFile); return true; } catch { return false; } })();
    if (!processManifest(fresh) || job.processesUncertain || error)
      return { confirmed: false, stopped: 0, killed: 0, remaining: saved?.length ?? 1 };
    saved = fresh;
    if (retryPending) {
      const wrapper = fresh.find(row => row.pid === job.pid && String(row.args).includes(job.token));
      if (!wrapper || !cleanupSnapshotMatches(retryRecord, wrapper))
        return { confirmed: false, stopped: 0, killed: 0, remaining: saved.length };
      if (!resolveCleanupSnapshot(job, retryRecord, wrapper)) {
        markProcessUncertain(job, 'cleanup snapshot history resolution failed');
        return { confirmed: false, stopped: 0, killed: 0, remaining: saved.length };
      }
    }
  }
  if (!processManifest(saved)) {
    const legacy = cleanupLegacyAgentJob(job, ports, manifest, errorFile, custodyPath);
    return legacy ?? { confirmed: false, stopped: 0, killed: 0, remaining: 0 };
  }
  stopAgentJob(job, ports);
  const result = await terminateCaptured(saved, { list: async () => (ports.list ?? lifecycleRows)(ports), signal: ports.kill ?? process.kill,
    sleep: ports.sleep, grace: ports.grace ?? GRACE_MS, poll: ports.poll });
  // The wrapper can write custody or an error while its group shuts down. Read
  // again before reporting a clean result so that marker is not missed.
  if (errorFile && (() => { try { readFileSync(errorFile); return true; } catch { return false; } })())
    return { ...result, confirmed: false, remaining: Math.max(result.remaining, 1) };
  const currentCustody = custodyPath ? readJson(custodyPath) : undefined;
  if (currentCustody !== undefined && !validCustodyRecord(currentCustody))
    return { ...result, confirmed: false, remaining: Math.max(result.remaining, 1) };
  if (!result.confirmed) return result;
  const spec = readJson(job.token);
  const hasCustodyRoot = object(spec) && typeof spec.custodyRoot === 'string' && spec.custodyRoot;
  if (!hasCustodyRoot) return currentCustody ? { ...result, confirmed: false, remaining: Math.max(result.remaining, 1) } : result;
  const platform = ports.platform ?? process.platform;
  if (!['darwin', 'linux'].includes(platform) || (ports.alive ?? nativeAlive)(job.pid, job.token))
    return { ...result, confirmed: false, remaining: Math.max(result.remaining, 1) };
  let currentRoot = null;
  try { currentRoot = realpathSync(spec.custodyRoot); } catch {}
  if (!currentRoot || currentCustody && currentRoot !== currentCustody.root)
    return { ...result, confirmed: false, remaining: Math.max(result.remaining, 1) };
  const retained = currentCustody?.observations.flatMap(row => row.identities) ?? [], boundary = Number.isFinite(spec?.custodyBoundary) ? spec.custodyBoundary : null;
  const finding = worktreeCustody(job, currentRoot, ports, retained, false, boundary);
  if (!finding) {
    if (!currentCustody || currentCustody.resolution) return result;
    const resolved = { ...currentCustody, resolution: { at: Date.now(), completeProcessTable: true, completeCwdInventory: true,
      recordedIdentitiesGone: true, unsavedProcessesInRoot: 0, manifestConfirmed: true } };
    try { writeAtomic(custodyPath, JSON.stringify(resolved)); } catch { return { ...result, confirmed: false, remaining: Math.max(result.remaining, 1) }; }
    return result;
  }
  if (Array.isArray(finding.identities) && processManifest(finding.identities)) {
    if (!currentCustody) markCustodyUncertain(job, finding);
    else {
      const updated = { ...currentCustody, observations: [...currentCustody.observations, { at: Date.now(), reason: finding.reason, identities: finding.identities }], resolution: null };
      try { writeAtomic(custodyPath, JSON.stringify(updated)); } catch { /* Keep the previous uncertainty record. */ }
    }
    return { ...result, confirmed: false, remaining: Math.max(result.remaining, finding.identities.length) };
  }
  return { ...result, confirmed: false, remaining: Math.max(result.remaining, 1) };
}

// The hung-command watch (agent jobs only). An agent waits for each command it runs, and its log is silent meanwhile.
// A command that the agent waits on (it started after the log's last change and is no helper of the agent) whose
// process tree makes almost no CPU while the log stays silent for `after` ms is stopped alone; the agent sees it fail.
const etimeSeconds = text => {
  const [days, clock] = String(text).includes('-') ? String(text).split('-') : ['0', String(text)];
  return clock.split(':').reduce((sum, part) => sum * 60 + Number(part), 0) + Number(days) * 86400;
};
function processTable() {
  const table = spawnSync('ps', ['-A', '-ww', '-o', 'pid=,ppid=,pgid=,time=,etime=,command='], { encoding: 'utf8', timeout: 5000, maxBuffer: 64 * 1024 * 1024, env: { ...process.env, LC_ALL: 'C', LANG: 'C' } });
  if (table.status !== 0) return null;
  const now = Date.now();
  return String(table.stdout).split('\n').map(line => /^\s*(\d+)\s+(\d+)\s+(\d+)\s+(\S+)\s+(\S+)\s?(.*)$/.exec(line)).filter(Boolean)
    .map(([, pid, ppid, pgid, time, etime, command]) => ({ pid: Number(pid), ppid: Number(ppid), pgid: Number(pgid), cpu: cpuSeconds(time), start: now - etimeSeconds(etime) * 1000, command: command.trim() }))
    .filter(row => Number.isFinite(row.cpu) && Number.isFinite(row.start));
}
function lastLogLine(file) {
  let fd;
  try {
    fd = openSync(file, 'r');
    const size = fstatSync(fd).size, length = Math.min(64 * 1024, size), buffer = Buffer.alloc(length);
    readSync(fd, buffer, 0, length, size - length);
    return buffer.toString('utf8').split(/\r?\n/).map(line => line.trim()).filter(Boolean).at(-1)?.slice(0, 300) ?? '';
  } catch { return ''; } finally { if (fd !== undefined) try { closeSync(fd); } catch { /* Closed. */ } }
}
const PDD_WAIT = /(?:^|[\s/'"])pdd(?:\.mjs)?['"]?\s+(?:test|lint)(?=\s|$)|PDD_CLI['"}]*\s+(?:test|lint)(?=\s|$)/;
// One round of the hung-command watch as a pure function (the test feeds it process tables and times, so it checks the
// decisions and not wall time). memo keeps the helpers, the reference CPU of each command and the stopped commands
// between rounds. It returns the commands to stop: [{row, sub, minutes}].
export function hungRound(memo, { rows, log, now, agentPid, settings }) {
  const { after, cpu: cpuLimit } = settings, SAME = 3000, FRESH = 10_000, stops = [];
  if (!Number.isSafeInteger(agentPid) || !log?.size || !Array.isArray(rows)) return stops;
  memo.refs ??= new Map(); memo.stopped ??= new Set();
  const children = new Map(), byPid = new Map(rows.map(row => [row.pid, row]));
  for (const row of rows) children.set(row.ppid, [...(children.get(row.ppid) ?? []), row]);
  const below = pid => { const found = [], queue = [...(children.get(pid) ?? [])]; for (let i = 0; i < queue.length && i < 2000; i++) { found.push(queue[i]); queue.push(...(children.get(queue[i].pid) ?? [])); } return found; };
  const tree = below(agentPid), inTree = new Set(tree.map(row => row.pid));
  for (const pid of memo.refs.keys()) if (!inTree.has(pid)) memo.refs.delete(pid);
  // The helpers: every process under the agent at the first round with log content (its MCP servers and helpers).
  if (!memo.helpers) { memo.helpers = new Map(tree.map(row => [row.pid, row.start])); return stops; }
  const helper = row => memo.helpers.has(row.pid) && Math.abs(memo.helpers.get(row.pid) - row.start) < SAME;
  const fresh = row => Boolean(row) && row.pid !== agentPid && !helper(row) && row.start >= log.mtimeMs - FRESH && inTree.has(row.pid);
  for (const row of tree) {
    if (!fresh(row) || fresh(byPid.get(row.ppid))) continue;
    const key = `${row.pid}:${Math.round(row.start / SAME)}`;
    if (memo.stopped.has(key)) continue;
    const sub = [row, ...below(row.pid)], used = sub.reduce((sum, r) => sum + r.cpu, 0);
    // A pdd test or lint that waits for Runtime capacity or a maintenance window has no output in this log and almost
    // no CPU, like a hang: it is never stopped here (lead, Nov 11). Its own time limits end it, and the engine's quiet
    // rule still sees a job that stays silent.
    if (sub.some(r => PDD_WAIT.test(r.command))) continue;
    let ref = memo.refs.get(row.pid);
    if (!ref || Math.abs(ref.start - row.start) >= SAME) ref = { start: row.start, since: Math.max(log.mtimeMs, row.start), cpu: used };
    if (used - ref.cpu >= cpuLimit) Object.assign(ref, { since: now, cpu: used });
    ref.since = Math.max(ref.since, log.mtimeMs);
    memo.refs.set(row.pid, ref);
    if (now - ref.since < after) continue;
    memo.stopped.add(key); memo.refs.delete(row.pid);
    stops.push({ row, sub, minutes: Math.round((now - ref.since) / 6000) / 10 });
  }
  return stops;
}
function watchHung(spec, agentPid, out) {
  const memo = {};
  const round = () => {
    const log = statSync(spec.log), now = Date.now();
    if (!log.size) return;
    for (const { row, sub, minutes } of hungRound(memo, { rows: processTable(), log, now, agentPid, settings: spec.hung })) {
      const last = lastLogLine(spec.log), command = row.command.slice(0, 500);
      const signalSub = signal => {
        for (const r of sub) {
          if (Number.isSafeInteger(r.pgid) && r.pgid > 1 && r.pid === r.pgid && r.pgid !== process.pid && r.pgid !== agentPid) {
            try { process.kill(-r.pgid, signal); } catch { /* Gone. */ }
          }
          try { process.kill(r.pid, signal); } catch { /* Gone. */ }
        }
      };
      signalSub('SIGTERM');
      setTimeout(() => signalSub('SIGKILL'), GRACE_MS).unref();
      const head = spawnSync('git', ['rev-parse', 'HEAD'], { cwd: spec.cwd, encoding: 'utf8', timeout: 5000 });
      const record = { at: now, pid: row.pid, command, minutes, last, head: head.status === 0 && /^[0-9a-f]{40}$/.test(head.stdout.trim()) ? head.stdout.trim() : null };
      try { writeFileSync(out, `agent-job: stopped a hung command after ${minutes} min with no output and almost no CPU: ${command} (last output: ${last})\n`); } catch { /* The record below still counts. */ }
      try { const old = readJson(spec.hangs); writeAtomic(spec.hangs, JSON.stringify([...(Array.isArray(old) ? old : []), record].slice(-50))); } catch { /* The log line stays. */ }
    }
  };
  // A failed round (a process table that cannot be read, a log that is gone) never stops the job.
  setInterval(() => { try { round(); } catch { /* The next round tries again. */ } }, spec.hung.every).unref();
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
  return `pdd path check: the agent shell finds ${found ? `pdd ${version ?? '(unknown version)'} at ${path}` : 'no pdd on PATH'}; the engine is ${engine}; using PDD_CLI (${cli})`;
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
    line: other.length ? `pdd skills check: installed skills are ${other.map(row => `${row.version} at ${row.folder}`).join(' and ')}, the engine is ${skills.version}; jobs use PDD_SKILLS (${skills.dir})` : null };
  try { writeAtomic(skillsCheckFile(spec.log), JSON.stringify(record)); if (record.line) writeSync(out, `${record.line}\n`); } catch { /* The check is a note only. */ }
  return record;
}
// With no nice program, the wrapper lowers its own nice value instead (every child inherits it).
function lowerPriority(spec) {
  if (executable(NICE)) return;
  try { setPriority(0, niceOf(spec)); } catch { /* A lower priority is best effort. */ }
}
// The stop of a whole job, in order, with ports (the test checks the order and not wall time): a stop signal sends
// SIGTERM to the group (this wrapper leads it) and keeps one timer; after the grace time the wrapper writes the exit
// record (best effort; the child's code and signal when it exited, else the stop signal) and then sends SIGKILL to the
// whole group, itself last. A failed write never skips the SIGKILL. A second stop changes nothing. A child that ends by
// a stop signal before the wrapper's own handler runs is that stop (guard, Nov 11).
const STOP_SIGNALS = ['SIGTERM', 'SIGINT', 'SIGHUP'];
export function jobStopper({ killGroup, setTimer, writeExit, exit, now = Date.now, grace = GRACE_MS }) {
  let finished = false, stopping = null, ended = null;
  const finish = (code, signal, group = false) => {
    if (finished) return; finished = true;
    try { writeExit({ code, signal: signal ?? null, at: now() }); }
    catch { /* The exit record is best effort; the job then reads as dead. */ }
    finally {
      if (group) try { killGroup('SIGKILL'); } catch { /* Only this wrapper is left. */ }
      exit();
    }
  };
  const stop = signal => {
    if (stopping) return; stopping = signal;
    killGroup('SIGTERM');
    // A kept timer: the wrapper waits the grace time also when its direct child exits at once (sh does).
    setTimer(() => finish(ended?.code ?? null, ended?.signal ?? signal, true), grace);
  };
  const exited = (code, signal) => { if (stopping) ended = { code, signal }; else if (STOP_SIGNALS.includes(signal)) { ended = { code, signal }; stop(signal); } else finish(code, signal); };
  return { finish, stop, exited };
}
// The detached wrapper: it owns the agent process and records how it ended.
function wrap(specFile) {
  const spec = JSON.parse(readFileSync(specFile, 'utf8'));
  const job = { pid: process.pid, token: specFile };
  const snapshot = () => snapshotAgentJob(job);
  snapshot();
  const earlySnapshot = setTimeout(snapshot, 25); earlySnapshot.unref();
  setInterval(snapshot, 250).unref();
  lowerPriority(spec);
  const stdin = openSync(spec.input, 'r'), out = openSync(spec.log, 'a', 0o600);
  let child;
  const signalChildGroups = signal => {
    if (signal === 'SIGTERM') snapshot();
    const saved = Array.isArray(job.processes) ? job.processes : [];
    const nowRows = signal === 'SIGKILL' ? lifecycleRows() : null;
    if (signal === 'SIGKILL' && !Array.isArray(nowRows)) return;
    const byPid = nowRows ? new Map(nowRows.map(row => [row.pid, row])) : null;
    const groups = new Set();
    for (const row of saved) {
      if (!Number.isSafeInteger(row?.pgid) || row.pgid <= 1 || row.pgid === process.pid || row.pid !== row.pgid) continue;
      if (byPid) {
        const current = byPid.get(row.pid);
        if (current && !sameProcess(row, current)) continue;
      }
      groups.add(row.pgid);
    }
    for (const pgid of groups) try { process.kill(-pgid, signal); } catch { /* Already gone. */ }
  };
  const { finish, stop, exited } = jobStopper({
    killGroup: signal => {
      signalChildGroups(signal);
      try { process.kill(-process.pid, signal); } catch { if (signal === 'SIGTERM') try { child?.kill('SIGTERM'); } catch { /* The child may already be gone. */ } }
    },
    setTimer: (fn, ms) => setTimeout(fn, ms),
    writeExit: record => { try { writeAtomic(spec.exit, JSON.stringify(record)); } finally { for (const fd of [stdin, out]) try { closeSync(fd); } catch { /* Already closed. */ } } },
    exit: () => process.exit(0) });
  for (const signal of ['SIGTERM', 'SIGINT', 'SIGHUP']) process.on(signal, () => stop(signal));
  const run = jobCommand(spec);
  try { child = spawn(run.command, run.args, { cwd: spec.cwd, env: process.env, stdio: [stdin, out, out] }); snapshot(); }
  catch (error) { writeFileSync(out, `agent-job: ${error.message}\n`); finish(127, null); return; }
  child.on('error', error => { try { writeFileSync(out, `agent-job: ${error.message}\n`); } catch {} finish(127, null); });
  if (object(spec.hung) && typeof spec.hangs === 'string') watchHung(spec, child.pid, out);
  // A group stop can reach the child before the wrapper's own handler runs: a child killed by a stop signal is that
  // stop, so the whole group still ends after the grace time (no process that ignores SIGTERM is left behind).
  child.on('exit', (code, signal) => {
    // `cwd` is only where this command runs. A caller must explicitly name a
    // disposable root before an unrelated process can retain its cleanup.
    if (['darwin', 'linux'].includes(process.platform) && typeof spec.custodyRoot === 'string' && spec.custodyRoot) {
      const job = { pid: process.pid, token: specFile };
      snapshotAgentJob(job);
      const boundary = Number.isFinite(spec.custodyBoundary) ? spec.custodyBoundary : null;
      const finding = worktreeCustody(job, spec.custodyRoot, {}, [], false, boundary);
      if (finding) markCustodyUncertain(job, finding);
    }
    exited(code, signal);
  });
  if (spec.pddCheck) { checkSkills(spec, out); checkShellPdd(spec, out); }
}

if (process.argv[1] && resolve(process.argv[1]) === self && process.argv[2] === '--wrapper') wrap(process.argv[3]);
