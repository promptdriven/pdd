// Generated from prompts/cli/runtime-client.prompt.md (sha256: 87bbc032cd9b455f004548038ea17613dbc9305cb8f1eb0e463f4d2c18eeea1a).
import { acquireRuntimeSlot, recordRuntimeRequest, releaseRuntimeSlot, listRuntimeJobs } from './runtime-slots.mjs';
import { bindingCoverage } from './runtime-bindings.mjs';
import { loadAgentDefinitions } from './agent-config.mjs';
import { spawn, spawnSync } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import { chmodSync, closeSync, fstatSync, fsyncSync, lstatSync, linkSync, mkdirSync, openSync, readFileSync, readdirSync, realpathSync, renameSync, unlinkSync, writeFileSync, writeSync } from 'node:fs';
import { isDeepStrictEqual } from 'node:util';
import { homedir, hostname } from 'node:os';
import { basename, dirname, join, relative, resolve, sep } from 'node:path';
import { DRAFT_SERVER_TEXT, PreflightError, TEST_SCHEMA, captureSource, checkInput, fillHashes, sharedSourceFiles, whyNoTests, findTests, formatSize, gitFiles, otherFiles,
  preflight, readPrompt, selectTests, sourceFilePort, sha256, STALE_HINT, staleHint } from './runtime-preflight.mjs';
import { catalogRecords, compareCopies } from './contract-refs.mjs';
import { askApproval, lineReader, promptPath } from './prompt-approve.mjs';
import { OPEN_STATES, causeText, cleanText, exitCodeFor, progressTicker, projectAnswer, renderJson, renderText, summaryLine, stepTimeLimit, tryUsage, validLink, coverageText } from './runtime-output.mjs';
import { lintSvgLayouts } from './svg-layout.mjs';
import { compareScreen, formatScreenComparison } from './screen-compare.mjs';

// The one place in pdd that names the PDD runtime address; PDD_RUNTIME_URL overrides it.
export const DEFAULT_RUNTIME_URL = 'https://runtime.promptdriven.ai';
const JOB_STATES = new Set(['queued', 'running', 'passed', 'failed', 'refused', 'unknown']);
const ENDED = new Set(['passed', 'failed', 'refused', 'unknown', 'not_run']);
const UUID = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
const BATCH = /^\d{8}-\d{6}-[a-z0-9]{4}$/;
// pdd's local rules match this engine build (checked Oct 27; spec OPEN 9: warn when the runtime runs another one).
const ENGINE_SHA = 'eae2202a68d00ab762fcbbf1eba0d8607a132a15';
// The same engine: the full sha or a prefix of it with at least 7 hex digits.
const sameEngine = sha => { const value = sha.toLowerCase(); return /^[0-9a-f]{7,40}$/.test(value) && ENGINE_SHA.startsWith(value); };
const POST_MS = 90_000, GET_MS = 30_000, TRY_MS = 300_000, MAX_READS = 8, PROGRESS_MS = 30_000;
// An agent (no terminal) waits at most 90 s, below the 2-minute default limit of Claude Code's shell tool; a person has no limit.
const AGENT_WAIT_MIN = 1.5;
// Under load a POST can time out and its job appear 3 to 4 min later: read a lost answer's ID for 5 min.
const LOST_READ_MS = 300_000;

class Stop extends Error { constructor(exitCode, message) { super(message); this.exitCode = exitCode; } }
function requestedCalls(raw) {
  if (raw === undefined) return null;
  if (!(typeof raw === 'number' || typeof raw === 'string' && /^[1-9][0-9]{0,3}$/.test(raw))
    || !Number.isSafeInteger(Number(raw)) || Number(raw) < 1 || Number(raw) > 1000)
    throw new Stop(2, '--max-calls must be a whole number from 1 to 1000, the interpreter maximum.');
  return Number(raw);
}
const line = (stream, text) => stream.write(`${text}\n`);
const statOrNull = path => { try { return lstatSync(path); } catch { return null; } };
const isObject = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const clock = ms => new Date(ms).toTimeString().slice(0, 8);


// A virtual program named gh must not shadow the real sign-in tool on the printed PATH.
function authExecutable(env, preferred) {
  const candidates = [...(preferred ? [preferred] : []), ...(env.PATH || process.env.PATH || '').split(':').map(folder => join(folder, 'gh'))];
  for (const path of candidates) {
    try {
      const stat = lstatSync(path);
      if (!stat.isFile() && !stat.isSymbolicLink()) continue;
      if (readFileSync(path).subarray(0, 64).toString().includes('PDD Try launcher v1')) continue;
      return realpathSync(path);
    } catch { /* try the next PATH directory */ }
  }
  return null;
}

function withDefaults(ports) {
  const env = ports.env ?? process.env;
  const handlers = new Set(); let unsubscribe = null;
  const subscribe = ports.onInterrupt ?? (handler => {
    const signals = ['SIGINT', 'SIGHUP', 'SIGTERM'];
    for (const signal of signals) process.on(signal, handler);
    return () => { for (const signal of signals) process.off(signal, handler); };
  });
  const onInterrupt = handler => {
    handlers.add(handler);
    if (!unsubscribe) unsubscribe = subscribe(() => { for (const listener of [...handlers]) listener(); });
    return () => { handlers.delete(handler); if (!handlers.size) { unsubscribe?.(); unsubscribe = null; } };
  };
  return {
    env, acquireBatchLock: ports.acquireBatchLock ?? acquireRuntimeBatchLock, timers: ports.timers, random: ports.random, captureSource: ports.captureSource ?? captureSource, slotFiles: ports.slotFiles, isAlive: ports.isAlive, pid: ports.pid, agentBridge: ports.agentBridge, discoverAgents: ports.discoverAgents, askAgent: ports.askAgent, signal: ports.signal, ghPath: ports.ghPath, shell: ports.shell, serve: ports.serve, stdout: ports.stdout ?? process.stdout, stderr: ports.stderr ?? process.stderr, fetch: ports.fetch ?? globalThis.fetch,
    gh: ports.gh ?? (args => {
      const executable = authExecutable(env, ports.ghPath);
      return executable ? spawnSync(executable, args, { encoding: 'utf8', env, stdio: ['ignore', 'pipe', 'pipe'], timeout: 60_000 })
        : { status: null, error: { code: 'ENOENT' } };
    }),
    now: ports.now ?? Date.now, randomUUID: ports.randomUUID ?? randomUUID, pollMs: ports.pollMs ?? 2000, postMs: ports.postMs ?? POST_MS,
    interactive: ports.interactive ?? (!!process.stdout.isTTY && !!process.stdin.isTTY), watchMs: ports.watchMs ?? 5000, stdin: ports.stdin ?? process.stdin,
    sleep: ports.sleep ?? ((ms, signal) => new Promise(done => {
      if (signal?.aborted) { done(); return; }
      const finish = () => { clearTimeout(timer); signal?.removeEventListener('abort', finish); done(); };
      const timer = setTimeout(finish, ms);
      signal?.addEventListener('abort', finish, { once: true });
    })),
    onInterrupt,
    // open (macOS) or xdg-open (Linux); a launcher that is still busy after 10 s counts as opened.
    openUrl: ports.openUrl ?? (url => new Promise(done => {
      try {
        const child = spawn(process.platform === 'darwin' ? 'open' : 'xdg-open', [url], { stdio: 'ignore' });
        const timer = setTimeout(() => { child.unref(); done(true); }, 10_000);
        child.on('error', () => { clearTimeout(timer); done(false); });
        child.on('exit', code => { clearTimeout(timer); done(code === 0); });
      } catch { done(false); }
    })),
  };
}

function repoRoot(cwd) {
  const found = spawnSync('git', ['rev-parse', '--show-toplevel'], { cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  if (found.status !== 0 || !found.stdout.trim()) throw new Stop(2, 'pdd test and pdd simulate work in a Git repository. Run them inside your project.');
  return found.stdout.trim();
}

export function runtimeOrigin(env) {
  const raw = env.PDD_RUNTIME_URL || DEFAULT_RUNTIME_URL;
  let url;
  try { url = new URL(raw); } catch { url = null; }
  const loopback = url && ['127.0.0.1', 'localhost', '[::1]'].includes(url.hostname);
  if (!url || !(url.protocol === 'https:' || (url.protocol === 'http:' && loopback)) || url.username || url.password
    || url.pathname !== '/' || url.search || url.hash) throw new Stop(2, 'PDD_RUNTIME_URL must be an HTTPS origin, for example https://runtime.example.');
  return url.origin;
}

// The nearest existing folder's real path, so a symlinked state folder inside the repo is still found.
function realish(path) {
  const parts = [];
  let current = resolve(path);
  for (;;) {
    try { return join(realpathSync(current), ...parts.reverse()); } catch {
      parts.push(current.slice(dirname(current).length + 1)); const parent = dirname(current);
      if (parent === current) return resolve(path);
      current = parent;
    }
  }
}
const inside = (child, parent) => { const rel = relative(parent, child); return rel === '' || (!rel.startsWith('..') && !rel.startsWith(sep) && rel !== '..'); };

function stateDirectory(env, root) {
  const dir = resolve(env.PDD_STATE_DIR || join(env.HOME || homedir(), '.pdd', 'runtime'));
  if (inside(realish(dir), realpathSync(root))) throw new Stop(2, 'PDD_STATE_DIR is inside this repository. pdd keeps run state outside the repo. Choose another folder.');
  return dir;
}
function stateFor(env, root) { return new StateStore(stateDirectory(env,root)); }

export function readContractHistory({root,env = process.env}) {
  const warnings = [], latest = new Map();
  const empty = story_path => ({story_path,baseline:'not-checked',checked_at:null,result_state:null,files:[],references:[]});
  try {
    const found = findTests({root});
    for (const story of found.stories) latest.set(story.path,{value:empty(story.path),time:-Infinity,id:''});
    const directory = join(stateDirectory(env,root),'batches');
    let entries;
    try { entries = readdirSync(directory); } catch (error) { if (error.code === 'ENOENT') return {stories:[...latest.values()].map(row=>row.value),warnings}; throw error; }
    const read = path => {
      const stat = statOrNull(path);
      if (!stat?.isFile() || stat.isSymbolicLink()) return null;
      try { return JSON.parse(readFileSync(path,'utf8')); } catch { warnings.push('Some local Check history is unavailable.'); return null; }
    };
    for (const name of entries.sort()) {
      if (!BATCH.test(name) || !statOrNull(join(directory,name))?.isDirectory() || statOrNull(join(directory,name))?.isSymbolicLink()) continue;
      const folder=join(directory,name), saved=read(join(folder,'batch.json'));
      if (!saved || saved.root !== root || saved.intent === 'lint-only' || !Array.isArray(saved.rows)) continue;
      for (const row of saved.rows) {
        const snapshot = saved.contract_snapshots?.find(item=>item.tests?.includes(row.test));
        const legacy = found.tests.find(test=>test.path===row.test && test.story===row.story);
        const story_path = snapshot?.story_path ?? row.story_path ?? legacy?.storyPath;
        if (typeof story_path !== 'string') continue;
        for (const id of row.request_ids ?? []) {
          if (!UUID.test(id)) continue;
          const receipt=read(join(folder,`${id}.json`));
          const evaluated=receipt?.result?.report?.samples?.some(sample=>sample?.steps?.some(step=>Array.isArray(step?.checks)&&step.checks.length));
          if (!sameJob(receipt,id,'check') || !['passed','failed'].includes(receipt.state) || !evaluated) continue;
          const at = receipt.created_at ?? receipt.started_at ?? (typeof row.sent_at === 'number' ? new Date(row.sent_at).toISOString() : saved.created_at);
          const time=Date.parse(at); if (!Number.isFinite(time)) continue;
          const previous=latest.get(story_path);
          if (previous && (previous.time>time || previous.time===time && (
            previous.value.result_state==='failed' && receipt.state==='passed'
            || previous.value.result_state===receipt.state && previous.id>=id))) continue;
          const available = Array.isArray(snapshot?.files) && Array.isArray(snapshot?.references);
          latest.set(story_path,{time,id,value:{story_path,baseline:available?'checked':'unavailable',checked_at:new Date(time).toISOString(),result_state:receipt.state,files:available?snapshot.files:[],references:available?snapshot.references:[]}});
        }
      }
    }
  } catch (error) { warnings.push(`Local Check history is unavailable: ${cleanText(error.message).slice(0,500)}`); }
  return {stories:[...latest.values()].map(row=>warnings.length && row.value.baseline==='not-checked' ? {...row.value,baseline:'unavailable'} : row.value).sort((a,b)=>a.story_path<b.story_path?-1:a.story_path>b.story_path?1:0),warnings:[...new Set(warnings)]};
}

class StateStore {
  constructor(dir) { this.dir = dir; this.secrets = []; }
  folder(...parts) {
    let path = this.dir;
    for (const part of ['', ...parts]) { path = part ? join(path, part) : path; mkdirSync(path, { recursive: true, mode: 0o700 }); chmodSync(path, 0o700); }
    return path;
  }
  // The token never reaches a file, even when a server answer echoes it.
  write(path, value) {
    const temporary = `${path}.${process.pid}.${randomUUID()}.tmp`;
    let text = `${JSON.stringify(value, null, 2)}\n`;
    for (const secret of this.secrets) text = text.split(secret).join('[secret]');
    writeFileSync(temporary, text, { mode: 0o600 });
    chmodSync(temporary, 0o600); renameSync(temporary, path);
  }
  read(path) { try { return JSON.parse(readFileSync(path, 'utf8')); } catch { return null; } }
  // Exclusive create: a second POST with the same request ID is impossible.
  posted(folder, id) {
    const fd = openSync(join(folder, `${id}.posted`), 'wx', 0o600);
    try { writeSync(fd, `${id}\n`); } finally { closeSync(fd); }
  }
  repoKey(root) { return createHash('sha256').update(realpathSync(root)).digest('hex').slice(0, 16); }
  repo(root) { return this.read(join(this.folder('repos'), `${this.repoKey(root)}.json`)) ?? { root: realpathSync(root), last_batch: null, tries: {} }; }
  saveRepo(root, value) { this.write(join(this.folder('repos'), `${this.repoKey(root)}.json`), value); }
}

// Native boundary: one owner from the fresh batch load through the final saves.
export async function acquireRuntimeBatchLock(folder, { onWarning = () => {} } = {}) {
  const lock = join(folder, 'batch.lock');
  const owner = { pid: process.pid, host: hostname(), started_at: new Date().toISOString() };
  const problem = (code, path, record) => Object.assign(new Error(code), { code, lock: path, owner: record });
  const sameFile = (a, b) => a.dev === b.dev && a.ino === b.ino;
  const warnRelease = (path, error) => {
    try { onWarning(`Warning: could not release batch lock ${cleanText(path, [], { paths: false })} (${cleanText(error.code ?? 'state error')}).`); } catch { /* cleanup cannot replace the command outcome */ }
  };
  let abandoned;
  function snapshot(path) {
    const stat = lstatSync(path, { bigint: true });
    if (!stat.isFile()) throw problem('BATCH_LOCK_INVALID', path, null);
    try { return { stat, record: JSON.parse(readFileSync(path, 'utf8')) }; }
    catch (error) { if (error.code === 'ENOENT') throw error; throw problem('BATCH_LOCK_INVALID', path, null); }
  }
  function publish(path) {
    // A hard link publishes the complete fsynced inode with exclusive EEXIST semantics.
    const temporary = `${path}.${process.pid}.${randomUUID()}.tmp`;
    let fd;
    try {
      fd = openSync(temporary, 'wx', 0o600); chmodSync(temporary, 0o600);
      writeFileSync(fd, JSON.stringify(owner)); fsyncSync(fd);
      const owned = fstatSync(fd, { bigint: true }); closeSync(fd); fd = undefined;
      linkSync(temporary, path);
      return owned;
    } finally {
      if (fd !== undefined) closeSync(fd);
      try { unlinkSync(temporary); } catch (error) { if (error.code !== 'ENOENT') throw error; }
    }
  }
  function claim(path) {
    let owned;
    try { owned = publish(path); }
    catch (error) {
      if (error.code !== 'EEXIST') throw error;
      let before, previous;
      try { ({ stat: before, record: previous } = snapshot(path)); }
      catch (readError) { if (readError.code === 'ENOENT') return claim(path); throw readError; }
      if (previous?.host !== owner.host || !Number.isSafeInteger(previous.pid) || previous.pid < 1
        || typeof previous.started_at !== 'string' || !Number.isFinite(Date.parse(previous.started_at))) throw problem('BATCH_LOCK_INVALID', path, previous);
      let dead = false;
      try { process.kill(previous.pid, 0); }
      catch (pidError) {
        if (pidError.code === 'ESRCH') dead = true;
        else if (pidError.code !== 'EPERM') throw problem('BATCH_LOCK_INVALID', path, previous);
      }
      if (!dead) throw problem('BATCH_LOCK_BUSY', path, previous);
      const releaseGuard = claim(`${path}.recover.${previous.pid}`);
      try {
        let current;
        try { current = snapshot(path); } catch (statError) { if (statError.code !== 'ENOENT') throw statError; }
        if (current && sameFile(before, current.stat) && isDeepStrictEqual(previous, current.record)) {
          unlinkSync(path); if (path === lock) abandoned = previous;
        }
        return claim(path);
      } finally { releaseGuard(); }
    }
    let released = false;
    return () => {
      if (released) return; released = true;
      try {
        const current = snapshot(path);
        if (sameFile(owned, current.stat) && isDeepStrictEqual(owner, current.record)) unlinkSync(path);
      } catch (error) { if (error.code !== 'ENOENT') warnRelease(path, error); }
    };
  }
  const release = claim(lock);
  try { if (abandoned) onWarning(`Warning: recovered an abandoned batch lock from dead pid ${abandoned.pid} on ${abandoned.host}.`); }
  catch (error) { release(); throw error; }
  return release;
}

async function ownBatch(context, name) {
  if (context.releaseBatch) return;
  try {
    context.releaseBatch = await context.ports.acquireBatchLock(context.folder, { onWarning: text => line(context.ports.stderr, text) });
    context.lockedBatch = name;
  } catch (error) {
    const owner = error.owner, label = value => cleanText(value ?? 'unverified').slice(0, 120);
    if (error.code === 'BATCH_LOCK_BUSY') throw new Stop(3, `Another pdd test command is using batch ${name} (pid ${label(owner?.pid)}, host ${label(owner?.host)}, since ${label(owner?.started_at)}); run pdd test --read ${name} after it ends.`);
    if (error.code === 'BATCH_LOCK_INVALID') throw new Stop(2, `Lock file ${cleanText(error.lock ?? join(context.folder, 'batch.lock'), [], { paths: false })} has an unverifiable owner (host ${label(owner?.host)}). Delete it only if no pdd command is running on that host, then run the command again.`);
    throw new Stop(2, `Could not lock batch ${name} (${cleanText(error.code ?? 'state error')}). Nothing was sent.`);
  }
}

function signIn(gh, store) {
  const token = gh(['auth', 'token']);
  if (token.error?.code === 'ENOENT') throw new Stop(5, 'Install the GitHub CLI, then run gh auth login');
  const value = token.status === 0 ? String(token.stdout ?? '').trim() : '';
  if (!value) throw new Stop(5, 'Run gh auth login');
  if (store) store.secrets = [value];
  const user = gh(['api', 'user', '--jq', '.login + " " + (.id|tostring)']);
  const [login, id] = user.status === 0 ? String(user.stdout ?? '').trim().split(' ') : [];
  const why = user.status === 0 ? '' : causeText(user.stderr || user.error?.code, [value]);
  if (!login || !/^\d+$/.test(id ?? '')) throw new Stop(5, `pdd could not read your GitHub login (gh api user${why ? `: ${why}` : ''}). Run gh auth status.`);
  return { token: value, login, userId: id };
}

// Retry-After in seconds (1 to 300); no header or a bad one means 5 s.
function retryAfter(headers) {
  const raw = headers?.get?.('retry-after'), seconds = Number(raw);
  return raw && /^\d+$/.test(raw.trim()) ? Math.min(Math.max(seconds, 1), 300) * 1000 : 5000;
}

// Network errors that prove the request never reached the server: nothing was sent, so pdd can stop and say why.
const UNREACHABLE = { ENOTFOUND: 'the address was not found', EAI_AGAIN: 'the address was not found', ECONNREFUSED: 'the connection was refused',
  EHOSTUNREACH: 'there is no network route to it', ENETUNREACH: 'there is no network route to it', UND_ERR_CONNECT_TIMEOUT: 'the connection timed out' };
function lostReply(error, origin) {
  const code = String(error?.cause?.code ?? error?.code ?? ''), cert = /CERT|SELF_SIGNED|UNABLE_TO_VERIFY|ERR_TLS/.test(code);
  const reason = UNREACHABLE[code] ?? (cert ? 'its TLS certificate was not accepted' : null);
  if (reason) return { lost: true, unreachable: `pdd could not reach the PDD interpreter at ${origin}: ${reason} (${code}). Nothing was sent. Check your network and PDD_RUNTIME_URL, then run the command again.` };
  return { lost: true, why: code ? `connection failed: ${code}` : error?.name === 'AbortError' ? 'no answer in time' : null };
}
const AUTH_TEXT = 'The PDD interpreter did not accept your GitHub login (HTTP 401). Run gh auth login, then run the command again.';

// HTTP to the runtime. The token stays in this object and in request headers only.
class Runtime {
  constructor({ origin, token, ports, signal }) { Object.assign(this, { origin, token, ports, signal }); this.sources = new WeakMap(); }
  async send(path, init, ms) {
    if (this.signal?.aborted) return { lost: true };
    const controller = new AbortController(), stop = () => controller.abort();
    const timer = setTimeout(stop, ms);
    this.signal?.addEventListener('abort', stop, { once: true });
    try {
      const response = await this.ports.fetch(new URL(path, this.origin), { ...init, redirect: 'manual', signal: controller.signal,
        headers: { ...init.headers, Authorization: `Bearer ${this.token}` } });
      const text = await response.text();
      let json = null;
      try { json = JSON.parse(text); } catch { json = null; }
      return { status: response.status, headers: response.headers, text, json };
    } catch (error) { return lostReply(error, this.origin); } finally { clearTimeout(timer); this.signal?.removeEventListener('abort', stop); }
  }
  post(path, request, tar, timeoutMs = this.ports.postMs) {
    const form = new FormData();
    form.set('request', new Blob([JSON.stringify(request)], { type: 'application/json' }), 'request.json');
    let source = this.sources.get(tar);
    if (!source) { source = new Blob([tar], { type: 'application/x-tar' }); this.sources.set(tar, source); }
    form.set('source', source, 'source.tar');
    return this.send(path, { method: 'POST', body: form }, timeoutMs);
  }
  get(id, timeoutMs = GET_MS) { return this.send(`/v1/runs/${id}`, { method: 'GET' }, timeoutMs); }
  reopen(id) { return this.send(`/v1/try/${id}/reopen`, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: '{}' }, this.ports.postMs); }
  stop(tryId, requestId) { return this.send(`/v1/try/${tryId}`, { method: 'DELETE', headers: { 'X-Request-Id': requestId } }, this.ports.postMs); }
}

// Answers that stop everything with one plain line and exit 5: a login not on the invite list (403 not-invited), an
// account that PDD Cloud did not approve (403 no-cloud-access) or could not check (503 cloud-unavailable), and an
// old pdd that the server no longer serves (code update-required, any status, 0.1.6).
const UPDATE_TEXT = 'Please update pdd: npm install -g github:promptdriven/pdd';
const NO_CLOUD_TEXT = 'Your GitHub account does not have PDD interpreter access yet. Sign up at https://promptdriven.ai/login with GitHub; you can use the interpreter when your account is approved.';
const CLOUD_DOWN_TEXT = 'PDD Cloud could not confirm your access. Try again in a minute.';
function blockingAnswer(reply) {
  // error.code first: for pdd 0.1.9 a server sends a top-level update-required over error.code no-cloud-access.
  const json = reply.json, error = isObject(json?.error) ? json.error : null, code = error?.code ?? json?.code;
  const said = () => [error?.message, json?.message].map(text => typeof text === 'string' ? cleanText(text).slice(0, 300) : '').find(Boolean);
  if (code === 'update-required') return said() || UPDATE_TEXT;
  if (reply.status === 403 && code === 'no-cloud-access') return said() || NO_CLOUD_TEXT;
  // The server text says that pdd retries; pdd stops at once instead, so it prints its own line.
  if (reply.status === 503 && code === 'cloud-unavailable') return CLOUD_DOWN_TEXT;
  if (reply.status !== 403 || code !== 'not-invited') return null;
  const named = json.login ?? error?.details?.login;
  const login = typeof named === 'string' && /^[A-Za-z0-9-]{1,39}$/.test(named) ? named : null;
  return `Your GitHub login ${login ?? ''}${login ? ' ' : ''}is not on the PDD interpreter invite list yet. Ask the PDD team to add you.`;
}

const sameJob = (json, id, command) => isObject(json) && json.requestId === id && json.id === id && json.command === command && JOB_STATES.has(json.state);
const gateText = reply => reply.status === 503 && !reply.json && String(reply.text ?? '').includes('The runtime opens soon.');

// Only capacity refusals that prove no execution can authorize a fresh check ID.
function capacityDelay(refusal, headers) {
  const code = refusal?.code ?? '';
  const capacity = /(?:^|-)(?:queue|capacity|busy)(?:-|$)|^server-full$/.test(code);
  if (!capacity || (code !== 'check-queue-timeout' && code !== 'server-full' && refusal.details?.retryable !== true)) return null;
  if (headers?.get?.('retry-after')) return retryAfter(headers);
  const seconds = refusal.details?.retry_after;
  return (typeof seconds === 'number' && Number.isFinite(seconds) && seconds > 0 ? Math.min(300, Math.max(1, seconds)) : 5) * 1000;
}
function safeAdmission(reply) {
  const json = reply.json, report = json?.result?.report;
  return !(json?.usage && Object.hasOwn(json.usage, 'calls') && json.usage.calls !== 0)
    && json?.accounting_complete !== false && json?.usage?.accounting_complete !== false && report?.accounting_complete !== false
    && !(report && Object.hasOwn(report, 'provider_calls') && report.provider_calls !== 0) && !report?.samples?.some(sample => sample?.steps?.some(step => step?.checks?.length));
}
function checkCapacity(answer, headers) {
  const report = answer?.result?.report;
  if (answer?.command !== 'check' || answer.state !== 'refused' || answer.usage?.calls !== 0 || report?.dispatch !== 'not_started'
    || Object.hasOwn(report, 'provider_calls') && report.provider_calls !== 0 || report.accounting_complete === false || answer.usage?.accounting_complete === false
    || report.samples?.some(sample => sample?.steps?.some(step => step?.checks?.length))) return null;
  return [report.refusal, ...(Array.isArray(answer.result?.refusals) ? answer.result.refusals : [])].map(item => capacityDelay(item, headers)).find(wait => wait !== null) ?? null;
}
function accumulatedCalls(context, row) {
  const calls = row.request_ids.map(id => {
    const answer = context.store.read(join(context.folder, `${id}.json`));
    if (answer) return answer.usage?.calls;
    const admission = context.store.read(join(context.folder, `${id}.admission.json`));
    return admission?.dispatch === 'not_started' && safeAdmission({ json: admission }) ? 0 : 'unknown';
  });
  return calls.every(value => typeof value === 'number' && Number.isFinite(value)) ? calls.reduce((a, b) => a + b, 0) : 'unknown';
}
// A confirmed pause follows a POST. Keep its submission and accounting visible
// when an interrupt ends the pause rather than describing an unsent request.
function stoppedPause(context, target, kind) {
  const ids = target.request_ids, calls = accumulatedCalls(context, target);
  const recovery = context.batch ? ` Read saved results with: pdd test --read ${context.batch}`
    : calls === 'unknown' ? ' Read the saved request before sending anything again.' : '';
  return `Stopped. Submitted ${kind} ${ids.length === 1 ? 'request' : 'requests'}: ${ids.join(', ')}. `
    + 'The interpreter confirmed that the last attempt did not start; no work ran for this attempt. '
    + (calls === 'unknown' ? 'Total usage is unknown; earlier submissions may have run.' : `Recorded usage: ${calls} AI calls.`) + recovery;
}
function markBusy(context, row, wait, observedAt = context.ports.now(), legacy = context.reading) {
  const id = row.request_ids.at(-1);
  const anchored = row.busy_request_id === id && Number.isFinite(row.busy_observed_at)
    && Number.isFinite(row.retry_at) && Number.isFinite(row.capacity_until);
  if (!anchored) {
    const now = observedAt;
    // Legacy receipts have no trustworthy answer time. Repair once at observation,
    // retaining a later saved server wait; a POST start is never that anchor.
    const savedWait = legacy && Number.isFinite(row.retry_at) ? row.retry_at : 0;
    Object.assign(row, { busy_request_id: id, busy_observed_at: now,
      retry_at: Math.max(savedWait, now + (legacy ? 10_000 : Math.max(wait, 10_000))), capacity_until: now + 60_000 });
  }
  Object.assign(row, { state: context.reading ? 'not_run' : 'waiting', busy: true, can_retry: true, calls: 0, refusals: [],
    checks: null, criteria: null, all_checks: [], failed_checks: [], why: null, next_step: null,
    note: { code: 'check-busy', message: 'The interpreter is busy. No checks ran for this attempt. Retry this batch later.' } });
  if (row.restart_used) row.calls = accumulatedCalls(context, row);
  if (!context.reading) context.checkWindow = 1;
}

const restarted = answer => answer?.command === 'check' && answer.state === 'unknown' && [answer.result?.report?.refusal, ...(Array.isArray(answer.result?.refusals) ? answer.result.refusals : [])].some(item => item?.code === 'service-restarted');
const confirmedEnd = answer => ['passed', 'failed', 'refused', 'not_run'].includes(answer?.state) || restarted(answer);
function localLimit(context) {
  if (context.localLimit !== undefined) return context.localLimit;
  const raw = context.ports.env.PDD_MAX_JOBS;
  if (raw === undefined) return context.localLimit = Infinity;
  const value = Number(raw);
  if (/^[1-9][0-9]*$/.test(String(raw)) && Number.isSafeInteger(value)) return context.localLimit = value;
  line(context.ports.stderr, 'Warning: PDD_MAX_JOBS must be a positive safe integer; using no local cap.');
  return context.localLimit = Infinity;
}
function uploadLimit(context) {
  if (context.uploadLimit !== undefined) return context.uploadLimit;
  const raw = context.ports.env.PDD_MAX_UPLOADS;
  if (raw === undefined) return context.uploadLimit = 8;
  const value = Number(raw);
  if (/^[0-9]+$/.test(String(raw)) && Number.isSafeInteger(value) && value > 0) return context.uploadLimit = value;
  line(context.ports.stderr, 'Warning: PDD_MAX_UPLOADS must be a positive safe integer; using 8 uploads.');
  return context.uploadLimit = 8;
}
function slotPorts(context, deadline = context.deadline) {
  const { ports } = context;
  return { ...(ports.slotFiles ? { files: ports.slotFiles } : {}), ...(ports.isAlive ? { isAlive: ports.isAlive } : {}), ...(ports.pid ? { pid: ports.pid } : {}),
    ...(ports.timers ? { timers: ports.timers } : {}), ...(ports.random ? { random: ports.random } : {}),
    onInterrupt: ports.onInterrupt, deadline, now: ports.now, randomUUID: ports.randomUUID, sleep: ms => ports.sleep(ms, context.signal), interrupted: () => context.interrupted || !!context.stopped || !!context.sendError,
    say: message => line(ports.stderr, message), readRun: async id => {
      const { jobs } = await listRuntimeJobs({ stateDir: context.store.dir, origin: context.origin }, { files: ports.slotFiles });
      const owner = jobs.find(row => row.request_ids.includes(id));
      if (!owner) return 'unknown';
      if (context.interrupted || ports.now() >= deadline) return 'unknown';
      const reply = await context.runtime.get(id, Math.max(1, Math.min(GET_MS, deadline - ports.now()))), answer = reply.json;
      if (reply.status !== 200 || !sameJob(answer, id, owner.kind)) return 'unknown';
      return confirmedEnd(answer) ? 'ended' : ['queued', 'running'].includes(answer.state) ? 'running' : 'unknown';
    } };
}
async function finishReservation(context, target, answer) {
  if (target?.reservation && confirmedEnd(answer)) {
    await releaseRuntimeSlot(target.reservation, { ended: true }, slotPorts(context));
    target.reservation = null;
  }
}
function queueProgress(context, answer) {
  const q = answer?.queue;
  if (answer?.state === 'queued' && [q?.ahead, q?.slots_in_use, q?.slots].every(value => Number.isSafeInteger(value) && value >= 0)) {
    const message = `Queued on the interpreter: ${q.ahead} ahead, ${q.slots_in_use} of ${q.slots} slots busy. Your test is fine.`;
    context.queueLines ??= new Map();
    if (context.queueLines.get(answer.id) !== message) { line(context.ports.stderr, message); context.queueLines.set(answer.id, message); }
  }
}
const localMaintenanceEnd = until => new Intl.DateTimeFormat(undefined, {
  hour: '2-digit', minute: '2-digit', hourCycle: 'h23', timeZoneName: 'short',
}).format(new Date(until));
function showMaintenance(context, details) {
  const until = Date.parse(details?.until), reason = cleanText(details?.reason, context.secrets) || 'maintenance';
  const key = JSON.stringify([details?.until ?? null, reason]);
  if (context.maintenanceLine !== key) {
    context.maintenanceLine = key;
    line(context.ports.stderr, `The interpreter is in maintenance${Number.isFinite(until) ? ` until ${localMaintenanceEnd(until)}` : ''} (${reason}). pdd waits, then continues.`);
  }
}
function maintenanceNotice(context, verdict, reply) {
  const details = reply.json?.error?.details ?? reply.json?.maintenance ?? {};
  const until = Date.parse(details.until), now = context.ports.now();
  context.admissionMaintenance = { details, end: Math.max(now + verdict.wait, Number.isFinite(until) ? until : now) };
  verdict.wait = Math.min(60_000, context.admissionMaintenance.end - now);
  context.waitCause = 'maintenance';
  showMaintenance(context, details);
}
async function waitBudget(context, wait, deadline = context.deadline) {
  const end = Math.min(context.ports.now() + wait, deadline);
  while (!context.interrupted && context.ports.now() < end) {
    await context.ports.sleep(Math.min(60_000, end - context.ports.now()), context.signal);
  }
  return !context.interrupted && context.ports.now() < deadline;
}
const capacityCache = new Map(), interruptedAdmissions = new WeakSet();
async function readCapacity(context, deadline, refresh) {
  const key = JSON.stringify([context.origin, context.identity.login, context.identity.userId]), now = context.ports.now();
  let entry = capacityCache.get(key);
  if (!entry || !entry.pending && (refresh || now < entry.at || now - entry.at >= 10_000)) {
    entry = { at: now, pending: true, observers: 0, controller: new AbortController() };
    // Capacity is shared across commands. Its finite transport budget remains
    // bounded by the initiating phase, but no one observer owns its cancellation.
    const runtime = new Runtime({ origin: context.origin, token: context.identity.token, ports: context.ports, signal: entry.controller.signal });
    entry.promise = runtime.send('/v1/capacity', { method: 'GET' }, Math.max(1, Math.min(GET_MS, deadline - now))).then(reply => {
      entry.pending = false; entry.at = context.ports.now();
      // Keep unclear replies distinct and reusable until this completion TTL.
      // Recognized access gates retain their ordinary stop/recheck behavior.
      if ((blockingAnswer(reply) || reply.status === 401 || gateText(reply)) && capacityCache.get(key) === entry) capacityCache.delete(key);
      return reply;
    });
    capacityCache.set(key, entry);
  }
  entry.observers++;
  const timers = context.ports.timers ?? { setInterval, clearInterval };
  let timer, stop;
  try {
    return await Promise.race([entry.promise, new Promise(done => {
      stop = () => done(null);
      const observeDeadline = () => {
        if (timer !== undefined) { timers.clearInterval(timer); timer = undefined; }
        if (context.interrupted || context.signal?.aborted || context.ports.now() >= deadline) { stop(); return; }
        if (Number.isFinite(deadline)) timer = timers.setInterval(observeDeadline, Math.max(1, Math.min(60_000, deadline - context.ports.now())));
      };
      context.signal?.addEventListener('abort', stop, { once: true });
      observeDeadline();
    })]);
  } finally {
    if (timer !== undefined) timers.clearInterval(timer);
    context.signal?.removeEventListener('abort', stop);
    if (--entry.observers === 0 && entry.pending) {
      // No command still needs this read. Cancel ordinary transport work and
      // never cache observer cancellation as a completed unclear response.
      if (capacityCache.get(key) === entry) capacityCache.delete(key);
      entry.controller.abort();
    }
  }
}
async function capacityReady(context, deadline, busyRow = null) {
  let refresh = !!context.admissionMaintenance;
  while (!context.interrupted && !context.stopped && !context.sendError && context.ports.now() < deadline) {
    const reply = await readCapacity(context, deadline, refresh);
    if (reply === null || context.interrupted || context.signal?.aborted || context.ports.now() >= deadline) return false;
    const blocked = blockingAnswer(reply);
    const stop = blocked || (reply.status === 401 ? AUTH_TEXT : gateText(reply) ? 'The runtime opens soon.' : null);
    if (stop) { context.stopped = { code: 'blocked', message: stop }; throw new Stop(5, stop); }
    const understood = reply.status === 404 || reply.status === 200 && isObject(reply.json) && Object.hasOwn(reply.json, 'maintenance');
    if (!understood && !context.capacityWarning) {
      context.capacityWarning = true;
      line(context.ports.stderr, 'Warning: interpreter capacity could not be read; continuing with ordinary interpreter admission.');
    }
    const maintenance = reply.status === 200 ? reply.json?.maintenance : null, until = Date.parse(maintenance?.until);
    const pending = context.admissionMaintenance;
    const future = Number.isFinite(until) && until > context.ports.now();
    const end = Math.max(future ? until : 0, pending?.end ?? 0);
    if (end <= context.ports.now()) {
      context.admissionMaintenance = null; context.maintenanceLine = null;
      if (busyRow) {
        const now = context.ports.now(), counts = reply.status === 200 ? reply.json?.slots?.check : null;
        const usable = Number.isSafeInteger(counts?.running) && counts.running >= 0
          && Number.isSafeInteger(counts?.limit) && counts.limit >= 0;
        const minimum = Math.max(0, busyRow.retry_at - now);
        const full = usable && counts.running >= counts.limit && busyRow.capacity_until > now;
        if (minimum > 0 || full) {
          context.waitCause = 'server capacity';
          if (!await waitBudget(context, Math.min(10_000, minimum > 0 ? minimum : busyRow.capacity_until - now), deadline)) return false;
          refresh = false;
          continue;
        }
      }
      return true;
    }
    context.waitCause = 'maintenance';
    if (future) showMaintenance(context, maintenance); else if (pending) showMaintenance(context, pending.details);
    if (!await waitBudget(context, Math.min(60_000, end - context.ports.now()), deadline)) return false;
    refresh = true;
  }
  return false;
}
async function admission(context, kind, target, deadline = context.deadline) {
  context.waitCause = 'a local slot';
  const reservation = await acquireRuntimeSlot({ stateDir: context.store.dir, origin: context.origin, limit: localLimit(context), kind,
    deadline: Number.isFinite(deadline) ? deadline : null }, slotPorts(context, deadline));
  if (!reservation) return false;
  target.reservation = reservation;
  context.waitCause = 'server capacity';
  context.reservations ??= new Set(); context.reservations.add(reservation);
  let ready = false;
  try { ready = await capacityReady(context, deadline, kind === 'check' && target.busy ? target : null); return ready && !context.interrupted && !context.stopped && !context.sendError && context.ports.now() < deadline; }
  finally {
    if (context.interrupted) interruptedAdmissions.add(target);
    if (!ready || context.interrupted || context.stopped || context.sendError || context.ports.now() >= deadline) { await releaseRuntimeSlot(reservation, { ended: true }, slotPorts(context, deadline)); target.reservation = null; }
  }
}

// One answer to a POST, as the row table of the spec.
function judgePost(reply, id, command, secrets) {
  if (reply.unreachable) return { kind: 'stop', note: { code: null, message: reply.unreachable } };
  if (reply.lost) return { kind: 'unknown', why: 'The answer to the request was lost.' };
  const stopLine = blockingAnswer(reply);
  if (stopLine) return { kind: 'stop', note: { code: 'blocked', message: stopLine }, blocked: true };
  const error = isObject(reply.json?.error) ? reply.json.error : null;
  if ([429, 503].includes(reply.status) && reply.json?.dispatch === 'not_started' && !safeAdmission(reply))
    return { kind: 'unknown', why: 'The admission receipt has uncertain execution accounting.' };
  if (reply.status === 503 && error?.code === 'maintenance' && reply.json?.dispatch === 'not_started' && safeAdmission(reply))
    return { kind: 'busy', wait: retryAfter(reply.headers), admission: reply.json, maintenance: true };
  if (command === 'lint' && reply.status === 503 && error?.code === 'lint-queue-full' && lintQueueWait(error) !== null && safeAdmission(reply)) return { kind: 'busy', wait: capacityDelay(error, reply.headers), admission: reply.json };
  if (['check', 'try'].includes(command) && [429, 503].includes(reply.status) && reply.json?.dispatch === 'not_started' && safeAdmission(reply)) {
    const wait = capacityDelay(error, reply.headers);
    if (wait !== null) return { kind: 'busy', wait, admission: reply.json };
  }
  const note = fallback => ({ code: cleanText(error?.code, secrets) || null, message: cleanText(error?.message, secrets) || fallback });
  if (reply.status === 200 || reply.status === 202) {
    return sameJob(reply.json, id, command) ? { kind: 'accepted', answer: reply.json, wait: checkCapacity(reply.json, reply.headers) } : { kind: 'unknown', why: 'The interpreter answered with another request ID or command.' };
  }
  if (reply.status === 429) {
    return error?.code === 'server-full' && reply.json?.dispatch === 'not_started' && safeAdmission(reply) ? { kind: 'busy', wait: retryAfter(reply.headers), admission: reply.json }
      : { kind: 'not_run', note: note('The interpreter is busy. Try again later.') };
  }
  if (gateText(reply)) return { kind: 'stop', note: { code: null, message: 'The runtime opens soon.' } };
  if (reply.status === 401) return { kind: 'stop', note: { code: cleanText(error?.code, secrets) || 'auth-required', message: AUTH_TEXT } };
  if (reply.status === 503 && /^(?:pool-low-room|pool-copy-[a-z-]+|github-unavailable)$/.test(error?.code ?? '')) return { kind: 'not_run', note: note('Try again later.') };
  if ([400, 413, 415, 422].includes(reply.status) && error?.code) {
    return { kind: 'refused', refusal: { code: cleanText(error.code, secrets), section: null, message: cleanText(error.message, secrets) || null,
      engine_message: reply.json.details ? cleanText(JSON.stringify(reply.json.details), secrets) : null,
      ...(reply.status === 422 ? { reason: cleanText(error.reason, secrets) || null, fix: cleanText(error.fix, secrets) || null,
        hint: cleanText(error.hint, secrets) || null, cause: cleanText(error.cause, secrets) || null } : { hint: null }) } };
  }
  const said = cleanText(error?.message, secrets);
  return { kind: 'unknown', why: `The interpreter answered HTTP ${reply.status}${said ? `: ${said.replace(/\.$/, '')}` : ''}.` };
}

// One answer to a GET of a known request ID.
function judgeGet(reply, id, command) {
  if (reply.lost) return { kind: 'again', why: reply.unreachable ? 'cannot reach the interpreter' : reply.why, unreachable: reply.unreachable };
  const stopLine = blockingAnswer(reply);
  if (stopLine) return { kind: 'blocked', message: stopLine };
  if (reply.status === 200) return sameJob(reply.json, id, command) ? { kind: 'state', answer: reply.json, wait: checkCapacity(reply.json, reply.headers) } : { kind: 'unknown', why: 'The interpreter answered with another request ID or command.' };
  if (reply.status === 404) return { kind: 'missing' };
  if (reply.status === 410) return { kind: 'unknown', why: 'The result expired.', status: 410 };
  if (reply.status === 401) return { kind: 'auth' };
  if (gateText(reply)) return { kind: 'gate' };
  return { kind: 'again' };
}

async function eachLimited(items, limit, work) {
  const queue = [...items];
  await Promise.all(Array.from({ length: Math.min(limit, queue.length) }, async () => { while (queue.length) await work(queue.shift()); }));
}

function batchId(now, uuid) {
  const date = new Date(now), two = value => String(value).padStart(2, '0');
  const suffix = BigInt(`0x${uuid().replace(/-/g, '').slice(0, 12)}`).toString(36).padStart(4, '0').slice(-4);
  return `${date.getFullYear()}${two(date.getMonth() + 1)}${two(date.getDate())}-${two(date.getHours())}${two(date.getMinutes())}${two(date.getSeconds())}-${suffix}`;
}

// Local setup for a check or a try: root, tests, selected rows.
function localSetup(cwd, words) {
  const root = repoRoot(cwd), found = findTests({ root, files: gitFiles(root) });
  const realCwd = realpathSync(cwd), realRoot = realpathSync(root);
  const normalized = words.map(word => {
    const rel = relative(realRoot, resolve(realCwd, word)).split(sep).join('/');
    return found.visible.has(rel) ? rel : word;
  });
  return { root, found, normalized };
}

function storyList(found) {
  return found.tests.map(test => `  ${test.story}  ${test.path}${test.title && test.title !== test.story ? `  (${test.title})` : ''}`);
}

function select(found, words, root) {
  if (!found.tests.length) {
    throw new Stop(2, ['No tests found. A test is a Git-visible *.json file with "schema_version": "prompt-runtime.program-scenario.v1".',
      ...(root ? whyNoTests(root, found.visible) : [])].join('\n'));
  }
  const { selected, unknown } = selectTests(found, words);
  if (unknown.length) throw new Stop(2, [`Unknown story ${unknown.map(word => `"${cleanText(word)}"`).join(', ')}. Stories with tests:`, ...storyList(found)].join('\n'));
  return selected;
}

const localRows = rows => rows.map(row => ({ ...row, state: row.refusals.length ? 'refused' : 'ready', phase: row.refusals.length ? 'local' : 'server',
  request_ids: [], calls: 0, report_url: null, checks: null, failed_checks: [], all_checks: [] }));

// Lint verdict for each test: the prompts it reaches must be approved or a current draft, and not refused. A draft marks the row.
function judgeLint(answer, rows, root, visible, secrets = []) {
  const program = answer?.result?.report?.program;
  if (!isObject(program) || !Array.isArray(program.prompts)) return null;
  const byPath = new Map(program.prompts.filter(isObject).map(prompt => [prompt.path, prompt]));
  const refused = new Map((Array.isArray(program.refused_prompts) ? program.refused_prompts : []).filter(isObject).map(item => [item.path, item]));
  const verdicts = new Map();
  for (const row of rows) {
    const reached = new Set(), queue = row.steps.map(step => step.entry_path);
    let problem = null;
    while (queue.length && !problem) {
      const path = queue.shift();
      if (reached.has(path)) continue;
      reached.add(path);
      const prompt = byPath.get(path), state = prompt?.admission_state ?? prompt?.state;
      if (refused.has(path)) problem = { code: cleanText(refused.get(path).code, secrets) || 'lint-refused', section: 'lint', message: `${cleanText(path, secrets)}: ${cleanText(refused.get(path).message || refused.get(path).code, secrets)}` };
      else if (!prompt) problem = { code: 'unknown-target', section: 'lint', message: `${path} is not in the lint report.` };
      else if (state !== 'approved' && state !== 'draft') {
        const local = readPrompt(root, visible, path);
        problem = state === 'stale' ? { code: 'interface-stale', section: 'lint', message: `${path} changed after its hash was filled or approved.`, hint: staleHint }
          : { code: `interface-${cleanText(state, secrets) || 'unapproved'}`, section: 'lint', message: `${path} has no usable Runtime interface${local.error ? ` (${local.error})` : ''}.` };
      } else {
        if (state === 'draft') row.draft = true;
        for (const call of Array.isArray(prompt.interface?.calls) ? prompt.interface.calls : []) if (typeof call?.target === 'string') queue.push(call.target);
      }
    }
    if (problem) verdicts.set(row, problem);
  }
  return verdicts;
}

// Hints that make a server refusal readable: the local P9 rule or the P7 status.
function addHints(row, root, visible) {
  for (const item of row.refusals) {
    const index = Number(/^steps\[(\d+)\]/.exec(item.section ?? '')?.[1]), step = row.steps?.[index];
    if (!step) continue;
    const prompt = readPrompt(root, visible, step.entry_path);
    if (item.code === 'invalid-input') {
      const entry = prompt.interface?.entries?.find?.(candidate => candidate?.operation === step.operation);
      const local = entry ? checkInput(step.input, entry.input_schema, index).refusals : [];
      const match = local.find(problem => problem.section === item.section) ?? local[0];
      if (match) item.hint = match.message;
    } else if (item.code === 'interface-unapproved' && (row.draft || prompt.interface?.status === 'draft')) {
      item.message = DRAFT_SERVER_TEXT;
    } else if (item.code === 'interface-stale' && prompt.interface) item.hint = staleHint;
  }
}

// State owns the verdict; discard only the exact generic failure explanation.
function noVerdictAdvice(answer, view) {
  const why = view.why;
  return { why: why && why !== 'Checks failed.' ? why : null,
    next_step: checkCapacity(answer) === null ? view.next_step : null };
}

function applyAnswer(row, answer, context, observedWait = null, observedAt = context.ports.now()) {
  context.unsentInterruptions?.delete(row);
  const view = projectAnswer(answer, { origin: context.origin, secrets: context.secrets, steps: row.steps ?? [], criterionTexts: row.criterion_texts ?? {} });
  const advice = noVerdictAdvice(answer, view);
  const firstDiagnosis = view.failed_checks.find(check => check.diagnosis) ?? null, failed = view.state === 'failed';
  Object.assign(row, { state: view.state, checks: view.checks, criteria: view.criteria, failed_checks: view.failed_checks, all_checks: view.all_checks,
    refusals: view.refusals, calls: view.calls, requested_model: view.requested_model, report_url: view.report_url ?? row.report_url,
    server_seconds: view.server_seconds, time_limit: view.time_limit, known_calls: view.known_calls, unknown_calls: view.unknown_calls,
    why: failed ? view.why ?? firstDiagnosis?.diagnosis?.why ?? null : ['refused', 'not_run', 'unknown'].includes(view.state) ? advice.why ?? (view.state === 'unknown' && row.lost && row.why !== 'Checks failed.' ? row.why : null) : null,
    who: failed ? view.who ?? firstDiagnosis?.diagnosis?.who ?? null : null,
    next_step: failed ? view.next_step ?? firstDiagnosis?.diagnosis?.next_step ?? null : ['refused', 'not_run', 'unknown'].includes(view.state) ? advice.next_step : null,
    rerun: view.rerun ?? row.rerun,
    engine_sha: view.engine_sha, provider: view.provider,
    draft: view.draft ?? row.draft });
  if (row.restart_used) row.calls = accumulatedCalls(context, row);
  const wait = checkCapacity(answer);
  if (wait !== null) markBusy(context, row, observedWait ?? wait, observedAt, context.reading && observedWait === null);
  else { row.busy = false; row.can_retry = false; row.note = null; }
  if (row.state === 'refused') addHints(row, context.root, context.visible);
  if (ENDED.has(row.state) && row.sent_at && !row.ended_at && !context.reading) row.ended_at = context.ports.now();
  row.seconds = !ENDED.has(row.state) ? null : row.sent_at && row.ended_at ? (row.ended_at - row.sent_at) / 1000 : row.server_seconds;
}

// Declared operations estimate possible work; conditional branches may use fewer calls. Caps stay authoritative.
function costLine(rows, root, visible) {
  const prompts = new Map();
  const cost = (path, seen = new Set()) => {
    if (seen.has(path)) return 0;
    if (!prompts.has(path)) prompts.set(path, readPrompt(root, visible, path));
    const iface = prompts.get(path)?.interface;
    if (!iface) return 1;
    const next = new Set([...seen, path]);
    const resources = (iface.resources ?? []).reduce((sum, resource) => sum + (Array.isArray(resource.operations) ? resource.operations.length : 0), 0);
    const calls = (iface.calls ?? []).reduce((sum, call) => sum + (Number.isInteger(call?.max_calls) ? call.max_calls : 0) * cost(call?.target, next), 0);
    return 1 + resources + calls;
  };
  const most = rows.reduce((sum, row) => sum + row.max_calls, 0);
  const about = Math.min(most, rows.reduce((sum, row) => sum + row.steps.reduce((steps, step) => steps + cost(step?.entry_path), 0), 0));
  return `Checking all ${rows.length} ${rows.length === 1 ? 'story' : 'stories'}: about ${about} AI call${about === 1 ? '' : 's'} (at most ${most}).`;
}

function batchRecord(context) {
  const { batch, origin, root, identity, capture, rows, lint, warnings } = context;
  return { version: 1, batch, origin, root, head: context.head, login: identity.login, user_id: identity.userId,
    source_sha256: capture.sha256, files: capture.files.map(file => file.path), bytes: capture.bytes, timeout_min: context.timeoutMin,
    created_at: new Date(context.startedAt).toISOString(), intent: context.intent, lint, warnings, coverage: context.coverage,
    contract_snapshots: capture.stories,
    rows: rows.map(row => ({ test: row.test, story: row.story, story_path: row.story_path, title: row.title, request_ids: row.request_ids, state: row.state,
      ...(!row.request_ids.length && Object.hasOwn(row, 'calls') ? { calls: row.calls } : {}),
      phase: row.phase, post_verdict: row.post_verdict ?? null, report_url: row.report_url, refusals: row.refusals, note: row.note ?? null, why: row.why ?? null, next_step: row.next_step ?? null,
      sent_at: row.sent_at ?? null, ended_at: row.ended_at ?? null, max_calls: row.max_calls, warnings: row.warnings, steps: row.steps, criteria_total: row.criteria_total,
      reservation: row.reservation ?? null, restart_used: !!row.restart_used,
      busy: !!row.busy, can_retry: !!row.can_retry, eligible: !!row.eligible, retry_at: row.retry_at ?? null,
      busy_request_id: row.busy_request_id ?? null, busy_observed_at: row.busy_observed_at ?? null, capacity_until: row.capacity_until ?? null,
      engine_sha: row.engine_sha ?? null, criterion_texts: row.criterion_texts ?? {}, draft: !!row.draft })) };
}

// Claims are permanent and authoritative even if an older concurrent reader saves stale rows.
function claimPath(context, row, attempt = 0) {
  const key = createHash('sha256').update(row.test).digest('hex');
  return join(context.folder, `${key}.${attempt}.dispatch.json`);
}
function adoptClaims(context, row) {
  if (statOrNull(claimPath(context, row).replace(/\.0\.dispatch\.json$/, '.restart.json'))) row.restart_used = true;
  for (let attempt = 0; ; attempt++) {
    const path = claimPath(context, row, attempt);
    if (!statOrNull(path)) {
      // Older batches can have historical IDs from before row claims existed.
      if (attempt < row.request_ids.length) continue;
      break;
    }
    const claim = context.store.read(path);
    if (!UUID.test(claim?.id ?? '')) {
      row.dispatchIncomplete = true;
      break;
    }
    if (claim.restart) row.restart_used = true;
    if (claim.reservation && !row.admitting) row.reservation = claim.reservation;
    if (!row.request_ids.includes(claim.id)) {
      row.request_ids.push(claim.id);
      const unsent = context.unsentInterruptions?.get(row);
      Object.assign(row, { state: 'unknown', phase: 'server', calls: 'unknown', lost: true,
        note: unsent?.id === claim.id ? unsent.note : null, why: null, next_step: null, busy: false, can_retry: false });
    }
  }
}
function saveBatch(context) {
  if (!context.batch) return;
  for (const row of context.rows) {
    adoptClaims(context, row);
    const id = row.request_ids.at(-1), answer = id && context.store.read(join(context.folder, `${id}.json`));
    if (!row.busy && ['unknown', 'queued', 'running', 'sending'].includes(row.state) && answer && sameJob(answer, id, 'check')
      && ['passed', 'failed', 'refused'].includes(answer.state) && checkCapacity(answer) === null) applyAnswer(row, answer, context);
  }
  context.store.write(join(context.folder, 'batch.json'), batchRecord(context));
}
function saveAnswer(context, id, json) { if (isObject(json)) context.store.write(join(context.folder, `${id}.json`), json); }

async function postJob(context, path, command, request, row, timeoutMs, deadline = context.deadline) {
  const id = request.requestId;
  const target = row ?? context.lint;
  if (context.interrupted || context.stopped || context.sendError) { await finishReservation(context, target, { state: 'not_run' }); return { kind: 'not_sent' }; }
  const registered = await recordRuntimeRequest(target.reservation, id, slotPorts(context, deadline));
  if (registered === false) { await finishReservation(context, target, { state: 'not_run' }); return { kind: 'not_sent' }; }
  if (context.interrupted || context.stopped || context.sendError || context.ports.now() >= deadline) { await finishReservation(context, target, { state: 'not_run' }); return { kind: 'not_sent' }; }
  context.store.posted(context.folder, id);
  if (row) { if (!row.request_ids.includes(id)) row.request_ids.push(id); row.sent_at ??= context.ports.now(); row.state = 'sending'; row.phase = 'server'; row.calls = 'unknown'; row.post_verdict = 'uncertain'; }
  saveBatch(context);
  const reply = await context.runtime.post(path, request, context.capture.tar, timeoutMs);
  const verdict = judgePost(reply, id, command, context.secrets);
  verdict.observed_at = context.ports.now();
  if (row) row.post_verdict = verdict.kind;
  if (verdict.maintenance) maintenanceNotice(context, verdict, reply);
  if (verdict.answer) saveAnswer(context, id, verdict.answer);
  if (verdict.admission) context.store.write(join(context.folder, `${id}.admission.json`), verdict.admission);
  if (verdict.answer) { queueProgress(context, verdict.answer); await finishReservation(context, target, verdict.answer); }
  else if (['busy', 'not_run', 'stop', 'refused', 'not_sent'].includes(verdict.kind)) await finishReservation(context, target, { state: 'not_run' });
  return verdict;
}

// POST one check and fold the answer into its row.
async function sendCheck(context, row) {
  row.admitting = true;
  try { await sendCheckAttempt(context, row); } finally { row.admitting = false; }
}
async function sendCheckAttempt(context, row) {
  if (context.interrupted || context.ports.now() >= context.deadline || !['ready', 'waiting'].includes(row.state)) return;
  if (row.busy && row.request_ids.length && !await capacityReady(context, context.deadline, row)) return;
  const attempt = row.request_ids.length, previousCalls = row.restart_used || row.restart_pending ? accumulatedCalls(context, row) : 0;
  if (!await admission(context, 'check', row)) {
    if (context.interrupted && interruptedAdmissions.has(row)) Object.assign(row, { state: 'not_run', calls: previousCalls, phase: 'local', note: { code: null, message: 'Stopped before sending.' } });
    return;
  }
  adoptClaims(context, row);
  if (row.request_ids.length !== attempt || !['ready', 'waiting'].includes(row.state) || context.interrupted || context.ports.now() >= context.deadline) {
    await finishReservation(context, row, { state: 'not_run' });
    if (context.interrupted && row.request_ids.length === attempt && ['ready', 'waiting'].includes(row.state)) Object.assign(row, { state: 'not_run', calls: previousCalls, phase: 'local', note: { code: null, message: 'Stopped before sending.' } });
    return;
  }
  if (row.restart_pending) {
    const restartPath = claimPath(context, row).replace(/\.0\.dispatch\.json$/, '.restart.json');
    let claim;
    try { claim = openSync(restartPath, 'wx', 0o600); }
    catch (error) {
      await finishReservation(context, row, { state: 'not_run' });
      if (error.code !== 'EEXIST') throw error;
      row.restart_pending = false; adoptClaims(context, row); row.state = 'unknown'; return;
    }
    try { writeSync(claim, JSON.stringify({ used: true })); } finally { closeSync(claim); }
    row.restart_used = true; row.restart_pending = false;
    line(context.ports.stderr, 'The interpreter restarted during this check. pdd sends it again (1 of 1).');
  }
  // Acquire by original row and attempt, before allocating the UUID. Never remove a claim:
  // an interruption between claim and POST leaves dispatch uncertain, never replayable.
  const path = claimPath(context, row, attempt);
  let fd;
  try { fd = openSync(path, 'wx', 0o600); }
  catch (error) {
    if (error.code !== 'EEXIST') throw error;
    await finishReservation(context, row, { state: 'not_run' });
    adoptClaims(context, row);
    if (row.dispatchIncomplete) Object.assign(row, { state: 'unknown', phase: 'server', calls: 'unknown', final: true,
      why: 'An interrupted dispatch claim has no recoverable ID. No replacement check was sent.' });
    return;
  }
  let id;
  try { id = context.ports.randomUUID(); writeSync(fd, JSON.stringify({ id, reservation: row.reservation, restart: !!row.restart_used })); }
  finally { closeSync(fd); }
  if (context.interrupted || context.ports.now() >= context.deadline) {
    await finishReservation(context, row, { state: 'not_run' });
    adoptClaims(context, row);
    if (context.interrupted) row.note = { code: null, message: 'Stopped before sending.' };
    return;
  }
  row.attempts = (row.attempts ?? 0) + 1;
  row.sent_at = context.ports.now(); row.ended_at = null; row.retry_at = null; row.busy = false; row.can_retry = false;
  row.busy_request_id = null; row.busy_observed_at = null; row.capacity_until = null;
  row.phase = 'server';
  const request = { requestId: id, source_sha256: context.capture.sha256, scenario: row.test, max_calls: row.max_calls };
  const verdict = await postJob(context, '/v1/check', 'check', request, row, Math.max(1, Math.min(context.ports.postMs, context.deadline - context.ports.now())));
  if (verdict.kind === 'not_sent') {
    const note = { code: null, message: 'Stopped before sending.' };
    // Live knowledge owns this attempt's wording only; claim adoption still owns uncertainty.
    if (context.interrupted) (context.unsentInterruptions ??= new WeakMap()).set(row, { id, note });
    Object.assign(row, { state: 'not_run', calls: previousCalls, phase: 'local', note });
  }
  else if (verdict.kind === 'accepted') applyAnswer(row, verdict.answer, context, verdict.wait, verdict.observed_at);
  else if (verdict.kind === 'busy') markBusy(context, row, verdict.wait, verdict.observed_at);
  else if (verdict.kind === 'not_run') Object.assign(row, { state: 'not_run', note: verdict.note });
  else if (verdict.kind === 'stop') { Object.assign(row, { state: 'not_run', note: verdict.note }); context.stopped = verdict.note; if (verdict.blocked) context.blocked = verdict.note.message; }
  else if (verdict.kind === 'refused') Object.assign(row, { state: 'refused', refusals: [verdict.refusal] });
  // The agent's default limit caps this read too: pdd exits 3 and --read reads the same ID later.
  else Object.assign(row, { state: 'unknown', why: verdict.why, lost: true, read_until: context.agentLimit ? context.deadline
    : Math.max(Number.isFinite(context.deadline) ? context.deadline : 0, context.ports.now() + LOST_READ_MS) });
}

// GET one open row once.
async function readRow(context, row, deadline = Infinity) {
  const id = row.request_ids.at(-1), end = Math.min(deadline, row.lost ? row.read_until ?? context.deadline : context.deadline);
  if (!id) return;
  const verdict = judgeGet(await context.runtime.get(id, Math.max(1, Math.min(GET_MS, (end ?? Infinity) - context.ports.now()))), id, 'check');
  verdict.observed_at = context.ports.now();
  // A network problem while reading says so once; pdd keeps reading the same IDs.
  if (verdict.kind === 'again' && verdict.why && !context.readTrouble) line(context.ports.stderr, `pdd cannot read the results right now (${verdict.why}). It keeps trying.`);
  if (verdict.kind !== 'again') context.readTrouble = false; else if (verdict.why) context.readTrouble = true;
  if (verdict.kind === 'state') { saveAnswer(context, id, verdict.answer); queueProgress(context, verdict.answer); await finishReservation(context, row, verdict.answer); applyAnswer(row, verdict.answer, context, verdict.wait, verdict.observed_at); row.lost = false; }
  else if (verdict.kind === 'unknown') Object.assign(row, { state: 'unknown', why: verdict.why, lost: false, final: true });
  else if (verdict.kind === 'auth') context.readStop = AUTH_TEXT;
  else if (verdict.kind === 'blocked') context.readStop = verdict.message;
  else if (verdict.kind === 'gate') context.readStop = 'The runtime opens soon.';
}

const isOpen = row => OPEN_STATES.has(row.state) || (row.state === 'unknown' && row.lost);
const occupiesSlot = row => OPEN_STATES.has(row.state) || (row.state === 'unknown' && row.request_ids?.length);

// One line every 30 s while checks run.
function progressLine(rows, ms) {
  const stories = new Map();
  for (const row of rows) stories.set(row.story, (stories.get(row.story) ?? true) && ENDED.has(row.state) && !isOpen(row));
  const done = [...stories.values()].filter(Boolean).length, calls = rows.reduce((sum, row) => sum + (typeof row.calls === 'number' ? row.calls : 0), 0);
  return `Still running: ${done} of ${stories.size} ${stories.size === 1 ? 'Story' : 'Stories'} done · ${calls} AI call${calls === 1 ? '' : 's'} so far · `
    + `${ms < 60_000 ? `${Math.floor(ms / 1000)} s` : `${Math.floor(ms / 60_000)} min`}`;
}

function lintQueueWait(refusal) {
  if (!['lint-queue-timeout', 'lint-queue-full'].includes(refusal?.code) || refusal.details?.retryable !== true) return null;
  const seconds = refusal.details.retry_after;
  return (typeof seconds === 'number' && Number.isFinite(seconds) && seconds > 0 ? Math.min(300, Math.max(1, seconds)) : 5) * 1000;
}

function pendingLintMessage(context, answer) {
  return `Lint is still ${answer.state}. No checks were sent. ` + (context.batch
    ? `Read the result later with: pdd test --read ${context.batch}`
    : 'No Try was made. Lint uses no AI calls.');
}

// A wait's server state in plain words, for a progress tick.
const waitWord = (answer, read) => read?.kind === 'again' ? `waiting for an answer${read.why ? ` (${read.why})` : ''}`
  : answer?.state === 'queued' ? 'in line' : answer?.state === 'running' ? 'running' : 'waiting for an answer';

async function runLint(context, complete = false) {
  const agent = context.agentLimit ?? !context.ports.interactive;
  const lintEnd = context.batch ? context.deadline : Math.min(context.deadline, agent ? context.startedAt + AGENT_WAIT_MIN * 60_000 : Infinity);
  const tick = progressTicker(context.ports.stderr, context.ports.now);
  line(context.ports.stderr, `Checking ${context.capture.files.length} files (${formatSize(context.capture.bytes)}) on the PDD interpreter (lint, 0 AI calls)…`);
  let paused = false;
  const stopped = () => ({ kind: 'not_run', note: { code: null, message: paused ? stoppedPause(context, context.lint, 'lint')
    : `Stopped before sending.${context.waitCause === 'maintenance' ? ' pdd stopped while waiting for maintenance.' : ''}` } });
  const busy = () => context.interrupted && (paused || interruptedAdmissions.has(context.lint)) ? stopped()
    : ({ kind: 'not_run', note: { code: 'lint-busy', message: `Your wait ended while pdd waited for ${context.waitCause ?? 'server capacity'}. No checks ran. Run the same pdd command again later.` } });
  const pause = async (wait, maintenance = false) => {
    paused = true;
    context.waitCause = maintenance ? 'maintenance' : 'server capacity';
    if (context.interrupted || context.ports.now() >= lintEnd) return false;
    if (!maintenance) line(context.ports.stderr, 'The server is busy. Waiting for a lint slot…');
    return waitBudget(context, wait, lintEnd);
  };
  for (;;) {
    if (context.interrupted) return stopped();
    if (context.ports.now() >= lintEnd) return busy();
    paused = false;
    if (!await admission(context, 'lint', context.lint, lintEnd)) return busy();
    const request = { requestId: context.ports.randomUUID(), source_sha256: context.capture.sha256, ...(complete ? { complete: true } : {}) };
    context.lint.request_ids.push(request.requestId);
    const verdict = await postJob(context, '/v1/lint', 'lint', request, null, Math.max(1, Math.min(context.ports.postMs, lintEnd - context.ports.now())), lintEnd);
    if (verdict.kind === 'busy') { if (await pause(verdict.wait, verdict.maintenance)) continue; return busy(); }
    if (verdict.kind === 'not_sent') return context.interrupted ? stopped() : busy();
    if (verdict.blocked) throw new Stop(5, verdict.note.message);
    if (verdict.kind !== 'accepted' && verdict.kind !== 'unknown') return verdict;
    // Unknown dispatch still reads only this ID; only a confirmed terminal capacity refusal permits another attempt.
    const readEnd = lintEnd;
    let answer = verdict.answer ?? null, id = request.requestId, lost = false;
    while (!['passed', 'failed', 'refused', 'unknown'].includes(answer?.state) && context.ports.now() < readEnd && !context.interrupted) {
      await context.ports.sleep(Math.min(context.ports.pollMs, Math.max(0, readEnd - context.ports.now())), context.signal);
      if (context.interrupted || context.ports.now() >= readEnd) break;
      const read = judgeGet(await context.runtime.get(id, Math.max(1, Math.min(GET_MS, readEnd - context.ports.now()))), id, 'lint');
      if (read.kind === 'state') { answer = read.answer; saveAnswer(context, id, answer); queueProgress(context, answer); await finishReservation(context, context.lint, answer); }
      else if (read.kind === 'unknown') { lost = true; break; }
      else if (read.kind === 'blocked') throw new Stop(5, read.message);
      else if (read.kind === 'auth' || read.kind === 'gate') return { kind: 'stop', note: { code: null, message: read.kind === 'auth' ? AUTH_TEXT : 'The runtime opens soon.' } };
      if (!['passed', 'failed', 'refused', 'unknown'].includes(answer?.state)) tick(`Still checking the files: ${waitWord(answer, read)}`);
    }
    if (!lost && answer?.state === 'refused' && safeAdmission({ json: answer })) {
      const refusals = [answer.result?.report?.refusal, ...(Array.isArray(answer.result?.refusals) ? answer.result.refusals : [])];
      const wait = refusals.map(lintQueueWait).find(value => value !== null);
      if (wait !== undefined) { if (await pause(wait)) continue; return busy(); }
    }
    if (!lost && ['queued', 'running'].includes(answer?.state)) {
      Object.assign(context.lint, { state: answer.state, pending: true, unknown: false });
      saveBatch(context);
      return { kind: 'pending', answer };
    }
    return lost || !answer ? { kind: 'unknown' } : { kind: 'answer', answer };
  }
}

async function checkBatch(context, rows) {
  const { ports } = context, sendable = rows.filter(row => row.state === 'ready');
  const lint = await runLint(context);
  context.lint.state = lint.answer?.state ?? lint.kind;
  context.lint.unknown = false;
  const lintView = noVerdictAdvice(lint.answer, projectAnswer(lint.answer ?? {}, { origin: context.origin, secrets: context.secrets }));
  const notSent = (state, extra) => { for (const row of sendable) Object.assign(row, { state, calls: 0, phase: 'lint', why: lintView.why, next_step: lintView.next_step, ...extra }); };
  if (context.interrupted) { notSent('not_run', { note: lint.note ?? { code: null, message: 'Stopped before sending.' } }); return; }
  if (lint.kind === 'pending') {
    context.lintPending = true;
    notSent('not_run', { note: { code: 'lint-pending', message: pendingLintMessage(context, lint.answer) } });
    return;
  }
  if (lint.kind === 'not_run' || lint.kind === 'stop') { notSent('not_run', { note: lint.note, ...(lint.note?.code === 'lint-busy' ? { calls: 0, phase: 'lint' } : {}) }); return; }
  if (lint.kind === 'refused') { notSent('refused', { phase: 'lint', refusals: [lint.refusal] }); return; }
  const verdicts = lint.kind === 'answer' && ['passed', 'failed', 'refused'].includes(lint.answer.state) ? judgeLint(lint.answer, sendable, context.root, context.visible, context.secrets) : null;
  if (!verdicts) {
    const refusals = projectAnswer(lint.answer ?? {}, { origin: context.origin, secrets: context.secrets }).refusals;
    if (lint.answer?.state === 'refused' && refusals.length) { notSent('refused', { phase: 'lint', refusals }); return; }
    context.lintUnknown = context.lint.unknown = true;
    notSent('not_run', { note: { code: null, message: 'The lint result is unknown, so pdd sent no checks.' } });
    return;
  }
  for (const [row, problem] of verdicts) Object.assign(row, { state: 'refused', phase: 'lint', refusals: [problem], why: lintView.why, next_step: lintView.next_step });
  const toSend = sendable.filter(row => row.state === 'ready');
  line(ports.stderr, `${verdicts.size ? `Lint refused ${verdicts.size} of ${sendable.length} tests.` : 'Lint passed.'} Sent ${toSend.length} check${toSend.length === 1 ? '' : 's'} `
    + `at ${clock(ports.now())}: ${context.capture.files.length} files, ${formatSize(context.capture.bytes)}${context.otherNote ? ` ${context.otherNote}` : ''}.`);
  // Only now is there something to read again (lead, Oct 27): after lint passes, before the first check POST.
  if (toSend.length) line(ports.stderr, `If pdd stops, read the results with: pdd test --read ${context.batch}`);
  for (const row of toSend) row.eligible = true;
  await runScheduledChecks(context, rows, toSend);
}

async function runScheduledChecks(context, rows, toSend) {
  const { ports } = context;
  context.checkWindow ??= localLimit(context);
  for (const row of toSend) row.attempts = 0;
  const pendingSends = new Map(), uploads = uploadLimit(context);
  // Refill on a POST's settlement even while the polling loop awaits GETs.
  // Waiting rows stay outside admission and dispatch-claim allocation.
  const pumpSends = () => {
    if (context.interrupted || context.readStop || context.stopped || context.sendError || ports.now() >= context.deadline) return;
    const active = rows.filter(occupiesSlot).length;
    const available = Math.max(0, Math.min(uploads - pendingSends.size, context.checkWindow - active - pendingSends.size));
    const eligible = toSend.filter(row => !pendingSends.has(row) && ['ready', 'waiting'].includes(row.state)
      && (!row.retry_at || ports.now() >= row.retry_at));
    for (const row of eligible.slice(0, available)) {
      const pending = sendCheck(context, row).catch(error => { context.sendError ??= error; }).finally(() => {
        pendingSends.delete(row); pumpSends();
      });
      pendingSends.set(row, pending);
    }
  };
  let waitingShown = -1, shownAt = ports.now();
  const sentAt = shownAt;
  const readable = row => isOpen(row) && ports.now() < (row.lost ? row.read_until ?? context.deadline : context.deadline);
  try {
  while (!context.interrupted && !context.readStop) {
    // Never count an uncertain dispatched job as a free slot, even if it cannot currently be read.
    const active = rows.filter(occupiesSlot).length;
    if (!context.stopped && ports.now() < context.deadline && active < context.checkWindow) {
      pumpSends();
      // Admission can wait while previously dispatched rows continue to be read.
      if (!active && pendingSends.size) await Promise.race(pendingSends.values());
      else await new Promise(done => setImmediate(done));
      saveBatch(context);
    }
    if (context.blocked && !rows.some(isOpen)) throw new Stop(5, context.blocked);
    const waiting = toSend.filter(row => row.state === 'waiting');
    if (waiting.length !== waitingShown) {
      if (waiting.length) line(ports.stderr, `Server busy: ${rows.filter(isOpen).length} checks running, ${waiting.length} waiting for a free slot.`);
      waitingShown = waiting.length;
    }
    if (context.sendError) throw context.sendError;
    await recoverRestarts(context);
    const pending = toSend.some(row => ['ready', 'waiting'].includes(row.state));
    if (pending && active >= context.checkWindow && !rows.some(readable)) break;
    if ((!pending || context.stopped || ports.now() >= context.deadline) && !rows.some(readable) && !pendingSends.size) break;
    if (ports.now() - shownAt >= PROGRESS_MS) { shownAt = ports.now(); line(ports.stderr, progressLine(rows, shownAt - sentAt)); }
    const end = Math.max(context.deadline, ...rows.filter(row => row.lost).map(row => row.read_until ?? 0));
    await ports.sleep(Math.max(0, Math.min(ports.pollMs, end - ports.now())), context.signal);
    if (context.interrupted) break;
    await eachLimited(rows.filter(readable), MAX_READS, row => readRow(context, row));
    await recoverRestarts(context);
    for (const row of rows.filter(row => row.state === 'ready' && row.restart_used)) if (!toSend.includes(row)) toSend.push(row);
    saveBatch(context);
  }
  } catch (error) { context.sendError ??= error; throw error; }
  finally { await Promise.all(pendingSends.values()); }
  if (context.sendError) throw context.sendError;
  const stoppedEarly = context.interrupted || !!context.readStop;
  context.timedOut = !stoppedEarly && ports.now() >= context.deadline && rows.some(isOpen);
  for (const row of toSend) {
    if (['ready', 'waiting'].includes(row.state)) Object.assign(row, { state: 'not_run', calls: row.restart_used || row.restart_pending ? accumulatedCalls(context, row) : 0, busy: true, can_retry: true,
      phase: row.request_ids.length ? 'server' : 'local', note: { code: 'check-busy', message: context.interrupted && row.busy && row.request_ids.length
        ? stoppedPause(context, row, 'check') : row.request_ids.length
          ? 'The interpreter stayed busy. No checks ran for this attempt. Retry this batch later.' : 'Held locally; this check was not sent. Retry this batch later.' } });
    if (row.state === 'unknown' && row.lost) row.why ??= stoppedEarly ? 'pdd stopped before it could read this run.'
      : Number.isFinite(context.deadline) ? 'pdd could not read this run before the timeout.' : 'pdd could not read this run for 5 min after its answer was lost.';
  }
}

// The engine-build warning shows at most once a day for each engine sha (a stamp in the state folder).
function firstToday(context, sha) {
  if (!context.store) return true;
  const path = join(context.store.folder(), 'engine-warnings.json'), stamps = context.store.read(path) ?? {};
  const date = new Date(context.ports.now()), today = `${date.getFullYear()}-${String(date.getMonth() + 1).padStart(2, '0')}-${String(date.getDate()).padStart(2, '0')}`;
  if (stamps[sha] === today) return false;
  context.store.write(path, { ...stamps, [sha]: today });
  return true;
}

function printResult(context, rows, extra = {}) {
  rows = rows.map(row => heldForLint(row) && !row.dispatchIncomplete ? { ...row, calls: 0 } : row);
  const { ports } = context, exitCode = exitCodeFor(rows, { interrupted: context.interrupted, lintUnknown: context.lintUnknown || context.lintPending });
  const engines = [...new Set(rows.map(row => row.engine_sha).filter(sha => sha && !sameEngine(sha)))].filter(sha => firstToday(context, sha));
  const warnings = [...(context.warnings ?? []), ...engines.map(sha => `Warning: the interpreter engine is ${cleanText(sha).slice(0, 12)}, but pdd's local checks copy engine ${ENGINE_SHA.slice(0, 12)}. The engine stays the judge.`)];
  const summary = renderJson({ batch: context.batch ?? null, repo: context.root, sourceSha256: context.capture?.sha256 ?? null, coverage: context.coverage, rows, exitCode, summaryLine: summaryLine(rows),
    warnings: [...warnings, ...rows.flatMap(row => (row.warnings ?? []).map(text => `${row.test}: ${text}`))] });
  if (context.folder) context.store.write(join(context.folder, 'summary.json'), summary);
  if (context.batch && rows.some(row => row.can_retry)) line(ports.stderr, `Retry only unstarted checks with: pdd test --retry ${context.batch}`);
  if (context.readStop) line(ports.stderr, context.readStop);
  if (context.continuationNotice) line(ports.stderr, context.continuationNotice);
  if (context.stopped && !context.json) line(ports.stderr, context.stopped.message);
  const scrub = text => (context.secrets ?? []).reduce((value, secret) => secret ? value.split(secret).join('[secret]') : value, text);
  if (context.json) line(ports.stdout, scrub(JSON.stringify(summary)));
  else ports.stdout.write(scrub(renderText({ batch: context.batch, rows, coverage: context.coverage, warnings, details: context.details, timeoutMin: context.timeoutMin,
    interrupted: context.interrupted || !!context.readStop, reading: !!context.reading, exitCode, secrets: context.secrets, ...extra })));
  // At the time limit the jobs keep running on the server.
  if (exitCode === 3 && context.batch) line(ports.stderr, context.timedOut ? `Still running. Read the results later with: pdd test --read ${context.batch}`
    : `If pdd stops, read the results with: pdd test --read ${context.batch}`);
  return exitCode;
}

function runFiles(cwd, words, options, ports) {
  const { root, found, normalized } = localSetup(cwd, words);
  const selected = select(found, normalized, root), coverage = bindingCoverage({ root, found, selected });
  const tests = selected.map(test => test.path);
  const appMap = options['--app-map'] === undefined ? null : appMapFor(found, options['--app-map'], cwd, root, ports.stderr);
  const capture = ports.captureSource(root, { tests, appMap });
  for (const warning of capture.warnings ?? []) line(ports.stderr, warning);
  const other = otherFiles(capture.files, found), width = Math.max(0, ...capture.files.map(file => file.path.length));
  for (const file of capture.files) line(ports.stdout, `  ${file.path.padEnd(width)}  ${file.size} bytes`);
  line(ports.stdout, `${capture.files.length} files, ${formatSize(capture.bytes)} (${capture.bytes} bytes). ${other.length} of them are not prompt, story or test files.`);
  line(ports.stderr, coverageText(coverage));
  return 0;
}

// pdd lint: only the server's lint (0 AI calls) on the captured files.
// Locally the selected prompts' limits gate, SVG advice and privacy/capture checks run; other engine rules are the server's.
async function runLintOnly(context, cwd, words, options, setRelease) {
  const { ports } = context, origin = runtimeOrigin(ports.env), { root, found, normalized } = localSetup(cwd, words);
  const selected = select(found, normalized, root);
  context.coverage = bindingCoverage({ root, found, selected });
  const rows = selected.map(test => ({ test: test.path, story: test.story, title: test.title, state: 'ready', phase: 'lint',
    refusals: [], request_ids: [], warnings: [], steps: Array.isArray(test.doc?.steps) ? test.doc.steps.filter(isObject) : [],
    criterion_texts: Object.fromEntries((Array.isArray(test.doc?.criteria) ? test.doc.criteria : []).filter(isObject).map(item => [item.id, item.text])) }));
  const {readPrompt,interfaceSchemaProblems} = await import('./runtime-preflight.mjs');
  const prompts = new Map();
  const limitsFor = (path, seen) => {
    if (typeof path !== 'string' || seen.has(path)) return [];
    seen.add(path);
    if (!prompts.has(path)) prompts.set(path,readPrompt(root,found.visible,path));
    const prompt = prompts.get(path);
    if (!prompt.interface) return [];
    const own = interfaceSchemaProblems(prompt.interface).filter(problem =>
      ['invalid-limits','invalid-interface'].includes(problem.code) && problem.pointer.startsWith('/limits'))
      .map(problem => ({code:problem.code,section:problem.pointer,path,message:`${path} ${problem.pointer} ${problem.rule}`,hint:problem.hint}));
    return [...own,...(Array.isArray(prompt.interface.calls) ? prompt.interface.calls : []).flatMap(call => limitsFor(call?.target,seen))];
  };
  const limitRows = rows.map(row => {
    const seen = new Set();
    return {...row,refusals:row.steps.flatMap(step => limitsFor(step.entry_path,seen))};
  });
  if (limitRows.some(row => row.refusals.length)) {
    const refusedRows = limitRows.map(row => ({story:row.story,title:row.title,test:row.test,state:row.refusals.length ? 'refused' : 'not_run',refusals:row.refusals}));
    const problems = [];
    for (const problem of refusedRows.flatMap(row => row.refusals)) {
      if (!problems.some(item => item.code === problem.code && item.path === problem.path && item.section === problem.section)) problems.push(problem);
    }
    const summary = 'Lint refused local Runtime limits. 0 AI calls. No files were sent.';
    if (context.json) line(ports.stdout, JSON.stringify({batch:null,repo:root,exit_code:4,lint_state:'refused',summary_line:summary,
      coverage:context.coverage,problems,rows:refusedRows,warnings:found.warnings}));
    else {
      for (const problem of problems) {
        line(ports.stderr, `${problem.code}  ${problem.message}`);
        if (problem.hint) line(ports.stderr, problem.hint);
      }
      for (const row of refusedRows) line(ports.stdout, `  ${row.test}  ${row.state === 'refused' ? `refused: ${row.refusals.map(item => item.code).join(', ')}` : 'not run'}`);
      line(ports.stdout,summary);
      line(ports.stdout,coverageText(context.coverage));
    }
    return 4;
  }
  const capture = ports.captureSource(root, { tests: selected.map(test => test.path), appMap: null });
  const svgWarnings = lintSvgLayouts({ root, files: [...found.visible], promptPaths: capture.files.map(file => file.path).filter(path => path.endsWith('.prompt.md')) });
  const drift=[];
  try {
    const files=sourceFilePort(root,found.visible), sources=[];
    for (const path of [...found.visible].sort().filter(path=>path.startsWith('contracts/') && /\.(?:md|json)$/.test(path))) {
      try { sources.push({path,text:files.read({path}).content}); } catch { drift.push(`Warning: ${path}: contract catalog advice unavailable.`); }
    }
    const catalog=catalogRecords(sources,capture.references.map(ref=>ref.target));
    const compared=compareCopies(capture.files.filter(file=>file.path.endsWith('.prompt.md')).map(file=>({path:file.path,text:files.read({path:file.path}).content})),catalog.records);
    drift.push(...[...catalog.warnings,...compared.warnings].map(warning=>`Warning: ${warning}`));
    for (const match of compared.matches.filter(match=>match.kind==='near')) drift.push(`Warning: ${match.path} ${match.source_pointer}: copy of ${match.target} differs (${match.differences.join('; ')}). Use {"$contract":${JSON.stringify(match.target)}}.`);
  } catch { drift.push('Warning: contract catalog advice is unavailable.'); }
  context.warnings = [...svgWarnings, ...found.warnings,...drift,...(capture.warnings ?? [])];
  if (!context.json) for (const warning of [...svgWarnings,...drift,...(capture.warnings ?? [])]) line(ports.stderr, warning);
  const identity = signIn(ports.gh, context.store), startedAt = ports.now(), batch = batchId(startedAt, ports.randomUUID);
  const timeoutMin = options['--timeout'] !== undefined ? Number(options['--timeout']) : ports.interactive ? null : AGENT_WAIT_MIN;
  Object.assign(context, { origin, visible: found.visible, capture, identity, batch, startedAt, deadline: timeoutMin ? startedAt + timeoutMin * 60_000 : Infinity, rows, head: null,
    intent: 'lint-only', agentLimit: options['--timeout'] === undefined && !ports.interactive, secrets: [identity.token], lint: { request_ids: [], state: null }, timeoutMin });
  context.folder = context.store.folder('batches', batch);
  setRelease(interruptible(context));
  await ownBatch(context, batch);
  saveBatch(context);
  context.runtime = new Runtime({ origin, token: identity.token, ports, signal: context.signal });
  const lint = await runLint(context, true);
  if (lint.kind === 'pending') { Object.assign(context.lint, { state: lint.answer.state, pending: true });
    for (const row of rows) Object.assign(row, { state: 'not_run', calls: 0, phase: 'lint', note: { code: 'lint-pending', message: pendingLintMessage(context, lint.answer) } });
    saveBatch(context); throw new Stop(3, pendingLintMessage(context, lint.answer)); }
  if (lint.kind === 'not_run' && context.json) {
    for (const row of rows) Object.assign(row, { state: 'not_run', calls: 0, note: lint.note });
    saveBatch(context); line(ports.stderr, lint.note.message);
    line(ports.stdout, JSON.stringify({ batch, repo: root, exit_code: 5, lint_state: 'not_run', summary_line: `Lint did not run. 0 AI calls. No checks were sent.`, coverage: context.coverage, problems: [],
      rows: rows.map(row => ({ story: row.story, title: row.title, test: row.test, state: row.state, refusals: row.refusals })), warnings: context.warnings }));
    return 5;
  }
  if (lint.kind === 'not_run' || lint.kind === 'stop') throw new Stop(5, `${lint.note.message}${lint.note.code && lint.note.code !== 'blocked' ? ` (${lint.note.code})` : ''}`);
  const answer = lint.answer, program = answer?.result?.report?.program;
  const problems = lint.kind === 'refused' ? [{ ...lint.refusal, path: null }]
    : (answer?.state === 'refused' && !isObject(program) ? projectAnswer(answer, { origin, secrets: context.secrets }).refusals.map(item => ({ ...item, path: null })) : []);
  if (!problems.length && (context.interrupted || lint.kind === 'unknown' || !['passed', 'failed', 'refused'].includes(answer?.state) || !isObject(program))) {
    throw new Stop(3, 'The lint result is unknown. Run pdd lint again; a lint uses no AI calls.');
  }
  const canonical = Array.isArray(answer?.result?.problems) ? answer.result.problems : answer?.result?.report?.problems;
  for (const item of Array.isArray(canonical) ? canonical.filter(isObject) : []) {
    const reason = cleanText(item.reason, context.secrets), fix = cleanText(item.fix, context.secrets);
    problems.push({ code: cleanText(item.code, context.secrets) || 'lint-refused', path: cleanText(item.file ?? item.path, context.secrets) || null,
      section: cleanText(item.at ?? item.section, context.secrets) || null,
      message: cleanText(item.message, context.secrets) || [reason, fix].filter(Boolean).join(' ') || null, hint: null,
      severity: cleanText(item.severity, context.secrets) || 'error', pointer: cleanText(item.pointer, context.secrets) || null,
      source: cleanText(item.source, context.secrets) || null });
  }
  for (const item of isObject(program) && Array.isArray(program.refused_prompts) ? program.refused_prompts.filter(isObject) : []) {
    const problem = { code: cleanText(item.code, context.secrets) || 'lint-refused', path: cleanText(item.path, context.secrets) || null,
      section: cleanText(item.section, context.secrets) || null, message: cleanText(item.message, context.secrets) || null, hint: null };
    if (!problems.some(p => p.code === problem.code && p.path === problem.path && p.section === problem.section)) problems.push(problem);
  }
  const verdicts = isObject(program) ? judgeLint(answer, rows, root, found.visible, context.secrets) : new Map();
  for (const [row, problem] of verdicts) {
    Object.assign(row, { state: 'refused', refusals: [problem] });
    const path = /^(\S+?\.prompt\.md)\b/.exec(problem.message ?? '')?.[1] ?? null;
    if (!problems.some(item => item.code === problem.code && item.path === path)) problems.push({ ...problem, path, section: null });
  }
  if (lint.kind === 'refused' || (answer?.state === 'refused' && !isObject(program))) for (const row of rows) Object.assign(row, { state: 'refused', refusals: problems });
  for (const item of Array.isArray(answer?.result?.tests) ? answer.result.tests.filter(isObject) : []) {
    const row = rows.find(row => row.test === item.path);
    if (!row || item.verdict !== 'refused') continue;
    const own = problems.filter(p => p.path === row.test && p.severity !== 'warning');
    Object.assign(row, { state: 'refused', refusals: own.length ? own : row.refusals.length ? row.refusals
      : [{ code: 'lint-refused', section: 'lint', message: `${row.test} was refused by complete lint.` }] });
  }
  for (const row of rows) if (row.state === 'ready') row.state = 'passed';
  const passing = rows.filter(row => row.state === 'passed').length, exitCode = passing === rows.length ? 0 : 4;
  const summary = `Lint: ${passing} of ${rows.length} tests pass. 0 AI calls. No checks were sent.`;
  if (context.json) {
    line(ports.stdout, JSON.stringify({ batch, repo: root, exit_code: exitCode, lint_state: exitCode === 0 ? 'passed' : 'refused', summary_line: summary, coverage: context.coverage, problems,
      rows: rows.map(row => ({ story: row.story, title: row.title, test: row.test, state: row.state, refusals: row.refusals })), warnings: context.warnings }));
    return exitCode;
  }
  const out = [];
  if (problems.length) {
    out.push('Lint problems (from the PDD interpreter):');
    for (const item of problems) out.push(`  ${[item.code, item.path, item.section, item.message].filter(Boolean).join('  ')}`, ...(item.hint ? [`    ${item.hint}`] : []));
  }
  for (const row of rows) out.push(`  ${row.test}  ${row.state === 'passed' ? 'passes lint' : `refused: ${row.refusals.map(item => item.code).join(', ')}`}`);
  out.push(summary, coverageText(context.coverage), ...found.warnings);
  ports.stdout.write(`${out.join('\n')}\n`);
  return exitCode;
}

function runFillHash(root, ports) {
  const result = fillHashes({ root });
  for (const { message } of result.warnings) line(ports.stdout, `Warning: ${message}`);
  for (const { path } of result.filled) line(ports.stdout, `Filled prose_sha256: ${path}`);
  for (const { message } of result.refused) line(ports.stdout, `Refused: ${message}`);
  for (const { path } of result.stale) line(ports.stdout, `Stale: ${path} is approved, but ${STALE_HINT}.`);
  line(ports.stdout, `Hashes: ${result.filled.length} filled, ${result.current.length} current, ${result.refused.length} refused, ${result.stale.length} stale.`);
  return result.refused.length || result.stale.length ? 4 : 0;
}

function interruptible(context) {
  const controller = new AbortController();
  context.signal = controller.signal;
  return context.ports.onInterrupt(() => { context.interrupted = true; controller.abort(); });
}

async function readUnsentLint(context, rows) {
  const lint = context.lint, id = lint?.request_ids?.at(-1);
  if (!id) return;
  const unresolved = lint.pending || lint.unknown || [null, undefined, 'queued', 'running'].includes(lint.state);
  const held = rows.filter(row => !row.request_ids?.length && row.state === 'not_run' && (unresolved
    || ['lint-pending', 'lint-finished'].includes(row.note?.code) || /lint result is unknown/i.test(row.note?.message ?? '')));
  if (!held.length) return;
  let answer = context.store.read(join(context.folder, `${id}.json`));
  if (!sameJob(answer, id, 'lint') || !['passed', 'failed', 'refused'].includes(answer.state)) {
    const remaining = context.deadline - context.ports.now();
    if (context.interrupted || remaining <= 0) {
      context.lintPending = !!lint.pending;
      context.lintUnknown = !!lint.unknown || !context.lintPending;
      return;
    }
    const read = judgeGet(await context.runtime.get(id, Math.min(GET_MS, remaining)), id, 'lint');
    if (read.kind === 'blocked') throw new Stop(5, read.message);
    if (read.kind === 'auth') throw new Stop(5, AUTH_TEXT);
    if (read.kind === 'gate') throw new Stop(5, 'The runtime opens soon.');
    answer = read.kind === 'state' ? read.answer : null;
    if (answer) saveAnswer(context, id, answer);
  }
  if (answer) await finishReservation(context, lint, answer);
  const lintView = noVerdictAdvice(answer, projectAnswer(answer ?? {}, { origin: context.origin, secrets: context.secrets }));
  const unknown = () => {
    Object.assign(lint, { state: answer?.state ?? 'unknown', pending: false, unknown: true });
    context.lintUnknown = true;
    for (const row of held) Object.assign(row, { state: 'not_run', calls: 0, phase: 'lint', refusals: [], why: lintView.why, next_step: lintView.next_step,
      note: { code: null, message: 'The lint result is unknown, so pdd sent no checks.' } });
  };
  if (['queued', 'running'].includes(answer?.state)) {
    Object.assign(lint, { state: answer.state, pending: true, unknown: false });
    context.lintPending = true;
    for (const row of held) Object.assign(row, { state: 'not_run', calls: 0, phase: 'lint', refusals: [], why: lintView.why, next_step: lintView.next_step,
      note: { code: 'lint-pending', message: pendingLintMessage(context, answer) } });
    return;
  }
  if (!answer || answer.state === 'unknown') { unknown(); return; }
  const rawRefusals = [answer.result?.report?.refusal, ...(Array.isArray(answer.result?.refusals) ? answer.result.refusals : [])];
  const busy = answer.state === 'refused' && rawRefusals.some(item => lintQueueWait(item) !== null);
  const refusals = projectAnswer(answer, { origin: context.origin, secrets: context.secrets }).refusals;
  const verdicts = judgeLint(answer, held, context.root, context.visible, context.secrets);
  if (!busy && !verdicts && !(answer.state === 'refused' && refusals.length)) { unknown(); return; }
  Object.assign(lint, { state: answer.state, pending: false, unknown: false });
  for (const row of held) {
    const problem = verdicts?.get(row);
    Object.assign(row, { state: 'not_run', calls: 0, phase: 'lint', refusals: [], why: lintView.why, next_step: lintView.next_step, note: null });
    if (problem || (!verdicts && !busy && refusals.length)) {
      Object.assign(row, { state: 'refused', refusals: problem ? [problem] : refusals });
    } else {
      row.note = busy ? { code: 'lint-busy', message: 'The saved lint could not get a slot. No checks ran. Run the same command again later.' }
        : { code: 'lint-finished', message: `The saved lint finished${refusals.length ? ' with refusals' : ''}. This check was not sent. `
          + (refusals.length ? refusals.map(item => item.message || item.code).join(' ') + ' ' : '')
          + 'Run a fresh pdd test command to start checks.' };
    }
  }
}

function heldForLint(row) {
  return !row.request_ids?.length && row.state === 'not_run' && !row.busy && !row.can_retry
    && (row.note?.code === 'lint-pending'
      || /lint result is unknown.*sent no checks/i.test(row.note?.message ?? '')
      || row.phase === 'lint' && row.note?.code === 'lint-finished');
}
function validSavedCallCeiling(row) {
  return Number.isInteger(row.max_calls) && row.max_calls >= 1 && row.max_calls <= 1000;
}
function validSavedCheck(row) {
  const text = value => typeof value === 'string' && !!value.trim();
  if (!validSavedCallCeiling(row)
    || !Number.isInteger(row.criteria_total) || row.criteria_total <= 0
    || !Array.isArray(row.steps) || !row.steps.length) return false;
  const ids = new Set(), criteria = new Set();
  for (const step of row.steps) {
    if (!isObject(step) || !text(step.step_id) || ids.has(step.step_id) || !text(step.entry_path) || !text(step.operation)
      || !Array.isArray(step.checks) || !step.checks.length) return false;
    ids.add(step.step_id);
    for (const check of step.checks) {
      if (!isObject(check) || !text(check.criterion_id)) return false;
      criteria.add(check.criterion_id);
    }
  }
  return criteria.size === row.criteria_total;
}

async function continueHeld(context, candidates, saved) {
  if (!candidates.length || context.interrupted || context.ports.now() >= context.deadline) return;
  if (saved.intent === 'lint-only') return;
  candidates = candidates.filter(row => !row.request_ids.length && !row.dispatchIncomplete);
  if (!candidates.length) return;
  if (saved.version !== 1 || (saved.intent !== undefined && saved.intent !== 'check')
    || !candidates.every(validSavedCallCeiling)
    || (saved.intent === undefined && !candidates.every(validSavedCheck))
    || candidates.some(row => Object.hasOwn(row, 'calls') && row.calls !== 0)) {
    context.continuationNotice = 'No checks were sent for the lint-held rows: the saved batch lacks valid original call ceilings, unambiguous Check intent or zero-call lint-held proof. Start a fresh selected pdd test.';
    return;
  }
  if (context.lintPending || context.lintUnknown) return;
  const lintId = context.lint?.request_ids?.at(-1), lint = lintId && context.store.read(join(context.folder, `${lintId}.json`));
  if (!sameJob(lint, lintId, 'lint') || lint.state !== 'passed') return;
  const globalRefusals = projectAnswer(lint, { origin: context.origin, secrets: context.secrets }).refusals;
  const verdicts = judgeLint(lint, candidates, context.root, context.visible, context.secrets);
  if (!verdicts || verdicts.size || globalRefusals.length) return;
  let capture;
  try { capture = context.ports.captureSource(context.root, { tests: saved.rows.map(row => row.test), appMap: null }); }
  catch (error) {
    if (!(error instanceof PreflightError)) throw error;
    context.continuationNotice = `No checks were sent for the lint-held rows: the saved source cannot be verified. ${error.message}`;
    return;
  }
  if (capture.sha256 !== saved.source_sha256) { context.continuationNotice = 'No checks were sent for the lint-held rows: the saved source no longer matches: source changed. Start a fresh selected pdd test instead.'; return; }
  capture.stories = context.capture.stories;
  if (context.interrupted || context.ports.now() >= context.deadline) return;
  Object.assign(context, { capture, reading: false });
  const selected = candidates.filter(row => !row.request_ids.length && !row.dispatchIncomplete);
  for (const row of selected) Object.assign(row, { state: 'ready', eligible: true, note: null });
  if (selected.length) await runScheduledChecks(context, context.rows, selected);
}

async function runRead(context, batchWord, quiet = false, options = {}) {
  const { store, ports, root } = context;
  const timeout = options['--timeout'] === undefined ? AGENT_WAIT_MIN : Number(options['--timeout']);
  context.deadline ??= ports.now() + timeout * 60_000;
  context.timeoutMin = timeout; context.agentLimit = true;
  const name = batchWord ?? store.repo(root).last_batch;
  if (!name || !BATCH.test(name)) throw new Stop(2, name ? 'BATCH looks like 20261027-092747-k3f9.' : 'No saved check for this repository. Run pdd test first.');
  context.folder = join(store.dir, 'batches', name);
  if (!statOrNull(join(context.folder, 'batch.json'))) throw new Stop(2, `No saved batch ${name}.`);
  await ownBatch(context, name);
  const saved = store.read(join(context.folder, 'batch.json'));
  if (!saved) throw new Stop(2, `No saved batch ${name}.`);
  if (saved.root !== root) throw new Stop(2, 'This saved batch belongs to a different repository.');
  const identity = signIn(ports.gh, context.store);
  if (identity.login !== saved.login) throw new Stop(5, `These runs belong to ${saved.login}. Run: gh auth switch -u ${saved.login}`);
  Object.assign(context, { batch: name, origin: saved.origin, coverage: saved.coverage, identity, intent: saved.intent, secrets: [identity.token], warnings: saved.warnings ?? [],
    capture: { sha256: saved.source_sha256, files: saved.files.map(path => ({ path })), bytes: saved.bytes, stories:saved.contract_snapshots }, lint: saved.lint, head: saved.head, startedAt: Date.parse(saved.created_at) });
  runtimeOrigin({ PDD_RUNTIME_URL: saved.origin });
  context.runtime = new Runtime({ origin: saved.origin, token: identity.token, ports, signal: context.signal });
  const rows = saved.rows.map(row => ({ ...row, why: ['refused', 'not_run', 'unknown'].includes(row.state) && row.why === 'Checks failed.' ? null : row.why, ...(row.request_ids?.length ? { calls: 'unknown' } : {}), request_ids: [...(row.request_ids ?? [])], checks: null, failed_checks: [], all_checks: [] }));
  const candidates = rows.filter(row => heldForLint(row));
  // Preserve the producer's original evidence before refresh can normalize unsent usage.
  const evidence = candidates.map(row => ({ row, hadCalls: Object.hasOwn(row, 'calls'), calls: row.calls }));
  for (const row of rows) adoptClaims(context, row);
  Object.assign(context, { rows, visible: findTests({ root }).visible, reading: true });
  // A pdd that was killed can leave rows that never got an answer: read them if they were posted.
  for (const row of rows) if (['ready', 'sending', 'waiting'].includes(row.state)) {
    if (row.request_ids.length) row.state = 'unknown';
    else Object.assign(row, { state: 'not_run', calls: 0, phase: 'local', note: { code: null, message: 'pdd stopped before sending this check.' } });
  }
  // A final POST refusal has no run receipt. Legacy rows retain their final verdict,
  // but stale busy flags are not evidence that an allocated ID was unstarted.
  const finalPost = (row, answer) => !answer && (['refused', 'not_run', 'stop'].includes(row.post_verdict)
    || (!row.post_verdict && (row.state === 'refused' || (row.state === 'not_run' && !row.busy && !row.can_retry))));
  await readUnsentLint(context, rows);
  for (const item of evidence) {
    if (item.row.request_ids.length || item.row.dispatchIncomplete) item.row.calls = 'unknown';
    else if (item.hadCalls) item.row.calls = item.calls;
    else delete item.row.calls;
  }
  for (const row of rows.filter(row => row.dispatchIncomplete)) Object.assign(row, { state: 'unknown', phase: 'server', calls: 'unknown', final: true,
    why: 'An interrupted dispatch claim has no recoverable ID. No replacement check was sent.' });
  await continueHeld(context, candidates, saved);
  await eachLimited(rows, MAX_READS, async row => {
    const id = row.request_ids.at(-1);
    if (!id) return;
    row.phase = 'server';
    const admission = store.read(join(context.folder, `${id}.admission.json`));
    if (admission?.dispatch === 'not_started') {
      const wait = capacityDelay(admission.error);
      if (wait !== null) { markBusy(context, row, wait); return; }
    }
    const answer = store.read(join(context.folder, `${id}.json`));
    // Local terminal receipts remain available even when another row used the network wait.
    if (answer && confirmedEnd(answer) && sameJob(answer, id, 'check')) { await finishReservation(context, row, answer); applyAnswer(row, answer, context); return; }
    if (finalPost(row, answer)) return;
    if (row.final && (ports.now() >= (context.deadline ?? Infinity) || context.interrupted)) return;
    // A verified open receipt stays open when another row consumed this wait.
    if ((ports.now() >= (context.deadline ?? Infinity) || context.interrupted)
      && answer && sameJob(answer, id, 'check') && ['queued', 'running'].includes(answer.state)) { applyAnswer(row, answer, context); return; }
    // Polling an open cache is not evidence that its saved advice came from a lost read.
    if (!row.lost && (row.state !== 'unknown' || row.lost === false)) row.why = null;
    Object.assign(row, { state: 'unknown', calls: 'unknown', checks: null, criteria: null, failed_checks: [], all_checks: [], busy: false, can_retry: false, note: null, lost: true });
    if (ports.now() >= (context.deadline ?? Infinity) || context.interrupted) return;
    if (!quiet) line(ports.stderr, 'Reading 1 result from the PDD interpreter…');
    await readRow(context, row, context.deadline);
    if (row.state === 'unknown' && row.lost) row.why ??= 'pdd could not read this run yet.';
  });
  const replacements = await recoverRestarts(context);
  if (replacements.length) await runScheduledChecks(context, rows, replacements);
  saveBatch(context);
  return quiet ? rows : printResult(context, rows);
}

async function recoverRestarts(context) {
  const eligible = context.rows.filter(row => {
    adoptClaims(context, row);
    const id = row.request_ids.at(-1), answer = id && context.store.read(join(context.folder, `${id}.json`));
    return !row.restart_used && !row.restart_pending && !row.admitting && !context.restartDecisions?.has(id) && sameJob(answer, id, 'check') && restarted(answer);
  });
  if (!eligible.length || context.interrupted || context.ports.now() >= context.deadline) return [];
  context.restartDecisions ??= new Set();
  for (const row of eligible) context.restartDecisions.add(row.request_ids.at(-1));
  const capture = context.ports.captureSource(context.root, { tests: context.rows.map(row => row.test), appMap: null });
  if (capture.sha256 !== context.capture.sha256) { context.continuationNotice = 'The saved source changed; no restarted check was sent again.'; return []; }
  capture.stories = context.capture.stories;
  context.capture = capture;
  const selected = [];
  for (const row of eligible) {
    if (context.interrupted || context.ports.now() >= context.deadline || !validSavedCheck(row)) continue;
    Object.assign(row, { state: 'ready', lost: false, final: false, eligible: true, retry_at: null, restart_pending: true });
    selected.push(row);
  }
  if (selected.length) context.reading = false;
  return selected;
}

async function runRetry(context, name, options) {
  const { ports } = context;
  const timeout = options['--timeout'] === undefined ? AGENT_WAIT_MIN : Number(options['--timeout']);
  context.deadline = ports.now() + timeout * 60_000;
  const rows = await runRead(context, name, true, options);
  if (context.interrupted || ports.now() >= context.deadline) return printResult(context, rows);
  const capture = context.ports.captureSource(context.root, { tests: rows.map(row => row.test), appMap: null });
  if (capture.sha256 !== context.capture.sha256) throw new Stop(2, 'The saved source no longer matches: source changed. Start a fresh selected pdd test instead.');
  capture.stories = context.capture.stories;
  const lintId = context.lint?.request_ids?.at(-1), lint = lintId && context.store.read(join(context.folder, `${lintId}.json`));
  if (!lint || !sameJob(lint, lintId, 'lint') || lint.state !== 'passed' || context.lint.unknown || context.lint.pending)
    throw new Stop(2, 'The saved lint cannot authorize recovery. Start a fresh selected pdd test.');
  const selected = rows.filter(row => row.can_retry && row.eligible && (row.busy || !row.request_ids.length));
  Object.assign(context, { capture, reading: false, timeoutMin: timeout });
  for (const row of selected) row.state = row.retry_at > ports.now() ? 'waiting' : 'ready';
  if (selected.length) line(ports.stderr, `Retrying ${selected.length} unstarted check${selected.length === 1 ? '' : 's'}…`);
  await runScheduledChecks(context, rows, selected);
  saveBatch(context);
  return printResult(context, rows);
}

async function runRequest(context, id) {
  if (!UUID.test(id)) throw new Stop(2, 'The request ID must be a UUID.');
  const { ports } = context, identity = signIn(ports.gh, context.store), origin = runtimeOrigin(ports.env);
  Object.assign(context, { origin, secrets: [identity.token] });
  const runtime = new Runtime({ origin, token: identity.token, ports, signal: context.signal });
  const row = { test: '-', story: '-', title: '-', phase: 'server', request_ids: [id], state: 'unknown', refusals: [], warnings: [] };
  const read = judgeGet(await runtime.get(id), id, 'check');
  if (read.kind === 'state') applyAnswer(row, read.answer, context);
  else row.why = read.unreachable ?? read.why ?? (read.kind === 'auth' ? AUTH_TEXT : 'pdd could not read this run.');
  return printResult(context, [row], { recovery: `pdd test --request '${id}'` });
}

// Refresh only caches owned by this exact repository, runtime and signed-in account.
function refreshCheckBatches(context, identity, origin, id, answer) {
  const { store, root } = context, batches = join(store.dir, 'batches');
  let names;
  try { names = readdirSync(batches); } catch { return; }
  for (const name of names.filter(name => BATCH.test(name))) {
    try {
      const folder = join(batches, name), saved = store.read(join(folder, 'batch.json'));
      if (!saved || saved.root !== root || saved.origin !== origin || saved.login !== identity.login
        || String(saved.user_id) !== String(identity.userId)) continue;
      if (!saved.rows?.some(row => row.request_ids?.includes(id))) continue;
      const cached = store.read(join(folder, `${id}.json`));
      if (sameJob(cached, id, 'check') && ['passed', 'failed', 'refused'].includes(cached.state)
        && !['passed', 'failed', 'refused'].includes(answer.state)) continue;
      store.write(join(folder, `${id}.json`), answer);
    } catch { /* A cache failure must not hide an authoritative read or other caches. */ }
  }
}

// A read is observation only; it does not replay the call or settle backend accounting.
async function runCallRead(context, id) {
  const { ports, store } = context;
  const saved = store.read(join(store.dir, 'calls', `${id}.meta.json`));
  const identity = signIn(ports.gh, store);
  if (saved && identity.login !== saved.login) throw new Stop(5, `These runs belong to ${saved.login}. Run: gh auth switch -u ${saved.login}`);
  const origin = runtimeOrigin(saved ? { PDD_RUNTIME_URL: saved.origin } : ports.env);
  const runtime = new Runtime({ origin, token: identity.token, ports, signal: context.signal });
  const reply = await runtime.get(id), blocked = blockingAnswer(reply);
  if (blocked) throw new Stop(5, blocked);
  const command = ['call', 'check'].includes(reply.json?.command) ? reply.json.command : null;
  const verified = [200, 202].includes(reply.status) && command && sameJob(reply.json, id, command)
    && !(saved?.session_id && reply.json.session_id && saved.session_id !== reply.json.session_id);
  const answer = verified && !(command === 'call' && reply.json.state === 'passed' && !isObject(reply.json.result?.program_result)) ? reply.json : null;
  if (answer?.command === 'check') {
    Object.assign(context, { origin, secrets: [identity.token] });
    const row = { test: '-', story: '-', title: '-', phase: 'server', request_ids: [id], state: 'unknown', refusals: [], warnings: [] };
    applyAnswer(row, answer, context);
    refreshCheckBatches(context, identity, origin, id, answer);
    return printResult(context, [row], { recovery: `pdd test --read ${id}` });
  }
  const state = answer?.state ?? 'unknown', exitCode = exitCodeFor([{ state }]);
  const sanitize = value => typeof value === 'string' ? value.split(identity.token).join('[secret]').replace(/\x1b\[[0-9;?]*[ -/]*[@-~]/g, '').replace(/[\x00-\x08\x0b\x0c\x0e-\x1f\x7f-\x9f]/g, '').replace(/\b(?:gh[pousr]_[A-Za-z0-9_]+|github_pat_[A-Za-z0-9_]+|sk-[A-Za-z0-9_-]{12,})\b/g, '[secret]')
    : Array.isArray(value) ? value.map(sanitize) : isObject(value) ? Object.fromEntries(Object.entries(value).map(([k, v]) => [sanitize(k), sanitize(v)])) : value;
  const out = sanitize({ request_id: id, command: 'call', state, exit_code: exitCode,
    calls: answer?.usage?.calls ?? 'unknown', usage: answer?.usage ?? null,
    program_result: answer?.result?.program_result ?? null, result: answer?.result ?? null,
    report_url: answer?.report_url ? validLink(answer.report_url, origin, 'report') : null,
    why: answer ? answer.why ?? null : reply.status === 401 ? AUTH_TEXT : reply.status === 410 ? 'The result expired.' : 'The call receipt could not be verified.' });
  if (answer) store.write(join(store.folder('calls'), `${id}.json`), answer);
  if (context.json) line(ports.stdout, JSON.stringify(out));
  else {
    line(ports.stdout, `Call ${id}: ${state} · ${out.calls} AI calls`);
    if (out.program_result !== null) {
      const { stdout, stderr, ...fields } = out.program_result;
      if (typeof stdout === 'string') { line(ports.stdout, 'stdout:'); ports.stdout.write(stdout); if (!stdout.endsWith('\n')) line(ports.stdout, ''); }
      if (typeof stderr === 'string') { line(ports.stdout, 'stderr:'); ports.stdout.write(stderr); if (!stderr.endsWith('\n')) line(ports.stdout, ''); }
      line(ports.stdout, JSON.stringify({ ...fields, ...(typeof stdout !== 'string' && stdout !== undefined ? { stdout } : {}), ...(typeof stderr !== 'string' && stderr !== undefined ? { stderr } : {}) }, null, 2));
    }
    if (out.usage) line(ports.stdout, `Usage: ${JSON.stringify(out.usage)}`);
    if (out.report_url) line(ports.stdout, out.report_url);
    if (out.why) line(ports.stdout, out.why);
  }
  if (exitCode === 3) line(ports.stderr, `Read the result later with: pdd test --read ${id}`);
  return exitCode;
}

// pdd test. Returns the exit code.
export async function runCheck({ words = [], options = {}, cwd = process.cwd() } = {}, givenPorts = {}) {
  const ports = withDefaults(givenPorts);
  const context = { ports, json: options['--json'] === true, details: options['--details'] === true, interrupted: false, warnings: [] };
  let release = () => {};
  try {
    // Local modes dispatch before repository runtime state, origin or sign-in.
    if (options['--screen'] !== undefined || options['--drawing'] !== undefined) {
      if (!options['--screen'] || !options['--drawing'] || words.length || Object.keys(options).some(name => !['--screen', '--drawing', '--json'].includes(name))) throw new Stop(2, 'Use pdd test --screen URL --drawing PATH [--json], without other options or Stories.');
      try {
        const report = await compareScreen({ url: options['--screen'], drawingPath: options['--drawing'], cwd, chromePath: ports.env.PDD_CHROME_PATH }, { env: ports.env, browser: givenPorts.screenBrowser });
        const exitCode = report.passed ? 0 : 1;
        line(ports.stdout, context.json ? JSON.stringify({ ...report, exit_code: exitCode }) : formatScreenComparison(report));
        return exitCode;
      } catch (error) { throw new Stop(error.exitCode === 2 ? 2 : 5, `Screen comparison: ${causeText(error.message) || 'browser execution failed'}`); }
    }
    if (options['--local'] !== undefined) {
      if (options['--local'] !== true || options['--lint'] !== true || Object.keys(options).some(name => !['--lint', '--local', '--json'].includes(name))) throw new Stop(2, '--local requires --lint and accepts only Story words and --json.');
      try {
        const root = repoRoot(cwd), files = gitFiles(root);
        let promptPaths;
        if (words.length) {
          const { found, normalized } = localSetup(cwd, words), selected = select(found, normalized, root);
          promptPaths = ports.captureSource(root, { tests: selected.map(test => test.path), appMap: null }).files.map(file => file.path).filter(path => path.endsWith('.prompt.md'));
        }
        const warnings = lintSvgLayouts({ root, files, promptPaths }), summary = `SVG layout lint: ${warnings.length} warnings. 0 AI calls. No checks were sent.`;
        line(ports.stdout, context.json ? JSON.stringify({ repo: root, exit_code: 0, warnings, summary_line: summary }) : [...warnings, summary].join('\n'));
        return 0;
      } catch (error) { throw new Stop(2, error.message); }
    }
    requestedCalls(options['--max-calls']);
    const modes = ['--read', '--retry', '--fill-hash', '--files', '--request', '--lint'].filter(name => options[name] !== undefined);
    const others = Object.keys(options).filter(name => !modes.includes(name) && !(modes[0] === '--retry' && ['--json', '--details', '--timeout'].includes(name)) && !(name === '--json' && ['--read', '--request', '--lint'].includes(modes[0])) && !(name === '--timeout' && ['--read', '--lint'].includes(modes[0])) && !(name === '--app-map' && modes[0] === '--files'));
    if (modes.length > 1 || (modes.length && others.length) || (['--fill-hash', '--request', '--retry'].includes(modes[0]) && words.length)
      || (modes[0] === '--read' && words.length > 1) || (!modes.length && options['--app-map'] !== undefined)) throw new Stop(2, 'This mix of options does not work together. Run pdd test --help.');
    if (modes[0] === '--request') { release = interruptible(context); return await runRequest(context, options['--request']); }
    const root = repoRoot(cwd);
    if (modes[0] === '--fill-hash') return runFillHash(root, ports);
    if (modes[0] === '--files') return runFiles(cwd, words, options, ports);
    context.root = root; context.store = stateFor(ports.env, root);
    if (modes[0] === '--retry') { release = interruptible(context); return await runRetry(context, options['--retry'], options); }
    if (modes[0] === '--read') { release = interruptible(context); return UUID.test(words[0] ?? '') ? await runCallRead(context, words[0]) : await runRead(context, words[0], false, options); }
    if (modes[0] === '--lint') return await runLintOnly(context, cwd, words, options, value => { release = value; });
    return await runBatch(context, cwd, words, options, value => { release = value; });
  } catch (error) {
    if (error instanceof Stop || error instanceof PreflightError) {
      line(ports.stderr, error.message);
      if (context.json && error.bindingInventory) line(ports.stdout, JSON.stringify({ batch: null, repo: context.root, exit_code: 4, lint_state: 'refused',
        coverage: { available: false, bound: null, total: null, modules: [] }, problems: [{ code: 'binding-invalid', path: 'pdd-bindings.json', message: error.message }], rows: [], warnings: [] }));
      else if (context.coverage && error.exitCode !== 5) {
        if (context.json) line(ports.stdout, JSON.stringify({ batch: context.batch ?? null, repo: context.root, exit_code: error.exitCode,
          coverage: context.coverage, lint_state: error.exitCode === 3 ? 'unknown' : 'not_run', problems: [], rows: [], warnings: context.warnings, message: error.message }));
        else line(ports.stdout, coverageText(context.coverage));
      }
      return error.exitCode;
    }
    throw error;
  } finally {
    try { context.releaseBatch?.(); }
    catch (error) {
      try { line(ports.stderr, `Warning: could not release batch ${context.lockedBatch ?? context.batch ?? 'ownership'} (${cleanText(error.code ?? 'state error')}).`); } catch { /* preserve the command outcome */ }
    } finally { release(); await Promise.all([...(context.reservations ?? [])].map(reservation => releaseRuntimeSlot(reservation, { ended: false }, slotPorts(context)))); }
  }
}

async function runBatch(context, cwd, words, options, setRelease) {
  const { ports } = context;
  const origin = runtimeOrigin(ports.env);
  const { root, found, normalized } = localSetup(cwd, words);
  context.visible = found.visible; context.origin = origin;
  // A person has no time limit; an agent has 90 s; --timeout MIN overrides both.
  context.agentLimit = options['--timeout'] === undefined && !ports.interactive;
  context.timeoutMin = options['--timeout'] !== undefined ? Number(options['--timeout']) : context.agentLimit ? AGENT_WAIT_MIN : null;
  const selected = select(found, normalized, root);
  context.coverage = bindingCoverage({ root, found, selected });
  const checked = preflight({ root, found, selected });
  const rows = localRows(checked.rows);
  for (const row of rows) {
    const test = selected.find(item => item.path === row.test);
    row.story_path = test?.storyPath;
    row.criterion_texts = Object.fromEntries((Array.isArray(test?.doc?.criteria) ? test.doc.criteria : []).filter(isObject).map(item => [item.id, item.text]));
  }
  if (options['--max-calls'] !== undefined) for (const row of rows) row.max_calls = Number(options['--max-calls']);
  context.warnings = [...found.warnings, ...checked.warnings, ...sharedSourceFiles(root, found.visible)];
  if (!rows.some(row => row.state === 'ready')) return printResult(context, rows);
  if (!words.length) line(ports.stderr, costLine(rows.filter(row => row.state === 'ready'), root, found.visible));
  const capture = ports.captureSource(root, { tests: selected.map(test => test.path), appMap: null });
  context.warnings.push(...(capture.warnings ?? []));
  context.otherNote = otherNote(otherFiles(capture.files, found).length);
  const identity = signIn(ports.gh, context.store);
  const startedAt = ports.now(), batch = batchId(startedAt, ports.randomUUID);
  const head = spawnSync('git', ['rev-parse', 'HEAD'], { cwd: root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  Object.assign(context, { capture, identity, batch, startedAt, deadline: context.timeoutMin ? startedAt + context.timeoutMin * 60_000 : Infinity, rows,
    intent: 'check', head: head.status === 0 ? head.stdout.trim() : null, secrets: [identity.token], lint: { request_ids: [], state: null } });
  context.folder = context.store.folder('batches', batch);
  setRelease(interruptible(context));
  await ownBatch(context, batch);
  saveBatch(context);
  const repoState = context.store.repo(root);
  context.store.saveRepo(root, { ...repoState, last_batch: batch });
  context.runtime = new Runtime({ origin, token: identity.token, ports, signal: context.signal });
  await checkBatch(context, rows);
  saveBatch(context);
  return printResult(context, rows);
}

// ---- pdd simulate ----

// The app map for the Screen tab: --app-map, else app-map.json at the root, else app/app-map.json.
// An app map is a Git-visible JSON object with schema_version prompt-runtime.app-map.v1 and a name (the engine's first checks).
const APP_MAP_VERSION = 'prompt-runtime.app-map.v1';
function appMapProblem(root, path) {
  let doc;
  try { doc = JSON.parse(readFileSync(join(root, path), 'utf8')); } catch { return 'it is not JSON'; }
  if (!isObject(doc) || doc.schema_version !== APP_MAP_VERSION) return `its schema_version is not "${APP_MAP_VERSION}"`;
  if (typeof doc.name !== 'string' || !doc.name) return 'it has no "name"';
  return null;
}

function appMapFor(found, given, cwd, root, stderr) {
  if (given === undefined) {
    const path = ['app-map.json', 'app/app-map.json'].find(candidate => found.visible.has(candidate));
    const problem = path ? appMapProblem(root, path) : null;
    if (problem) line(stderr, `${path} is not an app map (${problem}), so pdd sends no app map.`);
    return path && !problem ? path : null;
  }
  const rel = relative(realpathSync(root), resolve(realpathSync(cwd), given)).split(sep).join('/');
  if (!found.visible.has(rel)) throw new Stop(2, `--app-map ${cleanText(given)} is not a Git-visible file in this repository.`);
  const problem = appMapProblem(root, rel);
  if (problem) throw new Stop(2, `--app-map ${cleanText(given)} is not an app map: ${problem}. An app map is a JSON file with "schema_version": "${APP_MAP_VERSION}". See RUNBOOK.md §13.`);
  return rel;
}

function oneTest(found, words, root) {
  const selected = select(found, words, root);
  if (selected.length !== 1) throw new Stop(2, ['pdd simulate needs one story. Choose one:', ...storyList({ tests: selected })].join('\n'));
  return selected[0];
}

async function readUntil(context, id, command, isDone, ms, label) {
  const end = Math.min(context.deadline ?? Infinity, context.ports.now() + ms), tick = progressTicker(context.ports.stderr, context.ports.now);
  let last = null;
  for (;;) {
    if (context.interrupted || context.ports.now() >= end) return { answer: last, open: true };
    const read = judgeGet(await context.runtime.get(id, Math.max(1, Math.min(GET_MS, end - context.ports.now()))), id, command);
    if (read.kind === 'state') { last = read.answer; queueProgress(context, last); context.store.write(join(context.store.folder('tries'), `${id}.json`), last); if (isDone(last)) return { answer: last }; }
    else if (read.kind === 'unknown') return { unknownWhy: read.why };
    else if (read.kind === 'auth') throw new Stop(5, AUTH_TEXT);
    else if (read.kind === 'blocked') throw new Stop(5, read.message);
    if (label) tick(`${label}: ${waitWord(last, read)}`);
    if (context.interrupted || context.ports.now() >= end) return { answer: last, open: true };
    await context.ports.sleep(context.ports.pollMs, context.signal);
  }
}

// Why a ready Try's link was refused, in one line, without the secret link itself.
function refusedLink(answer, origin) {
  let at = null;
  try { at = new URL(answer.result.url).origin; } catch { at = null; }
  if (at && at !== 'null' && at !== origin) return `Try link refused: it points at ${cleanText(at)}, not ${origin}. The server's address setting may be wrong; tell the PDD team.`;
  return 'Try link refused: it is not a valid Try link. Tell the PDD team.';
}

const otherNote = count => count ? `(${count} ${count === 1 ? 'is' : 'are'} not prompt, story or test files; run \`pdd test --files\` to see them)` : '';

// Paused sessions require an explicit owner reopen; only running sessions have a ready link.
const LIVE_SESSION = new Set(['running', 'paused']);
function tryLink(answer, origin) {
  return answer?.state === 'passed' && answer.result?.session?.state === 'running' ? validLink(answer.result?.url, origin, 'try') : null;
}

async function reopenTry(context, record, test) {
  const target = /^[A-Za-z0-9_./-]+$/.test(test.path) ? test.path : "'" + test.path.replace(/'/g, "'\"'\"'") + "'";
  const again = `pdd simulate ${target}`;
  if (context.interrupted) throw new Stop(3, 'Stopped before reopening the Try.');
  line(context.ports.stderr, 'Reopening your Try…');
  const reply = await context.runtime.reopen(record.id);
  if (reply.unreachable) throw new Stop(5, reply.unreachable);
  const blocked = blockingAnswer(reply);
  if (blocked) throw new Stop(5, blocked);
  if (reply.status === 401) throw new Stop(5, AUTH_TEXT);
  if (gateText(reply)) throw new Stop(5, 'The runtime opens soon.');
  if (!reply.lost && ![200, 202].includes(reply.status)) {
    const reason = cleanText(reply.json?.error?.message, context.secrets) || `HTTP ${reply.status}`;
    throw new Stop(reply.status === 429 ? 5 : 3, `This Try could not reopen: ${reason} Read the same Try again with: ${again}`);
  }
  if (!reply.lost && !sameJob(reply.json, record.id, 'try')) throw new Stop(3, 'The reopen answer has another request ID or command. Read the same Try again later.');
  const initial = reply.json;
  if (tryLink(initial, context.origin)) return initial;
  const done = await readUntil(context, record.id, 'try', answer => answer.result?.session?.state === 'running'
    || ['failed', 'refused', 'unknown'].includes(answer.state)
    || (answer.state === 'passed' && ['stopped', 'stopping', 'unknown'].includes(answer.result?.session?.state)), TRY_MS, 'Still reopening your Try');
  if (done.answer?.state === 'passed' && done.answer.result?.session?.state === 'running') return done.answer;
  throw new Stop(3, `Reopening this Try was not confirmed. Read the same Try again with: ${again}`);
}

async function stopTry(context, record) {
  const id = context.ports.randomUUID();
  context.store.posted(context.store.folder('tries'), id);
  const reply = await context.runtime.stop(record.id, id);
  // The server no longer knows this Try (404) or it expired (410): it is stopped, and the record can go.
  if (reply.status === 404 || reply.status === 410) return;
  const verdict = judgePost(reply, id, 'stop', context.secrets);
  if (verdict.kind === 'stop') throw new Stop(5, verdict.note.message);
  if (verdict.kind === 'not_run') throw new Stop(5, `${verdict.note.message}${verdict.note.code ? ` (${verdict.note.code})` : ''}`);
  if (verdict.kind === 'refused') throw new Stop(4, `The interpreter refused to stop this Try: ${verdict.refusal.message} (${verdict.refusal.code})`);
  if (verdict.kind !== 'accepted') throw new Stop(3, 'The stop result is unknown. Run pdd simulate --stop again later; it sends a new stop request.');
  const done = verdict.answer.state === 'passed' ? { answer: verdict.answer } : await readUntil(context, id, 'stop', answer => ENDED.has(answer.state), TRY_MS, 'Still stopping the Try');
  if (done.answer?.state !== 'passed') throw new Stop(done.answer?.state === 'refused' ? 4 : 3, 'The Try did not confirm that it stopped. Run pdd simulate --stop again later.');
}

function tryPromptProblem(root, found, test, record, capture) {
  const hashes=record.prompt_hashes;
  if (!capture && isObject(hashes)) {
    const files=sourceFilePort(root,found.visible), sources=[], references=[], raw_prompt_hashes={};
    for (const path of Object.keys(hashes)) {
      const prepared=readPrompt(root,found.visible,path);
      if (!prepared.text) return 'A prompt changed or this Try has no source record.';
      sources.push({path,bytes:Buffer.from(prepared.text,'utf8')});references.push(...(prepared.references??[]));
      raw_prompt_hashes[path]=sha256(Buffer.from(files.read({path}).content,'utf8'));
    }
    capture={sources,references,raw_prompt_hashes};
  }
  if (!isObject(hashes) || !Object.keys(hashes).length || (test && !test.doc?.steps?.every(step=>typeof hashes[step.entry_path]==='string'))
    || !Object.entries(hashes).every(([path,expected])=>found.visible.has(path) && capture.raw_prompt_hashes[path]===expected)) return 'A prompt changed or this Try has no source record.';
  const current=Object.fromEntries(capture.sources.filter(file=>file.path.endsWith('.prompt.md')).map(file=>[file.path,sha256(file.bytes)]));
  if (isObject(record.effective_prompt_hashes) && Object.keys(hashes).every(path=>typeof record.effective_prompt_hashes[path]==='string')) {
    if (!Object.entries(record.effective_prompt_hashes).every(([path,expected])=>current[path]===expected)) return 'A prompt or shared contract changed since this Try.';
  } else if (capture.references.some(ref=>ref.consumer.endsWith('.prompt.md'))) return 'This Try reference baseline is unavailable.';
  return null;
}


// pdd simulate. Returns the exit code.
export async function runTry({ words = [], options = {}, cwd = process.cwd() } = {}, givenPorts = {}) {
  const ports = withDefaults(givenPorts), context = { ports, interrupted: false, doorMode: !!(options['--cli'] || options['--serve']) };
  let release = () => {};
  try {
    const requestedBudget = requestedCalls(options['--max-calls']);
    if (options['--agent'] !== undefined && (typeof options['--agent'] !== 'string' || !options['--agent'].trim() || ['--no-wait','--stop','--save-last','--cli','--serve'].some(key => options[key] !== undefined))) throw new Stop(2, '--agent chooses a configured agent name for an ordinary connected pdd simulate; omit --no-wait and door modes.');
    const doorModes = ['--cli', '--serve', '--save-last'].filter(key => options[key]);
    if (doorModes.length > 1 || (options['--shell'] && !options['--cli']) || (doorModes.length && options['--stop'])
      || (options['--save-last'] && (words.length || Object.keys(options).length !== 1))) throw new Stop(2, 'Choose one of --cli, --serve, --save-last or --stop; --shell needs --cli.');
    if (options['--save-last']) {
      const root = repoRoot(cwd), store = stateFor(ports.env, root), identity = signIn(ports.gh, store);
      return await (await import('./try-doors.mjs')).saveLast({ root, store, identity, ports });
    }
    if (options['--stop'] && (options['--tab'] || options['--new'] || options['--no-open'] || options['--no-wait'] || options['--app-map'] !== undefined || requestedBudget !== null)) throw new Stop(2, 'pdd simulate --stop takes only a STORY. Run pdd simulate --help.');
    if (words.length > 1) throw new Stop(2, 'pdd simulate takes one STORY.');
    const origin = runtimeOrigin(ports.env);
    if (options['--stop']) return await stopByName(context, cwd, words, origin);
    const { root, found, normalized } = localSetup(cwd, words), store = stateFor(ports.env, root);
    context.agentConnection = !options['--no-wait'] && !context.doorMode && ports.agentBridge !== false
      && (ports.stdout.isTTY === true || options['--agent'] !== undefined);
    if (context.agentConnection) {
      try { context.agentDefinitions = loadAgentDefinitions({cwd:root,env:ports.env}); }
      catch (error) { throw new Stop(2,error.message); }
      if (!context.agentDefinitions.length) throw new Stop(2,'No agents are configured. Add an agent or enable defaults in agents.json.');
      if (options['--agent'] !== undefined && !context.agentDefinitions.some(d => d.name === options['--agent'] || (['codex','claude','gemini'].includes(d.id) && d.id === options['--agent']))) throw new Stop(2,'Unknown agent name. Choose a name from agents.json or an enabled default.');
    }
    const appMap = appMapFor(found, options['--app-map'], cwd, root, ports.stderr);
    const test = oneTest(found, normalized, root), repoState = store.repo(root), record = repoState.tries?.[test.path];
    Object.assign(context, { root, store, origin, visible: found.visible, appMap, cwd: realpathSync(cwd), seedTest: { path: test.path, storyPath: test.storyPath } });
    const checked = preflight({ root, found, selected: [test] }), row = localRows(checked.rows)[0];
    if (row.state === 'refused') {
      if (options['--cli'] || options['--serve']) throw new Stop(125, row.refusals?.map(r => r.message || r.code).join('; ') || 'The Story input was refused.');
      line(ports.stdout, renderText({ rows: [row], exitCode: 4 })); return 4;
    }
    const capture = ports.captureSource(root, { tests: [test.path], appMap }), note = otherNote(otherFiles(capture.files, found).length);
    for (const warning of capture.warnings ?? []) line(ports.stderr, warning);
    const identity = signIn(ports.gh, context.store);
    Object.assign(context, { capture, identity, secrets: [identity.token], startedAt: ports.now(), deadline: ports.now() + TRY_MS, lint: { request_ids: [], state: null },
      batch: null, rows: [row], timeoutMin: TRY_MS / 60_000, head: null });
    context.folder = store.folder('tries');
    release = interruptible(context);
    context.runtime = new Runtime({ origin, token: identity.token, ports, signal: context.signal });
    if (record) {
      const needsOwner = context.doorMode || requestedBudget !== null || context.agentConnection;
      if (needsOwner && record.login && record.login !== identity.login) throw new Stop(context.doorMode ? 125 : 5, `This Try belongs to ${record.login}. Run: gh auth switch -u ${record.login}`);
      if (needsOwner && record.origin !== origin) throw new Stop(2, 'This Try belongs to another interpreter address. Use its original PDD_RUNTIME_URL, or stop it first.');
      const read = judgeGet(await context.runtime.get(record.id), record.id, 'try');
      if (read.kind === 'auth') throw new Stop(5, AUTH_TEXT);
      if (read.kind === 'blocked') throw new Stop(5, read.message);
      if (read.kind === 'gate') throw new Stop(5, 'The runtime opens soon.');
      if (read.unreachable) throw new Stop(5, read.unreachable);
      let answer = read.kind === 'state' ? read.answer : null, link = tryLink(answer, origin);
      if (answer) await finishReservation(context, record, answer);
      const live = answer?.state === 'passed' && LIVE_SESSION.has(answer.result?.session?.state);
      if (requestedBudget !== null && !options['--new'] && !live) throw new Stop(3, 'This Try is not confirmed open. Its budget was not changed. Read the same Try again later; use --new only to replace it deliberately.');
      if (requestedBudget !== null && !options['--new'] && (!Number.isSafeInteger(answer?.result?.session?.max_calls) || answer.result.session.max_calls < 1)) throw new Stop(3, 'The interpreter did not confirm this Try’s current budget. No budget change or reopen was sent.');
      if (requestedBudget !== null && !options['--new'] && requestedBudget > answer.result.session.max_calls) throw new Stop(5, 'This interpreter does not support raising this Try’s budget yet. The same Try and saved data are kept.');
      // 404 (unknown to the server) and 410 (expired) count as ended: the record goes and a new Try is made.
      // A Try the server lost (state unknown, for example after a restart) counts as ended too: a new Try costs no AI calls.
      const ended = read.kind === 'missing' || read.status === 410 || ['failed', 'refused', 'unknown'].includes(answer?.state)
        || (answer?.state === 'passed' && ['stopped', 'stopping', 'unknown'].includes(answer.result?.session?.state));
      if (live && !options['--new'] && (options['--app-map'] !== undefined || options['--tab'])) {
        throw new Stop(2, `A Try for "${test.title}" is already open. --app-map and --tab apply only to a new Try: run pdd simulate ${test.story} --new (it stops the open Try first).`);
      }
      if (live && (options['--serve'] || context.agentConnection) && !options['--new']) {
        const problem=tryPromptProblem(root,found,test,record,capture);
        if (problem) throw new Stop(options['--serve'] ? 125 : 4, `${problem} Run pdd simulate STORY${options['--serve'] ? ' --serve' : ''} --new.`);
      }
      if (answer?.state === 'passed' && answer.result?.session?.state === 'paused' && !options['--new']) {
        if (!validLink(answer.result?.url, origin, 'try')) throw new Stop(3, refusedLink(answer, origin));
        answer = await reopenTry(context, record, test); link = tryLink(answer, origin);
      }
      if (link && !options['--new']) {
        if (!record.storyPath && record.story !== test.story) throw new Stop(4, 'The original Try story changed. Restore its test file, or use --new to start a new Try.');
        context.seedTest.storyPath = record.storyPath ?? test.storyPath;
        return await showTry(context, test, link, options, record.id, true, answer?.result?.session);
      }
      if (!link && answer?.state === 'passed' && LIVE_SESSION.has(answer.result?.session?.state) && !options['--new']) throw new Stop(3, refusedLink(answer, origin));
      // A Try that may still start or run is never made twice by accident.
      if (!ended && !options['--new']) {
        throw new Stop(3, `The last Try for "${test.title}" is not ready or its state is unknown. Run pdd simulate ${test.story} again later, or pdd simulate ${test.story} --new to stop it and make a new one.`);
      }
      if (!ended) { line(ports.stderr, 'Stopping the old Try…'); await stopTry(context, record); }
      delete repoState.tries[test.path];
      store.saveRepo(root, repoState);
    }
    await checkLint(context, [row]);
    if (context.interrupted) throw new Stop(3, 'Stopped before the Try was made. Nothing new was sent.');
    if (row.state !== 'ready') {
      if (options['--cli'] || options['--serve']) throw new Stop(125, row.refusals?.map(r => r.message || r.code).join('; ') || 'The Story did not pass lint.');
      return printTryProblem(context, row);
    }
    let request, verdict, reply, done;
    const setup = { request_ids: [], reservation: null };
    for (;;) {
      if (!await admission(context, 'try', setup)) throw new Stop(context.interrupted ? 3 : 5, context.interrupted ? 'Stopped before sending.' : 'The interpreter stayed busy until the Try setup wait ended. No new Try was sent.');
      request = { requestId: ports.randomUUID(), source_sha256: capture.sha256, seed: test.path, max_calls: requestedBudget ?? 400, ...(appMap ? { app_map: appMap } : {}),
        tab: options['--tab'] ?? (options['--cli'] ? 'terminal' : appMap ? 'screen' : 'call') };
      setup.request_ids.push(request.requestId);
      const registered = await recordRuntimeRequest(setup.reservation, request.requestId, slotPorts(context));
      if (registered === false) { await finishReservation(context, setup, { state: 'not_run' }); throw new Stop(3, context.interrupted ? 'Stopped before sending.' : 'Stopped before the Try was sent.'); }
      if (context.interrupted || ports.now() >= context.deadline) { await finishReservation(context, setup, { state: 'not_run' }); throw new Stop(3, context.interrupted ? 'Stopped before sending.' : 'Stopped before the Try was sent.'); }
      const uploadedSeed=capture.sources.find(file=>file.path===test.path);
      store.saveRepo(root, { ...repoState, tries: { ...repoState.tries, [test.path]: { id: request.requestId, ...setup, story: test.story, storyPath: test.storyPath, title: test.title, origin, login: identity.login, seed_scenario: uploadedSeed ? JSON.parse(uploadedSeed.bytes.toString('utf8')) : test.doc, story_sha256: createHash('sha256').update(readFileSync(join(root, test.storyPath))).digest('hex'), prompt_hashes: capture.raw_prompt_hashes,
        effective_prompt_hashes:Object.fromEntries(capture.sources.filter(file=>file.path.endsWith('.prompt.md')).map(file=>[file.path,sha256(file.bytes)])),contract_references:capture.references } } });
      store.posted(context.folder, request.requestId);
      line(ports.stderr, `Starting your Try: sending ${capture.files.length} files, ${formatSize(capture.bytes)}${note ? ` ${note}` : ''}…`);
      reply = await context.runtime.post('/v1/try', request, capture.tar, Math.max(1, Math.min(ports.postMs, context.deadline - ports.now())));
      verdict = judgePost(reply, request.requestId, 'try', context.secrets);
      if (verdict.maintenance) maintenanceNotice(context, verdict, reply);
      if (verdict.answer) { store.write(join(context.folder, `${request.requestId}.json`), verdict.answer); queueProgress(context, verdict.answer); await finishReservation(context, setup, verdict.answer); }
      if (verdict.admission) store.write(join(context.folder, `${request.requestId}.admission.json`), verdict.admission);
      if (verdict.kind === 'busy') {
        await finishReservation(context, setup, { state: 'not_run' });
        if (!verdict.maintenance) line(ports.stderr, 'The interpreter is busy. Waiting to start your Try…');
        if (await waitBudget(context, verdict.wait)) continue;
        delete repoState.tries[test.path]; store.saveRepo(root, repoState);
        throw new Stop(context.interrupted ? 3 : 5, context.interrupted ? stoppedPause(context, setup, 'Try setup') : 'The interpreter stayed busy until the Try setup wait ended.');
      }
      if (verdict.kind !== 'accepted') {
        if (verdict.kind !== 'unknown') { await finishReservation(context, setup, { state: 'not_run' }); delete repoState.tries[test.path]; store.saveRepo(root, repoState); }
        if (reply.status === 429) throw new Stop(5, cleanText(reply.json?.error?.message, context.secrets) || 'Too many Try links are open. Stop one with pdd simulate --stop');
        if (verdict.kind === 'refused') return trySetupRefused(context, test, appMap, [{ ...reply.json.error, ...verdict.refusal }], null);
        if (verdict.blocked) throw new Stop(5, verdict.note.message);
        if (verdict.kind === 'not_run' || verdict.kind === 'stop') throw new Stop(5, `${verdict.note.message}${verdict.note.code ? ` (${verdict.note.code})` : ''}`);
        throw new Stop(3, `The Try setup result is unknown. Run pdd simulate ${test.story} again later: it reads this Try first and sends nothing new while it runs.`);
      }
      done = ENDED.has(verdict.answer.state) ? { answer: verdict.answer }
        : await readUntil(context, request.requestId, 'try', answer => ENDED.has(answer.state), TRY_MS, 'Still starting your Try');
      if (done.answer) await finishReservation(context, setup, done.answer);
      break;
    }
    const link = tryLink(done.answer, origin);
    if (link) {
      const cap = done.answer?.result?.session?.max_calls;
      if (Number.isSafeInteger(cap) && cap !== request.max_calls) throw new Stop(5, `The interpreter confirmed a budget of ${cap} calls instead of the requested ${request.max_calls}. This Try is kept; its saved data was not reset.`);
      if (requestedBudget !== null && !Number.isSafeInteger(cap)) throw new Stop(3, 'The interpreter did not confirm the requested Try budget. The same Try is kept; read it again without changing its budget.');
      return await showTry(context, test, link, options, request.requestId, false, done.answer?.result?.session);
    }
    if (stepTimeLimit(done.answer, { steps: row.steps, secrets: context.secrets })) { applyAnswer(row, done.answer, context); return printTryProblem(context, row); }
    if (done.answer?.state === 'unknown') {
      delete repoState.tries[test.path];
      store.saveRepo(root, repoState);
      throw new Stop(3, `The Try setup did not finish on the server (its state is unknown; the server may have restarted). It used no AI calls. Run pdd simulate ${test.story} to make a new Try.`);
    }
    if (done.unknownWhy || done.open || !done.answer) {
      throw new Stop(3, `The Try setup is not finished after ${TRY_MS / 60_000} min${done.answer?.state ? ` (last state: ${cleanText(done.answer.state)})` : ''}. Run pdd simulate ${test.story} again later; it reads this Try first and makes no second one.`);
    }
    // A ready Try with a bad link stays recorded, so pdd simulate --stop can still end it; pdd never prints that link.
    if (done.answer.state === 'passed' && LIVE_SESSION.has(done.answer.result?.session?.state)) throw new Stop(3, refusedLink(done.answer, origin));
    applyAnswer(row, done.answer, context);
    delete repoState.tries[test.path];
    store.saveRepo(root, repoState);
    if (row.state === 'refused') {
      const report = isObject(done.answer.result?.report?.refusal) ? done.answer.result.report.refusal : null, given = done.answer.result?.refusals;
      const refusals = (Array.isArray(given) && given.length ? given : report ? [report] : []).filter(isObject)
        .map(item => ({ ...item, ...(report?.code === item.code ? { reason: item.reason ?? report.reason, fix: item.fix ?? report.fix } : {}) }));
      return trySetupRefused(context, test, appMap, refusals, row.report_url);
    }
    return printTryProblem(context, row);
  } catch (error) {
    if (options['--cli'] || options['--serve'] || options['--save-last']) { line(ports.stderr, `pdd: ${cleanText(error.message || 'The Try could not start.', context.secrets ?? [])}`); return error.exitCode === 2 ? 2 : 125; }
    if (error instanceof Stop || error instanceof PreflightError) { line(ports.stderr, error.message); return error.exitCode; }
    throw error;
  } finally { release(); await Promise.all([...(context.reservations ?? [])].map(reservation => releaseRuntimeSlot(reservation, { ended: false }, slotPorts(context)))); }
}

// pdd simulate --stop [STORY]: find the Try by its story name in the state record, so it works on any branch (real-user issue 14).
async function stopByName(context, cwd, words, origin) {
  const { ports } = context, root = repoRoot(cwd), store = stateFor(ports.env, root), repoState = store.repo(root);
  const entries = Object.entries(repoState.tries ?? {}), word = words[0]?.replace(/^\.\//, '');
  const names = entries.map(([path, record]) => record.story ?? basename(path, '.json')).join(', ') || 'none';
  const hits = word === undefined ? entries : entries.filter(([path, record]) => [record.story, path, basename(path, '.json')].includes(word));
  if (hits.length !== 1) {
    throw new Stop(2, word !== undefined ? `No open Try for "${cleanText(word)}". Open Try links: ${names}.`
      : entries.length ? `Name the Try to stop. Open Try links: ${names}.` : 'No open Try in this repository.');
  }
  const [path, record] = hits[0], title = record.title ?? record.story ?? path;
  Object.assign(context, { root, store, origin });
  const identity = signIn(ports.gh, store);
  context.secrets = [identity.token];
  context.runtime = new Runtime({ origin: record.origin ?? origin, token: identity.token, ports });
  line(ports.stderr, `Stopping the Try for "${title}"…`);
  await stopTry(context, record);
  delete repoState.tries[path];
  store.saveRepo(root, repoState);
  line(ports.stdout, `The Try link for "${title}" is stopped.`);
  return 0;
}

async function checkLint(context, rows) {
  const lint = await runLint(context);
  if (lint.kind === 'pending') throw new Stop(3, pendingLintMessage(context, lint.answer));
  const verdicts = lint.kind === 'answer' && ['passed', 'failed', 'refused'].includes(lint.answer.state) ? judgeLint(lint.answer, rows, context.root, context.visible, context.secrets) : null;
  if (lint.kind === 'not_run' || lint.kind === 'stop') throw new Stop(5, `${lint.note.message}${lint.note.code ? ` (${lint.note.code})` : ''}`);
  if (lint.kind === 'refused') { Object.assign(rows[0], { state: 'refused', phase: 'lint', refusals: [lint.refusal] }); return; }
  if (context.doorMode && lint.kind === 'answer' && lint.answer?.state === 'refused' && !isObject(lint.answer.result?.report?.program)) {
    const refusal = lint.answer.result?.refusals?.[0] ?? lint.answer.result?.report?.refusal;
    throw new Stop(125, refusal?.reason || refusal?.message || refusal?.code || 'The interpreter refused lint.');
  }
  if (!verdicts) throw new Stop(3, 'The lint result is unknown, so pdd made no Try link. Run pdd simulate again later.');
  for (const [row, problem] of verdicts) Object.assign(row, { state: 'refused', phase: 'lint', refusals: [problem] });
}

// A refused Try setup is not a check (runtime team, Oct 27): two plain lines with what was refused, why and the fix; no table.
const APP_MAP_RULES = { 'ambiguous-handler': 'on one screen, all taps of one kind must match by the same key',
  'template-reference-schema': 'a field that gets a value from the screen ($ref) must be a plain {"type": "string"}' };
const GENERIC_REFUSAL = /^The runtime refused this job\b/;
function trySetupRefused(context, test, appMap, refusals, reportUrl) {
  if (context.doorMode) throw new Stop(125, refusals.map(item => item.reason || item.engine_message || item.message || item.code).filter(Boolean).join('; ') || 'The interpreter refused this Try.');
  const text = value => typeof value === 'string' ? cleanText(value, context.secrets) : '';
  const items = (refusals.length ? refusals : [{ code: 'refused' }]).map(item => ({ code: text(item.code) || 'refused', section: text(item.section),
    reason: [text(item.reason), APP_MAP_RULES[text(item.code)], text(item.engine_message), GENERIC_REFUSAL.test(text(item.message)) ? '' : text(item.message)].find(Boolean),
    fix: text(item.fix), where: text(item.where) || [text(item.file), text(item.at)].filter(Boolean).join(' ') }));
  const mapped = !!appMap && items.some(item => Object.hasOwn(APP_MAP_RULES, item.code) || /^app-map-/.test(item.code) || /app[-_]map/i.test(item.section));
  const why = items.map(item => `${item.reason ? `${item.code}: ${item.reason}` : item.code}${item.where ? `; at ${item.where}` : ''}`).join('; '), fix = items.find(item => item.fix)?.fix;
  const again = `run pdd simulate ${test.story} --new.`;
  line(context.ports.stdout, `The Try could not start: ${mapped ? 'the app map was refused' : 'the server refused it'} (${why}).`);
  line(context.ports.stdout, fix ? `${fix} Then ${again}` : mapped ? `Fix ${appMap} (RUNBOOK §13), then ${again}`
    : `Fix what it names, then ${again}${reportUrl ? ` Details: ${reportUrl}` : ''}`);
  return 4;
}

function printTryProblem(context, row) {
  if (context.doorMode) throw new Stop(125, row.time_limit ? `${row.time_limit.message} ${row.time_limit.fix}` : row.refusals?.map(r => r.message || r.code).join('; ') || `The Try could not start (${row.state}).`);
  const exitCode = exitCodeFor([row]);
  context.ports.stdout.write(renderText({ rows: [row], exitCode, secrets: context.secrets, recovery: `pdd simulate ${row.story}` }));
  return exitCode;
}

async function showTry(context, test, link, options, tryId, reused = false, session) {
  const budget = Number.isSafeInteger(session?.max_calls) && session.max_calls > 0 && Number.isSafeInteger(session?.remaining_calls)
    && session.remaining_calls >= 0 && session.remaining_calls <= session.max_calls
    ? `Try budget ${session.max_calls} calls; ${session.remaining_calls} remaining. You are charged only for calls that run.`
    : 'The interpreter did not report this Try’s budget.';
  line(options['--cli'] || options['--serve'] ? context.ports.stderr : context.ports.stdout, budget);
  if (options['--cli'] || options['--serve']) {
    const doors = await import('./try-doors.mjs');
    return options['--cli'] ? doors.openCli(context, test, tryId, options) : (await import('./try-http.mjs')).openServe(context, test, tryId, options);
  }
  const { ports } = context, ends = reused ? `It keeps its original 24-hour expiry; stop it with: pdd simulate --stop ${test.story}`
    : `It ends in 24 hours, or with: pdd simulate --stop ${test.story}`;
  let bridge = null, answers = null;
  try {
    if (context.agentConnection) {
      const finalRuntime = new Runtime({ origin: context.origin, token: context.identity.token, ports });
      context.agentFinalSend = finalRuntime.send.bind(finalRuntime);
      try { bridge = await (ports.agentBridge ?? (await import('./agent-chat.mjs')).createAgentBridge)(context, test, tryId, options, link); }
      catch (error) { throw new Stop(5, cleanText(error.message || 'Your agent could not connect.', context.secrets)); }
    }
    if (!options['--no-open'] && await ports.openUrl(bridge?.url ?? link)) line(ports.stdout, `Try ready for "${test.title}": ${link} (open in your browser). ${ends}`);
    else {
      line(ports.stdout, `Try ready for "${test.title}": ${link}`);
      line(ports.stdout, `${options['--no-open'] ? '' : 'pdd could not open a browser. Open the link yourself. '}Anyone with the link can use it. ${ends}`);
      if (bridge) line(ports.stdout, `Owner agent chat link (private; do not share): ${bridge.url}`);
    }
    if (!bridge) { await watchSavedTests(context, tryId, !options['--no-wait'] && ports.interactive, test.story); return 0; }
    answers = ports.interactive ? lineReader(ports.stdin) : null;
    context.onAgentChatClose = () => answers?.close();
    return await bridge.run(async () => {
      const tests = await collectSavedTests(context, tryId), approvals = await collectApprovals(context, tryId, test.story, answers);
      return tests !== 'ended' && approvals !== 'ended';
    });
  } finally { answers?.close(); await bridge?.close(); }
}

// ---- Save as test: cases saved on the Try page become steps of the story's test file ----

const slug = text => String(text ?? '').toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-+|-+$/g, '').slice(0, 60);

// The [start, end) offsets of the top-level "steps" array in a JSON text, or null.
function stepsArray(text) {
  let depth = 0, key = null, index = 0;
  const skipString = at => { let i = at + 1; while (i < text.length && text[i] !== '"') i += text[i] === '\\' ? 2 : 1; return i + 1; };
  while (index < text.length) {
    const char = text[index];
    if (char === '"') {
      const end = skipString(index);
      if (depth === 1 && /^\s*:/.test(text.slice(end))) key = JSON.parse(text.slice(index, end));
      index = end; continue;
    }
    if (char === '[' && depth === 1 && key === 'steps') {
      let inner = 0, at = index;
      while (at < text.length) {
        if (text[at] === '"') { at = skipString(at); continue; }
        if (text[at] === '[' || text[at] === '{') inner += 1;
        if (text[at] === ']' || text[at] === '}') { inner -= 1; if (inner === 0) return [index, at + 1]; }
        at += 1;
      }
      return null;
    }
    if (char === '{' || char === '[') depth += 1;
    if (char === '}' || char === ']') depth -= 1;
    index += 1;
  }
  return null;
}

// Append one step and keep every other byte of the file; fall back to a plain rewrite.
function appendStep(text, doc, step) {
  const want = { ...doc, steps: [...doc.steps, step] }, range = stepsArray(text);
  if (range) {
    const [start, end] = range, close = end - 1, before = text.slice(start + 1, close).trimEnd();
    const lineStart = text.lastIndexOf('\n', close) + 1, closing = text.slice(lineStart, close);
    // A "]" on its own line gets an indented step; a one-line array gets a one-line step.
    const next = /^[ \t]*$/.test(closing)
      ? `${text.slice(0, start + 1)}${before}${before ? ',' : ''}\n${closing}  ${JSON.stringify(step, null, 2).replace(/\n/g, `\n${closing}  `)}\n${closing}${text.slice(close)}`
      : `${text.slice(0, start + 1)}${before}${before ? ', ' : ''}${JSON.stringify(step)}${text.slice(close)}`;
    try { if (isDeepStrictEqual(JSON.parse(next), want)) return next; } catch { /* fall back */ }
  }
  return `${JSON.stringify(want, null, 2)}\n`;
}

// Anyone with a Try link can save a case, so a saved case is untrusted: pdd writes only to a real file inside the repo,
// only to a scenario test file found by discovery or a new tests/<story>.json, and never follows a symbolic link.
const NOT_TEST_FILES = /^(?:\..*|package(?:-lock)?\.json|tsconfig(?:\..+)?\.json|jsconfig\.json|composer\.json|deno\.json|bower\.json|app-map\.json|.+\.config\.json)$/;
const inRepo = (realRoot, path) => { try { return realpathSync(join(realRoot, path)) === join(realRoot, path); } catch { return false; } };

// One saved case → a new step in its story's test file. Returns the line to print ("added …" or "not added: …").
function addSavedCase(root, saved, seedTest) {
  try { return addSavedCaseSafely(realpathSync(root), saved, seedTest); } catch (error) { return `not added: pdd could not write the case (${cleanText(error.code ?? error.message)}).`; }
}

function addSavedCaseSafely(root, saved, seedTest) {
  const test = saved?.test, story = typeof saved?.story_path === 'string' ? saved.story_path : test?.story_path;
  const label = cleanText(saved?.name || saved?.id || 'a saved case');
  if (!isObject(test) || !Array.isArray(test.steps) || !test.steps.length || typeof story !== 'string') return `not added: "${label}" is not a test the interpreter can run.`;
  const found = findTests({ root });
  if (!story.endsWith('.md') || story.split('/').some(part => !part || part === '.' || part === '..') || !found.visible.has(story) || !inRepo(root, story)) {
    return `not added: its story "${cleanText(story)}" is not a story file in this repository.`;
  }
  const candidates = found.tests.filter(item => item.storyPath === story && item.doc).sort((a, b) => a.path.localeCompare(b.path));
  const seededStory = seedTest?.storyPath === story;
  const target = seededStory ? candidates.find(item => item.path === seedTest.path)
    : saved?.original_path ? candidates.find(item => item.path === saved.original_path) : candidates[0];
  if (seededStory && !target) return `not added: the original test ${cleanText(seedTest.path)} is missing or no longer belongs to ${cleanText(story)}. Restore it before importing the case.`;
  if (saved?.original_path && !target) return 'not added: the original test file is missing or its Story changed.';
  if (!target) {
    // A story with no test gets tests/<story>.json (a slug, never a path from the server), as the runbook names test files.
    const folder = statOrNull(join(root, 'tests'));
    if (folder?.isSymbolicLink()) return 'not added: tests/ is a symbolic link. pdd writes test files only inside the repository.';
    if (folder && !folder.isDirectory()) return 'not added: tests is not a folder.';
    const base = slug(story.split('/').at(-1).replace(/\.md$/, '')) || 'saved';
    let path = `tests/${base}.json`;
    for (let number = 2; statOrNull(join(root, path)); number += 1) path = `tests/${base}-${number}.json`;
    if (!folder) mkdirSync(join(root, 'tests'));
    if (!inRepo(root, 'tests')) return 'not added: tests/ is not inside the repository.';
    writeFileSync(join(root, path), `${JSON.stringify(test, null, 2)}\n`, { flag: 'wx' });
    return `added to ${path} as step ${cleanText(test.steps.map(step => step?.step_id).join(', '))}`;
  }
  if (!target.path.endsWith('.json') || NOT_TEST_FILES.test(target.path.split('/').at(-1))) {
    return `not added: ${target.path} is not a file pdd adds steps to. Move the test to tests/.`;
  }
  const file = join(root, target.path), stat = statOrNull(file);
  if (!stat?.isFile() || !inRepo(root, target.path)) return `not added: ${target.path} is not a regular file inside the repository.`;
  const text = readFileSync(file, 'utf8'), doc = JSON.parse(text);
  if (!isObject(doc) || doc.schema_version !== TEST_SCHEMA || !Array.isArray(doc.steps)) return `not added: ${target.path} is not a "${TEST_SCHEMA}" test.`;
  const byText = new Map((Array.isArray(doc.criteria) ? doc.criteria : []).map(item => [item.text, item.id]));
  const savedText = new Map((Array.isArray(test.criteria) ? test.criteria : []).map(item => [item.id, item.text]));
  let next = text, current = doc;
  const ids = [];
  for (const raw of test.steps) {
    const checks = Array.isArray(raw?.checks) ? raw.checks : [];
    const mapped = checks.map(check => ({ ...check, criterion_id: byText.get(savedText.get(check?.criterion_id)) ?? (byText.has(savedText.get(check?.criterion_id)) ? check.criterion_id : null) }));
    const lost = checks.find((check, index) => !mapped[index].criterion_id);
    if (lost || !checks.length) return `not added: "${label}" checks a criterion that ${target.path} does not have ("${cleanText(savedText.get(lost?.criterion_id) ?? lost?.criterion_id ?? 'none')}"). Add it by hand.`;
    const taken = new Set(current.steps.map(step => step?.step_id));
    let id = slug(raw.step_id) || slug(saved.name) || slug(saved.id) || 'saved-case';
    for (let number = 2, base = id; taken.has(id); number += 1) id = `${base}-${number}`;
    const step = { ...raw, step_id: id, checks: mapped };
    next = appendStep(next, current, step);
    current = { ...current, steps: [...current.steps, step] };
    ids.push(id);
  }
  writeFileSync(file, next);
  return `added to ${target.path} as step ${ids.join(', ')}`;
}

// Saved cases: add each new one once. Returns 'ok', 'missing' (no endpoint yet) or 'ended'.
async function collectSavedTests(context, tryId) {
  const { ports, store, root } = context, path = join(store.folder('tries'), `${tryId}.tests.json`);
  const reply = await context.runtime.send(`/v1/try/${tryId}/tests`, { method: 'GET' }, GET_MS);
  if ([401, 403, 410].includes(reply.status)) return 'ended';
  if (reply.status !== 200 || !Array.isArray(reply.json?.tests)) return reply.lost ? 'ok' : 'missing';
  const done = store.read(path) ?? {};
  for (const saved of reply.json.tests) {
    const key = typeof saved?.id === 'string' ? saved.id : null;
    if (!key || done[key]) continue;
    const said = addSavedCase(root, saved, context.seedTest);
    done[key] = { at: new Date(ports.now()).toISOString(), result: said };
    store.write(path, done);
    try { context.onAgentCaseSaved?.({ id: key, name: saved.name, story_path: saved.story_path ?? saved.test?.story_path, result: said }); } catch {}
    line(ports.stdout, said);
  }
  return 'ok';
}

// Approval requests from the Try page (#9): only a person's y in this terminal approves; the page gets done or declined.
async function collectApprovals(context, tryId, story, answers) {
  const { ports, store, root } = context, path = join(store.folder('tries'), `${tryId}.approvals.json`);
  const reply = await context.runtime.send(`/v1/try/${tryId}/approvals`, { method: 'GET' }, GET_MS);
  if ([401, 403, 410].includes(reply.status)) return 'ended';
  if (reply.status !== 200 || !Array.isArray(reply.json?.approvals)) return reply.lost ? 'ok' : 'missing';
  const handled = store.read(path) ?? {};
  for (const request of reply.json.approvals) {
    const id = typeof request?.id === 'string' && /^[A-Za-z0-9_-]{1,128}$/.test(request.id) ? request.id : null;
    if (!id || request.state !== 'pending' || handled[id]?.posted) continue;
    const asked = cleanText(request.prompt_path);
    if (!handled[id]?.state) {
      if (!answers) {
        if (!handled[id]?.noticed) line(ports.stdout, `The Try page asks to approve ${asked}. A person answers it in a terminal: pdd simulate ${story}`);
        handled[id] = { noticed: true }; store.write(path, handled);
        continue;
      }
      const real = realpathSync(root), prompt = typeof request.prompt_path === 'string' ? promptPath(real, real, request.prompt_path) : null;
      const result = prompt ? await askApproval({ root: real, path: prompt, stdout: ports.stdout, answers, expectedHash: request.prose_sha256 })
        : { state: 'declined', message: `not approved: ${asked} is not a Git-visible *.prompt.md file in this repository.` };
      line(ports.stdout, result.message);
      handled[id] = { state: result.state, at: new Date(ports.now()).toISOString() };
      store.write(path, handled);
    }
    const answer = await context.runtime.send(`/v1/try/${tryId}/approvals/${id}`,
      { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ state: handled[id].state }) }, GET_MS);
    if (answer.status >= 200 && answer.status < 300) { handled[id].posted = true; store.write(path, handled); }
  }
  return 'ok';
}

// Read saved cases and approval requests once; with `wait` (a person's terminal), keep reading until Ctrl-C or the Try ends.
async function watchSavedTests(context, tryId, wait, story) {
  const { ports } = context, answers = wait ? lineReader(ports.stdin) : null;
  let polls = 0, told = false, tests = 'ok', approvals = 'ok';
  try {
    for (;;) {
      if (tests !== 'missing') tests = await collectSavedTests(context, tryId);
      if (tests === 'missing' && wait && !told) line(ports.stdout, 'The interpreter does not keep saved tests yet. Copy a saved test from the Try page into tests/ by hand.');
      if (approvals !== 'missing') approvals = await collectApprovals(context, tryId, story, answers);
      if (tests === 'ended' || approvals === 'ended' || !wait || context.interrupted) return;
      if (tests === 'missing' && approvals === 'missing') return;
      if (!told) { line(ports.stdout, 'Waiting for tests saved and approvals asked in the Try page. Press Ctrl-C to stop waiting; the Try link stays open.'); told = true; }
      await ports.sleep(ports.watchMs, context.signal);
      if (context.interrupted) { line(ports.stdout, 'Stopped waiting. The Try link stays open. Run pdd simulate again to add tests saved later.'); return; }
      polls += 1;
      if (polls % 6 === 0) {
        const read = judgeGet(await context.runtime.get(tryId), tryId, 'try');
        if ((read.kind === 'state' && !LIVE_SESSION.has(read.answer.result?.session?.state)) || read.kind === 'missing' || read.status === 410) {
          wait = false; line(ports.stdout, 'The Try has ended.');
        }
      }
    }
  } finally { answers?.close(); }
}


// The doors use the same gh identity, private store, one-shot dispatch and owner-scoped ledger as Try.
export const saveDoorCase = (root, saved, options = {}) => {
  if (!options.isolated) return addSavedCase(root, saved);
  try {
    root = realpathSync(root);
    const found = findTests({ root }), test = saved?.test;
    const original = found.tests.find(item => item.path === saved.original_path && item.storyPath === saved.story_path);
    if (!original?.doc || !inRepo(root, original.path) || !inRepo(root, saved.story_path)) return 'not added: the original Story or test is missing or changed.';
    if (!isObject(test) || !isObject(test.initial_world) || !Array.isArray(test.steps) || test.steps.length !== 1 || test.story_path !== original.storyPath
      || !isDeepStrictEqual(test.criteria, original.doc.criteria)
      || !isDeepStrictEqual(test.simulation ?? {}, original.doc.simulation ?? {})
      || !isDeepStrictEqual(test.context ?? [], original.doc.context ?? [])) return 'not added: the recorded case lacks its original Story criteria, simulation, context or confirmed starting world.';
    const folder = join(root, 'tests'), stat = statOrNull(folder);
    if (stat && (!stat.isDirectory() || stat.isSymbolicLink()) || stat && !inRepo(root, 'tests')) return 'not added: tests/ must be a real folder inside the repository.';
    if (!stat) mkdirSync(folder);
    const id = slug(saved.id), story = slug(original.story);
    if (!id || !story) return 'not added: the recorded case has no safe identity.';
    const path = `tests/${story}-try-${id}.json`, file = join(root, path), existing = statOrNull(file);
    if (existing) {
      if (!existing.isFile() || existing.isSymbolicLink() || !inRepo(root, path)) return 'not added: the recorded case path is not a regular repository file.';
      if (isDeepStrictEqual(JSON.parse(readFileSync(file, 'utf8')), test)) return `already saved to ${path}`;
      return 'not added: a different case already uses this recorded run identity.';
    }
    writeFileSync(file, `${JSON.stringify(test, null, 2)}\n`, { flag: 'wx' });
    return `added to ${path} as step ${cleanText(test.steps[0].step_id)}`;
  } catch (error) { return `not added: pdd could not write the recorded case (${cleanText(error.code ?? error.message)}).`; }
};
export async function runDoorCall(descriptor, input, givenPorts = {}) {
  const ports = withDefaults(givenPorts), { root, origin, sessionId, login, prompt, operation } = descriptor;
  const store = stateFor(ports.env, root), identity = signIn(ports.gh, store);
  if (identity.login !== login) throw new Stop(5, `This Try belongs to ${login}. Run: gh auth switch -u ${login}`);
  if (runtimeOrigin({ PDD_RUNTIME_URL: origin }) !== origin) throw new Stop(2, 'The saved interpreter address is invalid.');
  const repo=store.read(join(store.dir,'repos',`${store.repoKey(root)}.json`));
  const saved=Object.entries(repo?.tries ?? {}).find(([,record])=>record.id===sessionId);
  if (saved) {
    const found=findTests({root}), test=found.tests.find(test=>test.path===saved[0]);
    const problem=tryPromptProblem(root,found,test,saved[1]);
    if (problem) throw new Stop(125,`${problem} Run pdd simulate STORY --new.`);
  }
  const runtime = new Runtime({ origin, token: identity.token, ports, signal: ports.signal });
  if (ports.signal?.aborted) throw new Stop(125, 'The local server stopped before the command was sent.');
  const id = ports.randomUUID(), request = { requestId: id, prompt, operation, input };
  const recovery = ` Read the result with: pdd test --read ${id}`;
  store.write(join(store.folder('calls'), `${id}.meta.json`), { id, origin, root, login, user_id: identity.userId, session_id: sessionId });
  store.posted(store.folder('tries'), id);
  let knownOutcome = false;
  try {
    const reply = await runtime.send(`/v1/try/${sessionId}/call`, { method: 'POST',
      headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(request) }, ports.postMs);
    if (reply.status && ![200, 202].includes(reply.status)) {
      knownOutcome = reply.status >= 400 && reply.status < 500 && reply.status != 408;
      throw new Stop(125, cleanText(reply.json?.error?.message || reply.json?.error?.code || `The interpreter refused the command (HTTP ${reply.status}).`, [identity.token]) + recovery);
    }
    const end = ports.now() + 900_000;
    let answer = null;
    for (;;) {
      if (ports.signal?.aborted) throw new Stop(125, 'The local server stopped; this command result is unknown. Do not repeat it automatically.' + recovery);
      if (answer && (!sameJob(answer, id, 'call') || (answer.session_id && answer.session_id !== sessionId))) throw new Stop(125, 'The interpreter returned a different command.' + recovery);
      if (answer && ENDED.has(answer.state)) {
        store.write(join(store.folder('tries'), `${id}.json`), answer);
        if (answer.state !== 'passed' || !isObject(answer.result?.program_result)) {
          knownOutcome = ['failed', 'refused', 'not_run'].includes(answer.state);
          const limit = stepTimeLimit(answer, { steps: [{ step_id: operation }], secrets: [identity.token] });
          const why = answer.result?.refusals?.[0];
          if (limit) throw Object.assign(new Stop(125, `${limit.message} ${limit.fix}${recovery}`), { tryUsage: tryUsage(answer, { cap: descriptor.callCap }) });
          throw Object.assign(new Stop(125, cleanText(why?.engine_message || why?.message || why?.code || 'The command result is unknown. Do not repeat it automatically.', [identity.token]) + (['failed', 'refused'].includes(answer.state) ? '' : recovery)), { tryUsage: tryUsage(answer, { cap: descriptor.callCap }) });
        }
        let observation = answer.result.report ?? {};
        if (typeof observation.action_id === 'string') {
          try {
            const state = await runtime.send(`/v1/try/${sessionId}/state`, { method: 'GET' }, GET_MS);
            const matched = state.status === 200 && Array.isArray(state.json?.actions)
              ? state.json.actions.find(action => action.action_id === observation.action_id) : null;
            if (matched) observation = { ...observation,
              ...(Object.hasOwn(matched, 'input_world') ? { input_world: matched.input_world } : {}),
              ...(Object.hasOwn(matched, 'world') ? { world: matched.world } : {}) };
          } catch { /* Observation is optional; the confirmed result remains confirmed. */ }
        }
        return { id, result: answer.result.program_result, usage: tryUsage(answer, { cap: descriptor.callCap }), inputWorld: observation.input_world, world: observation.world };
      }
      if (ports.now() >= end) throw new Stop(125, 'The command result is unknown. Do not repeat it automatically.' + recovery);
      await ports.sleep(ports.pollMs, ports.signal);
      if (ports.signal?.aborted) throw new Stop(125, 'The local server stopped; this command result is unknown. Do not repeat it automatically.' + recovery);
      const read = await runtime.get(id);
      if ([401, 403, 410].includes(read.status)) throw new Stop(125, cleanText(read.json?.error?.message || 'The command could not be read. Do not repeat it automatically.', [identity.token]) + recovery);
      answer = [200, 202].includes(read.status) ? read.json : null;
    }
  } catch (error) {
    if (!knownOutcome) error.unknownOutcome = true;
    throw error;
  }
}

export async function readTryOwner({ cwd = process.cwd(), story } = {}, givenPorts = {}) {
  const ports = withDefaults(givenPorts), root = repoRoot(cwd), found = findTests({ root }), store = stateFor(ports.env, root);
  const repo = store.repo(root), open = found.tests.filter(test => repo.tries?.[test.path]);
  let selected = story === undefined ? (open.length === 1 ? open : found.tests) : selectTests(found, [story]).selected;
  if (selected.length > 1) { const live = selected.filter(test => repo.tries?.[test.path]); if (live.length === 1) selected = live; }
  if (selected.length !== 1) throw new Error(`Choose one Story${story ? ` matching "${story}"` : ''}. Available: ${found.tests.map(test => `${test.story} (${test.path})`).join(', ') || 'none'}.`);
  const test = selected[0];
  async function openTry() {
    const code = await runTry({ cwd, words: [test.path], options: { '--no-open': true, '--no-wait': true } }, { ...ports, stdout: ports.stderr, interactive: false, agentBridge: false });
    if (code !== 0) throw new Error('The Try could not open. Read the progress on stderr and fix the reported problem.');
  }
  let record = repo.tries?.[test.path];
  if (!record) { await openTry(); record = store.repo(root).tries?.[test.path]; }
  if (!record) throw new Error('No confirmed Try is recorded. Run pdd simulate STORY.');
  const identity = signIn(ports.gh, store);
  if (record.login !== identity.login) throw new Error(`This Try belongs to ${record.login}. Run: gh auth switch -u ${record.login}`);
  if (runtimeOrigin({ PDD_RUNTIME_URL: record.origin }) !== record.origin) throw new Error('The saved interpreter address is invalid.');
  const promptProblem=tryPromptProblem(root,found,test,record);
  if (record.storyPath !== test.storyPath || record.story_sha256 && createHash('sha256').update(readFileSync(join(root, test.storyPath))).digest('hex') !== record.story_sha256 || promptProblem)
    throw new Error(`${promptProblem ?? 'The Story changed.'} Run pdd simulate STORY --new.`);
  let runtime = new Runtime({ origin: record.origin, token: identity.token, ports, signal: ports.signal });
  let metadata = await runtime.send(`/v1/try/${record.id}/model`, { method: 'GET' }, GET_MS);
  let paused = false;
  if (metadata.status === 409 && metadata.json?.error?.code === 'session-stopped') {
    const saved = await runtime.get(record.id);
    paused = saved.status === 200 && sameJob(saved.json, record.id, 'try') && saved.json.state === 'passed'
      && saved.json.result?.session?.state === 'paused';
  }
  if (paused || [404, 410].includes(metadata.status)) {
    await openTry(); record = store.repo(root).tries?.[test.path];
    runtime = new Runtime({ origin: record.origin, token: identity.token, ports, signal: ports.signal });
    metadata = await runtime.send(`/v1/try/${record.id}/model`, { method: 'GET' }, GET_MS);
  }
  if (metadata.status !== 200 || !Array.isArray(metadata.json?.entries)) throw new Error(cleanText(metadata.json?.error?.message || `The Try model could not be read${metadata.status ? ` (HTTP ${metadata.status})` : ''}. Read this Try again; no new run was sent.`, [identity.token]));
  const state = await runtime.send(`/v1/try/${record.id}/state`, { method: 'GET' }, GET_MS);
  return { root, test: record.seed_scenario ? { ...test, doc: record.seed_scenario } : test, record, model: metadata.json, actions: Array.isArray(state.json?.actions) ? state.json.actions : null,
    ...(state.status === 200 && Object.hasOwn(state.json ?? {}, 'world') ? { data: state.json.world } : { data_error: `Current saved data unavailable${state.status ? ` (HTTP ${state.status})` : ''}; no initial data was substituted.` }) };
}
