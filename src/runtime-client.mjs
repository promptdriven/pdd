// Generated from prompts/cli/runtime-client.prompt.md (sha256: b35cbf3b8f772c24b218b886d3b0412440535222267a311bd500ad568b752a4b).
import { spawn, spawnSync } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import { chmodSync, closeSync, lstatSync, mkdirSync, openSync, readFileSync, realpathSync, renameSync, writeFileSync, writeSync } from 'node:fs';
import { isDeepStrictEqual } from 'node:util';
import { homedir } from 'node:os';
import { basename, dirname, join, relative, resolve, sep } from 'node:path';
import { DRAFT_SERVER_TEXT, PreflightError, TEST_SCHEMA, captureSource, checkInput, fillHashes, sharedSourceFiles, whyNoTests, findTests, formatSize, gitFiles, otherFiles,
  preflight, readPrompt, selectTests, STALE_HINT, staleHint } from './runtime-preflight.mjs';
import { askApproval, lineReader, promptPath } from './prompt-approve.mjs';
import { OPEN_STATES, cleanText, exitCodeFor, projectAnswer, renderJson, renderText, summaryLine, validLink } from './runtime-output.mjs';

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
const POST_MS = 90_000, GET_MS = 30_000, LINT_MS = 120_000, TRY_MS = 300_000, MAX_READS = 8, PROGRESS_MS = 30_000;
// An agent (no terminal) waits at most 90 s, below the 2-minute default limit of Claude Code's shell tool; a person has no limit.
const AGENT_WAIT_MIN = 1.5;
// Under load a POST can time out and its job appear 3 to 4 min later: read a lost answer's ID for 5 min.
const LOST_READ_MS = 300_000;

class Stop extends Error { constructor(exitCode, message) { super(message); this.exitCode = exitCode; } }
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
  return {
    env, signal: ports.signal, ghPath: ports.ghPath, shell: ports.shell, serve: ports.serve, stdout: ports.stdout ?? process.stdout, stderr: ports.stderr ?? process.stderr, fetch: ports.fetch ?? globalThis.fetch,
    gh: ports.gh ?? (args => {
      const executable = authExecutable(env, ports.ghPath);
      return executable ? spawnSync(executable, args, { encoding: 'utf8', env, stdio: ['ignore', 'pipe', 'pipe'], timeout: 60_000 })
        : { status: null, error: { code: 'ENOENT' } };
    }),
    now: ports.now ?? Date.now, randomUUID: ports.randomUUID ?? randomUUID, pollMs: ports.pollMs ?? 2000, postMs: ports.postMs ?? POST_MS,
    interactive: ports.interactive ?? (!!process.stdout.isTTY && !!process.stdin.isTTY), watchMs: ports.watchMs ?? 5000, stdin: ports.stdin ?? process.stdin,
    sleep: ports.sleep ?? ((ms, signal) => new Promise(done => {
      const timer = setTimeout(done, ms);
      signal?.addEventListener('abort', () => { clearTimeout(timer); done(); }, { once: true });
    })),
    onInterrupt: ports.onInterrupt ?? (handler => { process.on('SIGINT', handler); return () => process.off('SIGINT', handler); }),
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
  const found = spawnSync('git', ['rev-parse', '--show-toplevel'], { cwd, encoding: 'utf8' });
  if (found.status !== 0 || !found.stdout.trim()) throw new Stop(2, 'pdd check and pdd try work in a Git repository. Run them inside your project.');
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

function stateFor(env, root) {
  const dir = resolve(env.PDD_STATE_DIR || join(env.HOME || homedir(), '.pdd', 'runtime'));
  if (inside(realish(dir), realpathSync(root))) throw new Stop(2, 'PDD_STATE_DIR is inside this repository. pdd keeps run state outside the repo. Choose another folder.');
  return new StateStore(dir);
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
    const temporary = `${path}.${process.pid}.tmp`;
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

function signIn(gh, store) {
  const token = gh(['auth', 'token']);
  if (token.error?.code === 'ENOENT') throw new Stop(5, 'Install the GitHub CLI, then run gh auth login');
  const value = token.status === 0 ? String(token.stdout ?? '').trim() : '';
  if (!value) throw new Stop(5, 'Run gh auth login');
  if (store) store.secrets = [value];
  const user = gh(['api', 'user', '--jq', '.login + " " + (.id|tostring)']);
  const [login, id] = user.status === 0 ? String(user.stdout ?? '').trim().split(' ') : [];
  if (!login || !/^\d+$/.test(id ?? '')) throw new Stop(5, 'pdd could not read your GitHub login (gh api user). Run gh auth status.');
  return { token: value, login, userId: id };
}

// Retry-After in seconds (1 to 300); no header or a bad one means 5 s.
function retryAfter(headers) {
  const raw = headers?.get?.('retry-after'), seconds = Number(raw);
  return raw && /^\d+$/.test(raw.trim()) ? Math.min(Math.max(seconds, 1), 300) * 1000 : 5000;
}

// HTTP to the runtime. The token stays in this object and in request headers only.
class Runtime {
  constructor({ origin, token, ports, signal }) { Object.assign(this, { origin, token, ports, signal }); }
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
    } catch { return { lost: true }; } finally { clearTimeout(timer); this.signal?.removeEventListener('abort', stop); }
  }
  post(path, request, tar, timeoutMs = this.ports.postMs) {
    const form = new FormData();
    form.set('request', new Blob([JSON.stringify(request)], { type: 'application/json' }), 'request.json');
    form.set('source', new Blob([tar], { type: 'application/x-tar' }), 'source.tar');
    return this.send(path, { method: 'POST', body: form }, timeoutMs);
  }
  get(id, timeoutMs = GET_MS) { return this.send(`/v1/runs/${id}`, { method: 'GET' }, timeoutMs); }
  reopen(id) { return this.send(`/v1/try/${id}/reopen`, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: '{}' }, this.ports.postMs); }
  stop(tryId, requestId) { return this.send(`/v1/try/${tryId}`, { method: 'DELETE', headers: { 'X-Request-Id': requestId } }, this.ports.postMs); }
}

// Answers that stop everything with one plain line and exit 5: a login not on the invite list (403 not-invited), and an
// old pdd that the server no longer serves (code update-required, any status, 0.1.6).
const UPDATE_TEXT = 'Please update pdd: npm install -g github:promptdriven/pdd#alpha';
function blockingAnswer(reply) {
  const json = reply.json, code = json?.code ?? json?.error?.code;
  if (code === 'update-required') {
    const said = cleanText(typeof json?.message === 'string' ? json.message : json?.error?.message).slice(0, 300);
    return said || UPDATE_TEXT;
  }
  if (reply.status !== 403 || code !== 'not-invited') return null;
  const login = typeof json.login === 'string' && /^[A-Za-z0-9-]{1,39}$/.test(json.login) ? json.login : null;
  return `Your GitHub login ${login ?? ''}${login ? ' ' : ''}is not on the PDD runtime invite list yet. Ask the PDD team to add you.`;
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
function checkCapacity(answer) {
  const report = answer?.result?.report;
  if (answer?.command !== 'check' || answer.state !== 'refused' || answer.usage?.calls !== 0 || report?.dispatch !== 'not_started'
    || report.provider_calls > 0 || report.accounting_complete === false || answer.usage?.accounting_complete === false
    || report.samples?.some(sample => sample?.steps?.some(step => step?.checks?.length))) return null;
  return [report.refusal, ...(Array.isArray(answer.result?.refusals) ? answer.result.refusals : [])].map(item => capacityDelay(item)).find(wait => wait !== null) ?? null;
}
function markBusy(context, row, wait) {
  Object.assign(row, { state: context.reading ? 'not_run' : 'waiting', busy: true, can_retry: true, calls: 0, refusals: [],
    checks: null, criteria: null, all_checks: [], failed_checks: [], why: null,
    retry_at: context.reading && Number.isFinite(row.retry_at) ? row.retry_at : context.ports.now() + wait, note: { code: 'check-busy', message: 'The runtime is busy. No checks ran for this attempt. Retry this batch later.' } });
  if (!context.reading) context.checkWindow = 1;
}

// One answer to a POST, as the row table of the spec.
function judgePost(reply, id, command, secrets) {
  if (reply.lost) return { kind: 'unknown', why: 'The answer to the request was lost.' };
  const stopLine = blockingAnswer(reply);
  if (stopLine) return { kind: 'stop', note: { code: 'blocked', message: stopLine }, blocked: true };
  const error = isObject(reply.json?.error) ? reply.json.error : null;
  if (command === 'lint' && reply.status === 503 && error?.code === 'lint-queue-full' && lintQueueWait(error) !== null) return { kind: 'busy', wait: lintQueueWait(error) };
  if (command === 'check' && [429, 503].includes(reply.status) && reply.json?.dispatch === 'not_started') {
    const wait = capacityDelay(error, reply.headers);
    if (wait !== null) return { kind: 'busy', wait, admission: reply.json };
  }
  const note = fallback => ({ code: cleanText(error?.code, secrets) || null, message: cleanText(error?.message, secrets) || fallback });
  if (reply.status === 200 || reply.status === 202) {
    return sameJob(reply.json, id, command) ? { kind: 'accepted', answer: reply.json } : { kind: 'unknown', why: 'The runtime answered with another request ID or command.' };
  }
  if (reply.status === 429) {
    return error?.code === 'server-full' && reply.json?.dispatch === 'not_started' ? { kind: 'busy', wait: retryAfter(reply.headers) }
      : { kind: 'not_run', note: note('The runtime is busy. Try again later.') };
  }
  if (gateText(reply)) return { kind: 'stop', note: { code: null, message: 'The runtime opens soon.' } };
  if (reply.status === 401) return { kind: 'stop', note: { code: cleanText(error?.code, secrets) || 'auth-required', message: 'Run gh auth login' } };
  if (reply.status === 503 && /^(?:pool-low-room|pool-copy-[a-z-]+|github-unavailable)$/.test(error?.code ?? '')) return { kind: 'not_run', note: note('Try again later.') };
  if ([400, 413, 415, 422].includes(reply.status) && error?.code) {
    return { kind: 'refused', refusal: { code: cleanText(error.code, secrets), section: null, message: cleanText(error.message, secrets) || null,
      engine_message: reply.json.details ? cleanText(JSON.stringify(reply.json.details), secrets) : null, hint: null } };
  }
  return { kind: 'unknown', why: `The runtime answered HTTP ${reply.status}.` };
}

// One answer to a GET of a known request ID.
function judgeGet(reply, id, command) {
  if (reply.lost) return { kind: 'again' };
  const stopLine = blockingAnswer(reply);
  if (stopLine) return { kind: 'blocked', message: stopLine };
  if (reply.status === 200) return sameJob(reply.json, id, command) ? { kind: 'state', answer: reply.json } : { kind: 'unknown', why: 'The runtime answered with another request ID or command.' };
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

function applyAnswer(row, answer, context) {
  const view = projectAnswer(answer, { origin: context.origin, secrets: context.secrets });
  Object.assign(row, { state: view.state, checks: view.checks, criteria: view.criteria, failed_checks: view.failed_checks, all_checks: view.all_checks,
    refusals: view.refusals, calls: view.calls, requested_model: view.requested_model, report_url: view.report_url ?? row.report_url,
    server_seconds: view.server_seconds, why: view.state === 'unknown' ? view.why : row.why, engine_sha: view.engine_sha, provider: view.provider,
    draft: view.draft ?? row.draft });
  const wait = checkCapacity(answer);
  if (wait !== null) markBusy(context, row, wait);
  else { row.busy = false; row.can_retry = false; row.note = null; }
  if (row.state === 'refused') addHints(row, context.root, context.visible);
  if (ENDED.has(row.state) && row.sent_at && !row.ended_at && !context.reading) row.ended_at = context.ports.now();
  row.seconds = !ENDED.has(row.state) ? null : row.sent_at && row.ended_at ? (row.ended_at - row.sent_at) / 1000 : row.server_seconds;
}

// Before a check of every story (cli 12b): about one AI call for each step plus the calls its prompt may make; the cap is the sum of max_calls.
function costLine(rows, root, visible) {
  const prompts = new Map(), callsOf = path => {
    if (!prompts.has(path)) prompts.set(path, readPrompt(root, visible, path));
    const calls = prompts.get(path)?.interface?.calls;
    return (Array.isArray(calls) ? calls : []).reduce((sum, call) => sum + (Number.isInteger(call?.max_calls) ? call.max_calls : 0), 0);
  };
  const about = rows.reduce((sum, row) => sum + row.steps.reduce((steps, step) => steps + 1 + callsOf(step?.entry_path), 0), 0);
  const most = rows.reduce((sum, row) => sum + row.max_calls, 0);
  return `Checking all ${rows.length} ${rows.length === 1 ? 'story' : 'stories'}: about ${about} AI call${about === 1 ? '' : 's'} (at most ${most}).`;
}

function batchRecord(context) {
  const { batch, origin, root, identity, capture, rows, lint, warnings } = context;
  return { version: 1, batch, origin, root, head: context.head, login: identity.login, user_id: identity.userId,
    source_sha256: capture.sha256, files: capture.files.map(file => file.path), bytes: capture.bytes, timeout_min: context.timeoutMin,
    created_at: new Date(context.startedAt).toISOString(), lint, warnings,
    rows: rows.map(row => ({ test: row.test, story: row.story, title: row.title, request_ids: row.request_ids, state: row.state,
      phase: row.phase, report_url: row.report_url, refusals: row.refusals, note: row.note ?? null, why: row.why ?? null,
      sent_at: row.sent_at ?? null, ended_at: row.ended_at ?? null, max_calls: row.max_calls, warnings: row.warnings, steps: row.steps, criteria_total: row.criteria_total,
      busy: !!row.busy, can_retry: !!row.can_retry, eligible: !!row.eligible, retry_at: row.retry_at ?? null,
      engine_sha: row.engine_sha ?? null, draft: !!row.draft })) };
}

function saveBatch(context) { if (context.batch) context.store.write(join(context.folder, 'batch.json'), batchRecord(context)); }
function saveAnswer(context, id, json) { if (isObject(json)) context.store.write(join(context.folder, `${id}.json`), json); }

async function postJob(context, path, command, request, row, timeoutMs) {
  const id = request.requestId;
  if (context.interrupted) return { kind: 'not_sent' };
  context.store.posted(context.folder, id);
  if (row) { row.request_ids.push(id); row.sent_at ??= context.ports.now(); row.state = 'sending'; row.calls = 'unknown'; }
  saveBatch(context);
  const reply = await context.runtime.post(path, request, context.capture.tar, timeoutMs);
  const verdict = judgePost(reply, id, command, context.secrets);
  if (verdict.answer) saveAnswer(context, id, verdict.answer);
  if (verdict.admission) context.store.write(join(context.folder, `${id}.admission.json`), verdict.admission);
  return verdict;
}

// POST one check and fold the answer into its row.
async function sendCheck(context, row) {
  if (context.interrupted || context.ports.now() >= context.deadline) return;
  row.attempts = (row.attempts ?? 0) + 1;
  row.sent_at = context.ports.now(); row.ended_at = null; row.retry_at = null; row.busy = false; row.can_retry = false;
  const request = { requestId: context.ports.randomUUID(), source_sha256: context.capture.sha256, scenario: row.test, max_calls: row.max_calls };
  const verdict = await postJob(context, '/v1/check', 'check', request, row, Math.max(1, Math.min(context.ports.postMs, context.deadline - context.ports.now())));
  if (verdict.kind === 'not_sent') Object.assign(row, { state: 'not_run', calls: 0, phase: 'local', note: { code: null, message: 'Stopped before sending.' } });
  else if (verdict.kind === 'accepted') applyAnswer(row, verdict.answer, context);
  else if (verdict.kind === 'busy') markBusy(context, row, verdict.wait);
  else if (verdict.kind === 'not_run') Object.assign(row, { state: 'not_run', note: verdict.note });
  else if (verdict.kind === 'stop') { Object.assign(row, { state: 'not_run', note: verdict.note }); context.stopped = verdict.note; if (verdict.blocked) context.blocked = verdict.note.message; }
  else if (verdict.kind === 'refused') Object.assign(row, { state: 'refused', refusals: [verdict.refusal] });
  // The agent's default limit caps this read too: pdd exits 3 and --read reads the same ID later.
  else Object.assign(row, { state: 'unknown', why: verdict.why, lost: true, read_until: context.agentLimit ? context.deadline
    : Math.max(Number.isFinite(context.deadline) ? context.deadline : 0, context.ports.now() + LOST_READ_MS) });
}

// GET one open row once.
async function readRow(context, row) {
  const id = row.request_ids.at(-1), end = row.lost ? row.read_until ?? context.deadline : context.deadline;
  const verdict = judgeGet(await context.runtime.get(id, Math.max(1, Math.min(GET_MS, (end ?? Infinity) - context.ports.now()))), id, 'check');
  if (verdict.kind === 'state') { saveAnswer(context, id, verdict.answer); applyAnswer(row, verdict.answer, context); row.lost = false; }
  else if (verdict.kind === 'unknown') Object.assign(row, { state: 'unknown', why: verdict.why, lost: false, final: true });
  else if (verdict.kind === 'auth') context.readStop = 'Run gh auth login';
  else if (verdict.kind === 'blocked') context.readStop = verdict.message;
  else if (verdict.kind === 'gate') context.readStop = 'The runtime opens soon.';
}

const isOpen = row => OPEN_STATES.has(row.state) || (row.state === 'unknown' && row.lost);
const occupiesSlot = row => OPEN_STATES.has(row.state) || (row.state === 'unknown' && row.request_ids?.length);

// One line every 30 s while checks run (Serhan: no timeouts, so pdd shows that it still waits).
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
  return (typeof seconds === 'number' && Number.isFinite(seconds) && seconds > 0 ? Math.min(30, Math.max(1, seconds)) : 5) * 1000;
}

function pendingLintMessage(context, answer) {
  return `Lint is still ${answer.state}. No checks were sent. ` + (context.batch
    ? `Read the result later with: pdd check --read ${context.batch}`
    : 'No Try was created. Lint uses no AI calls.');
}

async function runLint(context, complete = false) {
  const agent = context.agentLimit ?? !context.ports.interactive;
  const lintEnd = Math.min(context.deadline, context.startedAt + LINT_MS, agent ? context.startedAt + AGENT_WAIT_MIN * 60_000 : Infinity);
  let attempts = 0;
  const busy = () => ({ kind: 'not_run', note: { code: 'lint-busy', message: `The server stayed busy after ${attempts} lint attempts. No checks ran. Run the same pdd command again later.` } });
  const pause = async wait => {
    if (context.interrupted || attempts >= 3 || context.ports.now() + wait >= lintEnd) return false;
    line(context.ports.stderr, 'The server is busy. Waiting for a lint slot…');
    await context.ports.sleep(wait, context.signal);
    return !context.interrupted && context.ports.now() < lintEnd;
  };
  for (;;) {
    if (context.interrupted) return { kind: 'not_run', note: { code: null, message: 'Stopped before sending.' } };
    if (context.ports.now() >= lintEnd) return busy();
    const request = { requestId: context.ports.randomUUID(), source_sha256: context.capture.sha256, ...(complete ? { complete: true } : {}) };
    context.lint.request_ids.push(request.requestId); attempts++;
    const verdict = await postJob(context, '/v1/lint', 'lint', request, null, Math.max(1, Math.min(context.ports.postMs, lintEnd - context.ports.now())));
    if (verdict.kind === 'busy') { if (await pause(verdict.wait)) continue; return busy(); }
    if (verdict.kind === 'not_sent') return { kind: 'not_run', note: { code: null, message: 'Stopped before sending.' } };
    if (verdict.blocked) throw new Stop(5, verdict.note.message);
    if (verdict.kind !== 'accepted' && verdict.kind !== 'unknown') return verdict;
    // Unknown dispatch still reads only this ID; only a confirmed terminal capacity refusal permits another attempt.
    const readEnd = verdict.kind === 'unknown' && !agent ? Math.max(lintEnd, context.ports.now() + LOST_READ_MS) : lintEnd;
    let answer = verdict.answer ?? null, id = request.requestId, lost = false;
    while (!['passed', 'failed', 'refused', 'unknown'].includes(answer?.state) && context.ports.now() < readEnd && !context.interrupted) {
      await context.ports.sleep(Math.min(context.ports.pollMs, Math.max(0, readEnd - context.ports.now())), context.signal);
      if (context.interrupted || context.ports.now() >= readEnd) break;
      const read = judgeGet(await context.runtime.get(id, Math.max(1, Math.min(GET_MS, readEnd - context.ports.now()))), id, 'lint');
      if (read.kind === 'state') { answer = read.answer; saveAnswer(context, id, answer); }
      else if (read.kind === 'unknown') { lost = true; break; }
      else if (read.kind === 'blocked') throw new Stop(5, read.message);
      else if (read.kind === 'auth' || read.kind === 'gate') return { kind: 'stop', note: { code: null, message: read.kind === 'auth' ? 'Run gh auth login' : 'The runtime opens soon.' } };
    }
    if (!lost && answer?.state === 'refused') {
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
  const notSent = (state, extra) => { for (const row of sendable) Object.assign(row, { state, calls: 0, phase: 'lint', ...extra }); };
  if (context.interrupted) { notSent('not_run', { note: { code: null, message: 'Stopped before sending.' } }); return; }
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
  for (const [row, problem] of verdicts) Object.assign(row, { state: 'refused', phase: 'lint', refusals: [problem] });
  const toSend = sendable.filter(row => row.state === 'ready');
  line(ports.stderr, `${verdicts.size ? `Lint refused ${verdicts.size} of ${sendable.length} tests.` : 'Lint passed.'} Sent ${toSend.length} check${toSend.length === 1 ? '' : 's'} `
    + `at ${clock(ports.now())}: ${context.capture.files.length} files, ${formatSize(context.capture.bytes)}${context.otherNote ? ` ${context.otherNote}` : ''}.`);
  // Only now is there something to read again (lead, Oct 27): after lint passes, before the first check POST.
  if (toSend.length) line(ports.stderr, `If pdd stops, read the results with: pdd check --read ${context.batch}`);
  for (const row of toSend) row.eligible = true;
  await runScheduledChecks(context, rows, toSend);
}

async function runScheduledChecks(context, rows, toSend) {
  const { ports } = context;
  context.checkWindow ??= 5;
  for (const row of toSend) row.attempts = 0;
  let waitingShown = -1, shownAt = ports.now();
  const sentAt = shownAt;
  const readable = row => isOpen(row) && ports.now() < (row.lost ? row.read_until ?? context.deadline : context.deadline);
  while (!context.interrupted && !context.readStop) {
    // Never count an uncertain dispatched job as a free slot, even if it cannot currently be read.
    const active = rows.filter(occupiesSlot).length;
    const eligible = toSend.filter(row => ['ready', 'waiting'].includes(row.state) && (row.attempts ?? 0) < 3
      && (!row.retry_at || ports.now() >= row.retry_at));
    if (!context.stopped && ports.now() < context.deadline && active < context.checkWindow) {
      await Promise.all(eligible.slice(0, context.checkWindow - active).map(row => sendCheck(context, row)));
      saveBatch(context);
    }
    if (context.blocked && !rows.some(isOpen)) throw new Stop(5, context.blocked);
    const waiting = toSend.filter(row => row.state === 'waiting');
    if (waiting.length !== waitingShown) {
      if (waiting.length) line(ports.stderr, `Server busy: ${rows.filter(isOpen).length} checks running, ${waiting.length} waiting for a free slot.`);
      waitingShown = waiting.length;
    }
    for (const row of waiting.filter(row => row.attempts >= 3)) row.state = 'not_run';
    const pending = toSend.some(row => ['ready', 'waiting'].includes(row.state));
    if (pending && active >= context.checkWindow && !rows.some(readable)) break;
    if ((!pending || context.stopped || ports.now() >= context.deadline) && !rows.some(readable)) break;
    if (ports.now() - shownAt >= PROGRESS_MS) { shownAt = ports.now(); line(ports.stderr, progressLine(rows, shownAt - sentAt)); }
    const end = Math.max(context.deadline, ...rows.filter(row => row.lost).map(row => row.read_until ?? 0));
    await ports.sleep(Math.max(0, Math.min(ports.pollMs, end - ports.now())), context.signal);
    if (context.interrupted) break;
    await eachLimited(rows.filter(readable), MAX_READS, row => readRow(context, row));
    saveBatch(context);
  }
  const stoppedEarly = context.interrupted || !!context.readStop;
  context.timedOut = !stoppedEarly && ports.now() >= context.deadline && rows.some(isOpen);
  for (const row of toSend) {
    if (['ready', 'waiting'].includes(row.state)) Object.assign(row, { state: 'not_run', calls: 0, busy: true, can_retry: true,
      phase: row.request_ids.length ? 'server' : 'local', note: { code: 'check-busy', message: row.request_ids.length
        ? 'The runtime stayed busy. No checks ran for this attempt. Retry this batch later.' : 'Held locally; this check was not sent. Retry this batch later.' } });
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
  const { ports } = context, exitCode = exitCodeFor(rows, { interrupted: context.interrupted, lintUnknown: context.lintUnknown || context.lintPending });
  const engines = [...new Set(rows.map(row => row.engine_sha).filter(sha => sha && !sameEngine(sha)))].filter(sha => firstToday(context, sha));
  const warnings = [...(context.warnings ?? []), ...engines.map(sha => `Warning: the runtime engine is ${cleanText(sha).slice(0, 12)}, but pdd's local checks copy engine ${ENGINE_SHA.slice(0, 12)}. The engine stays the judge.`)];
  const summary = renderJson({ batch: context.batch ?? null, repo: context.root, sourceSha256: context.capture?.sha256 ?? null, rows, exitCode, summaryLine: summaryLine(rows),
    warnings: [...warnings, ...rows.flatMap(row => (row.warnings ?? []).map(text => `${row.test}: ${text}`))] });
  if (context.folder) context.store.write(join(context.folder, 'summary.json'), summary);
  if (context.batch && rows.some(row => row.can_retry)) line(ports.stderr, `Retry only unstarted checks with: pdd check --retry ${context.batch}`);
  if (context.readStop) line(ports.stderr, context.readStop);
  if (context.stopped && !context.json) line(ports.stderr, context.stopped.message);
  const scrub = text => (context.secrets ?? []).reduce((value, secret) => secret ? value.split(secret).join('[secret]') : value, text);
  if (context.json) line(ports.stdout, scrub(JSON.stringify(summary)));
  else ports.stdout.write(scrub(renderText({ batch: context.batch, rows, warnings, details: context.details, timeoutMin: context.timeoutMin,
    interrupted: context.interrupted || !!context.readStop, reading: !!context.reading, exitCode, secrets: context.secrets, ...extra })));
  // At the time limit the jobs keep running on the server.
  if (exitCode === 3 && context.batch) line(ports.stderr, context.timedOut ? `Still running. Read the results later with: pdd check --read ${context.batch}`
    : `If pdd stops, read the results with: pdd check --read ${context.batch}`);
  return exitCode;
}

function runFiles(cwd, words, options, ports) {
  const { root, found, normalized } = localSetup(cwd, words);
  const tests = select(found, normalized, root).map(test => test.path);
  const appMap = options['--app-map'] === undefined ? null : appMapFor(found, options['--app-map'], cwd, root, ports.stderr);
  const capture = captureSource(root, { tests, appMap });
  const other = otherFiles(capture.files, found), width = Math.max(0, ...capture.files.map(file => file.path.length));
  for (const file of capture.files) line(ports.stdout, `  ${file.path.padEnd(width)}  ${file.size} bytes`);
  line(ports.stdout, `${capture.files.length} files, ${formatSize(capture.bytes)} (${capture.bytes} bytes). ${other.length} of them are not prompt, story or test files.`);
  return 0;
}

// pdd check --lint (Serhan: runtime logic belongs on the server): only the server's lint (0 AI calls) on the captured files.
// Locally only the privacy and capture checks run (secret names, links, size and file limits); the engine rules are the server's.
async function runLintOnly(context, cwd, words, setRelease) {
  const { ports } = context, origin = runtimeOrigin(ports.env), { root, found, normalized } = localSetup(cwd, words);
  const selected = select(found, normalized, root);
  const rows = selected.map(test => ({ test: test.path, story: test.story, title: test.title, state: 'ready', phase: 'lint',
    refusals: [], request_ids: [], warnings: [], steps: Array.isArray(test.doc?.steps) ? test.doc.steps.filter(isObject) : [] }));
  const capture = captureSource(root, { tests: selected.map(test => test.path), appMap: null }), identity = signIn(ports.gh, context.store), startedAt = ports.now(), batch = batchId(startedAt, ports.randomUUID);
  Object.assign(context, { origin, visible: found.visible, capture, identity, batch, startedAt, deadline: startedAt + LINT_MS, rows, head: null,
    secrets: [identity.token], lint: { request_ids: [], state: null }, timeoutMin: LINT_MS / 60_000 });
  context.folder = context.store.folder('batches', batch);
  saveBatch(context);
  setRelease(interruptible(context));
  context.runtime = new Runtime({ origin, token: identity.token, ports, signal: context.signal });
  const lint = await runLint(context, true);
  if (lint.kind === 'pending') throw new Stop(3, pendingLintMessage(context, lint.answer));
  if (lint.kind === 'not_run' || lint.kind === 'stop') throw new Stop(5, `${lint.note.message}${lint.note.code && lint.note.code !== 'blocked' ? ` (${lint.note.code})` : ''}`);
  const answer = lint.answer, program = answer?.result?.report?.program;
  const problems = lint.kind === 'refused' ? [{ ...lint.refusal, path: null }]
    : (answer?.state === 'refused' && !isObject(program) ? projectAnswer(answer, { origin, secrets: context.secrets }).refusals.map(item => ({ ...item, path: null })) : []);
  if (!problems.length && (context.interrupted || lint.kind === 'unknown' || !['passed', 'failed', 'refused'].includes(answer?.state) || !isObject(program))) {
    throw new Stop(3, 'The lint result is unknown. Run pdd check --lint again; a lint uses no AI calls.');
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
    line(ports.stdout, JSON.stringify({ batch, repo: root, exit_code: exitCode, lint_state: exitCode === 0 ? 'passed' : 'refused', summary_line: summary, problems,
      rows: rows.map(row => ({ story: row.story, title: row.title, test: row.test, state: row.state, refusals: row.refusals })), warnings: found.warnings }));
    return exitCode;
  }
  const out = [];
  if (problems.length) {
    out.push('Lint problems (from the PDD runtime):');
    for (const item of problems) out.push(`  ${[item.code, item.path, item.section, item.message].filter(Boolean).join('  ')}`, ...(item.hint ? [`    ${item.hint}`] : []));
  }
  for (const row of rows) out.push(`  ${row.test}  ${row.state === 'passed' ? 'passes lint' : `refused: ${row.refusals.map(item => item.code).join(', ')}`}`);
  out.push(summary, ...found.warnings);
  ports.stdout.write(`${out.join('\n')}\n`);
  return exitCode;
}

function runFillHash(root, ports) {
  const result = fillHashes({ root });
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
    || row.note?.code === 'lint-pending' || /lint result is unknown/i.test(row.note?.message ?? '')));
  if (!held.length) return;
  let answer = context.store.read(join(context.folder, `${id}.json`));
  if (!sameJob(answer, id, 'lint') || !['passed', 'failed', 'refused'].includes(answer.state)) {
    const read = judgeGet(await context.runtime.get(id), id, 'lint');
    if (read.kind === 'blocked') throw new Stop(5, read.message);
    if (read.kind === 'auth') throw new Stop(5, 'Run gh auth login');
    if (read.kind === 'gate') throw new Stop(5, 'The runtime opens soon.');
    answer = read.kind === 'state' ? read.answer : null;
    if (answer) saveAnswer(context, id, answer);
  }
  const unknown = () => {
    Object.assign(lint, { state: answer?.state ?? 'unknown', pending: false, unknown: true });
    context.lintUnknown = true;
    for (const row of held) Object.assign(row, { state: 'not_run', calls: 0, phase: 'lint', refusals: [],
      note: { code: null, message: 'The lint result is unknown, so pdd sent no checks.' } });
  };
  if (['queued', 'running'].includes(answer?.state)) {
    Object.assign(lint, { state: answer.state, pending: true, unknown: false });
    context.lintPending = true;
    for (const row of held) Object.assign(row, { state: 'not_run', calls: 0, phase: 'lint', refusals: [],
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
    Object.assign(row, { state: 'not_run', calls: 0, phase: 'lint', refusals: [], note: null });
    if (problem || (!verdicts && !busy && refusals.length)) {
      Object.assign(row, { state: 'refused', refusals: problem ? [problem] : refusals });
    } else {
      row.note = busy ? { code: 'lint-busy', message: 'The saved lint could not get a slot. No checks ran. Run the same command again later.' }
        : { code: 'lint-finished', message: `The saved lint finished${refusals.length ? ' with refusals' : ''}. No checks were sent. `
          + (refusals.length ? refusals.map(item => item.message || item.code).join(' ') + ' ' : '')
          + 'Run a fresh pdd check command to start checks.' };
    }
  }
}

async function runRead(context, batchWord, quiet = false) {
  const { store, ports, root } = context;
  const name = batchWord ?? store.repo(root).last_batch;
  if (!name || !BATCH.test(name)) throw new Stop(2, name ? 'BATCH looks like 20261027-092747-k3f9.' : 'No saved check for this repository. Run pdd check first.');
  context.folder = join(store.dir, 'batches', name);
  const saved = store.read(join(context.folder, 'batch.json'));
  if (!saved) throw new Stop(2, `No saved batch ${name}.`);
  if (saved.root !== root) throw new Stop(2, 'This saved batch belongs to a different repository.');
  const identity = signIn(ports.gh, context.store);
  if (identity.login !== saved.login) throw new Stop(5, `These runs belong to ${saved.login}. Run: gh auth switch -u ${saved.login}`);
  Object.assign(context, { batch: name, origin: saved.origin, identity, secrets: [identity.token], warnings: saved.warnings ?? [], timeoutMin: saved.timeout_min ?? null,
    capture: { sha256: saved.source_sha256, files: saved.files.map(path => ({ path })), bytes: saved.bytes }, lint: saved.lint, head: saved.head, startedAt: Date.parse(saved.created_at) });
  context.runtime = new Runtime({ origin: saved.origin, token: identity.token, ports, signal: context.signal });
  const rows = saved.rows.map(row => ({ ...row, checks: null, failed_checks: [], all_checks: [],
    ...(!row.request_ids?.length && ['not_run', 'refused', 'ready'].includes(row.state) ? { calls: 0, phase: 'local' } : {}) }));
  Object.assign(context, { rows, visible: findTests({ root }).visible, reading: true });
  // A pdd that was killed can leave rows that never got an answer: read them if they were posted.
  for (const row of rows) if (['ready', 'sending', 'waiting'].includes(row.state)) {
    if (row.request_ids.length) row.state = 'unknown';
    else Object.assign(row, { state: 'not_run', calls: 0, phase: 'local', note: { code: null, message: 'pdd stopped before sending this check.' } });
  }
  await readUnsentLint(context, rows);
  await eachLimited(rows, MAX_READS, async row => {
    const id = row.request_ids.at(-1);
    if (!id || row.phase !== 'server') return;
    const admission = store.read(join(context.folder, `${id}.admission.json`));
    if (admission?.dispatch === 'not_started') {
      const wait = capacityDelay(admission.error);
      if (wait !== null) { markBusy(context, row, wait); return; }
    }
    if (ports.now() >= (context.deadline ?? Infinity) || context.interrupted) return;
    const answer = store.read(join(context.folder, `${id}.json`));
    if (answer && ['passed', 'failed', 'refused'].includes(answer.state) && sameJob(answer, id, 'check')) { applyAnswer(row, answer, context); return; }
    if (['queued', 'running', 'unknown'].includes(row.state)) {
      row.lost = true;
      await readRow(context, row);
      if (row.state === 'unknown' && row.lost) row.why ??= 'pdd could not read this run yet.';
    } else if (answer) applyAnswer(row, answer, context);
  });
  saveBatch(context);
  return quiet ? rows : printResult(context, rows);
}

async function runRetry(context, name, options) {
  const { ports } = context;
  const timeout = options['--timeout'] === undefined ? AGENT_WAIT_MIN : Number(options['--timeout']);
  context.deadline = ports.now() + timeout * 60_000;
  const rows = await runRead(context, name, true);
  const capture = captureSource(context.root, { tests: rows.map(row => row.test), appMap: null });
  if (capture.sha256 !== context.capture.sha256) throw new Stop(2, 'The saved source no longer matches: source changed. Start a fresh selected pdd check instead.');
  const lintId = context.lint?.request_ids?.at(-1), lint = lintId && context.store.read(join(context.folder, `${lintId}.json`));
  if (!lint || !sameJob(lint, lintId, 'lint') || lint.state !== 'passed' || context.lint.unknown || context.lint.pending)
    throw new Stop(2, 'The saved lint cannot authorize recovery. Start a fresh selected pdd check.');
  const selected = rows.filter(row => row.can_retry && row.eligible && (row.busy || !row.request_ids.length));
  Object.assign(context, { capture, reading: false, timeoutMin: timeout });
  for (const row of selected) row.state = row.retry_at > ports.now() ? 'waiting' : 'ready';
  if (selected.length) await runScheduledChecks(context, rows, selected);
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
  else row.why = read.why ?? (read.kind === 'auth' ? 'Run gh auth login' : 'pdd could not read this run.');
  return printResult(context, [row], { recovery: `pdd check --request '${id}'` });
}

// pdd check. Returns the exit code.
export async function runCheck({ words = [], options = {}, cwd = process.cwd() } = {}, givenPorts = {}) {
  const ports = withDefaults(givenPorts);
  const context = { ports, json: options['--json'] === true, details: options['--details'] === true, interrupted: false, warnings: [] };
  let release = () => {};
  try {
    const modes = ['--read', '--retry', '--fill-hash', '--files', '--request', '--lint'].filter(name => options[name] !== undefined);
    const others = Object.keys(options).filter(name => !modes.includes(name) && !(modes[0] === '--retry' && ['--json', '--details', '--timeout'].includes(name)) && !(name === '--json' && ['--read', '--request', '--lint'].includes(modes[0])) && !(name === '--app-map' && modes[0] === '--files'));
    if (modes.length > 1 || (modes.length && others.length) || (['--fill-hash', '--request', '--retry'].includes(modes[0]) && words.length)
      || (modes[0] === '--read' && words.length > 1) || (!modes.length && options['--app-map'] !== undefined)) throw new Stop(2, 'This mix of options does not work together. Run pdd check --help.');
    if (modes[0] === '--request') { release = interruptible(context); return await runRequest(context, options['--request']); }
    const root = repoRoot(cwd);
    if (modes[0] === '--fill-hash') return runFillHash(root, ports);
    if (modes[0] === '--files') return runFiles(cwd, words, options, ports);
    context.root = root; context.store = stateFor(ports.env, root);
    if (modes[0] === '--retry') { release = interruptible(context); return await runRetry(context, options['--retry'], options); }
    if (modes[0] === '--read') { release = interruptible(context); return await runRead(context, words[0]); }
    if (modes[0] === '--lint') return await runLintOnly(context, cwd, words, value => { release = value; });
    return await runBatch(context, cwd, words, options, value => { release = value; });
  } catch (error) {
    if (error instanceof Stop || error instanceof PreflightError) { line(ports.stderr, error.message); return error.exitCode; }
    throw error;
  } finally { release(); }
}

async function runBatch(context, cwd, words, options, setRelease) {
  const { ports } = context;
  const origin = runtimeOrigin(ports.env);
  const { root, found, normalized } = localSetup(cwd, words);
  context.visible = found.visible; context.origin = origin;
  // A person has no time limit (Serhan: no timeouts); an agent has 90 s; --timeout MIN overrides both.
  context.agentLimit = options['--timeout'] === undefined && !ports.interactive;
  context.timeoutMin = options['--timeout'] !== undefined ? Number(options['--timeout']) : context.agentLimit ? AGENT_WAIT_MIN : null;
  const selected = select(found, normalized, root);
  const checked = preflight({ root, found, selected });
  const rows = localRows(checked.rows);
  if (options['--max-calls'] !== undefined) for (const row of rows) row.max_calls = Number(options['--max-calls']);
  context.warnings = [...found.warnings, ...checked.warnings, ...sharedSourceFiles(root, found.visible)];
  if (!rows.some(row => row.state === 'ready')) return printResult(context, rows);
  if (!words.length) line(ports.stderr, costLine(rows.filter(row => row.state === 'ready'), root, found.visible));
  const capture = captureSource(root, { tests: selected.map(test => test.path), appMap: null });
  context.otherNote = otherNote(otherFiles(capture.files, found).length);
  const identity = signIn(ports.gh, context.store);
  const startedAt = ports.now(), batch = batchId(startedAt, ports.randomUUID);
  const head = spawnSync('git', ['rev-parse', 'HEAD'], { cwd: root, encoding: 'utf8' });
  Object.assign(context, { capture, identity, batch, startedAt, deadline: context.timeoutMin ? startedAt + context.timeoutMin * 60_000 : Infinity, rows,
    head: head.status === 0 ? head.stdout.trim() : null, secrets: [identity.token], lint: { request_ids: [], state: null } });
  context.folder = context.store.folder('batches', batch);
  saveBatch(context);
  const repoState = context.store.repo(root);
  context.store.saveRepo(root, { ...repoState, last_batch: batch });
  setRelease(interruptible(context));
  context.runtime = new Runtime({ origin, token: identity.token, ports, signal: context.signal });
  await checkBatch(context, rows);
  saveBatch(context);
  return printResult(context, rows);
}

// ---- pdd try ----

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
  if (selected.length !== 1) throw new Stop(2, ['pdd try needs one story. Choose one:', ...storyList({ tests: selected })].join('\n'));
  return selected[0];
}

async function readUntil(context, id, command, isDone, ms) {
  const end = context.ports.now() + ms;
  let last = null;
  for (;;) {
    const read = judgeGet(await context.runtime.get(id), id, command);
    if (read.kind === 'state') { last = read.answer; context.store.write(join(context.store.folder('tries'), `${id}.json`), last); if (isDone(last)) return { answer: last }; }
    else if (read.kind === 'unknown') return { unknownWhy: read.why };
    else if (read.kind === 'auth') throw new Stop(5, 'Run gh auth login');
    else if (read.kind === 'blocked') throw new Stop(5, read.message);
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

const otherNote = count => count ? `(${count} ${count === 1 ? 'is' : 'are'} not prompt, story or test files; run \`pdd check --files\` to see them)` : '';

// Paused sessions require an explicit owner reopen; only running sessions have a ready link.
const LIVE_SESSION = new Set(['running', 'paused']);
function tryLink(answer, origin) {
  return answer?.state === 'passed' && answer.result?.session?.state === 'running' ? validLink(answer.result?.url, origin, 'try') : null;
}

async function reopenTry(context, record, test) {
  const target = /^[A-Za-z0-9_./-]+$/.test(test.path) ? test.path : "'" + test.path.replace(/'/g, "'\"'\"'") + "'";
  const again = `pdd try ${target}`;
  if (context.interrupted) throw new Stop(3, 'Stopped before reopening the Try.');
  const reply = await context.runtime.reopen(record.id);
  const blocked = blockingAnswer(reply);
  if (blocked) throw new Stop(5, blocked);
  if (reply.status === 401) throw new Stop(5, 'Run gh auth login');
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
    || (answer.state === 'passed' && ['stopped', 'stopping', 'unknown'].includes(answer.result?.session?.state)), TRY_MS);
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
  if (verdict.kind === 'refused') throw new Stop(4, `The runtime refused to stop this Try: ${verdict.refusal.message} (${verdict.refusal.code})`);
  if (verdict.kind !== 'accepted') throw new Stop(3, 'The stop result is unknown. Run pdd try --stop again later; it sends a new stop request.');
  const done = verdict.answer.state === 'passed' ? { answer: verdict.answer } : await readUntil(context, id, 'stop', answer => ENDED.has(answer.state), TRY_MS);
  if (done.answer?.state !== 'passed') throw new Stop(done.answer?.state === 'refused' ? 4 : 3, 'The Try did not confirm that it stopped. Run pdd try --stop again later.');
}

// pdd try. Returns the exit code.
export async function runTry({ words = [], options = {}, cwd = process.cwd() } = {}, givenPorts = {}) {
  const ports = withDefaults(givenPorts), context = { ports, interrupted: false, doorMode: !!(options['--cli'] || options['--serve']) };
  let release = () => {};
  try {
    const doorModes = ['--cli', '--serve', '--save-last'].filter(key => options[key]);
    if (doorModes.length > 1 || (options['--shell'] && !options['--cli']) || (doorModes.length && options['--stop'])
      || (options['--save-last'] && (words.length || Object.keys(options).length !== 1))) throw new Stop(2, 'Choose one of --cli, --serve, --save-last or --stop; --shell needs --cli.');
    if (options['--save-last']) {
      const root = repoRoot(cwd), store = stateFor(ports.env, root), identity = signIn(ports.gh, store);
      return await (await import('./try-doors.mjs')).saveLast({ root, store, identity, ports });
    }
    if (options['--stop'] && (options['--tab'] || options['--new'] || options['--no-open'] || options['--no-wait'] || options['--app-map'] !== undefined)) throw new Stop(2, 'pdd try --stop takes only a STORY. Run pdd try --help.');
    if (words.length > 1) throw new Stop(2, 'pdd try takes one STORY.');
    const origin = runtimeOrigin(ports.env);
    if (options['--stop']) return await stopByName(context, cwd, words, origin);
    const { root, found, normalized } = localSetup(cwd, words), store = stateFor(ports.env, root);
    const appMap = appMapFor(found, options['--app-map'], cwd, root, ports.stderr);
    const test = oneTest(found, normalized, root), repoState = store.repo(root), record = repoState.tries?.[test.path];
    Object.assign(context, { root, store, origin, visible: found.visible, appMap, cwd: realpathSync(cwd), seedTest: { path: test.path, storyPath: test.storyPath } });
    const checked = preflight({ root, found, selected: [test] }), row = localRows(checked.rows)[0];
    if (row.state === 'refused') {
      if (options['--cli'] || options['--serve']) throw new Stop(125, row.refusals?.map(r => r.message || r.code).join('; ') || 'The Story input was refused.');
      line(ports.stdout, renderText({ rows: [row], exitCode: 4 })); return 4;
    }
    const capture = captureSource(root, { tests: [test.path], appMap }), note = otherNote(otherFiles(capture.files, found).length);
    const identity = signIn(ports.gh, context.store);
    Object.assign(context, { capture, identity, secrets: [identity.token], startedAt: ports.now(), deadline: ports.now() + TRY_MS, lint: { request_ids: [], state: null },
      batch: null, rows: [row], timeoutMin: TRY_MS / 60_000, head: null });
    context.folder = store.folder('tries');
    release = interruptible(context);
    context.runtime = new Runtime({ origin, token: identity.token, ports, signal: context.signal });
    if (record) {
      if ((options['--cli'] || options['--serve']) && record.login && record.login !== identity.login) throw new Stop(125, `This Try belongs to ${record.login}. Run: gh auth switch -u ${record.login}`);
      if ((options['--cli'] || options['--serve']) && record.origin !== origin) throw new Stop(2, 'This Try belongs to another runtime address. Use its original PDD_RUNTIME_URL, or stop it first.');
      const read = judgeGet(await context.runtime.get(record.id), record.id, 'try');
      if (read.kind === 'auth') throw new Stop(5, 'Run gh auth login');
      if (read.kind === 'blocked') throw new Stop(5, read.message);
      if (read.kind === 'gate') throw new Stop(5, 'The runtime opens soon.');
      let answer = read.kind === 'state' ? read.answer : null, link = tryLink(answer, origin);
      const live = answer?.state === 'passed' && LIVE_SESSION.has(answer.result?.session?.state);
      // 404 (unknown to the server) and 410 (expired) count as ended: the record goes and a new Try is made.
      // A Try the server lost (state unknown, for example after a restart) counts as ended too: a new Try costs no AI calls.
      const ended = read.kind === 'missing' || read.status === 410 || ['failed', 'refused', 'unknown'].includes(answer?.state)
        || (answer?.state === 'passed' && ['stopped', 'stopping', 'unknown'].includes(answer.result?.session?.state));
      if (live && !options['--new'] && (options['--app-map'] !== undefined || options['--tab'])) {
        throw new Stop(2, `A Try for "${test.title}" is already open. --app-map and --tab apply only to a new Try: run pdd try ${test.story} --new (it stops the open Try first).`);
      }
      if (live && options['--serve'] && !options['--new']) {
        let matches = false;
        try {
          const hashes = record.prompt_hashes;
          matches = isObject(hashes) && Object.keys(hashes).length > 0
            && test.doc.steps.every(step => typeof hashes[step.entry_path] === 'string')
            && Object.entries(hashes).every(([path, expected]) => found.visible.has(path)
              && createHash('sha256').update(readFileSync(join(root, path))).digest('hex') === expected);
        } catch { /* A removed prompt cannot match the uploaded source. */ }
        if (!matches) throw new Stop(125, 'A prompt changed or this Try has no source record. Run pdd try STORY --serve --new.');
      }
      if (answer?.state === 'passed' && answer.result?.session?.state === 'paused' && !options['--new']) {
        if (!validLink(answer.result?.url, origin, 'try')) throw new Stop(3, refusedLink(answer, origin));
        answer = await reopenTry(context, record, test); link = tryLink(answer, origin);
      }
      if (link && !options['--new']) {
        if (!record.storyPath && record.story !== test.story) throw new Stop(4, 'The original Try story changed. Restore its test file, or use --new to start a new Try.');
        context.seedTest.storyPath = record.storyPath ?? test.storyPath;
        return await showTry(context, test, link, options, record.id, true);
      }
      if (!link && answer?.state === 'passed' && LIVE_SESSION.has(answer.result?.session?.state) && !options['--new']) throw new Stop(3, refusedLink(answer, origin));
      // A Try that may still start or run is never made twice by accident.
      if (!ended && !options['--new']) {
        throw new Stop(3, `The last Try for "${test.title}" is not ready or its state is unknown. Run pdd try ${test.story} again later, or pdd try ${test.story} --new to stop it and make a new one.`);
      }
      if (!ended) await stopTry(context, record);
      delete repoState.tries[test.path];
      store.saveRepo(root, repoState);
    }
    await checkLint(context, [row]);
    if (context.interrupted) throw new Stop(3, 'Stopped before the Try was made. Nothing new was sent.');
    if (row.state !== 'ready') {
      if (options['--cli'] || options['--serve']) throw new Stop(125, row.refusals?.map(r => r.message || r.code).join('; ') || 'The Story did not pass lint.');
      return printTryProblem(context, row);
    }
    const request = { requestId: ports.randomUUID(), source_sha256: capture.sha256, seed: test.path, ...(appMap ? { app_map: appMap } : {}),
      tab: options['--tab'] ?? (options['--cli'] ? 'terminal' : appMap ? 'screen' : 'call') };
    store.saveRepo(root, { ...repoState, tries: { ...repoState.tries, [test.path]: { id: request.requestId, story: test.story, storyPath: test.storyPath, title: test.title, origin, login: identity.login, prompt_hashes: Object.fromEntries(capture.files.map(file => file.path).filter(path => path.endsWith('.prompt.md')).map(path => [path, createHash('sha256').update(readFileSync(join(root, path))).digest('hex')])) } } });
    store.posted(context.folder, request.requestId);
    if (note) line(ports.stderr, `Sent ${capture.files.length} files ${note}.`);
    const reply = await context.runtime.post('/v1/try', request, capture.tar), verdict = judgePost(reply, request.requestId, 'try', context.secrets);
    if (verdict.answer) store.write(join(context.folder, `${request.requestId}.json`), verdict.answer);
    if (verdict.kind !== 'accepted') {
      if (verdict.kind !== 'unknown') { delete repoState.tries[test.path]; store.saveRepo(root, repoState); }
      if (reply.status === 429) throw new Stop(5, 'Too many Try links are open. Stop one with pdd try --stop');
      if (verdict.kind === 'refused') return trySetupRefused(context, test, appMap, [{ ...reply.json.error, ...verdict.refusal }], null);
      if (verdict.blocked) throw new Stop(5, verdict.note.message);
      if (verdict.kind === 'not_run' || verdict.kind === 'stop') throw new Stop(5, `${verdict.note.message}${verdict.note.code ? ` (${verdict.note.code})` : ''}`);
      throw new Stop(3, `The Try setup result is unknown. Run pdd try ${test.story} again later: it reads this Try first and sends nothing new while it runs.`);
    }
    const done = ENDED.has(verdict.answer.state) ? { answer: verdict.answer }
      : await readUntil(context, request.requestId, 'try', answer => ENDED.has(answer.state), TRY_MS);
    const link = tryLink(done.answer, origin);
    if (link) return await showTry(context, test, link, options, request.requestId);
    if (done.answer?.state === 'unknown') {
      delete repoState.tries[test.path];
      store.saveRepo(root, repoState);
      throw new Stop(3, `The Try setup did not finish on the server (its state is unknown; the server may have restarted). It used no AI calls. Run pdd try ${test.story} to make a new Try.`);
    }
    if (done.unknownWhy || done.open || !done.answer) {
      throw new Stop(3, `The Try setup is not finished yet. Run pdd try ${test.story} again later; it reads this Try first and makes no second one.`);
    }
    // A ready Try with a bad link stays recorded, so pdd try --stop can still end it; pdd never prints that link.
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
    if (options['--cli'] || options['--serve'] || options['--save-last']) { line(ports.stderr, `pdd try: ${cleanText(error.message || 'The Try could not start.', context.secrets ?? [])}`); return error.exitCode === 2 ? 2 : 125; }
    if (error instanceof Stop || error instanceof PreflightError) { line(ports.stderr, error.message); return error.exitCode; }
    throw error;
  } finally { release(); }
}

// pdd try --stop [STORY]: find the Try by its story name in the state record, so it works on any branch (real-user issue 14).
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
    throw new Stop(125, refusal?.reason || refusal?.message || refusal?.code || 'The runtime refused lint.');
  }
  if (!verdicts) throw new Stop(3, 'The lint result is unknown, so pdd made no Try link. Run pdd try again later.');
  for (const [row, problem] of verdicts) Object.assign(row, { state: 'refused', phase: 'lint', refusals: [problem] });
}

// A refused Try setup is not a check (runtime team, Oct 27): two plain lines with what was refused, why and the fix; no table.
const APP_MAP_RULES = { 'ambiguous-handler': 'on one screen, all taps of one kind must match by the same key',
  'template-reference-schema': 'a field that gets a value from the screen ($ref) must be a plain {"type": "string"}' };
const GENERIC_REFUSAL = /^The runtime refused this job\b/;
function trySetupRefused(context, test, appMap, refusals, reportUrl) {
  if (context.doorMode) throw new Stop(125, refusals.map(item => item.reason || item.engine_message || item.message || item.code).filter(Boolean).join('; ') || 'The runtime refused this Try.');
  const text = value => typeof value === 'string' ? cleanText(value, context.secrets) : '';
  const items = (refusals.length ? refusals : [{ code: 'refused' }]).map(item => ({ code: text(item.code) || 'refused', section: text(item.section),
    reason: [text(item.reason), APP_MAP_RULES[text(item.code)], text(item.engine_message), GENERIC_REFUSAL.test(text(item.message)) ? '' : text(item.message)].find(Boolean),
    fix: text(item.fix), where: text(item.where) || [text(item.file), text(item.at)].filter(Boolean).join(' ') }));
  const mapped = !!appMap && items.some(item => Object.hasOwn(APP_MAP_RULES, item.code) || /^app-map-/.test(item.code) || /app[-_]map/i.test(item.section));
  const why = items.map(item => `${item.reason ? `${item.code}: ${item.reason}` : item.code}${item.where ? `; at ${item.where}` : ''}`).join('; '), fix = items.find(item => item.fix)?.fix;
  const again = `run pdd try ${test.story} --new.`;
  line(context.ports.stdout, `The Try could not start: ${mapped ? 'the app map was refused' : 'the server refused it'} (${why}).`);
  line(context.ports.stdout, fix ? `${fix} Then ${again}` : mapped ? `Fix ${appMap} (RUNBOOK §13), then ${again}`
    : `Fix what it names, then ${again}${reportUrl ? ` Details: ${reportUrl}` : ''}`);
  return 4;
}

function printTryProblem(context, row) {
  if (context.doorMode) throw new Stop(125, row.refusals?.map(r => r.message || r.code).join('; ') || `The Try could not start (${row.state}).`);
  const exitCode = exitCodeFor([row]);
  context.ports.stdout.write(renderText({ rows: [row], exitCode, secrets: context.secrets, recovery: `pdd try ${row.story}` }));
  return exitCode;
}

async function showTry(context, test, link, options, tryId, reused = false) {
  if (options['--cli'] || options['--serve']) {
    const doors = await import('./try-doors.mjs');
    return options['--cli'] ? doors.openCli(context, test, tryId, options) : (await import('./try-http.mjs')).openServe(context, test, tryId, options);
  }
  const { ports } = context, ends = reused ? `It keeps its original 24-hour expiry; stop it with: pdd try --stop ${test.story}`
    : `It ends in 24 hours, or with: pdd try --stop ${test.story}`;
  if (!options['--no-open'] && await ports.openUrl(link)) line(ports.stdout, `Try link for "${test.title}" is open in your browser. ${ends}`);
  else {
    line(ports.stdout, `Try link for "${test.title}": ${link}`);
    line(ports.stdout, `${options['--no-open'] ? '' : 'pdd could not open a browser. Open the link yourself. '}Anyone with the link can use it. ${ends}`);
  }
  await watchSavedTests(context, tryId, !options['--no-wait'] && ports.interactive, test.story);
  return 0;
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
  if (!isObject(test) || !Array.isArray(test.steps) || !test.steps.length || typeof story !== 'string') return `not added: "${label}" is not a test the runtime can run.`;
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
        if (!handled[id]?.noticed) line(ports.stdout, `The Try page asks to approve ${asked}. A person answers it in a terminal: pdd try ${story}`);
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
      if (tests === 'missing' && wait && !told) line(ports.stdout, 'The runtime does not keep saved tests yet. Copy a saved test from the Try page into tests/ by hand.');
      if (approvals !== 'missing') approvals = await collectApprovals(context, tryId, story, answers);
      if (tests === 'ended' || approvals === 'ended' || !wait || context.interrupted) return;
      if (tests === 'missing' && approvals === 'missing') return;
      if (!told) { line(ports.stdout, 'Waiting for tests saved and approvals asked on the Try page. Press Ctrl-C to stop waiting; the Try link stays open.'); told = true; }
      await ports.sleep(ports.watchMs, context.signal);
      if (context.interrupted) { line(ports.stdout, 'Stopped waiting. The Try link stays open. Run pdd try again to add tests saved later.'); return; }
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
export const saveDoorCase = (root, saved) => addSavedCase(root, saved);
export async function runDoorCall(descriptor, input, givenPorts = {}) {
  const ports = withDefaults(givenPorts), { root, origin, sessionId, login, prompt, operation } = descriptor;
  const store = stateFor(ports.env, root), identity = signIn(ports.gh, store);
  if (identity.login !== login) throw new Stop(5, `This Try belongs to ${login}. Run: gh auth switch -u ${login}`);
  if (runtimeOrigin({ PDD_RUNTIME_URL: origin }) !== origin) throw new Stop(2, 'The saved runtime address is invalid.');
  const runtime = new Runtime({ origin, token: identity.token, ports, signal: ports.signal });
  if (ports.signal?.aborted) throw new Stop(125, 'The local server stopped before the command was sent.');
  const id = ports.randomUUID(), request = { requestId: id, prompt, operation, input };
  store.posted(store.folder('tries'), id);
  const reply = await runtime.send(`/v1/try/${sessionId}/call`, { method: 'POST',
    headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(request) }, ports.postMs);
  if (reply.status && ![200, 202].includes(reply.status)) {
    throw new Stop(125, cleanText(reply.json?.error?.message || reply.json?.error?.code || `The runtime refused the command (HTTP ${reply.status}).`, [identity.token]));
  }
  const end = ports.now() + 900_000;
  let answer = null;
  for (;;) {
    if (ports.signal?.aborted) throw new Stop(125, 'The local server stopped; this command result is unknown. Do not repeat it automatically.');
    if (answer && (answer.id !== id || answer.command !== 'call' || (answer.session_id && answer.session_id !== sessionId))) throw new Stop(125, 'The runtime returned a different command.');
    if (answer && ENDED.has(answer.state)) {
      store.write(join(store.folder('tries'), `${id}.json`), answer);
      if (answer.state !== 'passed' || !isObject(answer.result?.program_result)) {
        const why = answer.result?.refusals?.[0];
        throw new Stop(125, cleanText(why?.engine_message || why?.message || why?.code || 'The command result is unknown. Do not repeat it automatically.', [identity.token]));
      }
      return { id, result: answer.result.program_result, inputWorld: answer.result.report.input_world, world: answer.result.report.world };
    }
    if (ports.now() >= end) throw new Stop(125, 'The command result is unknown. Do not repeat it automatically.');
    await ports.sleep(ports.pollMs, ports.signal);
    if (ports.signal?.aborted) throw new Stop(125, 'The local server stopped; this command result is unknown. Do not repeat it automatically.');
    const read = await runtime.get(id);
    if ([401, 403, 410].includes(read.status)) throw new Stop(125, cleanText(read.json?.error?.message || 'The command could not be read. Do not repeat it automatically.', [identity.token]));
    answer = [200, 202].includes(read.status) ? read.json : null;
  }
}
