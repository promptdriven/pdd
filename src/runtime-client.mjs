// Generated from prompts/cli/runtime-client.prompt.md (sha256: 74ef0940ad609682a2108ee5ff027ad17e4ca32dbb32394fd5c594623fe9d278).
import { spawn, spawnSync } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import { chmodSync, closeSync, mkdirSync, openSync, readFileSync, realpathSync, renameSync, writeFileSync, writeSync } from 'node:fs';
import { homedir } from 'node:os';
import { dirname, join, relative, resolve, sep } from 'node:path';
import { PreflightError, captureSource, checkInput, draftHint, fillHashes, findTests, formatSize, gitFiles, otherFiles,
  preflight, readPrompt, selectTests, STALE_HINT } from './runtime-preflight.mjs';
import { OPEN_STATES, cleanText, exitCodeFor, projectAnswer, renderJson, renderText, validLink } from './runtime-output.mjs';

const DEFAULT_ORIGIN = 'https://runtime.34-72-131-98.sslip.io';
const JOB_STATES = new Set(['queued', 'running', 'passed', 'failed', 'refused', 'unknown']);
const ENDED = new Set(['passed', 'failed', 'refused', 'unknown', 'not_run']);
const UUID = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
const BATCH = /^\d{8}-\d{6}-[a-z0-9]{4}$/;
const POST_MS = 90_000, GET_MS = 30_000, LINT_MS = 120_000, TRY_MS = 300_000, MAX_READS = 8;

class Stop extends Error { constructor(exitCode, message) { super(message); this.exitCode = exitCode; } }
const line = (stream, text) => stream.write(`${text}\n`);
const isObject = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const clock = ms => new Date(ms).toTimeString().slice(0, 8);

function withDefaults(ports) {
  const env = ports.env ?? process.env;
  return {
    env, stdout: ports.stdout ?? process.stdout, stderr: ports.stderr ?? process.stderr, fetch: ports.fetch ?? globalThis.fetch,
    gh: ports.gh ?? (args => spawnSync('gh', args, { encoding: 'utf8', env, stdio: ['ignore', 'pipe', 'pipe'], timeout: 60_000 })),
    now: ports.now ?? Date.now, randomUUID: ports.randomUUID ?? randomUUID, pollMs: ports.pollMs ?? 2000,
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
  const raw = env.PDD_RUNTIME_URL || DEFAULT_ORIGIN;
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
  post(path, request, tar) {
    const form = new FormData();
    form.set('request', new Blob([JSON.stringify(request)], { type: 'application/json' }), 'request.json');
    form.set('source', new Blob([tar], { type: 'application/x-tar' }), 'source.tar');
    return this.send(path, { method: 'POST', body: form }, POST_MS);
  }
  get(id) { return this.send(`/v1/runs/${id}`, { method: 'GET' }, GET_MS); }
  stop(tryId, requestId) { return this.send(`/v1/try/${tryId}`, { method: 'DELETE', headers: { 'X-Request-Id': requestId } }, POST_MS); }
}

const sameJob = (json, id, command) => isObject(json) && json.requestId === id && json.id === id && json.command === command && JOB_STATES.has(json.state);
const gateText = reply => reply.status === 503 && !reply.json && String(reply.text ?? '').includes('The runtime opens soon.');

// One answer to a POST, as the row table of the spec.
function judgePost(reply, id, command, secrets) {
  if (reply.lost) return { kind: 'unknown', why: 'The answer to the request was lost.' };
  const error = isObject(reply.json?.error) ? reply.json.error : null;
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
  if (reply.status === 200) return sameJob(reply.json, id, command) ? { kind: 'state', answer: reply.json } : { kind: 'unknown', why: 'The runtime answered with another request ID or command.' };
  if (reply.status === 404) return { kind: 'missing' };
  if (reply.status === 410) return { kind: 'unknown', why: 'The result expired.' };
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

function select(found, words) {
  if (!found.tests.length) throw new Stop(2, 'No tests found. A test is a Git-visible *.json file with "schema_version": "prompt-runtime.program-scenario.v1".');
  const { selected, unknown } = selectTests(found, words);
  if (unknown.length) throw new Stop(2, [`Unknown story ${unknown.map(word => `"${cleanText(word)}"`).join(', ')}. Stories with tests:`, ...storyList(found)].join('\n'));
  return selected;
}

const localRows = rows => rows.map(row => ({ ...row, state: row.refusals.length ? 'refused' : 'ready', phase: row.refusals.length ? 'local' : 'server',
  request_ids: [], report_url: null, checks: null, failed_checks: [], all_checks: [] }));

// Lint verdict for each test: the prompts it reaches must be approved and not refused.
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
      else if (state !== 'approved') {
        const local = readPrompt(root, visible, path);
        problem = state === 'stale' ? { code: 'interface-stale', section: 'lint', message: `${path} changed after its interface was approved.`, hint: STALE_HINT }
          : state === 'draft' ? { code: 'interface-unapproved', section: 'lint', message: `${path} is not approved.`, hint: draftHint(path) }
          : { code: `interface-${cleanText(state, secrets) || 'unapproved'}`, section: 'lint', message: `${path} has no approved Runtime interface${local.error ? ` (${local.error})` : ''}.` };
      } else for (const call of Array.isArray(prompt.interface?.calls) ? prompt.interface.calls : []) if (typeof call?.target === 'string') queue.push(call.target);
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
      const local = entry ? checkInput(step.input, entry.input_schema, index) : null;
      if (local?.message) item.hint = local.message;
    } else if (['interface-unapproved', 'interface-stale'].includes(item.code) && prompt.interface) {
      item.hint = prompt.interface.status !== 'approved' ? draftHint(step.entry_path) : STALE_HINT;
    }
  }
}

function applyAnswer(row, answer, context) {
  const view = projectAnswer(answer, { origin: context.origin, secrets: context.secrets });
  Object.assign(row, { state: view.state, checks: view.checks, failed_checks: view.failed_checks, all_checks: view.all_checks,
    refusals: view.refusals, calls: view.calls, requested_model: view.requested_model, report_url: view.report_url ?? row.report_url,
    server_seconds: view.server_seconds, why: view.state === 'unknown' ? view.why : row.why, engine_sha: view.engine_sha });
  if (row.state === 'refused') addHints(row, context.root, context.visible);
  if (ENDED.has(row.state) && row.sent_at && !row.ended_at && !context.reading) row.ended_at = context.ports.now();
  row.seconds = !ENDED.has(row.state) ? null : row.sent_at && row.ended_at ? (row.ended_at - row.sent_at) / 1000 : row.server_seconds;
}

function batchRecord(context) {
  const { batch, origin, root, identity, capture, rows, lint, warnings } = context;
  return { version: 1, batch, origin, root, head: context.head, login: identity.login, user_id: identity.userId,
    source_sha256: capture.sha256, files: capture.files.map(file => file.path), bytes: capture.bytes, timeout_min: context.timeoutMin,
    created_at: new Date(context.startedAt).toISOString(), lint, warnings,
    rows: rows.map(row => ({ test: row.test, story: row.story, title: row.title, request_ids: row.request_ids, state: row.state,
      phase: row.phase, report_url: row.report_url, refusals: row.refusals, note: row.note ?? null, why: row.why ?? null,
      sent_at: row.sent_at ?? null, ended_at: row.ended_at ?? null, max_calls: row.max_calls, warnings: row.warnings, steps: row.steps })) };
}

function saveBatch(context) { if (context.batch) context.store.write(join(context.folder, 'batch.json'), batchRecord(context)); }
function saveAnswer(context, id, json) { if (isObject(json)) context.store.write(join(context.folder, `${id}.json`), json); }

async function postJob(context, path, command, request, row) {
  const id = request.requestId;
  if (context.interrupted) return { kind: 'not_sent' };
  context.store.posted(context.folder, id);
  if (row) { row.request_ids.push(id); row.sent_at ??= context.ports.now(); row.state = 'sending'; }
  saveBatch(context);
  const reply = await context.runtime.post(path, request, context.capture.tar);
  const verdict = judgePost(reply, id, command, context.secrets);
  if (verdict.answer) saveAnswer(context, id, verdict.answer);
  return verdict;
}

// POST one check and fold the answer into its row.
async function sendCheck(context, row) {
  const request = { requestId: context.ports.randomUUID(), source_sha256: context.capture.sha256, scenario: row.test, max_calls: row.max_calls };
  const verdict = await postJob(context, '/v1/check', 'check', request, row);
  row.retry_at = null;
  if (verdict.kind === 'not_sent') Object.assign(row, { state: 'not_run', note: { code: null, message: 'Stopped before sending.' } });
  else if (verdict.kind === 'accepted') applyAnswer(row, verdict.answer, context);
  else if (verdict.kind === 'busy') { row.state = 'waiting'; row.retry_at = context.ports.now() + verdict.wait; }
  else if (verdict.kind === 'not_run') Object.assign(row, { state: 'not_run', note: verdict.note });
  else if (verdict.kind === 'stop') { Object.assign(row, { state: 'not_run', note: verdict.note }); context.stopped = verdict.note; }
  else if (verdict.kind === 'refused') Object.assign(row, { state: 'refused', refusals: [verdict.refusal] });
  else Object.assign(row, { state: 'unknown', why: verdict.why, lost: true });
}

// GET one open row once.
async function readRow(context, row) {
  const id = row.request_ids.at(-1), verdict = judgeGet(await context.runtime.get(id), id, 'check');
  if (verdict.kind === 'state') { saveAnswer(context, id, verdict.answer); applyAnswer(row, verdict.answer, context); row.lost = false; }
  else if (verdict.kind === 'unknown') Object.assign(row, { state: 'unknown', why: verdict.why, lost: false, final: true });
  else if (verdict.kind === 'auth') context.readStop = 'Run gh auth login';
  else if (verdict.kind === 'gate') context.readStop = 'The runtime opens soon.';
}

const isOpen = row => OPEN_STATES.has(row.state) || (row.state === 'unknown' && row.lost);

async function runLint(context) {
  const lintEnd = Math.min(context.deadline, context.startedAt + LINT_MS);
  for (;;) {
    const request = { requestId: context.ports.randomUUID(), source_sha256: context.capture.sha256 };
    context.lint.request_ids.push(request.requestId);
    const verdict = await postJob(context, '/v1/lint', 'lint', request, null);
    if (verdict.kind === 'busy' && context.ports.now() + verdict.wait < lintEnd && !context.interrupted) {
      line(context.ports.stderr, 'Server busy: lint is waiting for a free slot.');
      await context.ports.sleep(verdict.wait, context.signal); continue;
    }
    if (verdict.kind === 'not_sent') return { kind: 'not_run', note: { code: null, message: 'Stopped before sending.' } };
    if (verdict.kind !== 'accepted') return verdict.kind === 'busy' ? { kind: 'not_run', note: { code: 'server-full', message: 'The runtime is busy. Try again later.' } } : verdict;
    let answer = verdict.answer, id = request.requestId, lost = false;
    while (!['passed', 'failed', 'refused', 'unknown'].includes(answer?.state) && context.ports.now() < lintEnd && !context.interrupted) {
      await context.ports.sleep(context.ports.pollMs, context.signal);
      if (context.interrupted) break;
      const read = judgeGet(await context.runtime.get(id), id, 'lint');
      if (read.kind === 'state') { answer = read.answer; saveAnswer(context, id, answer); }
      else if (read.kind === 'unknown') { lost = true; break; }
      else if (read.kind === 'auth' || read.kind === 'gate') return { kind: 'stop', note: { code: null, message: read.kind === 'auth' ? 'Run gh auth login' : 'The runtime opens soon.' } };
    }
    return lost ? { kind: 'unknown' } : { kind: 'answer', answer };
  }
}

async function checkBatch(context, rows) {
  const { ports } = context, sendable = rows.filter(row => row.state === 'ready');
  const lint = await runLint(context);
  context.lint.state = lint.answer?.state ?? lint.kind;
  context.lint.unknown = false;
  const notSent = (state, extra) => { for (const row of sendable) Object.assign(row, { state, ...extra }); };
  if (context.interrupted) { notSent('not_run', { note: { code: null, message: 'Stopped before sending.' } }); return; }
  if (lint.kind === 'not_run' || lint.kind === 'stop') { notSent('not_run', { note: lint.note }); return; }
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
    + `(${context.capture.files.length} files, ${formatSize(context.capture.bytes)}) at ${clock(ports.now())}.`);
  await Promise.all(toSend.map(row => sendCheck(context, row)));
  saveBatch(context);
  let waitingShown = -1;
  while (!context.interrupted && !context.readStop) {
    const waiting = toSend.filter(row => row.state === 'waiting'), open = toSend.filter(isOpen);
    if (!waiting.length && !open.length) break;
    if (ports.now() >= context.deadline) break;
    if (waiting.length !== waitingShown) {
      if (waiting.length) line(ports.stderr, `Server busy: ${open.length} checks running, ${waiting.length} waiting for a free slot.`);
      waitingShown = waiting.length;
    }
    await ports.sleep(ports.pollMs, context.signal);
    if (context.interrupted) break;
    const before = toSend.filter(row => ENDED.has(row.state)).length;
    await eachLimited(toSend.filter(isOpen), MAX_READS, row => readRow(context, row));
    const freed = toSend.filter(row => ENDED.has(row.state)).length > before;
    if (context.interrupted) break;
    if (!context.stopped) await Promise.all(toSend.filter(row => row.state === 'waiting' && (freed || ports.now() >= row.retry_at)).map(row => sendCheck(context, row)));
    else for (const row of toSend.filter(row => row.state === 'waiting')) Object.assign(row, { state: 'not_run', note: context.stopped });
    saveBatch(context);
  }
  for (const row of toSend) {
    if (row.state === 'waiting') Object.assign(row, { state: 'not_run', note: { code: 'server-full', message: 'The runtime stayed busy until the timeout.' } });
    if (row.state === 'unknown' && row.lost) row.why ??= 'pdd could not read this run before the timeout.';
  }
}

function printResult(context, rows, extra = {}) {
  const { ports } = context, exitCode = exitCodeFor(rows, { interrupted: context.interrupted, lintUnknown: context.lintUnknown });
  const warnings = context.warnings ?? [];
  const summary = renderJson({ batch: context.batch ?? null, repo: context.root, rows, exitCode,
    warnings: [...warnings, ...rows.flatMap(row => (row.warnings ?? []).map(text => `${row.test}: ${text}`))] });
  if (context.folder) context.store.write(join(context.folder, 'summary.json'), summary);
  if (context.readStop) line(ports.stderr, context.readStop);
  if (context.stopped && !context.json) line(ports.stderr, context.stopped.message);
  const scrub = text => (context.secrets ?? []).reduce((value, secret) => secret ? value.split(secret).join('[secret]') : value, text);
  if (context.json) line(ports.stdout, scrub(JSON.stringify(summary)));
  else ports.stdout.write(scrub(renderText({ batch: context.batch, rows, warnings, details: context.details, timeoutMin: context.timeoutMin,
    interrupted: context.interrupted || !!context.readStop, exitCode, secrets: context.secrets, ...extra })));
  if (exitCode === 3 && context.batch) line(ports.stderr, `If pdd stops, read the results with: pdd check --read ${context.batch}`);
  return exitCode;
}

function runFiles(root, ports) {
  const capture = captureSource(root), found = findTests({ root });
  const other = otherFiles(capture.files, found), width = Math.max(0, ...capture.files.map(file => file.path.length));
  for (const file of capture.files) line(ports.stdout, `  ${file.path.padEnd(width)}  ${formatSize(file.size)}`);
  line(ports.stdout, `${capture.files.length} files, ${formatSize(capture.bytes)}. ${other.length} of them are not prompt, story or test files.`);
  return 0;
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

async function runRead(context, batchWord) {
  const { store, ports, root } = context;
  const name = batchWord ?? store.repo(root).last_batch;
  if (!name || !BATCH.test(name)) throw new Stop(2, name ? 'BATCH looks like 20261027-092747-k3f9.' : 'No saved check for this repository. Run pdd check first.');
  context.folder = join(store.dir, 'batches', name);
  const saved = store.read(join(context.folder, 'batch.json'));
  if (!saved) throw new Stop(2, `No saved batch ${name}.`);
  const identity = signIn(ports.gh, context.store);
  if (identity.login !== saved.login) throw new Stop(5, `These runs belong to ${saved.login}. Run: gh auth switch -u ${saved.login}`);
  Object.assign(context, { batch: name, origin: saved.origin, identity, secrets: [identity.token], warnings: saved.warnings ?? [], timeoutMin: saved.timeout_min ?? 10,
    capture: { sha256: saved.source_sha256, files: saved.files.map(path => ({ path })), bytes: saved.bytes }, lint: saved.lint, head: saved.head, startedAt: Date.parse(saved.created_at) });
  context.runtime = new Runtime({ origin: saved.origin, token: identity.token, ports, signal: context.signal });
  const rows = saved.rows.map(row => ({ ...row, checks: null, failed_checks: [], all_checks: [] }));
  Object.assign(context, { rows, visible: findTests({ root }).visible, reading: true });
  // A pdd that was killed can leave rows that never got an answer: read them if they were posted.
  for (const row of rows) if (['ready', 'sending', 'waiting'].includes(row.state)) {
    if (row.request_ids.length) row.state = 'unknown';
    else Object.assign(row, { state: 'not_run', note: { code: null, message: 'pdd stopped before sending this check.' } });
  }
  if (context.lint?.unknown) {
    const id = context.lint.request_ids?.at(-1), read = id ? judgeGet(await context.runtime.get(id), id, 'lint') : { kind: 'missing' };
    if (read.kind === 'state') { saveAnswer(context, id, read.answer); context.lint.state = read.answer.state; }
    context.lintUnknown = context.lint.unknown = !['passed', 'failed', 'refused'].includes(context.lint.state);
  }
  await eachLimited(rows, MAX_READS, async row => {
    const id = row.request_ids.at(-1);
    if (!id || row.phase !== 'server') return;
    const answer = store.read(join(context.folder, `${id}.json`));
    if (answer && ['passed', 'failed', 'refused'].includes(answer.state) && sameJob(answer, id, 'check')) { applyAnswer(row, answer, context); return; }
    if (['queued', 'running', 'unknown'].includes(row.state)) {
      row.lost = true;
      await readRow(context, row);
      if (row.state === 'unknown' && row.lost) row.why ??= 'pdd could not read this run yet.';
    } else if (answer) applyAnswer(row, answer, context);
  });
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
    const modes = ['--read', '--fill-hash', '--files', '--request'].filter(name => options[name] !== undefined);
    const others = Object.keys(options).filter(name => !modes.includes(name) && !(name === '--json' && ['--read', '--request'].includes(modes[0])));
    if (modes.length > 1 || (modes.length && others.length) || (['--fill-hash', '--files', '--request'].includes(modes[0]) && words.length)
      || (modes[0] === '--read' && words.length > 1)) throw new Stop(2, 'This mix of options does not work together. Run pdd check --help.');
    if (modes[0] === '--request') { release = interruptible(context); return await runRequest(context, options['--request']); }
    const root = repoRoot(cwd);
    if (modes[0] === '--fill-hash') return runFillHash(root, ports);
    if (modes[0] === '--files') return runFiles(root, ports);
    context.root = root; context.store = stateFor(ports.env, root);
    if (modes[0] === '--read') { release = interruptible(context); return await runRead(context, words[0]); }
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
  context.timeoutMin = Number(options['--timeout'] ?? 10);
  const selected = select(found, normalized);
  const checked = preflight({ root, found, selected });
  const rows = localRows(checked.rows);
  if (options['--max-calls'] !== undefined) for (const row of rows) row.max_calls = Number(options['--max-calls']);
  context.warnings = [...found.warnings, ...checked.warnings];
  if (!rows.some(row => row.state === 'ready')) return printResult(context, rows);
  const capture = captureSource(root);
  const other = otherFiles(capture.files, found);
  if (other.length) context.warnings.push(`Warning: ${other.length} of the ${capture.files.length} files sent are not prompt, story or test files. Run pdd check --files to see them.`);
  const identity = signIn(ports.gh, context.store);
  const startedAt = ports.now(), batch = batchId(startedAt, ports.randomUUID);
  const head = spawnSync('git', ['rev-parse', 'HEAD'], { cwd: root, encoding: 'utf8' });
  Object.assign(context, { capture, identity, batch, startedAt, deadline: startedAt + context.timeoutMin * 60_000, rows,
    head: head.status === 0 ? head.stdout.trim() : null, secrets: [identity.token], lint: { request_ids: [], state: null } });
  context.folder = context.store.folder('batches', batch);
  saveBatch(context);
  const repoState = context.store.repo(root);
  context.store.saveRepo(root, { ...repoState, last_batch: batch });
  line(ports.stderr, `If pdd stops, read the results with: pdd check --read ${batch}`);
  setRelease(interruptible(context));
  context.runtime = new Runtime({ origin, token: identity.token, ports, signal: context.signal });
  await checkBatch(context, rows);
  saveBatch(context);
  return printResult(context, rows);
}

// ---- pdd try ----

function oneTest(found, words) {
  const selected = select(found, words);
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
    if (context.interrupted || context.ports.now() >= end) return { answer: last, open: true };
    await context.ports.sleep(context.ports.pollMs, context.signal);
  }
}

function tryLink(answer, origin) {
  return answer?.state === 'passed' && answer.result?.session?.state === 'running' ? validLink(answer.result?.url, origin, 'try') : null;
}

async function stopTry(context, record) {
  const id = context.ports.randomUUID();
  context.store.posted(context.store.folder('tries'), id);
  const reply = await context.runtime.stop(record.id, id), verdict = judgePost(reply, id, 'stop', context.secrets);
  if (verdict.kind === 'stop') throw new Stop(5, verdict.note.message);
  if (verdict.kind === 'not_run') throw new Stop(5, `${verdict.note.message}${verdict.note.code ? ` (${verdict.note.code})` : ''}`);
  if (verdict.kind === 'refused') throw new Stop(4, `The runtime refused to stop this Try: ${verdict.refusal.message} (${verdict.refusal.code})`);
  if (verdict.kind !== 'accepted') throw new Stop(3, 'The stop result is unknown. Run pdd try --stop again later; it sends a new stop request.');
  const done = verdict.answer.state === 'passed' ? { answer: verdict.answer } : await readUntil(context, id, 'stop', answer => ENDED.has(answer.state), TRY_MS);
  if (done.answer?.state !== 'passed') throw new Stop(done.answer?.state === 'refused' ? 4 : 3, 'The Try did not confirm that it stopped. Run pdd try --stop again later.');
}

// pdd try. Returns the exit code.
export async function runTry({ words = [], options = {}, cwd = process.cwd() } = {}, givenPorts = {}) {
  const ports = withDefaults(givenPorts), context = { ports, interrupted: false };
  let release = () => {};
  try {
    if (options['--stop'] && (options['--tab'] || options['--new'] || options['--no-open'])) throw new Stop(2, 'pdd try --stop takes only a STORY. Run pdd try --help.');
    if (words.length > 1) throw new Stop(2, 'pdd try takes one STORY.');
    const origin = runtimeOrigin(ports.env), { root, found, normalized } = localSetup(cwd, words), store = stateFor(ports.env, root);
    const test = oneTest(found, normalized), repoState = store.repo(root), record = repoState.tries?.[test.path];
    Object.assign(context, { root, store, origin, visible: found.visible });
    if (options['--stop']) {
      if (!record) throw new Stop(2, `No open Try for "${test.title}".`);
      const identity = signIn(ports.gh, context.store);
      context.secrets = [identity.token];
      context.runtime = new Runtime({ origin: record.origin ?? origin, token: identity.token, ports });
      await stopTry(context, record);
      delete repoState.tries[test.path];
      store.saveRepo(root, repoState);
      line(ports.stdout, `The Try link for "${test.title}" is stopped.`);
      return 0;
    }
    const checked = preflight({ root, found, selected: [test] }), row = localRows(checked.rows)[0];
    if (row.state === 'refused') { line(ports.stdout, renderText({ rows: [row], exitCode: 4 })); return 4; }
    const capture = captureSource(root), identity = signIn(ports.gh, context.store);
    Object.assign(context, { capture, identity, secrets: [identity.token], startedAt: ports.now(), deadline: ports.now() + TRY_MS, lint: { request_ids: [], state: null },
      batch: null, rows: [row], timeoutMin: TRY_MS / 60_000, head: null });
    context.folder = store.folder('tries');
    release = interruptible(context);
    context.runtime = new Runtime({ origin, token: identity.token, ports, signal: context.signal });
    if (record) {
      const read = judgeGet(await context.runtime.get(record.id), record.id, 'try');
      if (read.kind === 'auth') throw new Stop(5, 'Run gh auth login');
      if (read.kind === 'gate') throw new Stop(5, 'The runtime opens soon.');
      const answer = read.kind === 'state' ? read.answer : null, link = tryLink(answer, origin);
      const ended = read.kind === 'missing' || ['failed', 'refused'].includes(answer?.state)
        || (answer?.state === 'passed' && ['stopped', 'stopping'].includes(answer.result?.session?.state));
      if (link && !options['--new']) return await showTry(context, test, link, options);
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
    if (row.state !== 'ready') return printTryProblem(context, row);
    const request = { requestId: ports.randomUUID(), source_sha256: capture.sha256, seed: test.path, tab: options['--tab'] ?? 'call' };
    store.saveRepo(root, { ...repoState, tries: { ...repoState.tries, [test.path]: { id: request.requestId, story: test.story, title: test.title, origin } } });
    store.posted(context.folder, request.requestId);
    const reply = await context.runtime.post('/v1/try', request, capture.tar), verdict = judgePost(reply, request.requestId, 'try', context.secrets);
    if (verdict.answer) store.write(join(context.folder, `${request.requestId}.json`), verdict.answer);
    if (verdict.kind !== 'accepted') {
      if (verdict.kind !== 'unknown') { delete repoState.tries[test.path]; store.saveRepo(root, repoState); }
      if (reply.status === 429) throw new Stop(5, 'Too many Try links are open. Stop one with pdd try --stop');
      if (verdict.kind === 'refused') { Object.assign(row, { state: 'refused', phase: 'server', refusals: [verdict.refusal] }); return printTryProblem(context, row); }
      if (verdict.kind === 'not_run' || verdict.kind === 'stop') throw new Stop(5, `${verdict.note.message}${verdict.note.code ? ` (${verdict.note.code})` : ''}`);
      throw new Stop(3, `The Try setup result is unknown. Run pdd try ${test.story} again later: it reads this Try first and sends nothing new while it runs.`);
    }
    const done = ENDED.has(verdict.answer.state) ? { answer: verdict.answer }
      : await readUntil(context, request.requestId, 'try', answer => ENDED.has(answer.state), TRY_MS);
    const link = tryLink(done.answer, origin);
    if (link) return await showTry(context, test, link, options);
    if (done.unknownWhy || done.open || !done.answer || done.answer.state === 'unknown') {
      throw new Stop(3, `The Try setup is not finished or its result is unknown. Run pdd try ${test.story} again later; it reuses a running Try.`);
    }
    applyAnswer(row, done.answer, context);
    // A Try that is running with a bad link stays recorded, so pdd try --stop can still end it.
    if (row.state === 'passed') Object.assign(row, { state: 'unknown', why: `The runtime did not return a valid Try link. Stop this Try with: pdd try --stop ${test.story}` });
    else { delete repoState.tries[test.path]; store.saveRepo(root, repoState); }
    return printTryProblem(context, row);
  } catch (error) {
    if (error instanceof Stop || error instanceof PreflightError) { line(ports.stderr, error.message); return error.exitCode; }
    throw error;
  } finally { release(); }
}

async function checkLint(context, rows) {
  const lint = await runLint(context);
  const verdicts = lint.kind === 'answer' && ['passed', 'failed', 'refused'].includes(lint.answer.state) ? judgeLint(lint.answer, rows, context.root, context.visible, context.secrets) : null;
  if (lint.kind === 'not_run' || lint.kind === 'stop') throw new Stop(5, `${lint.note.message}${lint.note.code ? ` (${lint.note.code})` : ''}`);
  if (lint.kind === 'refused') { Object.assign(rows[0], { state: 'refused', phase: 'lint', refusals: [lint.refusal] }); return; }
  if (!verdicts) throw new Stop(3, 'The lint result is unknown, so pdd made no Try link. Run pdd try again later.');
  for (const [row, problem] of verdicts) Object.assign(row, { state: 'refused', phase: 'lint', refusals: [problem] });
}

function printTryProblem(context, row) {
  const exitCode = exitCodeFor([row]);
  context.ports.stdout.write(renderText({ rows: [row], exitCode, secrets: context.secrets, recovery: `pdd try ${row.story}` }));
  return exitCode;
}

async function showTry(context, test, link, options) {
  const { ports } = context, ends = `It ends in 24 hours, or with: pdd try --stop ${test.story}`;
  if (!options['--no-open'] && await ports.openUrl(link)) { line(ports.stdout, `Try link for "${test.title}" is open in your browser. ${ends}`); return 0; }
  line(ports.stdout, `Try link for "${test.title}": ${link}`);
  line(ports.stdout, `${options['--no-open'] ? '' : 'pdd could not open a browser. Open the link yourself. '}Anyone with the link can use it. ${ends}`);
  return 0;
}
