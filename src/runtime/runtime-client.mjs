// Generated from prompts/cli/runtime-client.prompt.md (sha256: 7ee5fc6a1bc717c02d7be2e57cca5a4fe9f4bb1c7a74d4c58fcf625e7566bcda).
import { composeProductTry, selectJourneys, productTapCallBound } from './product-composition.mjs';
import {expandSource, parseJsonValue, stringifyJsonValue} from './contract-refs.mjs';
import { describeCallPreflight } from './lint-call-preflight.mjs';
import { isRecentLintReceipt } from './runtime-lint-receipt.mjs';
import { rememberSecrets as fallbackRememberSecrets } from './secret-redaction.mjs';
import { bindingPlanLines, bindingRefusals } from './runtime-binding-plan.mjs';
import { buildCheckPlan, checkPlanResults, checkPlanLines, checkPlanResultLines, selectCheckTests, baselineReport } from './runtime-check-plan.mjs';
import { interfaceFindings } from './interface-draft.mjs';
import {loadRuntimeWorkspace,allowsRuntimePath,requireRuntimePath,RuntimeWorkspaceError} from './runtime-workspace.mjs';
import { hasProgress, outcomeDone, outcomeFor, outcomeOverall, outcomeText, progressText, resultOutcome, resultOverall } from './runtime-outcome.mjs';
import { acquireRuntimeSlot, recordRuntimeRequest, releaseRuntimeSlot, listRuntimeJobs } from './runtime-slots.mjs';
import { bindingCoverage } from './runtime-bindings.mjs';
import { spawn, spawnSync } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import { chmodSync, closeSync, constants, fstatSync, fsyncSync, lstatSync, linkSync, mkdirSync, openSync, readFileSync, readdirSync, realpathSync, readSync, renameSync, rmdirSync, unlinkSync, writeFileSync, writeSync } from 'node:fs';
import { isDeepStrictEqual } from 'node:util';
import { homedir, hostname } from 'node:os';
import { basename, dirname, join, relative, resolve, sep } from 'node:path';
import { createInterface } from 'node:readline';
import { DRAFT_SERVER_TEXT, PreflightError, TEST_SCHEMA, captureSource, scenarioShapeRefusal, checkInput, fillHashes, lintLocalHygiene, sharedSourceFiles, findTests, formatSize, gitFiles, otherFiles,
  discoveryRefusal, preflight, hasPromptInterface, interfaceBlocks, executableInterfaceText, readPrompt, formatWarningLines, schemaKeywordWarningLines, missingCliImplementationWarnings, prepareHashSelection, sourceFilePort, sha256, STALE_HINT, staleHint } from './runtime-preflight.mjs';
import { catalogRecords, compareCopies } from './contract-refs.mjs';
import { OPEN_STATES, causeText, cleanText, progressTicker, projectAnswer, refusalView, renderJson, renderText, summaryLine, stepTimeLimit, tokenUsageOf, tryUsage, validLink, coverageText } from './runtime-output.mjs';

const localInterfaceProblem = problem => ['interface-missing','interface-kind-invalid','native-reason-missing','interface-draft-incomplete'].includes(problem.code);
const unboundPortError = message => Object.assign(new Error(message), { unboundPort: true });
// The preflight owner's local format advice (#3206): an explicit full kind in a draft and unsupported schema
// keywords are warnings in lint and the files preview, never refusals; the engine is the one place that refuses.
// It reads the selected entry prompts and the prompts they call.
function formatAdvice(root, visible, paths, workspace) {
  const lines = [], seen = new Set();
  const visit = path => {
    if (typeof path !== 'string' || seen.has(path)) return;
    seen.add(path);
    let prompt;
    try { prompt = readPrompt(root, visible, path, workspace); } catch { return; }
    for (const text of [...formatWarningLines(prompt), ...schemaKeywordWarningLines(prompt)]) if (!lines.includes(text)) lines.push(text);
    for (const call of Array.isArray(prompt.interface?.calls) ? prompt.interface.calls : []) visit(call?.target);
  };
  for (const path of paths) visit(path);
  return lines;
}
function hasMissingPromptInterface(root, found, startPaths) {
  const seen = new Set(), queue = [...startPaths];
  while (queue.length) {
    const path = queue.shift();
    if (typeof path !== 'string' || seen.has(path) || !found.visible.has(path)) continue;
    seen.add(path);
    let prompt;
    try { prompt = readPrompt(root, found.visible, path, found.workspace); } catch { continue; }
    if (prompt.error === 'interface-missing') return true;
    for (const call of Array.isArray(prompt.interface?.calls) ? prompt.interface.calls : []) if (typeof call?.target === 'string') queue.push(call.target);
  }
  return false;
}
const entryPaths = tests => tests.filter(test => !test.error).flatMap(test => (Array.isArray(test.doc?.steps) ? test.doc.steps : []).map(step => step?.entry_path));

// The one place in pdd that names the PDD runtime address; PDD_RUNTIME_URL overrides it.
export const DEFAULT_RUNTIME_URL = 'https://runtime.promptdriven.ai';
const JOB_STATES = new Set(['queued', 'running', 'passed', 'failed', 'refused', 'unknown']);
const ENDED = new Set(['passed', 'failed', 'refused', 'unknown', 'not_run']);
const UUID = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
const BATCH = /^\d{8}-\d{6}-[a-z0-9]{4}$/;
// pdd's local rules match this engine build (checked Oct 27; spec OPEN 9: warn when the runtime runs another one).
const ENGINE_SHA = 'eae2202a68d00ab762fcbbf1eba0d8607a132a15';
export function defaultLineReader(stdin) {
  const reader = createInterface({ input: stdin }), lines = [], waiting = [];
  let closed = false;
  reader.on('line', text => { const next = waiting.shift(); if (next) next(text); else lines.push(text); });
  reader.on('close', () => { closed = true; for (const next of waiting.splice(0)) next(''); });
  return { ask: () => lines.length ? Promise.resolve(lines.shift()) : closed ? Promise.resolve('') : new Promise(done => waiting.push(done)), close: () => reader.close() };
}
// The same engine: the full sha or a prefix of it with at least 7 hex digits.
const sameEngine = sha => { const value = sha.toLowerCase(); return /^[0-9a-f]{7,40}$/.test(value) && ENGINE_SHA.startsWith(value); };
const POST_MS = 90_000, GET_MS = 30_000, TRY_MS = 300_000, MAX_READS = 8, PROGRESS_MS = 30_000;
// Standalone lint, Try lint and explicit batch retry retain their finite agent wait.
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
  const findTestsBound = ports.findTests ?? (input => findTests(input, ports));
  const defaultCaptureSource = (root, options) => captureSource(root, options, ports);
  defaultCaptureSource.isDefaultCapture = true;
  const captureSourceBound = ports.captureSource ?? defaultCaptureSource;
  const fillHashesBound = ports.fillHashes ?? (input => fillHashes(input, ports));
  const selectTestsBound = (found, words, options = {}) => {
    if (typeof ports.selectTests !== 'function') throw unboundPortError('Test selection port (selectTests) is not bound.');
    return ports.selectTests(found, words, { ...options, captureSource: options.captureSource ?? captureSourceBound });
  };
  const expectedTestPathBound = storyPath => {
    if (typeof ports.expectedTestPath !== 'function') throw unboundPortError('Test selection port (expectedTestPath) is not bound.');
    return ports.expectedTestPath(storyPath);
  };
  const whyNoTestsBound = (root, visible, found) => {
    if (typeof ports.whyNoTests !== 'function') throw unboundPortError('Test selection port (whyNoTests) is not bound.');
    return ports.whyNoTests(root, visible, found, {
      allowsPath: (r, p) => allowsRuntimePath(loadRuntimeWorkspace({ root: r }), p),
      hasInterfaceBlock: hasPromptInterface,
      discoverTests: (r, files) => findTestsBound({ root: r, files }),
    });
  };
  const noTestsMessage = () => {
    const value = ports.noTestsMessage ?? ports.NO_TESTS;
    if (typeof value !== 'string') throw unboundPortError('Test selection port (NO_TESTS) is not bound.');
    return value;
  };
  const exitCodeForBound = (rows, options) => {
    if (typeof ports.exitCodeFor === 'function') return ports.exitCodeFor(rows, options, { outcomeOverall });
    if (typeof ports.exitFor === 'function') return ports.exitFor(outcomeOverall(rows, options));
    throw unboundPortError('Exit code port (exitCodeFor or exitFor) is not bound.');
  };
  return {
    env, baselineFiles: ports.baselineFiles, baselineIdentity: ports.baselineIdentity, checkPlanPorts: ports.checkPlanPorts, tryLauncherUrl: ports.tryLauncherUrl, redaction: ports.redaction, redactSecrets: ports.redactSecrets, rememberSecrets: ports.rememberSecrets, clientVersion: ports.clientVersion, workflowBaseSha: ports.workflowBaseSha, headerPrompts: ports.headerPrompts, resolveOwners: ports.resolveOwners, promptClaims: ports.promptClaims, isTestOwnedPath: ports.isTestOwnedPath, evidenceEligibility: ports.evidenceEligibility, readEvidenceEligibility: ports.readEvidenceEligibility, evidencePorts: ports.evidencePorts, allRuns: ports.allRuns, assessNativeEvidence: ports.assessNativeEvidence, usableResult: ports.usableResult, resultLines: ports.resultLines, parseProductDocuments: ports.parseProductDocuments, parseProductWorldWriters: ports.parseProductWorldWriters, loadAgentDefinitions: ports.loadAgentDefinitions, agents: ports.agents, guidePorts: ports.guidePorts, askApproval: ports.askApproval, promptPath: ports.promptPath, lineReader: ports.lineReader ?? defaultLineReader, lintSvgLayouts: ports.lintSvgLayouts, compareScreen: ports.compareScreen, formatScreenComparison: ports.formatScreenComparison, caseHandoff:ports.caseHandoff, cacheFiles: ports.cacheFiles ?? nativeCacheFiles, cacheHash: ports.cacheHash ?? sha256, acquireBatchLock: ports.acquireBatchLock ?? acquireRuntimeBatchLock, timers: ports.timers, random: ports.random, findTests: findTestsBound, captureSource: captureSourceBound, fillHashes: fillHashesBound, prepareHashSelection: ports.prepareHashSelection, isStoryPath: ports.isStoryPath, hasAcceptance: ports.hasAcceptance, matchTests: ports.matchTests, orphanSummary: ports.orphanSummary, selectTests: selectTestsBound, expectedTestPath: expectedTestPathBound, whyNoTests: whyNoTestsBound, noTestsMessage, exitCodeFor: exitCodeForBound, exitFor: ports.exitFor, promptTestsLabel: ports.promptTestsLabel, slotFiles: ports.slotFiles, isAlive: ports.isAlive, pid: ports.pid, agentBridge: ports.agentBridge, discoverAgents: ports.discoverAgents, askAgent: ports.askAgent, signal: ports.signal, ghPath: ports.ghPath, shell: ports.shell, serve: ports.serve, stdout: ports.stdout ?? process.stdout, stderr: ports.stderr ?? process.stderr, fetch: ports.fetch ?? globalThis.fetch,
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

export function readContractHistory({root,env = process.env},ports={}) {
  const warnings = [], latest = new Map();
  const empty = story_path => ({story_path,baseline:'not-checked',checked_at:null,result_state:null,files:[],references:[]});
  try {
    const found = ports.findTests ? ports.findTests({root}) : findTests({root},ports);
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
      if (!saved || saved.intent === 'lint-only' || !Array.isArray(saved.rows)) continue;
      const eligibility=(ports.evidenceEligibility??ports.readEvidenceEligibility??(() => ({state:'unavailable',reason:'workflow evidence eligibility port is not bound'})))({root,producerRoot:saved.root,tests:[...new Set(saved.rows.map(row=>row?.test))],source_sha256:saved.source_sha256,runId:saved.association?.runId??null,stage:saved.association?.stage??null},{env,...ports.evidencePorts});
      if(eligibility.state!=='eligible'&&(saved.root!==root||saved.association))continue;
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
  } catch (error) { if (error?.unboundPort) throw error; warnings.push(`Local Check history is unavailable: ${cleanText(error.message).slice(0,500)}`); }
  return {stories:[...latest.values()].map(row=>warnings.length && row.value.baseline==='not-checked' ? {...row.value,baseline:'unavailable'} : row.value).sort((a,b)=>a.story_path<b.story_path?-1:a.story_path>b.story_path?1:0),warnings:[...new Set(warnings)]};
}

const AFFECTED_DISCLAIMER = 'Affected checks only; this is not a full workflow pass. Required full-pass gates still apply.';
function selectedCheckScope(plan, rows, selection) {
  const scope = checkPlanResults(plan, rows);
  if (scope && selection?.mode === 'affected' && scope.baseline.unresolved.length && !plan.prerequisites?.length) {
    const selected = scope.target.failures.length ? `Repair target failures: ${scope.target.failures.join(', ')}. `
      : scope.target.unresolved.length ? `Read the saved batch for unresolved selected checks: ${scope.target.unresolved.join(', ')}. ` : '';
    scope.guidance = `${selected}Omitted baseline work: ${scope.baseline.unresolved.join(', ')}. Historical observations are separate; run a full check for required full-pass gates.`;
  }
  return scope;
}
function historicalBaselineLines(report) {
  if (!report) return [];
  return [`Historical baseline report (${report.availability}); omitted tests: ${report.tests.join(', ') || 'none'}.`,
    ...report.observations.map(row => `${row.test}: historical ${row.state}; original batch ${row.batch}; Check ${row.request_id ?? 'not sent (local)'}; ${row.created_at ?? 'time unavailable'}; ${row.currentness} (original-batch); stage ${row.stage}${row.report_url ? `; Report: ${row.report_url}` : ''}`),
    ...report.missing_tests.map(path => `${path}: no admitted saved baseline observation.`), ...report.warnings];
}
// This reader consumes raw local bytes. It never signs in, repairs receipts or writes history.
async function readBaselineReport(context, plan, identity) {
  const {ports,root,origin} = context, observations = [], warnings = [], captures = new Map();
  const warn = message => { if (warnings.length < 20 && !warnings.includes(message)) warnings.push(message); };
  const project = availability => baselineReport({plan,observations,availability,warnings});
  const wanted = new Set(selectCheckTests(plan,{affected:true}).baseline_tests);
  if (!wanted.size) return project('available');
  if (!identity?.login || !/^\d+$/.test(String(identity.userId ?? ''))) {
    warn('Runtime/account identity is unavailable; saved baseline evidence was not admitted.'); return project('unavailable');
  }
  const files = ports.baselineFiles ?? {
    read(path) { safeCachePath(nativeCacheFiles,path); return nativeCacheFiles.read(path,'utf8',16 * 1024 * 1024); },
    list(path) { safeCachePath(nativeCacheFiles,path,{directory:true}); return readdirSync(path); },
    realpath:realpathSync
  };
  const real = async path => { try { return await (files.realpath ?? realpathSync)(path); } catch { return resolve(path); } };
  let stateRoot = stateDirectory(ports.env,root);
  if (!ports.baselineFiles) {
    if (statOrNull(stateRoot)?.isSymbolicLink()) { warn('Saved Check state root is a symlink; history is unavailable.'); return project('unavailable'); }
    // The accepted external state boundary may have aliased ancestors. Below it, links remain forbidden.
    stateRoot = realish(stateRoot);
  }
  const directory = join(stateRoot,'batches');
  let names, partial = false;
  try { names = await files.list(directory); }
  catch (error) { warn(error.code === 'ENOENT' ? 'No saved Check history is available.' : 'Saved Check history directory is unavailable.'); return project('unavailable'); }
  const read = async path => JSON.parse(await files.read(path));
  const capture = async (folder,selection) => {
    const key = JSON.stringify([folder,selection]);
    if (!captures.has(key)) captures.set(key,Promise.resolve().then(()=>ports.captureSource(folder,selection)));
    return captures.get(key);
  };
  for (const name of names.filter(name=>typeof name === 'string' && BATCH.test(name)).sort()) {
    const folder = join(directory,name); let saved;
    try { saved = await read(join(folder,'batch.json')); }
    catch { partial=true;warn('Some saved Check batches are unreadable or corrupt.');continue; }
    if (saved?.intent !== 'check' && (Object.hasOwn(saved ?? {},'intent') || !Array.isArray(saved?.rows) || !saved.rows.every(row=>isObject(row) && validSavedCheck(row)))) continue;
    if (saved.version !== 1 || saved.batch !== name || !Array.isArray(saved.rows) || typeof saved.root !== 'string') {
      partial=true;warn('Some saved Check batches have invalid original identity.');continue;
    }
    if (saved.origin !== origin || saved.login !== identity.login || String(saved.user_id) !== String(identity.userId)) {
      if (!saved.origin || !saved.login || saved.user_id == null) { partial=true;warn('Some saved Check batches lack runtime/account identity.'); }
      continue;
    }
    const tests = saved.source_selection == null ? [...new Set(saved.rows.filter(row=>!row?.unsent).map(row=>row?.test))] : saved.source_selection.tests;
    if (!Array.isArray(tests) || new Set(tests).size !== tests.length || tests.some(path=>typeof path !== 'string' || !path || path.startsWith('/') || path.split('/').some(part=>part === '..') || path.includes('\\'))) {
      partial=true;warn('Some saved Check batches lack a safe original selection.');continue;
    }
    let admission;
    try { const eligibilityPort = ports.evidenceEligibility ?? ports.readEvidenceEligibility ?? (() => ({state:'unavailable',reason:'workflow evidence eligibility port is not bound'})); admission = await eligibilityPort({root,producerRoot:saved.root,tests,source_sha256:saved.source_sha256,runId:saved.association?.runId??null,stage:saved.association?.stage??null}, {env:ports.env,captureSource:ports.captureSource,...ports.evidencePorts}); }
    catch { admission = null; }
    const sameRoot = await real(saved.root) === await real(root);
    if (admission?.state !== 'eligible' && (!sameRoot || saved.association)) { partial=true;warn('Some saved Check history was not admitted by workspace ownership.');continue; }
    const stage = admission?.state === 'eligible' ? admission.stage : sameRoot && !saved.association ? 'current' : 'unavailable';
    let currentness = 'unavailable', originalSource = null;
    if (/^[a-f0-9]{64}$/.test(saved.source_sha256 ?? '')) {
      try {
        const sourceRoot = admission?.sourceAnchor?.root ?? root;
        const selection = {tests,appMap:null,...(saved.source_selection ? {excludeFixtureProjects:saved.source_selection.exclude_fixture_projects === true} : saved.exclude_fixture_projects ? {excludeFixtureProjects:true} : {})};
        const original = await capture(sourceRoot,selection);
        currentness = original.sha256 === saved.source_sha256 ? 'current' : 'stale';
        if (currentness === 'current') originalSource = original;
        const nativeTests = saved.rows.filter(row=>row?.native_only?.length).map(row=>row.test);
        if (saved.native_source != null || nativeTests.length) {
          const nativeIdentity = saved.native_source;
          if (!isObject(nativeIdentity) || typeof nativeIdentity.sha256 !== 'string' || !/^[a-f0-9]{64}$/.test(nativeIdentity.sha256)
            || !Array.isArray(nativeIdentity.tests) || !nativeIdentity.tests.length
            || new Set(nativeIdentity.tests).size !== nativeIdentity.tests.length
            || nativeIdentity.tests.some(path=>typeof path !== 'string' || !path || path.startsWith('/') || path.includes('\\') || path.split('/').some(part=>!part || part==='.' || part==='..'))
            || !isDeepStrictEqual([...nativeIdentity.tests].sort(),[...nativeTests].sort())) throw Error('original native source identity unavailable');
          const native = await capture(sourceRoot,{...selection,tests:nativeIdentity.tests});
          if (typeof native.sha256 !== 'string' || !/^[a-f0-9]{64}$/.test(native.sha256)) throw Error('original native capture unavailable');
          if (native.sha256 !== nativeIdentity.sha256) currentness='stale';
        }
      } catch (error) {
        if (error?.unboundPort) throw error;
        if (currentness !== 'stale') currentness='unavailable';
        partial=true;warn('Some original-batch source selections are unavailable.');
      }
    }
    const created_at = typeof saved.created_at === 'string' && Number.isFinite(Date.parse(saved.created_at)) ? saved.created_at : null;
    const snapshots = Array.isArray(saved.contract_snapshots) ? saved.contract_snapshots : [];
    const manifest = Array.isArray(saved.files) ? new Set(saved.files) : null;
    const claims = new Map();
    let claimFiles = 0, claimsUnavailable = false;
    try {
      for (const file of await files.list(folder)) {
        const match = /^([a-f0-9]{64})\.[0-9]+\.dispatch\.json$/.exec(file);
        if (!match) continue;
        claimFiles++;
        try {
          const claim = await read(join(folder,file));
          if (!UUID.test(claim?.id ?? '')) throw Error('invalid dispatch claim');
          claims.set(claim.id,[...(claims.get(claim.id) ?? []),match[1]]);
        } catch { partial=true;warn('Some original Check dispatch identities are unavailable.'); }
      }
    } catch { claimsUnavailable=true;partial=true;warn('Original Check dispatch identities are unavailable.'); }
    let capabilities = null;
    const lintId = Array.isArray(saved.lint?.request_ids) ? saved.lint.request_ids.at(-1) : null;
    if (UUID.test(lintId ?? '')) {
      try {
        const lint = await read(join(folder,`${lintId}.json`));
        if (!sameJob(lint,lintId,'lint') || lint.source_sha256 != null && saved.source_sha256 != null && lint.source_sha256 !== saved.source_sha256) throw Error('mismatched original lint');
        if (Array.isArray(lint.result?.capabilities)) capabilities = lint.result.capabilities;
      } catch { partial=true;warn('Some original Check source manifests are unavailable or mismatched.'); }
    }
    const inconsistent = () => { partial=true;warn('Some saved Check rows contradict their original selection, Story, source or request identity.'); };
    for (const row of saved.rows) {
      if (!row || !wanted.has(row.test)) continue;
      const story_path = row.story_path ?? (Array.isArray(saved.contract_snapshots) ? saved.contract_snapshots : []).find(story=>Array.isArray(story?.tests) && story.tests.includes(row.test))?.story_path
        ?? (typeof row.story === 'string' && row.story.endsWith('.md') ? row.story : (()=>{const paths=[...new Set((Array.isArray(saved.files)?saved.files:[]).filter(path=>typeof path==='string' && path.endsWith('.md') && basename(path,'.md')===row.story))];return paths.length===1?paths[0]:null;})());
      if (typeof story_path !== 'string' || !story_path || story_path.startsWith('/') || story_path.includes('\\') || story_path.split('/').some(part=>!part || part==='.' || part==='..') || !Array.isArray(row.request_ids)) { partial=true;warn('Some saved Check rows lack original Story or request identity.');continue; }
      const ownSnapshots = snapshots.filter(story=>Array.isArray(story?.tests) && story.tests.includes(row.test));
      const snapshot = ownSnapshots[0];
      const sent = row.request_ids.length > 0;
      if (sent && !validSavedCheck(row)) { inconsistent();continue; }
      const originalFootprint = originalSource?.stories?.find(story=>story.tests?.includes(row.test));
      const duplicate = saved.rows.filter(other=>other?.test === row.test).length !== 1;
      const storyName = typeof row.story === 'string' ? row.story : null;
      const storyConflict = storyName && (storyName.endsWith('.md') ? storyName !== story_path : storyName !== basename(story_path,'.md'));
      const invalidSnapshot = ownSnapshots.length > 1 || (snapshot && (snapshot.story_path !== story_path
        || !Array.isArray(snapshot.files) || !snapshot.files.some(file=>file?.path === row.test)
        || !snapshot.files.some(file=>file?.path === story_path)
        || snapshot.files.some(file=>!file || typeof file.path !== 'string' || !/^[a-f0-9]{64}$/.test(file.sha256 ?? '') || manifest && !manifest.has(file.path))
        || new Set(snapshot.files.map(file=>file?.path)).size !== snapshot.files.length));
      const capabilityEntries = capabilities?.filter(item=>item?.path === row.test);
      const capability = capabilityEntries?.[0]?.report;
      const snapshotFiles = new Map((Array.isArray(snapshot?.files) ? snapshot.files : originalFootprint?.files ?? []).filter(isObject).map(file=>[file.path,file.sha256]));
      const capabilityConflict = sent && capabilities && (capabilityEntries.length !== 1
        || !Array.isArray(capability?.source?.files) || capability.source.scenario_sha256 !== snapshotFiles.get(row.test)
        || capability.source.files.some(file=>!isObject(file) || !/^[a-f0-9]{64}$/.test(file.sha256 ?? '') || snapshotFiles.has(file.path) && snapshotFiles.get(file.path) !== file.sha256)
        || !capability.source.files.some(file=>file?.path === story_path && file.sha256 === snapshotFiles.get(story_path))
        || !Array.isArray(capability.operations) || capability.operations.some(operation=>!(row.steps ?? []).some(step=>step.step_id === operation?.selection?.step_id
          && step.entry_path === operation.selection.prompt_path && step.operation === operation.selection.operation)));
      if (duplicate || storyConflict || invalidSnapshot || capabilityConflict
        || sent && (row.unsent || !tests.includes(row.test) || manifest && (!manifest.has(row.test) || !manifest.has(story_path)))
        || originalFootprint && (originalFootprint.story_path !== story_path || snapshot && !isDeepStrictEqual(snapshot,originalFootprint))) {
        inconsistent();continue;
      }
      // A legacy receipt without a snapshot can still retain a readable nonpass.
      // It cannot supply positive evidence without the original Story association.
      const boundStory = !!snapshot || originalFootprint?.story_path === story_path;
      if (sent && (!boundStory || !manifest)) { partial=true;warn('Some legacy Check history lacks original Story/source binding.'); }
      const retain = (view,request_id,evidence_kind,report_url) => observations.push({story_path,test:row.test,batch:name,request_id,evidence_kind,
        ...resultOutcome(view),created_at,report_url,source_sha256:typeof saved.source_sha256 === 'string' ? saved.source_sha256 : null,
        currentness,currentness_scope:'original-batch',stage:['current','pr1','before'].includes(stage)?stage:'unavailable'});
      if (!row.request_ids.length) {
        if (row.unsent && resultOutcome(row).state !== 'passed') retain(row,null,'local',null);
        continue;
      }
      for (const id of [...new Set(row.request_ids)]) {
        try {
          if (!UUID.test(id)) throw Error('invalid request identity');
          if (saved.rows.filter(other=>Array.isArray(other?.request_ids) && other.request_ids.includes(id)).length !== 1
            || claimsUnavailable || claimFiles > 0 && !claims.has(id)
            || claims.has(id) && (claims.get(id).length !== 1 || claims.get(id)[0] !== sha256(Buffer.from(row.test)))) {
            inconsistent();continue;
          }
          if (!claims.has(id)) { partial=true;warn('Some legacy Check receipts lack original dispatch ownership.'); }
          const originals = [];
          const admit = answer => {
            if (!sameJob(answer,id,'check')) { partial=true;warn('Some original Check receipts are missing, corrupt or mismatched.');return; }
            const report = answer.result?.report;
            const sourceMismatch = answer.source_sha256 != null && saved.source_sha256 != null && answer.source_sha256 !== saved.source_sha256;
            const files = new Map((Array.isArray(snapshot?.files) ? snapshot.files : originalFootprint?.files ?? []).filter(isObject).map(file=>[file.path,file.sha256]));
            const projectedMismatch = Array.isArray(report?.projected_context_bindings) && report.projected_context_bindings.some(binding=>
              !isObject(binding) || files.get(binding.prompt_path) !== binding.prompt_sha256 || !Array.isArray(binding.context_blobs) || binding.context_blobs.some(blob=>!isObject(blob) || files.get(blob.path) !== blob.sha256));
            const executionMismatch = Array.isArray(report?.call_depth) && report.call_depth.some(step=>
              !(row.steps ?? []).some(original=>original.step_id === step?.step_id && original.entry_path === step?.entry_path && original.operation === step?.operation));
            const malformedIdentity = isObject(report) && (Object.hasOwn(report,'projected_context_bindings') && !Array.isArray(report.projected_context_bindings)
              || Object.hasOwn(report,'call_depth') && !Array.isArray(report.call_depth));
            if (sourceMismatch || projectedMismatch || executionMismatch || malformedIdentity) { inconsistent();return; }
            // A whole-batch hash cannot identify the test that produced a receipt.
            // Without a dispatch claim, require actual execution that matches only
            // this producer test; an empty list proves no such relationship.
            const executionTests = Array.isArray(report?.call_depth) && report.call_depth.length
              ? saved.rows.filter(candidate=>tests.includes(candidate?.test) && report.call_depth.every(step=>(candidate.steps ?? []).some(original=>
                original.step_id === step?.step_id && original.entry_path === step?.entry_path && original.operation === step?.operation))) : [];
            const boundExecution = executionTests.length === 1 && executionTests[0].test === row.test;
            if (answer.source_sha256 == null || saved.source_sha256 == null) {
              partial=true;warn('Some legacy Check receipts lack a bound original source hash.');
            }
            if ((!boundStory || !manifest || saved.source_sha256 == null || !claims.has(id) && !boundExecution) && resultOutcome(projectAnswer(answer,{test:row.test,steps:row.steps??[]})).state === 'passed') return;
            if (!originals.some(previous=>isDeepStrictEqual(previous,answer))) originals.push(answer);
          };
          try {
            const previous = await read(join(folder,`${id}.observations.json`));
            if (!Array.isArray(previous)) throw Error('invalid original Check observations');
            for (const answer of previous) admit(answer);
          } catch (error) { if (error.code !== 'ENOENT') { partial=true;warn('Some retained original Check observations are unavailable.'); } }
          try { admit(await read(join(folder,`${id}.json`))); }
          catch { partial=true;warn('Some original Check receipts are missing, corrupt or mismatched.'); }
          for (const answer of originals) {
            const secrets = [...(context.secrets??[]),identity.token].filter(Boolean);
            const view = projectAnswer(answer,{origin:saved.origin,steps:row.steps??[],criterionTexts:row.criterion_texts??{},test:row.test,secrets});
            retain(view,id,'receipt',validLink(cleanText(answer.report_url,secrets),saved.origin,'report'));
          }
        } catch { partial=true;warn('Some original Check receipts are missing, corrupt or mismatched.'); }
      }
    }
  }
  observations.sort((a,b)=>(a.created_at === null ? Infinity : Date.parse(a.created_at))-(b.created_at === null ? Infinity : Date.parse(b.created_at)) || a.batch.localeCompare(b.batch) || a.test.localeCompare(b.test) || String(a.request_id??'').localeCompare(String(b.request_id??'')));
  return project(partial ? 'partial' : 'available');
}

// Read receipts without StateStore.folder: status must never allocate or mutate runtime state.
export async function savedStoryEvidence(input, ports = {}) {
  return createSavedStoryEvidenceReader(ports)(input);
}

export function createSavedStoryEvidenceReader(ports = {}) {
  const captures = new Map();
  return input => readSavedStoryEvidence(input, ports, captures);
}

async function readSavedStoryEvidence({ root, comparisonRoot = root, withTests = false, anyRoot = false, limit = null }, ports, captures) {
  const env = ports.env ?? process.env;
  const read = ports.readFile ?? (path => readFileSync(path, 'utf8'));
  const list = ports.readDir ?? (path => readdirSync(path));
  const canonical = ports.realpath ?? realpathSync;
  const capture = ports.captureSource ?? ((r, opts) => captureSource(r, opts, ports));
  const stories = [], warnings = [];
  const warning = (path, error) => warnings.push(`Could not read saved checks ${path} (${cleanText(error?.code ?? error?.message ?? 'invalid record')}).`);
  const legacyHint = () => warnings.push('Older checks are not counted; run pdd test again.');
  const real = async path => { try { return await canonical(path); } catch { return resolve(path); } };
  const wanted = anyRoot ? null : await real(root);
  const directory = join(resolve(env.PDD_STATE_DIR || join(env.HOME || homedir(), '.pdd', 'runtime')), 'batches');
  const relativeFile = path => typeof path === 'string' && path.length > 0 && !path.startsWith('/') && !path.includes('\\')
    && path.split('/').every(part => part && part !== '.' && part !== '..');
  let names;
  try { names = await list(directory); }
  catch (error) { if (error.code !== 'ENOENT') warning(directory, error); return { stories, warnings }; }
  const all = names.filter(name => typeof name === 'string' && BATCH.test(name)).sort();
  for (const name of Number.isSafeInteger(limit) && limit > 0 ? all.slice(-limit) : all) {
    const folder = join(directory, name), path = join(folder, 'batch.json');
    let batch;
    try {
      batch = JSON.parse(await read(path));
      if (!isObject(batch) || batch.version !== 1 || batch.batch !== name || typeof batch.root !== 'string' || !Array.isArray(batch.rows)) throw Error('invalid batch');
    } catch (error) { warning(path, error); continue; }
    if (!anyRoot && await real(batch.root) !== wanted) continue;
    const legacy = !Object.hasOwn(batch, 'intent');
    if (batch.intent !== 'check') {
      if (!legacy) continue;
      if (!batch.rows.every(row => isObject(row) && validSavedCheck(row))) { legacyHint(); continue; }
    }
    const valid = batch.rows.every(row => isObject(row) && relativeFile(row.test) && relativeFile(row.story) && Array.isArray(row.request_ids));
    if (!valid) { warning(path, Error('invalid Story identity')); continue; }
    // Older batches saved the display basename; only a unique captured path can recover its identity.
    const rows = batch.rows.map(row => {
      if (row.story.endsWith('.md')) return row;
      const candidates = [...new Set((Array.isArray(batch.files) ? batch.files : []).filter(file => relativeFile(file)
        && file.endsWith('.md') && basename(file, '.md') === row.story))];
      return candidates.length === 1 ? { ...row, story: candidates[0] } : null;
    });
    if (rows.some(row => row === null)) { warning(path, Error('missing or ambiguous Story identity')); continue; }
    let current = false;
    if (comparisonRoot !== null && /^[a-f0-9]{64}$/.test(batch.source_sha256 ?? '')) {
      try {
        const folder = await real(comparisonRoot), tests = [...new Set(batch.rows.map(row => row.test))].sort();
        const excludeFixtureProjects = batch.exclude_fixture_projects === true;
        const key = JSON.stringify([folder, tests, excludeFixtureProjects]);
        if (!captures.has(key)) captures.set(key, Promise.resolve().then(() => capture(folder, { tests, appMap: null, ...(excludeFixtureProjects ? { excludeFixtureProjects: true } : {}) }))
          .then(source => ({ sha256: source.sha256 })).catch(error => ({ error })));
        const source = await captures.get(key);
        if (source.error) throw source.error;
        current = source.sha256 === batch.source_sha256;
      } catch (error) { if (error?.unboundPort) throw error; warning(path, error); }
    }
    const selected = new Map(), sent = new Map(), grouped = new Map(), extra = new Map();
    // withTests: the failed checks, refusals and states of each Story's rows, and the rows that were never sent.
    const note = (story, add) => { const was = extra.get(story) ?? { failed: 0, failedSteps: [], refusals: [], states: [], codes: [], fixes: [], sent: false }; extra.set(story, add(was)); };
    const codesOf = list => Array.isArray(list) ? list.map(item => item?.code).filter(code => typeof code === 'string') : [];
    const fixesOf = list => Array.isArray(list) ? list.map(item => item?.fix).filter(fix => typeof fix === 'string' && fix.trim()) : [];
    for (const row of rows) {
      if (!selected.has(row.story)) selected.set(row.story, new Set());
      selected.get(row.story).add(row.test);
    }
    for (const row of rows) {
      note(row.story, was => ({ ...was, refusals: [...new Set([...was.refusals, ...codesOf(row.refusals)])], fixes: [...new Set([...was.fixes, ...fixesOf(row.refusals)])],
        states: [...new Set([...was.states, ...(typeof row.recovery_state === 'string' ? [row.recovery_state] : [])])],
        codes: [...new Set([...was.codes, ...(typeof row.reason?.code === 'string' ? [row.reason.code] : [])])], sent: was.sent || row.request_ids.length > 0 }));
      if (!row.request_ids.length) continue;
      if (!sent.has(row.story)) sent.set(row.story, new Set());
      sent.get(row.story).add(row.test);
      let pass = false;
      const id = row.request_ids.at(-1);
      if (typeof id === 'string' && UUID.test(id)) {
        const receiptPath = join(folder, `${id}.json`);
        try {
          const answer = JSON.parse(await read(receiptPath));
          if (answer?.requestId === id && answer.id === id && answer.command === 'check') {
            const view = projectAnswer(answer, { origin: batch.origin, steps: row.steps ?? [], criterionTexts: row.criterion_texts ?? {}, test: row.test });
            const failedChecks = Array.isArray(view.failed_checks) ? view.failed_checks : [];
            note(row.story, was => ({ ...was, failed: was.failed + failedChecks.length,
              failedSteps: [...new Set([...was.failedSteps, ...failedChecks.map(check => check?.step_id).filter(step => typeof step === 'string' && step)])].slice(0, 10),
              refusals: [...new Set([...was.refusals, ...codesOf(view.refusals)])], fixes: [...new Set([...was.fixes, ...fixesOf(view.refusals)])] }));
            let authored = Object.keys(row.criterion_texts ?? {});
            if (legacy) {
              const fromChecks = [...new Set(row.steps.flatMap(step => step.checks.map(check => check.criterion_id)))];
              if (authored.length !== row.criteria_total || !fromChecks.every(id => authored.includes(id))) authored = fromChecks;
            }
            const criteria = answer.result?.report?.criterion_results;
            if (legacy && !(Array.isArray(criteria) && criteria.length === row.criteria_total
              && new Set(criteria.map(item => item?.criterion_id)).size === row.criteria_total
              && criteria.every(item => authored.includes(item?.criterion_id)))) legacyHint();
            pass = view.state === 'passed' && Number.isInteger(row.criteria_total) && row.criteria_total > 0
              && authored.length === row.criteria_total && view.criteria?.total === row.criteria_total
              && view.criteria.passed === row.criteria_total && view.checks?.total > 0 && view.checks.passed === view.checks.total
              && Array.isArray(criteria) && new Set(criteria.map(item => item?.criterion_id)).size === row.criteria_total
              && criteria.every(item => authored.includes(item?.criterion_id) && item.status === 'passed');
          }
        } catch (error) { warning(receiptPath, error); }
      }
      const at = Number.isFinite(row.ended_at) ? row.ended_at : Date.parse(batch.created_at) || 0;
      const previous = grouped.get(row.story);
      grouped.set(row.story, { story: row.story, pass: pass && (previous?.pass ?? true), current, result: 'no verdict', at: Math.max(previous?.at ?? at, at) });
    }
    // withTests: pdd's own fix texts of a Story's refusals (its saved warnings, then each refusal's fix).
    const advised = story => {
      const { fixes, ...info } = extra.get(story), tests = [...selected.get(story)];
      const warned = (Array.isArray(batch.warnings) ? batch.warnings : []).filter(text => typeof text === 'string'
        && tests.some(test => text.startsWith(`Warning: ${test} `)) && info.refusals.some(code => text.includes(code)));
      return { ...info, advice: [...new Set([...warned, ...fixes])].slice(0, 3).map(text => text.slice(0, 800)) };
    };
    for (const row of grouped.values()) {
      if (row.pass && sent.get(row.story).size !== selected.get(row.story).size) continue;
      if (row.pass) row.result = '✓';
      stories.push(withTests ? { ...row, tests: [...selected.get(row.story)].sort(), ...advised(row.story), sent: true } : row);
    }
    // withTests: a Story whose tests were never sent (refused before execution, interrupted) is listed too.
    if (withTests) for (const story of extra.keys()) if (!grouped.has(story)) {
      const at = Math.max(0, ...rows.filter(row => row.story === story).map(row => Number.isFinite(row.ended_at) ? row.ended_at : Date.parse(batch.created_at) || 0));
      stories.push({ story, pass: false, current, result: 'not sent', at, tests: [...selected.get(story)].sort(), ...advised(story), sent: false });
    }
  }
  return { stories, warnings: [...new Set(warnings)] };
}

// Autopilot (#3241, rule B5): the Stories of root whose latest saved check can be sent once more. neverSent: no request
// ID, not run, no refusal, no local unsent mark, no access gate (held in maintenance, busy, stopped before sending).
// noVerdict: sent, and its saved answer ended with no verdict and no failed check (an AI provider failure). failed: a
// check failed (never sent again). A check that is still open, or whose answer was not saved, is in none of them.
// Local reads only, like savedStoryEvidence.
export async function resendableStoryChecks({ root, since = 0 }, ports = {}) {
  const env = ports.env ?? process.env;
  const read = ports.readFile ?? (path => readFileSync(path, 'utf8'));
  const list = ports.readDir ?? (path => readdirSync(path));
  const canonical = ports.realpath ?? realpathSync;
  const real = async path => { try { return await canonical(path); } catch { return resolve(path); } };
  const wanted = await real(root), directory = join(resolve(env.PDD_STATE_DIR || join(env.HOME || homedir(), '.pdd', 'runtime')), 'batches');
  const empty = { stories: [], neverSent: [], noVerdict: [], failed: [], maintenance: false };
  let names;
  try { names = await list(directory); } catch { return empty; }
  const latest = new Map();
  for (const name of names.filter(name => typeof name === 'string' && BATCH.test(name)).sort()) {
    let batch;
    try { batch = JSON.parse(await read(join(directory, name, 'batch.json'))); } catch { continue; }
    if (!isObject(batch) || batch.batch !== name || batch.intent !== 'check' || typeof batch.root !== 'string' || !Array.isArray(batch.rows)) continue;
    if (since > 0 && !(Date.parse(batch.created_at) >= since) || await real(batch.root) !== wanted) continue;
    const files = Array.isArray(batch.files) ? batch.files : [];
    const storyOf = row => typeof row?.story !== 'string' ? null : row.story.endsWith('.md') ? row.story
      : (found => found.length === 1 ? found[0] : null)([...new Set(files.filter(file => typeof file === 'string' && file.endsWith('.md') && basename(file, '.md') === row.story))]);
    // One row: never (never sent), sent-pass, failed, noVerdict (a saved answer with no verdict and no failed check), or other.
    const kind = async row => {
      const ids = Array.isArray(row.request_ids) ? row.request_ids : [];
      if (!ids.length) return row.recovery_state === 'not_run' && !(Array.isArray(row.refusals) && row.refusals.length) && !row.unsent && row.note?.code !== 'blocked' ? 'never' : 'other';
      if (row.recovery_state === 'passed') return 'pass';
      if (row.recovery_state === 'failed') return 'failed';
      const id = ids.at(-1);
      let answer = null;
      try { answer = typeof id === 'string' && UUID.test(id) ? JSON.parse(await read(join(directory, name, `${id}.json`))) : null; } catch { answer = null; }
      if (!sameJob(answer, id, 'check')) return 'other';
      const view = projectAnswer(answer, { origin: batch.origin, steps: row.steps ?? [], criterionTexts: row.criterion_texts ?? {}, test: row.test });
      if (answer.state === 'failed' || view.failed_checks?.length) return 'failed';
      return answer.state === 'unknown' ? 'noVerdict' : 'other';
    };
    const seen = new Map();
    for (const row of batch.rows) {
      const story = storyOf(row);
      if (!story) continue;
      const k = await kind(row), was = seen.get(story) ?? { kinds: [], notes: [] };
      seen.set(story, { kinds: [...was.kinds, k], notes: k === 'never' ? [...was.notes, String(row.note?.message ?? '')] : was.notes });
    }
    for (const [story, { kinds, notes }] of seen) {
      const state = kinds.includes('failed') ? 'failed' : kinds.includes('other') ? 'other' : kinds.includes('never') ? 'never' : kinds.includes('noVerdict') ? 'noVerdict' : 'pass';
      latest.set(story, { state, notes });
    }
  }
  const of = state => [...latest].filter(([, row]) => row.state === state).map(([story]) => story).sort();
  const neverSent = of('never'), noVerdict = of('noVerdict');
  return { stories: [...neverSent, ...noVerdict].sort(), neverSent, noVerdict, failed: of('failed'),
    maintenance: neverSent.some(story => latest.get(story).notes.some(note => /maintenance/i.test(note))) };
}

function validGithubIdentity(record) {
  return isObject(record)
    && typeof record.login === 'string' && record.login.length > 0 && !/\s/.test(record.login)
    && typeof record.user_id === 'string' && /^[1-9]\d*$/.test(record.user_id)
    && typeof record.token_sha256 === 'string' && /^[a-f0-9]{64}$/.test(record.token_sha256);
}
function validGithubUser(record) {
  return validGithubIdentity(record)
    && typeof record.cached_at === 'string' && Number.isFinite(Date.parse(record.cached_at));
}
const isGithubRateLimit = text => typeof text === 'string' && /rate limit|secondary rate limit|abuse detection/i.test(text);

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
  readGithubUser() {
    try {
      if (statOrNull(this.dir)?.isSymbolicLink()) return null;
      const path = join(this.dir, 'github-user.json'), stat = statOrNull(path);
      if (!stat?.isFile() || stat.isSymbolicLink()) return null;
      const record = JSON.parse(readFileSync(path, 'utf8'));
      return validGithubUser(record) ? { login: record.login, user_id: record.user_id, cached_at: record.cached_at, token_sha256: record.token_sha256 } : null;
    } catch { return null; }
  }
  readMatchingGithubIdentity(tokenSha256) {
    try {
      if (statOrNull(this.dir)?.isSymbolicLink()) return null;
      const path = join(this.dir, 'github-user.json'), stat = statOrNull(path);
      if (!stat?.isFile() || stat.isSymbolicLink()) return null;
      const record = JSON.parse(readFileSync(path, 'utf8'));
      return validGithubIdentity(record) && record.token_sha256 === tokenSha256
        ? { login: record.login, user_id: record.user_id, token_sha256: record.token_sha256 }
        : null;
    } catch { return null; }
  }
  writeGithubUser(record) {
    if (!validGithubUser(record)) return false;
    let folder;
    try {
      if (statOrNull(this.dir)?.isSymbolicLink()) return false;
      folder = this.folder();
    } catch { return false; }
    const path = join(folder, 'github-user.json');
    if (statOrNull(path)?.isSymbolicLink()) return false;
    const temporary = `${path}.${process.pid}.${randomUUID()}.tmp`;
    let text = `${JSON.stringify({ login: record.login, user_id: record.user_id, cached_at: record.cached_at, token_sha256: record.token_sha256 }, null, 2)}\n`;
    for (const secret of this.secrets) if (secret) text = text.split(secret).join('[secret]');
    try {
      const fd = openSync(temporary, 'wx', 0o600);
      try { chmodSync(temporary, 0o600); writeSync(fd, text); } finally { closeSync(fd); }
      renameSync(temporary, path);
      return true;
    } catch {
      try { unlinkSync(temporary); } catch { /* ignore temp cleanup failure */ }
      return false;
    }
  }
  deleteGithubUser() {
    try {
      if (statOrNull(this.dir)?.isSymbolicLink()) return;
      unlinkSync(join(this.dir, 'github-user.json'));
    } catch { /* ignore absent or unremovable cache file */ }
  }
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

function recordSecret(ports, ...values) {
  const remember = ports?.redaction?.remember;
  if (remember) remember(...values);
  if (ports?.rememberSecrets && ports.rememberSecrets !== remember) ports.rememberSecrets(...values);
  if (!remember && !ports?.rememberSecrets) fallbackRememberSecrets(...values);
}

function signIn(gh, store, ports, { forceRefresh = false, afterHttp401 = false, allowSavedLocalReadFallback = false, exitCode = 5 } = {}) {
  const now = ports?.now ?? Date.now, stderr = ports?.stderr ?? null;
  const token = gh(['auth', 'token']);
  if (token.error?.code === 'ENOENT') throw new Stop(exitCode, 'Install the GitHub CLI, then run gh auth login');
  const value = token.status === 0 ? String(token.stdout ?? '').trim() : '';
  if (!value) throw new Stop(exitCode, 'Run gh auth login');
  recordSecret(ports, value);
  if (store) store.secrets = [...new Set([...(store.secrets ?? []), value])];
  const tokenSha256 = sha256(Buffer.from(value, 'utf8'));
  const cached = store ? store.readGithubUser() : null;
  const matchingCached = cached && cached.token_sha256 === tokenSha256 ? cached : null;
  if (!forceRefresh && matchingCached) {
    return { token: value, login: matchingCached.login, userId: matchingCached.user_id, tokenSha256, fromCache: true, refreshedAfter401: false };
  }
  const user = gh(['api', 'user', '--jq', '.login + " " + (.id|tostring)']);
  const rawUser = user.status === 0 ? String(user.stdout ?? '').replace(/[\r\n]+$/, '') : '';
  const parts = rawUser ? rawUser.split(' ') : [];
  const [login, id] = parts.length === 2 ? parts : [];
  if (user.status === 0 && login && !/\s/.test(login) && /^[1-9]\d*$/.test(id ?? '')) {
    store?.writeGithubUser({ login, user_id: id, cached_at: new Date(now()).toISOString(), token_sha256: tokenSha256 });
    return { token: value, login, userId: id, tokenSha256, fromCache: false, refreshedAfter401: !!afterHttp401 };
  }
  const rawFailure = user.status === 0 ? '' : String(user.stderr || user.error?.code || '');
  const matchingIdentity = !afterHttp401 && allowSavedLocalReadFallback && user.status !== 0 && isGithubRateLimit(rawFailure)
    ? store?.readMatchingGithubIdentity(tokenSha256)
    : null;
  if (matchingIdentity) {
    if (stderr) line(stderr, `Warning: GitHub API rate limit reached; using saved GitHub login ${matchingIdentity.login} for this token.`);
    return { token: value, login: matchingIdentity.login, userId: matchingIdentity.user_id, tokenSha256, fromCache: true, refreshedAfter401: false };
  }
  const why = user.status === 0 ? '' : causeText(user.stderr || user.error?.code, [value]);
  throw new Stop(exitCode, `pdd could not read your GitHub login (gh api user${why ? `: ${why}` : ''}). Run gh auth status.`);
}

function authSession({ identity, store, ports, secrets = null, expectedOwnerLogin = null, ownerMismatchError = null, signInExitCode = 5, onRefresh = null }) {
  return { identity, store, ports, secrets, expectedOwnerLogin, ownerMismatchError, signInExitCode, onRefresh };
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
  constructor({ origin, token, ports, signal, auth }) { Object.assign(this, { origin, token, ports, signal, auth }); this.sources = new WeakMap(); }
  async sendOnce(path, init, ms) {
    if (this.signal?.aborted) return { lost: true };
    const controller = new AbortController(), stop = () => controller.abort();
    const timer = setTimeout(stop, ms);
    this.signal?.addEventListener('abort', stop, { once: true });
    const bearer = this.auth?.identity.token ?? this.token;
    const resolved = typeof init?.body === 'function' ? { ...init, body: init.body() } : init;
    try {
      const response = await this.ports.fetch(new URL(path, this.origin), { ...resolved, redirect: 'manual', signal: controller.signal,
        headers: { ...resolved?.headers, Authorization: `Bearer ${bearer}` } });
      const text = await response.text();
      let json = null;
      try { json = JSON.parse(text); } catch { json = null; }
      return { status: response.status, headers: response.headers, text, json };
    } catch (error) { return lostReply(error, this.origin); } finally { clearTimeout(timer); this.signal?.removeEventListener('abort', stop); }
  }
  async send(path, init, ms) {
    const previousToken = this.auth?.identity.token ?? this.token;
    const first = await this.sendOnce(path, init, ms);
    if (this.auth && path !== '/v1/capacity' && [200, 202].includes(first.status)) this.auth.verifiedByServer = true;
    if (first.status !== 401 || !this.auth) return first;
    this.auth.store?.deleteGithubUser();
    if (!this.auth.identity.fromCache || this.auth.identity.refreshedAfter401) return first;
    this.auth.identity.fromCache = false;
    this.auth.identity.refreshedAfter401 = true;
    let refreshed;
    try {
      refreshed = signIn(this.ports.gh, this.auth.store, this.ports, {
        forceRefresh: true,
        afterHttp401: true,
        exitCode: this.auth.signInExitCode,
      });
    } catch (error) {
      if (error instanceof Stop) { this.auth.store?.deleteGithubUser(); return first; }
      throw error;
    }
    Object.assign(this.auth.identity, refreshed, { fromCache: false, refreshedAfter401: true });
    this.token = refreshed.token;
    if (Array.isArray(this.auth.secrets) && !this.auth.secrets.includes(refreshed.token)) this.auth.secrets.push(refreshed.token);
    this.auth.onRefresh?.(this.auth.identity);
    const expectedOwner = typeof this.auth.expectedOwnerLogin === 'function' ? this.auth.expectedOwnerLogin() : this.auth.expectedOwnerLogin;
    if (expectedOwner && refreshed.login !== expectedOwner) throw this.auth.ownerMismatchError(expectedOwner);
    if (this.auth.verifiedByServer && refreshed.token === previousToken) {
      this.auth.store?.deleteGithubUser();
      return first;
    }
    const retry = await this.sendOnce(path, init, ms);
    if (retry.status === 401) this.auth.store?.deleteGithubUser();
    else if (path !== '/v1/capacity' && [200, 202].includes(retry.status)) this.auth.verifiedByServer = true;
    return retry;
  }
  post(path, request, tar, timeoutMs = this.ports.postMs) {
    const makeForm = () => {
      const form = new FormData();
      form.set('request', new Blob([JSON.stringify(request)], { type: 'application/json' }), 'request.json');
      let source = this.sources.get(tar);
      if (!source) { source = new Blob([tar], { type: 'application/x-tar' }); this.sources.set(tar, source); }
      form.set('source', source, 'source.tar');
      return form;
    };
    return this.send(path, { method: 'POST', body: makeForm }, timeoutMs);
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

// The free interpreter health check for Autopilot: one GET /v1/capacity with the gh token, the same read that admission
// uses. It sends no source, starts no check and makes no AI call. healthy: the server answered and is not in
// maintenance; unavailable: no answer, HTTP 408, 429 or 5xx, or maintenance; access: an answer that is neither, a
// sign-in or a setup problem on this machine that a person must fix (`fix` names how).
const HEALTH_SIGN_IN = 'Run gh auth status on this machine; sign in again with gh auth login, or ask the PDD team for interpreter access.';
const HEALTH_ADDRESS = 'Check PDD_RUNTIME_URL in the Autopilot environment: it must be the interpreter origin itself (unset it to use the default).';
export async function checkRuntimeHealth({ env = process.env } = {}, givenPorts = {}) {
  const ports = withDefaults({ ...givenPorts, env });
  let origin;
  try { origin = runtimeOrigin(env); } catch { return { state: 'access', detail: 'PDD_RUNTIME_URL is not an HTTPS origin', fix: HEALTH_ADDRESS }; }
  let token = '';
  try { const reply = ports.gh(['auth', 'token']); token = reply.status === 0 ? String(reply.stdout ?? '').trim() : ''; } catch { token = ''; }
  recordSecret(ports, token);
  if (!token) return { state: 'access', detail: 'no gh sign-in', fix: HEALTH_SIGN_IN };
  const reply = await new Runtime({ origin, token, ports }).send('/v1/capacity', { method: 'GET' }, givenPorts.timeoutMs ?? 10_000);
  if (reply.lost) return { state: 'unavailable', detail: reply.unreachable ? 'not reached' : 'no answer' };
  if (reply.status >= 500 || [408, 429].includes(reply.status)) return { state: 'unavailable', detail: `HTTP ${reply.status}` };
  if (reply.status === 200 && isObject(reply.json)) {
    const until = Date.parse(reply.json.maintenance?.until);
    // A maintenance answer names its end and reason, so the Autopilot core can wait for it (#3241).
    return Number.isFinite(until) && until > ports.now() ? { state: 'unavailable', detail: 'maintenance', until: new Date(until).toISOString(), reason: cleanText(reply.json.maintenance?.reason, [token]) || null }
      : { state: 'healthy', detail: 'HTTP 200' };
  }
  // An older interpreter without the capacity read still answered with JSON; a 404 page that is not JSON is a wrong address.
  if (reply.status === 404 && isObject(reply.json)) return { state: 'healthy', detail: 'HTTP 404' };
  if ([401, 403].includes(reply.status)) return { state: 'access', detail: `HTTP ${reply.status}: The interpreter did not accept the gh login`, fix: HEALTH_SIGN_IN };
  if (reply.status >= 300 && reply.status < 400) return { state: 'access', detail: `HTTP ${reply.status}: a redirect, not an interpreter answer`, fix: HEALTH_ADDRESS };
  return { state: 'access', detail: `HTTP ${reply.status}${[200, 404].includes(reply.status) ? ' that is not an interpreter answer' : ''}`, fix: HEALTH_ADDRESS };
}

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
function accountingProof(record) {
  const usage = record?.usage, result = record?.result, reports = [record?.report, result?.report].filter(isObject);
  if (!isObject(usage)) return false;
  const supplied = (object, key) => isObject(object) && Object.hasOwn(object, key);
  const surfaces = [record, usage, result, ...reports].filter(isObject);
  const dispatches = surfaces.filter(object => supplied(object, 'dispatch')).map(object => object.dispatch);
  if (!dispatches.length || dispatches.some(value => value !== 'not_started')) return false;
  const flagSurfaces = surfaces.filter(object => supplied(object, 'accounting_complete')).map(object => object.accounting_complete);
  if (!flagSurfaces.length || flagSurfaces.some(value => value !== true)) return false;
  const counters = surfaces.flatMap(object => ['calls', 'known_calls', 'unknown_calls', 'provider_calls'].map(key => [object, key]));
  if (!supplied(usage, 'calls') || usage.calls !== 0 || !counters.some(([object, key]) => key === 'provider_calls' && supplied(object, key))) return false;
  for (const [object, key] of counters) if (supplied(object, key)) {
    const value = object[key];
    if (!Number.isSafeInteger(value) || value < 0 || value !== 0) return false;
  }
  if (surfaces.some(object => supplied(object, 'job_created') && object.job_created !== false)) return false;
  if (supplied(record, 'calls') && supplied(usage, 'calls') && record.calls !== usage.calls) return false;
  if (supplied(usage, 'known_calls') && supplied(usage, 'calls') && usage.known_calls !== usage.calls) return false;
  if (supplied(usage, 'unknown_calls') && usage.unknown_calls !== 0) return false;
  const resultSurfaces = [result, ...reports].filter(isObject);
  if (resultSurfaces.some(object => supplied(object, 'criterion_results') && (!Array.isArray(object.criterion_results) || object.criterion_results.length))) return false;
  for (const surface of resultSurfaces) if (supplied(surface, 'samples')) {
    if (!Array.isArray(surface.samples)) return false;
    for (const sample of surface.samples) {
      if (!isObject(sample) || !Array.isArray(sample.steps)) return false;
      for (const step of sample.steps) {
        if (!isObject(step) || !Array.isArray(step.checks) || step.checks.length) return false;
      }
    }
  }
  if ([record, ...resultSurfaces].some(object => supplied(object, 'checks') && (!Array.isArray(object.checks) || object.checks.length))) return false;
  return true;
}
function capacityRefusal(refusals, headers) {
  return refusals.map(item => capacityDelay(item, headers)).find(wait => wait !== null) ?? null;
}
function checkCapacityCandidate(answer, headers) {
  const report = answer?.result?.report;
  return answer?.command === 'check' && answer.state === 'refused'
    && capacityRefusal([report?.refusal, ...(Array.isArray(answer.result?.refusals) ? answer.result.refusals : [])], headers) !== null;
}
function checkCapacity(answer, headers) {
  if (!checkCapacityCandidate(answer, headers) || !accountingProof(answer)) return null;
  return capacityRefusal([answer.result?.report?.refusal, ...(Array.isArray(answer.result?.refusals) ? answer.result.refusals : [])], headers);
}
function admissionCapacityCandidate(record, headers) {
  return capacityDelay(record?.error, headers) !== null || record?.error?.code === 'maintenance';
}
function isAdmissionCapacityRecord(record) {
  return isObject(record) && isObject(record.error);
}
function admissionMatches(record, id) {
  if (!isObject(record)) return false;
  for (const surface of [record, record.result].filter(isObject)) {
    for (const key of ['requestId', 'id']) if (Object.hasOwn(surface, key) && surface[key] !== id) return false;
    if (Object.hasOwn(surface, 'command') && surface.command !== 'check') return false;
  }
  return true;
}
function capacityHistoryHasEvidence(context, row) {
  if (!context.store || !context.folder) return false;
  for (const id of row.request_ids ?? []) {
    const admission = context.store.read(join(context.folder, `${id}.admission.json`));
    const latest = context.store.read(join(context.folder, `${id}.json`));
    const prior = context.store.read(join(context.folder, `${id}.observations.json`));
    if (isAdmissionCapacityRecord(admission) && admissionCapacityCandidate(admission)
      || [...(Array.isArray(prior) ? prior : []), ...(latest ? [latest] : [])].some(answer => checkCapacityCandidate(answer))) return true;
  }
  return false;
}
function capacityHistorySafe(context, row) {
  if (!context.store || !context.folder) return false;
  const restartOrigin = structuredRestartOrigin(context, row);
  let found = false;
  for (const id of row.request_ids ?? []) {
    if (id === restartOrigin) continue;
    const admission = context.store.read(join(context.folder, `${id}.admission.json`));
    const latest = context.store.read(join(context.folder, `${id}.json`));
    const prior = context.store.read(join(context.folder, `${id}.observations.json`));
    const history = [...(Array.isArray(prior) ? prior : []), ...(latest ? [latest] : [])];
    const terminalHistory = history.filter(answer => accountingEnd(answer, id));
    const firstTerminal = history.findIndex(answer => accountingEnd(answer, id));
    const progressConflict = history.some((answer, index) => !accountingEnd(answer, id)
      && (!['queued', 'running'].includes(answer?.state) || index > firstTerminal));
    const admissionCandidate = isAdmissionCapacityRecord(admission) && admissionCapacityCandidate(admission);
    const answerCandidates = terminalHistory.filter(answer => checkCapacityCandidate(answer));
    if (!admissionCandidate && !answerCandidates.length) continue;
    found = true;
    if (admissionCandidate && (!admissionMatches(admission, id) || !accountingProof(admission) || history.some(answer => !checkCapacityCandidate(answer)))) return false;
    if (answerCandidates.some(answer => !accountingProof(answer))) return false;
    if (answerCandidates.length !== terminalHistory.length || progressConflict) return false;
  }
  // A durable structured restart is the one bounded exception. Its unknown
  // usage stays in the published totals, but does not block a later zero-work
  // capacity receipt from continuing that replacement.
  const accountingRow = restartOrigin ? { ...row, request_ids: row.request_ids.filter(id => id !== restartOrigin) } : row;
  return found && accumulatedAccounting(context, accountingRow).accounting_complete === true;
}
function structuredRestartOrigin(context, row) {
  const fuse = claimPath(context, row).replace(/\.0\.dispatch\.json$/, '.restart.json');
  if (row.restart_used !== true || !statOrNull(fuse)) return null;
  const origins = (row.request_ids ?? []).filter(id => {
    const latest = context.store.read(join(context.folder, `${id}.json`));
    const prior = context.store.read(join(context.folder, `${id}.observations.json`));
    const history = [...(Array.isArray(prior) ? prior : []), ...(latest ? [latest] : [])]
      .filter((item, index, list) => list.findIndex(other => isDeepStrictEqual(other, item)) === index);
    const terminal = history.filter(answer => accountingEnd(answer, id));
    return history.length > 0 && history.every(answer => sameJob(answer, id, 'check'))
      && terminal.length > 0 && terminal.every(restarted);
  });
  return origins.length === 1 ? origins[0] : null;
}
function capacityRetryAllowed(context, row) {
  if (!capacityHistorySafe(context, row)) return false;
  const id = row.request_ids?.at(-1);
  if (!id) return false;
  const admission = context.store.read(join(context.folder, `${id}.admission.json`));
  if (isAdmissionCapacityRecord(admission) && admissionCapacityCandidate(admission))
    return admissionMatches(admission, id) && accountingProof(admission);
  const latest = context.store.read(join(context.folder, `${id}.json`));
  const prior = context.store.read(join(context.folder, `${id}.observations.json`));
  const history = [...(Array.isArray(prior) ? prior : []), ...(latest ? [latest] : [])]
    .filter((item, index, list) => list.findIndex(other => isDeepStrictEqual(other, item)) === index);
  const terminal = history.filter(answer => accountingEnd(answer, id));
  return terminal.length > 0 && terminal.every(answer => checkCapacityCandidate(answer) && accountingProof(answer));
}
function usagePart(record) {
  const usage = isObject(record?.usage) ? record.usage : {}, result = isObject(record?.result) ? record.result : {}, reports = [record?.report, result?.report].filter(isObject);
  const counter = value => Number.isSafeInteger(value) && value >= 0 ? value : undefined;
  const surfaces = [record, usage, result, ...reports];
  const values = key => surfaces.filter(source => Object.hasOwn(source, key)).map(source => counter(source[key]));
  const invalid = ['calls', 'known_calls', 'unknown_calls', 'provider_calls'].some(key => values(key).some(value => value === undefined));
  const conflicting = ['calls', 'known_calls', 'unknown_calls', 'provider_calls'].some(key => new Set(values(key).filter(value => value !== undefined)).size > 1);
  const flags = surfaces.filter(source => Object.hasOwn(source, 'accounting_complete')).map(source => source.accounting_complete);
  const invalidFlag = flags.some(value => typeof value !== 'boolean');
  const conflictingFlags = new Set(flags.filter(value => typeof value === 'boolean')).size > 1;
  const validCalls = values('calls').filter(value => value !== undefined);
  const validKnown = values('known_calls').filter(value => value !== undefined);
  const validUnknown = values('unknown_calls').filter(value => value !== undefined);
  const validProvider = values('provider_calls').filter(value => value !== undefined);
  const calls = counter(usage.calls);
  const unknownRaw = Math.max(...validUnknown, 0);
  const providerCalls = validProvider.length ? Math.max(...validProvider) : undefined;
  const deductedTotals = [...validCalls, ...validProvider].map(value => Math.max(0, value - unknownRaw));
  const known = validKnown.length ? Math.max(...validKnown, 0) : Math.max(...deductedTotals, 0);
  const complete = !invalid && !conflicting && !invalidFlag && !conflictingFlags && !flags.includes(false) && calls !== undefined
    && unknownRaw === 0 && (!validKnown.length || known <= calls) && (providerCalls === undefined || providerCalls === calls);
  const zeroWork = complete && calls === 0 && ((checkCapacityCandidate(record) && accountingProof(record))
    || (isAdmissionCapacityRecord(record) && admissionCapacityCandidate(record) && accountingProof(record)));
  return { known, unknown: complete ? 0 : Math.max(1, unknownRaw), complete, total: complete ? calls : null,
    zeroWork, tokens: tokenUsageOf(record, { incomplete: !complete }) };
}
function attemptAccounting(context, id) {
  const path = join(context.folder, `${id}.json`), answer = context.store.read(path);
  const observations = context.store.read(join(context.folder, `${id}.observations.json`));
  const admission = context.store.read(join(context.folder, `${id}.admission.json`));
  const history = [...(Array.isArray(observations) ? observations : []), ...(answer ? [answer] : [])]
    .filter((item, index, list) => list.findIndex(other => isDeepStrictEqual(other, item)) === index);
  const matchingHistory = history.filter(item => sameJob(item, id, 'check'));
  const terminalHistory = matchingHistory.filter(item => accountingEnd(item, id));
  const accountingHistory = terminalHistory.length ? terminalHistory : matchingHistory.slice(-1);
  const admissionCandidate = isAdmissionCapacityRecord(admission) && admissionCapacityCandidate(admission);
  const unsafeAdmission = admissionCandidate && !accountingProof(admission);
  const admissionConflict = admissionCandidate && (!admissionMatches(admission, id) || unsafeAdmission || history.some(item => !checkCapacityCandidate(item)));
  const records = [...accountingHistory, ...(admission ? [admission] : [])];
  const emptyTokens = { input_tokens: 'unknown', cached_input_tokens: 'unknown', output_tokens: 'unknown', cached_input_share: null };
  if (!records.length) return { known: 0, unknown: 1, complete: false, total: null, zeroWork: false, tokens: emptyTokens };
  const parts = records.map(usagePart), known = Math.max(...parts.map(part => part.known));
  const unknown = Math.max(1, ...parts.map(part => part.unknown));
  const complete = !admissionConflict && parts.every(part => part.complete) && new Set(parts.map(part => part.total)).size === 1;
  const zeroWork = complete && parts[0].total === 0 && parts.every(part => part.zeroWork);
  const agree = key => complete && !zeroWork && parts.every(part => typeof part.tokens[key] === 'number') && new Set(parts.map(part => part.tokens[key])).size === 1
    ? parts[0].tokens[key] : 'unknown';
  const input_tokens = agree('input_tokens');
  const cached_input_tokens = typeof input_tokens === 'number' ? agree('cached_input_tokens') : 'unknown';
  const output_tokens = agree('output_tokens');
  const cached_input_share = typeof input_tokens === 'number' && typeof cached_input_tokens === 'number' && input_tokens > 0 && cached_input_tokens <= input_tokens
    ? cached_input_tokens / input_tokens : null;
  return { known, unknown: complete ? 0 : unknown, complete, total: complete ? parts[0].total : null,
    zeroWork, tokens: { input_tokens, cached_input_tokens, output_tokens, cached_input_share } };
}
function accumulatedAccounting(context, row) {
  const ids = row.request_ids ?? [];
  if (!ids.length || !context.store || !context.folder) return { calls: row.calls, known_calls: row.known_calls, unknown_calls: row.unknown_calls ?? 0, accounting_complete: row.accounting_complete,
    input_tokens: row.input_tokens ?? 'unknown', cached_input_tokens: row.cached_input_tokens ?? 'unknown', output_tokens: row.output_tokens ?? 'unknown', cached_input_share: row.cached_input_share ?? null };
  const parts = ids.map(id => attemptAccounting(context, id)), known = parts.reduce((sum, part) => sum + part.known, 0);
  const unknown = parts.reduce((sum, part) => sum + part.unknown, 0), complete = parts.every(part => part.complete);
  const total = complete ? parts.reduce((sum, part) => sum + part.total, 0) : null;
  const dispatched = complete ? parts.filter(part => !part.zeroWork) : [];
  const sumToken = key => complete && dispatched.length > 0 && dispatched.every(part => typeof part.tokens[key] === 'number')
    ? dispatched.reduce((sum, part) => sum + part.tokens[key], 0) : 'unknown';
  const input_tokens = sumToken('input_tokens');
  const cached_input_tokens = typeof input_tokens === 'number' ? sumToken('cached_input_tokens') : 'unknown';
  const output_tokens = sumToken('output_tokens');
  const cached_input_share = typeof input_tokens === 'number' && typeof cached_input_tokens === 'number' && input_tokens > 0 && cached_input_tokens <= input_tokens
    ? cached_input_tokens / input_tokens : null;
  return { calls: complete ? total : 'unknown', known_calls: known, unknown_calls: complete ? 0 : Math.max(1, unknown), accounting_complete: complete,
    input_tokens, cached_input_tokens, output_tokens, cached_input_share };
}
function accumulatedCalls(context, row) { return accumulatedAccounting(context, row).calls; }
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
const capacityUnknownReason = 'The Check capacity response does not prove complete zero-work accounting. Usage is unknown.';
function sameIdReadAdvice(context, row) {
  return context.batch ? `Read the saved request with: pdd test --read ${context.batch}`
    : `Read request ${row.request_ids.at(-1)} before sending anything again.`;
}
function markCapacityUnknown(context, row) {
  const accounting = accumulatedAccounting(context, row);
  Object.assign(row, { state: 'unknown', phase: 'server', calls: 'unknown', known_calls: accounting.known_calls ?? 0,
    unknown_calls: Math.max(1, accounting.unknown_calls ?? 0), accounting_complete: false, capacity_uncertain: true,
    input_tokens: 'unknown', cached_input_tokens: 'unknown', output_tokens: 'unknown', cached_input_share: null,
    busy: false, can_retry: false, busy_display: null, retry_at: null, busy_request_id: null, busy_observed_at: null,
    capacity_until: null, note: null, why: capacityUnknownReason, next_step: sameIdReadAdvice(context, row) });
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
  Object.assign(row, accumulatedAccounting(context, row));
  if (!context.reading) context.checkWindow = 1;
}

const restarted = answer => answer?.command === 'check' && answer.state === 'unknown' && [answer.result?.report?.refusal, ...(Array.isArray(answer.result?.refusals) ? answer.result.refusals : [])].some(item => item?.code === 'service-restarted');
const confirmedEnd = answer => ['passed', 'failed', 'refused', 'not_run'].includes(answer?.state) || restarted(answer);
const accountingEnd = (answer, id) => sameJob(answer, id, 'check')
  && (confirmedEnd(answer) || answer.state === 'unknown');
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
  if (answer?.state === 'queued' && Number.isSafeInteger(q?.ahead) && q.ahead >= 0) {
    const message = `⏳ PDD is busy right now. Your check is ${q.ahead === 0 ? 'next in line' : `in line (${q.ahead} ahead of you)`} and starts by itself. You are not charged while you wait.`;
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
    const runtime = new Runtime({ origin: context.origin, token: context.identity.token, ports: context.ports, signal: entry.controller.signal, auth: context.auth });
    entry.promise = runtime.send('/v1/capacity', { method: 'GET' }, Math.max(1, Math.min(GET_MS, deadline - now))).then(reply => {
      entry.pending = false; entry.at = context.ports.now();
      const currentKey = JSON.stringify([context.origin, context.identity.login, context.identity.userId]);
      // Keep unclear replies distinct and reusable until this completion TTL.
      // Recognized access gates retain their ordinary stop/recheck behavior.
      if ((currentKey !== key || blockingAnswer(reply) || reply.status === 401 || gateText(reply)) && capacityCache.get(key) === entry) capacityCache.delete(key);
      return reply;
    }, error => {
      entry.pending = false;
      if (capacityCache.get(key) === entry) capacityCache.delete(key);
      throw error;
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
async function probeLazyInterfaces(context, origin, store) {
  if (context.lazyInterfacesProbed) return !!context.allowMissingInterfaces;
  context.lazyInterfacesProbed = true;
  let identity;
  try { identity = signIn(context.ports.gh, store, context.ports, { exitCode: context.doorMode ? 125 : 5 }); }
  catch (error) { if (error instanceof Stop) return false; throw error; }
  const auth = authSession({ identity, store, ports: context.ports, signInExitCode: context.doorMode ? 125 : 5 });
  const probe = { origin, identity, ports: context.ports, signal: context.signal, interrupted: context.interrupted, auth };
  const reply = await readCapacity(probe, context.ports.now() + GET_MS, false);
  if (reply?.status !== 200 || !Array.isArray(reply.json?.features)) return false;
  context.probedIdentity = identity;
  context.serverFeatures = reply.json.features;
  context.serverEngineSha = reply.json.engine_sha ?? null;
  context.allowMissingInterfaces = reply.json.features.includes('lazy-interfaces');
  return context.allowMissingInterfaces;
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
    // The interpreter declares what it supports; pdd names the tests to lint only when it says so.
    context.serverFeatures = reply.status === 200 && Array.isArray(reply.json?.features) ? reply.json.features : [];
    context.serverEngineSha = reply.status === 200 ? reply.json?.engine_sha ?? null : null;
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
  if (command === 'check' && [429, 503].includes(reply.status) && capacityDelay(error, reply.headers) !== null) {
    if (!admissionMatches(reply.json, id) || !accountingProof(reply.json)) return { kind: 'unknown', why: 'Check capacity accounting is incomplete or conflicting.', admission: reply.json, capacity_uncertain: true };
    return { kind: 'busy', wait: capacityDelay(error, reply.headers), admission: reply.json };
  }
  if ([429, 503].includes(reply.status) && reply.json?.dispatch === 'not_started' && !safeAdmission(reply))
    return { kind: 'unknown', why: 'The admission receipt has uncertain execution accounting.', ...(command === 'check' ? { admission: reply.json, capacity_uncertain: true } : {}) };
  if (reply.status === 503 && error?.code === 'maintenance' && reply.json?.dispatch === 'not_started' && safeAdmission(reply)) {
    if (command === 'check' && (!admissionMatches(reply.json, id) || !accountingProof(reply.json)))
      return { kind: 'unknown', why: 'Check maintenance accounting is incomplete or conflicting.', admission: reply.json, capacity_uncertain: true };
    return { kind: 'busy', wait: retryAfter(reply.headers), admission: reply.json, maintenance: true };
  }
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
    return { kind: 'refused', refusal: { code: cleanText(error.code, secrets), section: cleanText(error.section, secrets) || null, message: cleanText(error.message, secrets) || null,
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
function localSetup(cwd, words, ports) {
  const root = repoRoot(cwd), names=gitFiles(root), workspace=loadRuntimeWorkspace({root});
  for(const word of words){const path=relative(realpathSync(root),resolve(realpathSync(cwd),word)).split(sep).join('/');if(names.includes(path))requireRuntimePath(workspace,{path,from:'Selected source'});}
  const found = ports.findTests({ root, files: names, excludeFixtureProjects: words.length === 0 });
  const realCwd = realpathSync(cwd), realRoot = realpathSync(root);
  const normalized = words.map(word => {
    const rel = relative(realRoot, resolve(realCwd, word)).split(sep).join('/');
    return found.visible.has(rel) || (!rel.startsWith('../') && rel !== '..' && statOrNull(resolve(realCwd, word))?.isDirectory()) ? (rel || '.') : word;
  });
  return { root, found, normalized };
}

// Each JSON file in a test folder that matches no Story (text shows one summary line; --files and --json list each).
// The tests that a check uploads: every row but those that discovery could not use.
const sentTests = rows => rows.filter(row => !row.unsent && !row.native_only?.length).map(row => row.test);
const unmatchedLines = found => (found.orphans ?? []).map(item => `Warning: ${item.line}`);

function storyList(found, ports) {
  return [...found.tests.map(test => `  ${test.story}  ${test.path}${test.title && test.title !== test.story ? `  (${test.title})` : ''}`),
    ...(found.untested ?? []).map(item => `  ${item.story}  no test (expected ${ports.expectedTestPath(item.storyPath)})`)];
}

function select(found, words, root, ports) {
  if (!found.tests.length) throw new Stop(2, [ports.noTestsMessage(), ...(root ? ports.whyNoTests(root, found.discoveryVisible ?? found.visible, found) : []), ...(found.excludedFixtureProjects ?? []).map(path => `Warning: skipped nested fixture project ${path}.`)].join('\n'));
  const { selected, unknown, untested = [] } = ports.selectTests(found, words);
  if (untested.length) throw new Stop(2, untested.join('\n'));
  if (unknown.length) throw new Stop(2, [`Unknown story ${unknown.map(word => `"${cleanText(word)}"`).join(', ')}. Stories:`, ...storyList(found, ports)].join('\n'));
  return selected;
}

const localRows = rows => rows.map(row => ({ ...row, ...(row.refusals.length ? {unsent:true} : {}), state: row.refusals.length ? 'refused' : row.native_only?.length ? 'not_run' : 'ready', phase: row.refusals.length || row.native_only?.length ? 'local' : 'server',
  ...(row.native_only?.length ? {unsent:true,note:{code:'native-only',message:row.native_only.map(item => `${item.path}: ${item.reason}`).join('; ')}} : {}),
  refusals:row.refusals.map(item=>({...item,hint:item.hint??'Fix the named test or prompt rule, then run the selection again.'})),
  request_ids: [], calls: 0, report_url: null, checks: null, failed_checks: [], all_checks: [] }));

const incompleteCriteria = row => {
  if (!row.not_checked?.length) return;
  if (row.criteria) row.criteria = {...row.criteria,total:row.criteria_total};
  if (row.state === 'passed') Object.assign(row, {state:'not_run',note:{code:'criteria-not-checked',
    message:'The Story is not a full pass: some criteria were not checked.'}});
};

function capturedCriteria(rows, capture) {
  let broken = false;
  for (const row of rows.filter(row=>!row.unsent)) {
    const source = capture.sources?.find(source=>source.path===row.test);
    if (!source) continue;
    let doc; try { doc=JSON.parse(Buffer.from(source.bytes).toString('utf8')); } catch { /* Refuse captured invalid bytes below. */ }
    const shape=scenarioShapeRefusal(doc,row.test);
    if (shape) {
      const error=Object.assign(new PreflightError(4,`${row.test}: ${shape.message}`),
        {code:shape.code,hint:'Fix the named test JSON, schema version, criteria and steps, then run the selection again.'});
      refuseSource(row,error);broken=true;continue;
    }
    row.steps=doc.steps;
    row.app_maps=Array.isArray(doc.app_maps)?doc.app_maps.filter(path=>typeof path==='string'&&path.length>0):[];
    row.criteria_total=doc.criteria.length;
    row.criterion_texts=Object.fromEntries(doc.criteria.filter(isObject).map(item=>[item.id,item.text]));
    const exemptions=Array.isArray(doc.check_exemptions)?doc.check_exemptions:[];
    const unchecked=exemptions.filter(item=>isObject(item)&&item.reason==='out-of-scope').map(item=>({
      criterion_id:item.criterion_id,text:row.criterion_texts[item.criterion_id],reason:item.detail}));
    if (unchecked.length) row.not_checked=unchecked;
    else delete row.not_checked;
  }
  return broken;
}

// Retry a refused combined capture per test, so a broken closure cannot hide good tests.
const sourceUnavailable = error => !error.selection && (error instanceof PreflightError && error.exitCode === 4 || ['EACCES','EPERM','EISDIR'].includes(error.code));
function refuseSource(row, error) {
  if (error.not_checked?.length) Object.assign(row, {not_checked:error.not_checked,criteria_total:error.criteria_total});
  Object.assign(row, {state:'refused',phase:'local',unsent:true,calls:0,refusals:[{code:error.code ?? 'source-unavailable',
    section:error.section ?? 'source',message:error.message,hint:error.hint ?? 'Restore the named dependency, make it readable, or correct its declared path.'}]});
}
function captureIndependent(root, rows, ports, options) {
  const capture = tests => {
    const result=ports.captureSource(root,{...options,tests});
    const requiredBroken=rows.find(row=>row.unsent&&result.files.some(file=>file.path===row.test));
    if(requiredBroken)throw new PreflightError(4,`${requiredBroken.test} is broken and is required by the selected source. Fix that test or its declared reference.`);
    return result;
  };
  if (!sentTests(rows).length) return null;
  let captured;
  try { captured=capture(sentTests(rows)); }
  catch (error) {
    if (!sourceUnavailable(error)) throw error;
    let broken = false;
    for (const row of rows.filter(row => !row.unsent)) {
      try { capture([row.test]); }
      catch (own) {
        if (!sourceUnavailable(own)) throw own;
        broken = true;
        line(ports.stderr, own.message);
        refuseSource(row, own);
      }
    }
    if (!broken) throw error; // Aggregate limits and unstable/shared failures retain their rules.
    return captureIndependent(root,rows,ports,options);
  }
  // Each repeat removes at least one broken row. Nothing is uploaded until the selection is usable.
  for (const row of rows) {
    const plan=captured.bindingPlans?.find(plan=>plan.test===row.test);
    if (plan) {
      row.binding_plan=plan;
      if (plan.edges.some(edge=>edge.state==='missing')) for (const message of bindingPlanLines(plan)) line(ports.stderr,message);
    }
  }
  return capturedCriteria(rows,captured) ? captureIndependent(root,rows,ports,options) : captured;
}

const capturedManifests = new WeakMap();
function sourceFiles(capture) {
  if (!Array.isArray(capture?.sources)) return undefined;
  if (!capturedManifests.has(capture)) capturedManifests.set(capture, capture.sources.map(source => ({ path: source.path,
    sha256: createHash('sha256').update(source.bytes).digest('hex') })));
  return capturedManifests.get(capture);
}
// A recovered manifest authorizes nothing until the current archive matches the saved archive.
function recoverSourceContext(context) {
  if (Array.isArray(context.capture?.sources)) return true;
  if (context.sourceRecoveryAttempted) return false;
  context.sourceRecoveryAttempted = true;
  try {
    const capture = context.ports.captureSource(context.root, { tests: sentTests(context.rows), appMap: null, excludeFixtureProjects: context.excludeFixtureProjects, ...(context.allowMissingInterfaces ? { allowMissingInterfaces: true } : {}) });
    if (capture.sha256 !== context.capture.sha256) { context.sourceRecoveryMismatch = true; return false; }
    capture.stories = context.capture.stories;
    context.capture = capture;
    context.recoveredSourceCapture = capture;
    return true;
  } catch (error) { if (!(error instanceof PreflightError)) throw error; return false; }
}
function rowAppMaps(row, capture, appMap = null) {
  let declared = Array.isArray(row?.app_maps) ? row.app_maps : null;
  if (!declared && Array.isArray(capture?.sources)) {
    const source = capture.sources.find(item => item.path === row?.test);
    if (source) {
      try {
        const doc = JSON.parse(Buffer.from(source.bytes).toString('utf8'));
        if (Array.isArray(doc?.app_maps)) declared = doc.app_maps;
      } catch { /* Invalid bytes are handled by scenario preflight. */ }
    }
  }
  return [...new Set([appMap, ...(declared ?? [])].filter(path => typeof path === 'string' && path.length > 0))];
}
const lintOutcome = (answer, row, capture, appMap = null) => outcomeFor(answer ?? {}, { kind: 'lint', test: row.test, steps: row.steps ?? [], appMaps: rowAppMaps(row, capture, appMap), sourceFiles: sourceFiles(capture) });

// A generic Runtime refusal is not evidence that any particular local finding caused it.
function interfaceDiagnostic(view, raw, root, secrets = []) {
  if (view.code !== 'invalid-interface' && !String(view.code).startsWith('graph-schema-')) return view;
  const at = cleanText(raw?.at ?? raw?.details?.at, secrets);
  const pointer = cleanText(raw?.pointer ?? raw?.field ?? raw?.details?.pointer ?? raw?.details?.field, secrets) || (at.startsWith('/') ? at : null);
  const rule = cleanText(raw?.rule ?? raw?.details?.rule, secrets) || null;
  if (!pointer && view.field === (raw?.at ?? raw?.section)) view.field = null;
  if (pointer) {
    view.field = pointer;
    view.section = pointer;
  }
  if (pointer || rule) view.hint = [pointer, rule].filter(Boolean).join(': ');
  if (view.code === 'invalid-interface' && !pointer && !view.section?.startsWith('/')) {
    let findings = [];
    try { if (view.path) findings = interfaceFindings({root,paths:[view.path]}).filter(item => item.section?.startsWith('/')); } catch { /* No local diagnosis is available. */ }
    view.hint = [rule, 'The PDD interpreter did not identify the Runtime interface field.', findings.length
      ? `Local schema findings (not confirmed as the interpreter cause): ${findings.map(item => item.message).join('; ')}`
      : 'Inspect the interface or request a detailed Runtime diagnostic.'].filter(Boolean).join(' ');
  }
  return view;
}

// The lint outcome of each row, with server text cleaned and pdd's local hint for a prompt it reached.
function judgeLint(answer, rows, root, visible, secrets = [], capture, appMap = null) {
  return new Map(rows.map(row => {
    const outcome = lintOutcome(answer, row, capture, appMap);
    const view = projectAnswer(answer, { test: row.test, steps: row.steps ?? [], secrets, sourceFiles: sourceFiles(capture) });
    row.compatibility = view.compatibility; row.client_advice = view.client_advice;
    if (outcome.draft) row.draft = true;
    // Only a refusal pdd wrote for a prompt the test reaches gets the local stale hint or prompt error.
    const refusals = (outcome.refusals ?? []).map(item => {
      const view = interfaceDiagnostic(refusalView(item, secrets), item, root, secrets);
      if (!item.reached) return view;
      if (view.code === 'interface-stale') return { ...view, hint: staleHint };
      const local = /^interface-/.test(view.code) && view.path ? readPrompt(root, visible, view.path) : null;
      return local?.error ? { ...view, message: `${(view.message ?? view.code).replace(/\.$/, '')} (${local.error}).` } : view;
    });
    return [row, { ...outcome, rawRefusals: outcome.refusals ?? [], reason: cleanText(outcome.reason, secrets) || null, refusals }];
  }));
}

// The one lint gate for paid work (new checks, saved-lint continuation, retry, restart replacement, Try):
// a selected test is sent only when its own lint outcome is passed. Others keep their outcome.
const lintAdmits = (answer, row, capture, appMap = null) => lintOutcome(answer, row, capture, appMap).state === 'passed';

// Refusals that per-test passes scoped out stay visible as warnings; a refusal that already
// refused one of these rows is shown there instead. Returns the new lines.
function lintDiagnostics(context, answer, rows) {
  context.warnings ??= [];
  const result = answer?.result, list = value => Array.isArray(value) ? value.filter(isObject) : [];
  const refusals = list(result?.refusals).length ? list(result.refusals) : list([result?.report?.refusal]);
  const key = item => `${item.code}|${item.file ?? item.path ?? ''}`;
  const shown = new Set(rows.filter(row => row.state === 'refused').flatMap(row => (row.refusals ?? []).map(item => `${item.code}|${item.path ?? ''}`)));
  const added = [];
  for (const item of [...refusals, ...list(result?.report?.program?.refused_prompts)]) {
    if (shown.has(key(cleanItem(item, context.secrets)))) continue;
    const view = interfaceDiagnostic(refusalView(item, context.secrets), item, context.root, context.secrets);
    const text = `Lint diagnostic: ${[view.code, view.path, view.section, view.reason ?? view.message, view.hint].filter(Boolean).join('  ')}`;
    if (!context.warnings.includes(text)) { context.warnings.push(text); added.push(text); }
  }
  return added;
}
const cleanItem = (item, secrets) => ({ code: cleanText(item.code, secrets) || 'unknown', path: cleanText(item.file ?? item.path, secrets) || null });

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
    next_step: checkCapacityCandidate(answer) ? null : view.next_step };
}

// Only the confirmed answer can identify the engine/model that produced a pass.
function answerCacheIdentity(answer) {
  const engine = answer?.engine_sha;
  const models = [answer?.usage?.requested_model, answer?.result?.report?.evaluation?.requested_model].filter(value => value !== undefined && value !== null);
  const known = value => typeof value === 'string' && value.trim().length > 0 && value.trim().toLowerCase() !== 'unknown';
  if (!known(engine) || !models.length || !models.every(known) || new Set(models).size !== 1) return null;
  return { engine_sha: engine, requested_model: models[0] };
}
const observedIdentityMatches = (observed, identity) => !observed || (!observed.conflict && (!observed.engine_sha || observed.engine_sha === identity?.engine_sha)
  && observed.models.every(model => model === identity?.requested_model));
const cleanRecordMatches = (record, identity) => record?.clean === true && record.conflict === false && !record.in_progress?.length
  && typeof record.engine_sha === 'string' && record.engine_sha.trim() && record.engine_sha.trim().toLowerCase() !== 'unknown'
  && record.models.length === 1 && typeof record.models[0] === 'string' && record.models[0].trim() && record.models[0].trim().toLowerCase() !== 'unknown'
  && (record.engine_shas ?? [record.engine_sha]).every(value => value === record.engine_sha)
  && Number.isFinite(Date.parse(record.sampled_at)) && Number.isFinite(Date.parse(record.written_at))
  && Date.parse(record.sampled_at) <= Date.parse(record.written_at) && observedIdentityMatches(record, identity);
const sameCacheIdentity = (a, b) => !!a && !!b && a.engine_sha === b.engine_sha && a.requested_model === b.requested_model;

function applyAnswer(row, answer, context, observedWait = null, observedAt = context.ports.now()) {
  context.unsentInterruptions?.delete(row);
  const capacityCandidate = checkCapacityCandidate(answer);
  const capacitySafe = capacityCandidate && checkCapacity(answer) !== null && capacityHistorySafe(context, row);
  // Earlier contradictory capacity evidence remains uncertain until the Runtime
  // supplies an explicit reconciliation contract for that same request ID.
  const capacityUncertain = row.capacity_uncertain === true || capacityCandidate && !capacitySafe
    || capacityHistoryHasEvidence(context, row) && !capacityHistorySafe(context, row);
  if (capacityUncertain) row.capacity_uncertain = true;
  else if (capacitySafe) row.capacity_uncertain = false;
  row.cache_identity = answerCacheIdentity(answer);
  // Evidence is no newer than its original batch, even when read much later.
  const times = [context.startedAt, ...[answer?.finished_at, answer?.completed_at, answer?.ended_at].map(value => typeof value === 'number' ? value : Date.parse(value))].filter(Number.isFinite);
  row.cache_sample_at = times.length ? Math.min(...times) : null;
  const knownIdentity = value => typeof value === 'string' && value.trim() && value.trim().toLowerCase() !== 'unknown';
  context.observedTestIdentities ??= [];
  const models = [answer?.usage?.requested_model, answer?.result?.report?.evaluation?.requested_model];
  const accounting = context.store && context.folder && row.request_ids.length ? accumulatedAccounting(context, row) : usagePart(answer);
  const terminal = accountingEnd(answer, row.request_ids.at(-1));
  context.observedTestIdentities.push({ engine_sha: knownIdentity(answer?.engine_sha) ? answer.engine_sha : null,
    models: models.filter(knownIdentity), terminal, complete: terminal && !!row.cache_identity
      && (accounting.accounting_complete ?? accounting.complete) === true && !capacityUncertain,
    observed_at: new Date(context.ports.now()).toISOString() });
  const view = projectAnswer(answer, { origin: context.origin, secrets: context.secrets, steps: row.steps ?? [], criterionTexts: row.criterion_texts ?? {}, test: row.test, capacityUncertain });
  const advice = noVerdictAdvice(answer, view);
  const firstDiagnosis = view.failed_checks.find(check => check.diagnosis) ?? null, failed = view.state === 'failed';
  Object.assign(row, { state: view.state, checks: view.checks, criteria: view.criteria, failed_checks: view.failed_checks, all_checks: view.all_checks,
    refusals: view.refusals.map((item, index) => interfaceDiagnostic(item,
      (answer?.result?.refusals ?? [answer?.result?.report?.refusal])[index], context.root, context.secrets)), calls: view.calls,
    input_tokens: view.input_tokens, cached_input_tokens: view.cached_input_tokens, output_tokens: view.output_tokens, cached_input_share: view.cached_input_share,
    requested_model: view.requested_model, report_url: view.report_url ?? row.report_url,
    server_seconds: view.server_seconds, busy_display: view.busy_display, time_limit: view.time_limit, known_calls: view.known_calls, unknown_calls: view.unknown_calls,
    accounting_complete: view.accounting_complete,
    why: failed ? view.why ?? firstDiagnosis?.diagnosis?.why ?? null : ['refused', 'not_run', 'unknown'].includes(view.state) ? advice.why ?? (view.state === 'unknown' && row.lost && row.why !== 'Checks failed.' ? row.why : null) : null,
    who: failed ? view.who ?? firstDiagnosis?.diagnosis?.who ?? null : null,
    next_step: failed ? view.next_step ?? firstDiagnosis?.diagnosis?.next_step ?? null : ['refused', 'not_run', 'unknown'].includes(view.state) ? advice.next_step : null,
    rerun: view.rerun ?? row.rerun,
    engine_sha: view.engine_sha, provider: view.provider, progress: view.progress, ahead: view.ahead,
    draft: view.draft ?? row.draft });
  if (row.request_ids.length) Object.assign(row, context.store && context.folder ? accumulatedAccounting(context, row) : {
    calls: accounting.complete ? accounting.total : 'unknown', known_calls: accounting.known,
    unknown_calls: accounting.complete ? 0 : accounting.unknown, accounting_complete: accounting.complete,
    ...(accounting.tokens ?? {}) });
  const wait = capacitySafe ? checkCapacity(answer) : null;
  if (capacityUncertain) markCapacityUnknown(context, row);
  else if (wait !== null) markBusy(context, row, observedWait ?? wait, observedAt, context.reading && observedWait === null);
  else { row.busy = false; row.can_retry = false; row.note = view.note; }
  if (row.not_checked?.length) {
    const unchecked = new Set(row.not_checked.map(item=>item.criterion_id));
    const results = answer?.result?.report?.criterion_results;
    row.criteria = {passed:Array.isArray(results) ? results.filter(item=>item.status==='passed'&&!unchecked.has(item.criterion_id)).length : 0,total:row.criteria_total};
  }
  incompleteCriteria(row);
  if (row.state === 'refused') addHints(row, context.root, context.visible);
  if (ENDED.has(row.state) && row.sent_at && !row.ended_at && !context.reading) row.ended_at = context.ports.now();
  row.seconds = !ENDED.has(row.state) ? null : row.sent_at && row.ended_at ? (row.ended_at - row.sent_at) / 1000 : row.server_seconds;
}

function nativeSourceIdentity(context, rows) {
  const tests = rows.filter(row => row.native_only?.length).map(row => row.test);
  if (!tests.length) return null;
  try { return {tests,sha256:context.ports.captureSource(context.root,{tests,appMap:null,excludeFixtureProjects:context.excludeFixtureProjects === true}).sha256}; }
  catch (error) { if (error?.unboundPort) throw error; return {tests,sha256:null}; }
}

const localLayoutPaths = values => Array.isArray(values) && values.every(path => typeof path === 'string' && path.length
    && !/^[a-zA-Z]:|^[\\/]|[\\\x00-\x1f\x7f]/.test(path) && path.split('/').every(part => part && part !== '.' && part !== '..' && part !== '.git'))
    && isDeepStrictEqual(values, [...new Set(values)].sort());

// The saved local-layout contract is deliberately distinct from legacy native-only batches.
function localLayoutResult(batch, summary) {
  const keys = (value, names) => value && typeof value === 'object' && !Array.isArray(value)
    && isDeepStrictEqual(Object.keys(value).sort(), names.split(' ').sort());
  if (!keys(batch, 'version batch root created_at intent local_only source_sha256 local_scope summary_line exit_code warnings problems rows lint')
    || batch.version !== 1 || !BATCH.test(batch.batch) || typeof batch.root !== 'string' || !batch.root.startsWith('/')
    || typeof batch.created_at !== 'string' || !Number.isFinite(Date.parse(batch.created_at))
    || batch.intent !== 'lint-only' || batch.local_only !== true || batch.source_sha256 !== null
    || !keys(batch.local_scope, 'tests prompts') || !localLayoutPaths(batch.local_scope.tests) || !localLayoutPaths(batch.local_scope.prompts)
    || typeof batch.summary_line !== 'string' || ![0, 4].includes(batch.exit_code)
    || !Array.isArray(batch.warnings) || !batch.warnings.every(item => typeof item === 'string')
    || !Array.isArray(batch.problems) || !batch.problems.every(item => (keys(item, 'code path message') || keys(item, 'code path message section')) && Object.values(item).every(value => typeof value === 'string'))
    || !Array.isArray(batch.rows) || batch.rows.length || !keys(batch.lint, 'state lint_state reason request_ids')
    || batch.lint.state !== 'partial' || batch.lint.lint_state !== 'partial'
    || !isDeepStrictEqual(batch.lint.reason, {code:'local-only',message:'checked SVG layout only; prompts not checked'})
    || !Array.isArray(batch.lint.request_ids) || batch.lint.request_ids.length) return null;
  const result = {batch:batch.batch,repo:batch.root,exit_code:batch.exit_code,state:'partial',lint_state:'partial',reason:batch.lint.reason,
    local_only:true,local_scope:batch.local_scope,summary_line:batch.summary_line,warnings:batch.warnings,problems:batch.problems,rows:[],report_url:null};
  return isDeepStrictEqual(summary, result) ? result : {...result,exit_code:2,
    summary_line:'Local lint result not saved (the local save did not finish). partial (local-only).'};
}

function printLocalLayout(context, result) {
  if (result.exit_code === 2) line(context.ports.stderr,'Could not save local lint result. Run a fresh pdd lint --local after fixing the state folder.');
  line(context.ports.stdout, context.json ? JSON.stringify(result) : [...result.problems.map(item => `${item.code}: ${item.message}`), ...result.warnings, result.summary_line].join('\n'));
  return result.exit_code;
}

function saveLocalLayout(context, {root, tests, prompts, warnings, problems, summary}) {
  const store = stateFor(context.ports.env,root), now = context.ports.now(), batch = batchId(now,context.ports.randomUUID);
  try {
    const record = {version:1,batch,root,created_at:new Date(now).toISOString(),intent:'lint-only',local_only:true,source_sha256:null,
      local_scope:{tests:[...new Set(tests)].sort(),prompts:[...new Set(prompts)].sort()},summary_line:summary,exit_code:problems.length ? 4 : 0,
      warnings,problems,rows:[],lint:{state:'partial',lint_state:'partial',reason:resultOutcome({state:'partial',note:{code:'local-only',message:'checked SVG layout only; prompts not checked'}}).reason,request_ids:[]}};
    const projection = localLayoutResult(record,null);
    if (!projection) throw new Error('Local lint record cannot satisfy the saved result contract, including safe inspected scope.');
    const result = {...projection,exit_code:record.exit_code,summary_line:record.summary_line};
    const folder = join(store.folder('batches'),batch);
    // Exclusive creation keeps every previous batch intact even if the ordinary ID collides.
    mkdirSync(folder,{mode:0o700});
    store.write(join(folder,'batch.json'),record);
    store.saveRepo(root,{...store.repo(root),last_batch:batch});
    store.write(join(folder,'summary.json'),result);
    return result;
  } catch (error) { throw new Stop(2,`Could not save local lint result in PDD_STATE_DIR: ${error.message}`); }
}

// Local omissions are evidence too; recording them needs no owner token or job.
function saveLocalNativeResult(context, rows, intent, problems = []) {
  const startedAt = context.ports.now(), batch = batchId(startedAt, context.ports.randomUUID);
  for (const row of rows) row.unsent = true;
  context.sourceSelection = {tests:[],exclude_fixture_projects:context.excludeFixtureProjects === true};
  context.nativeSource = nativeSourceIdentity(context, rows);
  const capture = context.ports.captureSource(context.root,{tests:[],appMap:null,excludeFixtureProjects:context.excludeFixtureProjects === true});
  Object.assign(context,{localOnly:true,startedAt,batch,intent,capture,rows,identity:{login:null,userId:null},lint:{state:'not_run',request_ids:[],...(problems.length ? {problems} : {})}});
  context.folder = context.store.folder('batches',batch);
  saveBatch(context);
  context.store.saveRepo(context.root,{...context.store.repo(context.root),last_batch:batch});
}

function batchRecord(context) {
  const { batch, origin, root, identity, capture, rows, lint, warnings } = context;
  return { version: 1, batch, origin, root, check_plan: context.checkPlan ?? null, ...(context.checkSelection ? {check_selection:context.checkSelection,baseline_report:context.baselineReport} : {}), head: context.head, login: identity.login, user_id: identity.userId,
    source_sha256: capture.sha256, files: capture.files.map(file => file.path), bytes: capture.bytes, timeout_min: context.timeoutMin,
    ...(context.singleAttempt ? {single_attempt:true} : {}),
    source_selection: context.sourceSelection ?? {tests:sentTests(rows),exclude_fixture_projects:context.excludeFixtureProjects === true},
    native_source: context.nativeSource ?? null,
    ...(context.localOnly ? {local_only:true} : {}),
    ...(context.allowMissingInterfaces ? {lazy_interfaces:true} : {}),
    exclude_fixture_projects: context.excludeFixtureProjects === true,
    created_at: new Date(context.startedAt).toISOString(), intent: context.intent, lint: lint ? { ...lint, recovery_state: lint.state, ...resultOutcome(lint.public_result ?? lint) } : lint, warnings, coverage: context.coverage,
    contract_snapshots: capture.stories,
    test_cache: context.testCache ? { tokens: [...context.testCache.tokens] } : context.savedTestCache,
    rows: rows.map(row => ({ test: row.test, ...(row.app_maps?.length ? { app_maps: row.app_maps } : {}), native_only: row.native_only ?? [], story: row.story, story_path: row.story_path, title: row.title, request_ids: row.request_ids, recovery_state: row.state, ...resultOutcome(row),
      ...(!row.request_ids.length && Object.hasOwn(row, 'calls') ? { calls: row.calls } : {}),
      ...(row.unsent ? { unsent: true } : {}), ...(row.not_checked?.length ? {not_checked:row.not_checked} : {}), progress: row.progress, ahead: row.ahead, phase: row.phase, post_verdict: row.post_verdict ?? null, binding_plan: row.binding_plan, compatibility: row.compatibility, client_advice: row.client_advice, report_url: row.report_url, refusals: row.refusals, note: row.note ?? null, why: row.why ?? null, next_step: row.next_step ?? null,
      sent_at: row.sent_at ?? null, ended_at: row.ended_at ?? null, max_calls: row.max_calls, warnings: row.warnings, steps: row.steps, criteria_total: row.criteria_total,
      reservation: row.reservation ?? null, restart_used: !!row.restart_used,
      busy: !!row.busy, can_retry: !!row.can_retry, eligible: !!row.eligible, retry_at: row.retry_at ?? null,
      ...(row.known_calls !== undefined ? { known_calls: row.known_calls } : {}), ...(row.unknown_calls !== undefined ? { unknown_calls: row.unknown_calls } : {}),
      ...(row.accounting_complete !== undefined ? { accounting_complete: row.accounting_complete } : {}), ...(row.capacity_uncertain ? { capacity_uncertain: true } : {}),
      busy_request_id: row.busy_request_id ?? null, busy_observed_at: row.busy_observed_at ?? null, capacity_until: row.capacity_until ?? null,
      engine_sha: row.engine_sha ?? null, requested_model: row.requested_model ?? null, cache_identity: row.cache_identity ?? null,
      ...(row.cached ? {cached:true,passed_at:row.passed_at,checks:row.checks,criteria:row.criteria} : {}),
      ...(row.cache_reason ? { cache_reason: row.cache_reason } : {}), criterion_texts: row.criterion_texts ?? {}, draft: !!row.draft })) };
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
function markDeadline(context, rows) {
  if (context.interrupted || !Number.isFinite(context.deadline) || context.ports.now() < context.deadline) return;
  for (const row of rows) if (!row.time_limit && (['ready', 'waiting', 'sending', 'queued', 'running'].includes(row.state)
    || row.state === 'unknown' && row.lost || heldForLint(row) || row.busy && row.can_retry)) {
    row.note = { code: context.timeoutMin && !context.agentLimit ? 'timeout-flag' : 'deadline',
      message: context.timeoutMin && !context.agentLimit ? `Stopped waiting at --timeout ${context.timeoutMin} min.` : 'The wait deadline ended.' };
  }
}

function saveBatch(context) {
  if (!context.batch) return;
  markDeadline(context, [...context.rows, ...(context.lint ? [context.lint] : [])]);
  for (const row of context.rows) {
    adoptClaims(context, row);
    const id = row.request_ids.at(-1), answer = id && context.store.read(join(context.folder, `${id}.json`));
    if (!row.busy && ['unknown', 'queued', 'running', 'sending'].includes(row.state) && answer && sameJob(answer, id, 'check')
      && ['passed', 'failed', 'refused'].includes(answer.state) && checkCapacity(answer) === null) applyAnswer(row, answer, context);
  }
  context.store.write(join(context.folder, 'batch.json'), batchRecord(context));
}
function saveAnswerAt(store, folder, id, json) {
  if (!isObject(json)) return;
  const path = join(folder, `${id}.json`), previous = store.read(path);
  if (previous && !isDeepStrictEqual(previous, json)) {
    const historyPath = join(folder, `${id}.observations.json`), history = store.read(historyPath);
    const retained = Array.isArray(history) ? history : [];
    if (!retained.some(item => isDeepStrictEqual(item, previous))) retained.push(previous);
    store.write(historyPath, retained);
  }
  store.write(path, json);
}
function saveAnswer(context, id, json) { saveAnswerAt(context.store, context.folder, id, json); }

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
  const reply = await context.runtime.post(path, request, context.capture.tar, Math.max(1, Math.min(timeoutMs, deadline - context.ports.now())));
  const verdict = judgePost(reply, id, command, context.secrets);
  verdict.observed_at = context.ports.now();
  if (row && verdict.answer && ['queued', 'running', 'passed', 'failed'].includes(outcomeFor(verdict.answer, { kind: 'check' }).state))
    line(context.ports.stderr, `Sent 1 check at ${clock(context.ports.now())}: ${row.test}.`);
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
  // Recheck the saved raw cohort immediately before any capacity-driven new ID.
  // The one structured restart replacement has its own durable fuse and remains allowed.
  if (row.request_ids.length && (row.busy || row.capacity_uncertain) && !row.restart_pending && !capacityRetryAllowed(context, row)) {
    markCapacityUnknown(context, row);
    return;
  }
  if (row.busy && row.request_ids.length && !await capacityReady(context, context.deadline, row)) return;
  const attempt = row.request_ids.length, previousCalls = row.restart_used || row.restart_pending ? accumulatedCalls(context, row) : 0;
  if (!await admission(context, 'check', row)) {
    if (context.interrupted && interruptedAdmissions.has(row)) Object.assign(row, { state: 'not_run', calls: previousCalls, phase: 'local', note: { code: null, message: 'Stopped before sending.' } });
    return;
  }
  // Admission can wait while another reader records a conflicting receipt.
  // Revalidate while holding the local reservation, before creating a claim or UUID.
  if (row.request_ids.length && (row.busy || row.capacity_uncertain) && !row.restart_pending && !capacityRetryAllowed(context, row)) {
    await finishReservation(context, row, { state: 'not_run' });
    markCapacityUnknown(context, row);
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
  // Claim the original row and attempt before allocating an ID. Never remove a claim:
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
  const id = context.ports.randomUUID();
  try { writeSync(fd, JSON.stringify({ id, reservation: row.reservation, restart: !!row.restart_used })); }
  finally { closeSync(fd); }
  if (context.interrupted || context.ports.now() >= context.deadline) {
    await finishReservation(context, row, { state: 'not_run' });
    adoptClaims(context, row);
    if (context.interrupted) row.note = { code: null, message: 'Stopped before sending.' };
    return;
  }
  row.attempts = (row.attempts ?? 0) + 1;
  row.sent_at = context.ports.now(); row.ended_at = null; row.retry_at = null; row.busy = false; row.can_retry = false;
  row.busy_request_id = null; row.busy_observed_at = null; row.capacity_until = null; row.busy_display = null;
  row.phase = 'server';
  const request = { requestId: id, source_sha256: context.capture.sha256, scenario: row.test, max_calls: row.max_calls,
    ...(context.serverFeatures?.includes('lazy-interfaces') ? { lazy_interfaces: true } : {}) };
  const verdict = await context.postCheck(request, row, Math.max(1, Math.min(context.ports.postMs, context.deadline - context.ports.now())));
  if (verdict.kind === 'not_sent') {
    const note = { code: null, message: 'Stopped before sending.' };
    // Live knowledge owns this attempt's wording only; claim adoption still owns uncertainty.
    if (context.interrupted) (context.unsentInterruptions ??= new WeakMap()).set(row, { id, note });
    Object.assign(row, { state: 'not_run', calls: previousCalls, phase: 'local', note });
  }
  else if (verdict.kind === 'accepted') applyAnswer(row, verdict.answer, context, verdict.wait, verdict.observed_at);
  else if (verdict.kind === 'busy') {
    if (row.request_ids.length > 1 && !capacityRetryAllowed(context, row)) markCapacityUnknown(context, row);
    else markBusy(context, row, verdict.wait, verdict.observed_at);
  }
  else if (verdict.kind === 'not_run') Object.assign(row, { state: 'not_run', note: verdict.note });
  else if (verdict.kind === 'stop') { Object.assign(row, { state: 'not_run', note: verdict.note }); context.stopped = verdict.note; if (verdict.blocked) context.blocked = verdict.note.message; }
  else if (verdict.kind === 'refused') Object.assign(row, { state: 'refused', refusals: [verdict.refusal] });
  // An explicit caller deadline also bounds recovery of a lost POST answer.
  else {
    if (verdict.capacity_uncertain) markCapacityUnknown(context, row);
    else Object.assign(row, { state: 'unknown', why: verdict.why, lost: true, read_until: Number.isFinite(context.deadline)
      ? context.deadline : context.ports.now() + LOST_READ_MS });
    row.lost = true; row.read_until = Number.isFinite(context.deadline) ? context.deadline : context.ports.now() + LOST_READ_MS;
  }
}

// GET one open row once.
async function readRow(context, row, deadline = Infinity) {
  const id = row.request_ids.at(-1), end = Math.min(context.deadline, deadline, row.lost ? row.read_until ?? context.deadline : context.deadline);
  if (!id || context.interrupted || context.ports.now() >= end) return;
  const verdict = judgeGet(await context.runtime.get(id, Math.max(1, Math.min(GET_MS, (end ?? Infinity) - context.ports.now()))), id, 'check');
  verdict.observed_at = context.ports.now();
  // A network problem while reading says so once; pdd keeps reading the same IDs.
  if (verdict.kind === 'again' && verdict.why && !context.readTrouble) line(context.ports.stderr, `pdd cannot read the results right now (${verdict.why}). It keeps trying.`);
  if (verdict.kind !== 'again') context.readTrouble = false; else if (verdict.why) context.readTrouble = true;
  if (verdict.kind === 'state') { saveAnswer(context, id, verdict.answer); queueProgress(context, verdict.answer); await finishReservation(context, row, verdict.answer); applyAnswer(row, verdict.answer, context, verdict.wait, verdict.observed_at); row.lost = false; }
  else if (verdict.kind === 'unknown') {
    if (row.capacity_uncertain) markCapacityUnknown(context, row);
    else Object.assign(row, { state: 'unknown', why: verdict.why, lost: false, final: true });
    row.lost = false; row.final = true;
  }
  else if (verdict.kind === 'auth') context.readStop = AUTH_TEXT;
  else if (verdict.kind === 'blocked') context.readStop = verdict.message;
  else if (verdict.kind === 'gate') context.readStop = 'The runtime opens soon.';
}

const isOpen = row => OPEN_STATES.has(row.state) || (row.state === 'unknown' && row.lost);
const occupiesSlot = row => OPEN_STATES.has(row.state) || (row.state === 'unknown' && row.request_ids?.length);

// One line every 30 s while checks run.
function progressLine(rows, ms) {
  const stories = new Map();
  for (const row of rows) stories.set(row.story, (stories.get(row.story) ?? true) && outcomeDone(row) && !isOpen(row) && !heldForLint(row));
  const done = [...stories.values()].filter(Boolean).length;
  // One fragment for server progress, then the known calls of the other rows; no count is invented.
  const progress = progressText(rows), counts = rows.filter(row => !hasProgress(row) && typeof row.calls === 'number').map(row => row.calls);
  const calls = counts.reduce((sum, value) => sum + value, 0), callText = `${calls} AI call${calls === 1 ? '' : 's'}`;
  const usage = [...(progress ? [progress] : []), ...(counts.length ? [progress ? `${callText} in other checks` : `${callText} so far`] : progress ? [] : ['AI calls unknown'])];
  return `Still running: ${done} of ${stories.size} ${stories.size === 1 ? 'Story' : 'Stories'} done · ${usage.join(' · ')} · `
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

// The upload hash plus the authored file hashes: the upload copy drops an interface kind (#3210), the authored bytes keep it.
const authoredSha256 = capture => isObject(capture?.raw_file_hashes)
  ? sha256(Buffer.from(JSON.stringify(Object.entries(capture.raw_file_hashes).sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0)))) : null;
function lintReceiptScope(context) {
  return { root: context.root, origin: context.origin, login: context.identity.login, user_id: context.identity.userId,
    source_sha256: context.capture.sha256, authored_sha256: authoredSha256(context.capture), tests: [...new Set(sentTests(context.rows))].sort(), version: context.clientVersion ?? null,
    selected_cap: context.lint.selected_cap ?? null, ...(context.allowMissingInterfaces ? { lazy_interfaces: true } : {}) };
}
const lintReceiptPath = context => join(context.store.folder('lint-receipts'), `${context.store.repoKey(context.root)}.json`);
function lintReceiptBlocked(context) {
  const path = lintReceiptPath(context);
  return readdirSync(dirname(path)).some(name => name.startsWith(`${basename(path)}.unowned.`));
}
function lintReceiptTransaction(context, action) {
  const path = lintReceiptPath(context), lock = `${path}.lock`;
  const fd = openSync(lock, 'wx', 0o600);
  try { return action(path, context.store.read(path)); }
  finally { closeSync(fd); unlinkSync(lock); }
}
function passingLintReceipt(context, answer) {
  return UUID.test(answer?.requestId ?? '') && sameJob(answer, answer.requestId, 'lint') && answer.state === 'passed'
    && (answer.result?.report?.lint?.complete === true || answer.result?.problems_complete === true)
    && context.rows.length > 0 && context.rows.every(row => !row.unsent && !row.native_only?.length && lintAdmits(answer, row, context.capture));
}
function rememberRecentLint(context, answer) {
  if (!['check', 'lint-only'].includes(context.intent) || context.reading || context.interrupted) return;
  try {
    const scope = lintReceiptScope(context), now = context.ports.now();
    const receipt = { schema_version: 'pdd.lint-receipt.v1', scope, received_at: now, engine_sha: answer?.engine_sha, answer };
    if (context.lintReceiptOwner && isRecentLintReceipt({ receipt, scope, now, engineSha: answer?.engine_sha }) && passingLintReceipt(context, answer)) {
      lintReceiptTransaction(context, (path, current) => {
        if (current?.pending === context.batch) context.store.write(path, receipt);
      });
    }
  } catch { /* Optional reuse must never prevent a fresh check. */ }
}
function readRecentLint(context) {
  try {
    if (lintReceiptBlocked(context)) return null;
    const receipt = context.store.read(lintReceiptPath(context));
    // A candidate only: the current engine from capacity is compared before adoption.
    return isRecentLintReceipt({ receipt, scope: lintReceiptScope(context), now: context.ports.now(), engineSha: receipt?.engine_sha })
      && receipt.engine_sha === receipt.answer?.engine_sha && passingLintReceipt(context, receipt.answer) ? receipt : null;
  } catch { return null; }
}

// Every lint asks for complete per-test verdicts: only they can admit a test.
async function runLint(context) {
  const agent = context.agentLimit ?? !context.ports.interactive;
  const lintEnd = context.intent === 'check' && !context.checkDeadlineStarted
    ? context.timeoutMin ? context.startedAt + Math.min(context.timeoutMin * 60_000, context.ports.interactive ? Infinity : AGENT_WAIT_MIN * 60_000) : Infinity
    : context.batch ? context.deadline : Math.min(context.deadline, agent ? context.startedAt + AGENT_WAIT_MIN * 60_000 : Infinity);
  const tick = progressTicker(context.ports.stderr, context.ports.now);
  let paused = false;
  const stopped = () => ({ kind: 'not_run', note: { code: 'interrupted', message: paused ? stoppedPause(context, context.lint, 'lint')
    : `Stopped before sending.${context.waitCause === 'maintenance' ? ' pdd stopped while waiting for maintenance.' : ''}` } });
  const busy = () => {
    if (context.interrupted) return stopped();
    const ended = context.ports.now() >= lintEnd;
    const explicit = ended && context.explicitTimeout && lintEnd === context.deadline;
    const note = { code: ended ? explicit ? 'timeout-flag' : 'deadline' : 'lint-busy',
      message: `${explicit ? `Stopped waiting at --timeout ${context.timeoutMin} min. ` : ''}Your wait ended while pdd waited for ${context.waitCause ?? 'server capacity'}. No checks ran. Run the same pdd command again later.` };
    Object.assign(context.lint, { state: 'not_run', note });
    return { kind: 'not_run', note };
  };
  const pause = async (wait, maintenance = false) => {
    paused = true;
    context.waitCause = maintenance ? 'maintenance' : 'server capacity';
    if (context.interrupted || context.ports.now() >= lintEnd) return false;
    if (!maintenance) line(context.ports.stderr, 'The server is busy. Waiting for a lint slot…');
    return waitBudget(context, wait, lintEnd);
  };
  if (context.intent === 'check') {
    const receipt = readRecentLint(context);
    if (receipt) {
      if (!await capacityReady(context, lintEnd)) return busy();
      if (isRecentLintReceipt({ receipt, scope: lintReceiptScope(context), now: context.ports.now(), engineSha: context.serverEngineSha ?? null })) {
        try {
          const adopted = lintReceiptTransaction(context, (path, current) => {
            if (lintReceiptBlocked(context) || !isDeepStrictEqual(current, receipt)) return false;
            saveAnswer(context, receipt.answer.requestId, receipt.answer);
            context.lint.request_ids.push(receipt.answer.requestId);
            return true;
          });
          if (adopted) {
            line(context.ports.stderr, 'Reusing recent passing lint for unchanged source.');
            return { kind: 'answer', answer: receipt.answer };
          }
        } catch { /* A missing durable copy falls back to normal lint. */ }
      }
    }
  }
  line(context.ports.stderr, `Checking ${context.capture.files.length} files (${formatSize(context.capture.bytes)}) on the PDD interpreter (lint, 0 AI calls)…`);
  if (['check', 'lint-only'].includes(context.intent)) {
    try {
      lintReceiptTransaction(context, path => context.store.write(path, { pending: context.batch }));
      context.lintReceiptOwner = true;
    } catch {
      context.lintReceiptOwner = false;
      try {
        const path = `${lintReceiptPath(context)}.unowned.${context.batch}`;
        context.store.write(path, { batch: context.batch });
        context.lintReceiptBlocker = path;
      } catch { /* Unavailable optional state still permits fresh lint. */ }
    }
  }
  try {
  for (;;) {
    if (context.interrupted) return stopped();
    if (context.ports.now() >= lintEnd) return busy();
    paused = false;
    if (!await admission(context, 'lint', context.lint, lintEnd)) return busy();
    const uploaded = new Set(context.capture.files.map(file => file.path));
    const tests = [...new Set(sentTests(context.rows ?? []).filter(path => uploaded.has(path)))].sort();
    const maps = new Set(context.appMap ? [context.appMap] : []);
    for (const source of context.capture.sources ?? []) {
      if (!tests.includes(source.path)) continue;
      let doc;
      try { doc = JSON.parse(source.bytes.toString('utf8')); } catch { continue; }
      for (const path of Array.isArray(doc?.app_maps) ? doc.app_maps : []) if (typeof path === 'string') maps.add(path);
    }
    const named = context.serverFeatures?.includes('lint-tests') ? { tests, app_maps: [...maps].sort() } : {};
    const selectedCap = context.intent === 'lint-only' ? context.lint.selected_cap : null;
    if (selectedCap != null && !context.serverFeatures?.includes('lint-call-preflight')) return {
      kind: 'refused', refusal: { code: 'lint-call-preflight-unsupported', message: 'The PDD interpreter does not support selected-cap call preflight. No lint or checks were sent. Update the interpreter before inspecting this cap.' }
    };
    const request = { requestId: context.ports.randomUUID(), source_sha256: context.capture.sha256, complete: true, ...named,
      ...(selectedCap != null ? { max_calls: selectedCap } : {}),
      ...(context.serverFeatures?.includes('lazy-interfaces') ? { lazy_interfaces: true } : {}) };
    context.lint.request_ids.push(request.requestId);
    const verdict = await postJob(context, '/v1/lint', 'lint', request, null, Math.max(1, Math.min(context.ports.postMs, lintEnd - context.ports.now())), lintEnd);
    if (verdict.kind === 'busy') { if (await pause(verdict.wait, verdict.maintenance)) continue; return busy(); }
    if (verdict.kind === 'not_sent') return context.interrupted ? stopped() : busy();
    if (verdict.blocked) throw new Stop(5, verdict.note.message);
    if (verdict.kind !== 'accepted' && verdict.kind !== 'unknown') return verdict;
    // Unknown dispatch still reads only this ID; only a confirmed terminal capacity refusal permits another attempt.
    let readEnd = verdict.kind === 'unknown' && !Number.isFinite(lintEnd)
      ? context.ports.now() + LOST_READ_MS : lintEnd;
    let answer = verdict.answer ?? null, id = request.requestId, lost = false;
    while (!['passed', 'failed', 'refused', 'unknown'].includes(answer?.state) && context.ports.now() < readEnd && !context.interrupted) {
      await context.ports.sleep(Math.min(context.ports.pollMs, Math.max(0, readEnd - context.ports.now())), context.signal);
      if (context.interrupted || context.ports.now() >= readEnd) break;
      const read = judgeGet(await context.runtime.get(id, Math.max(1, Math.min(GET_MS, readEnd - context.ports.now()))), id, 'lint');
      if (read.kind === 'state') {
        answer = read.answer;
        if (['queued', 'running'].includes(answer.state)) readEnd = lintEnd;
        saveAnswer(context, id, answer); queueProgress(context, answer); await finishReservation(context, context.lint, answer);
      }
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
      const note = { code: context.interrupted ? 'interrupted' : 'deadline', message: pendingLintMessage(context, answer) };
      Object.assign(context.lint, { state: answer.state, pending: true, unknown: false, note });
      saveBatch(context);
      return { kind: 'pending', answer, note };
    }
    if (!lost && answer) rememberRecentLint(context, answer);
    return lost || !answer ? { kind: 'unknown' } : { kind: 'answer', answer };
  }
  } finally {
    if (context.lintReceiptBlocker) {
      try {
        lintReceiptTransaction(context, path => {
          context.store.write(path, null);
          unlinkSync(context.lintReceiptBlocker);
        });
      } catch { /* Retain the blocker if cleanup cannot establish ownership. */ }
    }
  }
}

// A check that lint did not admit: refused with its lint refusal; not run with the reason when the
// lint ended without a pass for it (final); not run and held while the lint itself has no verdict yet.
function unsentByLint(outcome) {
  if (outcome.state === 'refused') return ['refused', { refusals: outcome.refusals, note: null }];
  return ['not_run', { refusals: [], note: { code: outcome.code || 'no-server-verdict', message: outcome.state === 'unknown' ? 'The lint result is unknown, so pdd sent no checks.'
    : `No lint pass for this test (${outcome.reason ?? outcome.message}), so pdd sent no checks.` } }];
}

async function checkBatch(context, rows, priorLint = null) {
  const { ports } = context, sendable = rows.filter(row => row.state === 'ready');
  const lint = priorLint ?? await runLint(context);
  if (context.intent === 'check' && !context.checkDeadlineStarted) {
    context.checkDeadlineStarted = true;
    context.deadline = context.timeoutMin ? ports.now() + context.timeoutMin * 60_000 : Infinity;
  }
  context.lastCheckLint = lint;
  context.lint.state = lint.answer?.state ?? lint.kind;
  context.lint.unknown = false;
  const lintView = noVerdictAdvice(lint.answer, projectAnswer(lint.answer ?? {}, { origin: context.origin, secrets: context.secrets }));
  const notSent = (state, extra, only = sendable) => { for (const row of [only].flat()) Object.assign(row, { state, calls: 0, phase: 'lint', why: lintView.why, next_step: lintView.next_step, ...extra }); };
  if (context.interrupted) { notSent('not_run', { note: lint.note ?? { code: null, message: 'Stopped before sending.' } }); return; }
  if (lint.kind === 'pending') {
    context.lintPending = true;
    notSent('not_run', { note: { code: context.interrupted ? 'interrupted' : 'lint-pending', message: pendingLintMessage(context, lint.answer) } });
    return;
  }
  if (lint.kind === 'not_run' || lint.kind === 'stop') {
    if (lint.kind === 'stop') context.stopped = lint.note;
    notSent('not_run', { note: lint.note, ...(lint.note?.code === 'lint-busy' ? { calls: 0, phase: 'lint' } : {}) });
    return;
  }
  if (lint.kind === 'refused') { notSent('refused', { phase: 'lint', refusals: [lint.refusal] }); return; }
  const verdicts = judgeLint(lint.answer, sendable, context.root, context.visible, context.secrets, context.capture);
  context.lint.public_result = resultOverall([...verdicts.values()]);
  const toSend = sendable.filter(row => verdicts.get(row).state === 'passed');
  for (const [row, outcome] of verdicts) if (outcome.state !== 'passed') notSent(...unsentByLint(outcome), row);
  const refused = sendable.filter(row => row.state === 'refused').length, held = sendable.length - toSend.length - refused;
  context.lintUnknown = context.lint.unknown = [...verdicts.values()].some(outcome => outcome.state === 'unknown');
  if (!toSend.length && !refused) return;
  if (toSend.length) lintDiagnostics(context, lint.answer, sendable);
  const judged = toSend.length === sendable.length ? 'Lint passed.' : [refused ? `Lint refused ${refused} of ${sendable.length} tests.` : '',
    held ? `Lint gave no verdict for ${held} of ${sendable.length} tests.` : ''].filter(Boolean).join(' ');
  line(ports.stderr, judged);
  if (context.otherNote) line(ports.stderr, context.otherNote);
  // Only now is there something to read again (lead, Oct 27): after lint passes, before the first check POST.
  if (toSend.length && !priorLint) line(ports.stderr, `If pdd stops, read the results with: pdd test --read ${context.batch}`);
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
  let waitingShown = -1;
  const progress = context.checkProgress ??= { startedAt: ports.now(), shownAt: ports.now() };
  const readable = row => isOpen(row) && ports.now() < Math.min(context.deadline, row.lost ? row.read_until ?? context.deadline : context.deadline);
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
      if (waiting.length) line(ports.stderr, `⏳ PDD is busy right now. ${waiting.length} of your checks ${waiting.length === 1 ? 'is' : 'are'} waiting to start. You are not charged while you wait.`);
      waitingShown = waiting.length;
    }
    if (context.sendError) throw context.sendError;
    await recoverRestarts(context);
    const pending = toSend.some(row => ['ready', 'waiting'].includes(row.state));
    if (pending && active >= context.checkWindow && !rows.some(readable)) break;
    if ((!pending || context.stopped || ports.now() >= context.deadline) && !rows.some(readable) && !pendingSends.size) break;
    if (ports.now() - progress.shownAt >= PROGRESS_MS) { progress.shownAt = ports.now(); line(ports.stderr, progressLine(rows, progress.shownAt - progress.startedAt)); }
    const end = context.deadline;
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
  context.timedOut ||= !stoppedEarly && ports.now() >= context.deadline && rows.some(isOpen);
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
  if (context.intent === 'lint-only' && !context.interrupted && !context.lintPending && !context.lintUnknown && rows.every(row => !row.request_ids?.length)) {
    const id = context.lint?.request_ids?.at(-1), answer = id && context.store.read(join(context.folder, `${id}.json`));
    if (sameJob(answer, id, 'lint') && ['passed', 'failed', 'refused'].includes(answer.state))
      return printLintResult(context, rows, lintProblems(context, answer), context.warnings ?? [], answer);
  }
  markDeadline(context, rows);
  rows = rows.map(row => heldForLint(row) && !row.dispatchIncomplete ? { ...row, calls: 0 } : row);
  const { ports } = context, exitCode = context.localOnly && context.checkPlan?.full && context.checkPlan.prerequisites.length ? 4
    : ports.exitCodeFor(rows, { interrupted: context.interrupted, lintUnknown: context.lintUnknown || context.lintPending });
  const engines = [...new Set(rows.map(row => row.engine_sha).filter(sha => sha && !sameEngine(sha)))].filter(sha => firstToday(context, sha));
  const warnings = [...(context.warnings ?? []), ...engines.map(sha => `Warning: the interpreter engine is ${cleanText(sha).slice(0, 12)}, but pdd's local checks copy engine ${ENGINE_SHA.slice(0, 12)}. The engine stays the judge.`)];
  const coverage = exitCode === 5 && context.coverage?.runtime?.native_only === 0
    ? Object.fromEntries(Object.entries(context.coverage).filter(([key])=>key !== 'runtime')) : context.coverage;
  const summary = renderJson({ batch: context.batch ?? null, repo: context.root, sourceSha256: context.capture?.sha256 ?? null, coverage, rows, exitCode, summaryLine: context.noFailed ? 'No failed Stories. 0 AI calls.' : summaryLine(rows, null, ports),
    warnings: [...new Set([...warnings, ...(context.unmatched ?? [])]), ...rows.flatMap(row => (row.warnings ?? []).map(text => `${row.test}: ${text}`))] }, ports);
  if (context.intent === 'lint-only') {
    const id = context.lint?.request_ids?.at(-1), answer = id && context.store.read(join(context.folder, `${id}.json`));
    summary.report_url = sameJob(answer, id, 'lint') ? validLink(cleanText(answer.report_url, context.secrets), context.origin, 'report') : null;
  }
  if (context.checkPlan) {
    summary.check_plan = context.checkPlan;
    summary.check_scope = selectedCheckScope(context.checkPlan, rows, context.checkSelection);
  }
  if (context.checkSelection) {
    summary.check_selection = context.checkSelection; summary.baseline_report = context.baselineReport;
    summary.warnings = [...new Set([...summary.warnings, AFFECTED_DISCLAIMER])];
  }
  if (context.folder) context.store.write(join(context.folder, 'summary.json'), summary);
  if (context.batch && rows.some(row => row.can_retry)) line(ports.stderr, `Retry only unstarted checks with: pdd test --retry ${context.batch}`);
  if (context.readStop) line(ports.stderr, context.readStop);
  if (context.continuationNotice) line(ports.stderr, context.continuationNotice);
  if (context.stopped && (!context.json || context.stopped.message === AUTH_TEXT)) line(ports.stderr, context.stopped.message);
  const scrub = text => (context.secrets ?? []).reduce((value, secret) => secret ? value.split(secret).join('[secret]') : value, text);
  if (context.json) line(ports.stdout, scrub(JSON.stringify(summary)));
  else ports.stdout.write(scrub(renderText({ batch: context.batch, rows, coverage: context.coverage, warnings, details: context.details, timeoutMin: context.timeoutMin,
    now: ports.now(), noFailed: context.noFailed, interrupted: context.interrupted || !!context.readStop, reading: !!context.reading, exitCode, secrets: context.secrets, ...extra }, ports)));
  if (!context.json && summary.report_url) line(ports.stdout, `Report: ${summary.report_url}`);
  if (!context.json) for (const value of checkPlanResultLines(summary.check_scope)) line(ports.stdout, scrub(value));
  if (!context.json && context.checkSelection) {
    line(ports.stdout, AFFECTED_DISCLAIMER);
    for (const value of historicalBaselineLines(context.baselineReport)) line(ports.stdout, scrub(value));
  }
  // At the time limit the jobs keep running on the server.
  if (exitCode === 3 && context.batch) line(ports.stderr, context.timedOut ? `Still running. Read the results later with: pdd test --read ${context.batch}`
    : `If pdd stops, read the results with: pdd test --read ${context.batch}`);
  return exitCode;
}

function runExplainBindings(cwd, words, options, ports) {
  const {root,found,normalized}=localSetup(cwd,words,ports);
  const selected=select(found,normalized,root,ports);
  for (const test of selected) {
    const problem=discoveryRefusal(test) ?? test.criteriaRefusal ?? scenarioShapeRefusal(test.doc,test.path);
    if (problem) throw Object.assign(new PreflightError(4,`${test.path}: ${problem.message}`),{code:problem.code});
  }
  const capture=ports.captureSource(root,{tests:selected.map(test=>test.path),excludeFixtureProjects:words.length===0});
  const plans=capture.bindingPlans ?? [];
  const code=plans.some(plan=>plan.problems.length || plan.edges.some(edge=>edge.state==='missing')) ? 4 : 0;
  line(ports.stdout,options['--json'] ? JSON.stringify({schema_version:'pdd.binding-plans.v1',plans}) : plans.flatMap(bindingPlanLines).join('\n'));
  return code;
}

function runFiles(cwd, words, options, ports) {
  const { root, found, normalized } = localSetup(cwd, words, ports);
  const selected = select(found, normalized, root, ports), coverage = bindingCoverage({ root, found, selected, includeRuntime:true });
  const rows = selected.map(test => ({test:test.path,story:test.story,state:'ready',refusals:[],
    ...(discoveryRefusal(test) ? {state:'refused',unsent:true,refusals:[discoveryRefusal(test)]} : {})}));
  const nativeRows = new Map(preflight({root,found,selected}).rows.filter(row=>row.native_only?.length).map(row=>[row.test,row]));
  const advice = formatAdvice(root, found.visible, entryPaths(selected), found.workspace);
  for (const row of rows) {
    const native = nativeRows.get(row.test);
    if (native) Object.assign(row,{native_only:native.native_only,unsent:true,state:native.refusals.length ? 'refused' : 'not_run',
      refusals:native.refusals,note:{code:'native-only',message:native.native_only.map(item=>`${item.path}: ${item.reason}`).join('; ')}});
  }
  const appMap = options['--app-map'] === undefined ? null : appMapFor(found, options['--app-map'], cwd, root, ports.stderr);
  for (const path of found.excludedFixtureProjects ?? []) line(ports.stderr, `Warning: skipped nested fixture project ${path}.`);
  const capture = captureIndependent(root, rows, ports, {appMap,excludeFixtureProjects:words.length === 0})
    ?? {files:[],reads:[],bytes:0};
  const broken = rows.filter(row => row.unsent && row.refusals.length), exitCode = broken.length ? 4 : 0;
  const summary = `${capture.files.length} files, ${formatSize(capture.bytes)} (${capture.bytes} bytes). ${otherFiles(capture.files, found).length} of them are not prompt, story or test files.${broken.length ? ` ${broken.length} tests could not run.` : ''}`;
  if (options['--json']) {
    line(ports.stdout, JSON.stringify({repo:root,exit_code:exitCode,summary_line:summary,source_sha256:capture.sha256 ?? null,rows:[...rows.filter(row=>row.unsent).map(row=>({...row,...resultOutcome(row)})),...rows.filter(row=>!row.unsent)],files:capture.files,coverage,...(advice.length ? {warnings:advice} : {})}));
    return exitCode;
  }
  for (const row of broken) for (const problem of row.refusals) {
    line(ports.stdout, `${row.test}: ${problem.message}`);
    line(ports.stdout, problem.hint ?? 'Fix the named test file, then run the selection again.');
  }
  for (const row of rows.filter(row=>row.native_only?.length)) line(ports.stdout, `${row.test}: ${outcomeText(row)}: ${row.note.message}`);
  for (const warning of [...advice, ...(capture.warnings ?? []), ...unmatchedLines(found)]) line(ports.stderr, warning);
  const width = Math.max(0, ...capture.files.map(file => file.path.length));
  for(const read of capture.reads??[])line(ports.stderr,`Local read (${read.roles.join(', ')}, not uploaded): ${read.path}`);
  for (const file of capture.files) line(ports.stdout, `  ${(file.path + (file.target ? ` -> ${file.target}` : '')).padEnd(width)}  ${file.size} bytes`);
  line(ports.stdout, summary);
  if (capture.sha256) line(ports.stdout, `Source SHA-256: ${capture.sha256}`);
  line(ports.stderr, coverageText(coverage));
  return exitCode;
}

// pdd lint: only the server's lint (0 AI calls) on the captured files.
// Locally the selected prompts' limits and interface format gates, SVG advice and privacy/capture checks run.
async function runLintOnly(context, cwd, words, options, setRelease) {
  const { ports } = context, origin = runtimeOrigin(ports.env), { root, found, normalized } = localSetup(cwd, words, ports);
  context.excludeFixtureProjects = words.length === 0;
  const paths = words.length ? undefined : [...found.discoveryVisible].filter(path => path.endsWith('.prompt.md'));
  let findings = paths ? interfaceFindings({root,paths}).filter(localInterfaceProblem) : [];
  const advice = paths ? formatAdvice(root, found.visible, paths, found.workspace) : [];
  found.warnings.push(...advice);
  if (findings.length && !found.tests.length) {
    const summary = 'Lint refused Runtime interfaces. 0 AI calls. No files were sent.';
    if (context.json) line(ports.stdout,JSON.stringify({repo:root,exit_code:4,lint_state:'refused',problems:findings,rows:[],summary_line:summary}));
    else for (const text of [...findings.map(item => `${item.code}: ${item.message}`),summary]) line(ports.stdout,text);
    return 4;
  }
  let selected;
  try { selected = select(found, normalized, root, ports); }
  catch (error) {
    if (error instanceof Stop) {
      const noTestsAdvice = [...new Set([...advice, ...(paths ? lintLocalHygiene({ root, files: [...found.visible], promptPaths: paths, tests: [], workspace: found.workspace }, ports) : [])])];
      if (noTestsAdvice.length) error.message = [error.message, ...noTestsAdvice].join('\n');
    }
    throw error;
  }
  if (!paths) { advice.push(...formatAdvice(root, found.visible, entryPaths(selected), found.workspace)); found.warnings.push(...advice); }
  for (const warning of missingCliImplementationWarnings({ root, found, selected })) {
    if (!advice.includes(warning)) advice.push(warning);
    if (!found.warnings.includes(warning)) found.warnings.push(warning);
  }
  const hasMissing = findings.some(item => item.code === 'interface-missing') || hasMissingPromptInterface(root, found, entryPaths(selected));
  const allowMissingInterfaces = hasMissing ? await probeLazyInterfaces(context, origin, context.store) : false;
  if (allowMissingInterfaces) findings = findings.filter(item => item.code !== 'interface-missing');
  const activeLocalProblem = problem => localInterfaceProblem(problem) && !(allowMissingInterfaces && problem.code === 'interface-missing');
  context.coverage = bindingCoverage({ root, found, selected, includeRuntime:true, allowMissingInterfaces });
  // A test that the test name rule cannot use is refused here and never sent; the other tests are linted.
  const rows = selected.map(test => ({ test: test.path, story: test.story, title: test.title, state: 'ready', phase: 'lint',
    refusals: [], request_ids: [], warnings: [], steps: Array.isArray(test.doc?.steps) ? test.doc.steps.filter(isObject) : [],
    app_maps: Array.isArray(test.doc?.app_maps) ? test.doc.app_maps.filter(path => typeof path === 'string' && path.length > 0) : [],
    criterion_texts: Object.fromEntries((Array.isArray(test.doc?.criteria) ? test.doc.criteria : []).filter(isObject).map(item => [item.id, item.text])),
    ...(discoveryRefusal(test) ? { state: 'refused', phase: 'local', unsent:true, refusals: [discoveryRefusal(test)], steps: [], app_maps: [] } : {}) }));
  context.rows = rows;
  const nativeRows = new Map(preflight({root,found,selected,allowMissingInterfaces}).rows.filter(row => row.native_only?.length).map(row => [row.test,row]));
  for (const row of rows) {
    const native = nativeRows.get(row.test);
    if (native) Object.assign(row,{state:native.refusals.length ? 'refused' : 'not_run',refusals:native.refusals,phase:'local',native_only:native.native_only,unsent:true,note:{code:'native-only',message:native.native_only.map(item => `${item.path}: ${item.reason}`).join('; ')}});
  }
  if (!findings.length && rows.every(row => row.native_only?.length)) {
    const hygiene = lintLocalHygiene({ root, files: [...found.visible], promptPaths: words.length ? entryPaths(selected) : undefined, tests: selected, workspace: found.workspace }, ports);
    context.warnings = [...new Set([...found.warnings, ...hygiene])];
    saveLocalNativeResult(context, rows, 'lint-only');
    return printLintResult(context, rows, [], [...new Set([...advice, ...hygiene])]);
  }
  const local = row => row.phase === 'local';
  const {promptSchemaRefusals} = await import('./runtime-preflight.mjs');
  const prompts = new Map();
  const problemsFor = (path, seen) => {
    if (typeof path !== 'string' || seen.has(path)) return [];
    const finding = interfaceFindings({root,paths:[path]}).filter(activeLocalProblem);
    if (finding.length) return finding;
    if (!prompts.has(path)) prompts.set(path, readPrompt(root, found.visible, path, found.workspace));
    return promptSchemaRefusals(root, found, prompts.get(path), prompts, seen, { allowMissingInterfaces }).filter(problem =>
      activeLocalProblem(problem) || ['invalid-limits', 'invalid-interface'].includes(problem.code) && problem.section.startsWith('/limits'));
  };
  const limitRows = rows.map(row => {
    const seen = new Set();
    try { return local(row) ? row : {...row,refusals:row.steps.flatMap(step => problemsFor(step.entry_path,seen))}; }
    catch (error) { if (!sourceUnavailable(error)) throw error; refuseSource(row,error); return row; }
  });
  const limited = findings.length > 0 || limitRows.some(row => !local(row) && row.refusals.length);
  if (!limited && rows.every(local)) {
    if (rows.some(row => row.native_only?.length)) saveLocalNativeResult(context,rows,'lint-only');
    return printLintResult(context,rows,[],found.warnings);
  }
  if (limited) {
    const refusedRows = limitRows.map(row => ({...row,state:row.refusals.length ? 'refused' : 'not_run',refusals:row.refusals,
      ...(row.unsent ? {unsent:true} : {})})).sort((a,b)=>Number(!!b.unsent)-Number(!!a.unsent));
    const problems = [...findings];
    for (const problem of refusedRows.flatMap(row => row.refusals)) {
      if (!problems.some(item => item.code === problem.code && item.path === problem.path && item.section === problem.section)) problems.push(problem);
    }
    if (refusedRows.some(row => row.native_only?.length)) {
      context.warnings = found.warnings;
      saveLocalNativeResult(context, refusedRows, 'lint-only', problems);
      return printLintResult(context, refusedRows, problems);
    }
    const broken = refusedRows.filter(row=>row.unsent).length;
    const summary = `Lint refused local Runtime declarations.${broken ? ` ${broken} tests could not run.` : ''} 0 AI calls. No files were sent.`;
    if (context.json) line(ports.stdout, JSON.stringify({batch:null,repo:root,exit_code:4,lint_state:'refused',summary_line:summary,
      coverage:context.coverage,problems,rows:refusedRows.map(row => ({...row,...resultOutcome(row)})),warnings:found.warnings}));
    else {
      for (const row of refusedRows.filter(row=>row.unsent)) for (const problem of row.refusals) {
        line(ports.stdout, `${row.test}: ${problem.message}`);
        line(ports.stdout, problem.hint ?? 'Fix the named test file, then run the selection again.');
      }
      for (const problem of problems) {
        line(ports.stderr, `${problem.code}  ${problem.message}`);
        if (problem.hint) line(ports.stderr, problem.hint);
      }
      for (const row of refusedRows) line(ports.stdout, `  ${row.test}  ${outcomeText(row)}`);
      line(ports.stdout,summary);
      line(ports.stdout,coverageText(context.coverage));
    }
    return 4;
  }
  // Lint keeps engine validation ownership; only attach structural incomplete-coverage facts.
  for (const row of rows.filter(row => !row.unsent)) {
    const test = selected.find(test => test.path === row.test), checked = preflight({root,found,selected:[test],allowMissingInterfaces}).rows[0];
    if (checked.not_checked?.length) Object.assign(row, {not_checked:checked.not_checked,criteria_total:checked.criteria_total});
    if (checked.refusals.some(item=>item.code==='unchecked-criteria')) Object.assign(row,
      {state:'refused',phase:'local',unsent:true,refusals:checked.refusals});
  }
  const capture = captureIndependent(root, rows, ports, {appMap:null,excludeFixtureProjects:words.length === 0,...(allowMissingInterfaces ? {allowMissingInterfaces:true} : {})});
  context.sourceSelection = {tests:sentTests(rows),exclude_fixture_projects:words.length === 0};
  context.nativeSource = nativeSourceIdentity(context, rows);
  if (!capture) return printLintResult(context, rows, [], found.warnings);
  if (typeof ports.lintSvgLayouts !== 'function') throw unboundPortError('SVG layout port (lintSvgLayouts) is not bound.');
  const svgWarnings = ports.lintSvgLayouts({ root, files: [...found.visible], promptPaths: capture.files.map(file => file.path).filter(path => path.endsWith('.prompt.md')) });
  const hygieneWarnings = lintLocalHygiene({
    root,
    files: [...found.visible],
    promptPaths: words.length ? capture.files.map(file => file.path).filter(path => path.endsWith('.prompt.md')) : undefined,
    tests: selected,
    workspace: found.workspace,
  }, ports);
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
  context.warnings = [...new Set([...svgWarnings, ...found.warnings, ...drift, ...(capture.warnings ?? []), ...hygieneWarnings])];
  context.unmatched = unmatchedLines(found);
  if (!context.json) for (const warning of [...new Set([...svgWarnings, ...drift, ...(capture.warnings ?? []), ...hygieneWarnings])]) line(ports.stderr, warning);
  const identity = context.probedIdentity ?? signIn(ports.gh, context.store, ports), startedAt = ports.now(), batch = batchId(startedAt, ports.randomUUID);
  const timeoutMin = options['--timeout'] !== undefined ? Number(options['--timeout']) : ports.interactive ? null : AGENT_WAIT_MIN;
  Object.assign(context, { origin, visible: found.visible, capture, identity, batch, startedAt, deadline: timeoutMin ? startedAt + timeoutMin * 60_000 : Infinity, rows, head: null,
    intent: 'lint-only', agentLimit: options['--timeout'] === undefined && !ports.interactive, secrets: [identity.token], lint: { request_ids: [], state: null, selected_cap: requestedCalls(options['--max-calls']) ?? null }, timeoutMin });
  context.folder = context.store.folder('batches', batch);
  setRelease(interruptible(context));
  await ownBatch(context, batch);
  saveBatch(context);
  const repoState = context.store.repo(root);
  context.store.saveRepo(root, { ...repoState, last_batch: batch });
  context.auth = authSession({ identity, store: context.store, ports, secrets: context.secrets, onRefresh: next => { context.identity = next; saveBatch(context); } });
  context.runtime = new Runtime({ origin, token: identity.token, ports, signal: context.signal, auth: context.auth });
  let lint;
  try { lint = await runLint(context); }
  catch (error) {
    if (!(error instanceof Stop) || error.exitCode !== 5 || !rows.some(row=>row.native_only?.length)) throw error;
    lint = {kind:'stop',note:{code:'blocked',message:error.message}};
  }
  if (lint.kind === 'pending') { context.lintPending = true; Object.assign(context.lint, { state: lint.answer.state, pending: true });
    for (const row of rows) if (!local(row)) Object.assign(row, { state: 'not_run', calls: 0, phase: 'lint', note: { code: context.interrupted ? 'interrupted' : 'lint-pending', message: pendingLintMessage(context, lint.answer) } });
    saveBatch(context); line(ports.stderr, pendingLintMessage(context, lint.answer)); return printResult(context, rows); }
  if (lint.kind === 'not_run') {
    for (const row of rows) if (!local(row)) Object.assign(row, { state: 'not_run', calls: 0, note: lint.note });
    Object.assign(context.lint, { state: 'not_run', note: lint.note, public_result: resultOverall(rows) });
    saveBatch(context); line(ports.stderr, lint.note.message);
    return printLintResult(context, rows, []);
  }
  if (lint.kind === 'stop') {
    for (const row of rows) if (!local(row)) Object.assign(row,{state:'not_run',calls:0,note:lint.note});
    Object.assign(context.lint,{state:'not_run',note:lint.note,public_result:resultOverall(rows)});
    saveBatch(context); line(ports.stderr,lint.note.message);
    return printLintResult(context,rows,[]);
  }
  const answer = lint.answer;
  if (context.interrupted || lint.kind === 'unknown') {
    context.lintUnknown = true;
    for (const row of rows) if (!local(row)) Object.assign(row, { state: 'unknown', calls: 0, note: lint.note });
    saveBatch(context); return printResult(context, rows);
  }
  const problems = lintProblems(context, answer, lint.kind === 'refused' ? lint.refusal : null);
  // Each row is its selected test's lint outcome; a refusal of the lint request itself refuses every row.
  const verdicts = judgeLint(answer, rows.filter(row => !local(row)), root, found.visible, context.secrets, context.capture);
  context.lintUnknown = lint.kind !== 'refused' && [...verdicts.values()].some(outcome => outcome.state === 'unknown');
  for (const [row, outcome] of verdicts) {
    Object.assign(row, lint.kind === 'refused' ? { state: 'refused', refusals: problems }
      : { state: outcome.state, refusals: outcome.refusals, ...(outcome.reason ? { note: { code: outcome.code || 'no-server-verdict', message: outcome.reason } } : {}) });
    incompleteCriteria(row);
  }
  Object.assign(context.lint, { state: answer?.state ?? lint.kind, unknown: rows.some(row => row.state === 'unknown'), pending: false, public_result: resultOverall(rows) });
  saveBatch(context);
  return printLintResult(context, rows, problems, found.warnings, answer);
}

function lintProblems(context, answer, refusal = null) {
  const problems = refusal ? [{ ...refusal, path: null }] : [];
  const program = answer?.result?.report?.program;
  const canonical = Array.isArray(answer?.result?.problems) ? answer.result.problems : answer?.result?.report?.problems;
  const originalIdentity = item => JSON.stringify([cleanText(item.code, context.secrets) || 'lint-refused', cleanText(item.file ?? item.path, context.secrets) || null, cleanText(item.at ?? item.section, context.secrets) || null]);
  const canonicalLocations = new Set((Array.isArray(canonical) ? canonical.filter(isObject) : []).map(originalIdentity));
  for (const item of Array.isArray(canonical) ? canonical.filter(isObject) : []) {
    const reason = cleanText(item.reason, context.secrets), fix = cleanText(item.fix, context.secrets);
    problems.push(interfaceDiagnostic({ code: cleanText(item.code, context.secrets) || 'lint-refused', path: cleanText(item.file ?? item.path, context.secrets) || null,
      section: cleanText(item.at ?? item.section, context.secrets) || null,
      message: cleanText(item.message, context.secrets) || [reason, fix].filter(Boolean).join(' ') || null, hint: null,
      severity: cleanText(item.severity, context.secrets) || 'error', pointer: cleanText(item.pointer, context.secrets) || null,
      source: cleanText(item.source, context.secrets) || null }, item, context.root, context.secrets));
  }
  for (const item of isObject(program) && Array.isArray(program.refused_prompts) ? program.refused_prompts.filter(isObject) : []) {
    if (canonicalLocations.has(originalIdentity(item))) continue;
    const problem = interfaceDiagnostic({ code: cleanText(item.code, context.secrets) || 'lint-refused', path: cleanText(item.path, context.secrets) || null,
      section: cleanText(item.section, context.secrets) || null, message: cleanText(item.message, context.secrets) || null, hint: null }, item, context.root, context.secrets);
    if (!problems.some(p => p.code === problem.code && p.path === problem.path && p.section === problem.section)) problems.push(problem);
  }
  return problems;
}

function printLintResult(context, rows, problems, warnings = [], answer = null) {
  const { ports, batch, root } = context;
  for (const row of rows) {
    const listed = [answer?.result?.tests, answer?.result?.report?.lint?.tests].find(items => Array.isArray(items) && items.some(item => item?.path === row.test));
    const matching = (listed ?? []).filter(item => item?.path === row.test);
    row.call_preflight = matching.length === 1 ? matching[0].call_preflight ?? null : null;
  }
  rows.forEach(incompleteCriteria);
  rows = [...rows.filter(row=>row.unsent),...rows.filter(row=>!row.unsent)];
  for (const row of rows) for (const problem of row.refusals ?? []) {
    // pdd's own per-test words stay on the row; every server or reached-prompt problem is listed once.
    if (problem.code === 'lint-refused' && !problem.path) continue;
    if (!problems.some(item => item.code === problem.code && (item.path ?? null) === (problem.path ?? null))) problems.push({ ...problem, path: problem.path ?? null, section: null });
  }
  const localRefusal = context.localOnly && (problems.length > 0 || rows.some(row => row.state === 'refused'));
  const passing = rows.filter(row => row.state === 'passed').length, lintState = outcomeOverall(rows), exitCode = localRefusal ? 4 : context.ports.exitCodeFor(rows);
  const omitted = rows.filter(row=>row.native_only?.length && !row.refusals?.length).length;
  const broken = rows.filter(row=>row.unsent && (!row.native_only?.length || row.refusals?.length)).length, unchecked = rows.reduce((n,row)=>n+(row.not_checked?.length??0),0);
  const summary = `Lint: ${passing} of ${rows.length} tests pass.${broken ? ` ${broken} tests could not run.` : ''}${omitted ? ` ${omitted} native-only tests omitted.` : ''}${unchecked ? ` ${unchecked} criteria not checked. The Story is not a full pass.` : ''} 0 AI calls. No checks were sent.`;
  const reportedCoverage = answer?.result?.capabilities_complete ?? answer?.result?.report?.lint?.capabilities_complete;
  const capabilityCoverage = typeof reportedCoverage === 'boolean' ? reportedCoverage : null;
  const reportUrl = validLink(cleanText(answer?.report_url, context.secrets), context.origin, 'report');
  const result = { batch, repo: root, exit_code: exitCode, lint_state: resultOverall(rows).state, ...resultOverall(rows), report_url: reportUrl, summary_line: summary, capabilities_complete: capabilityCoverage, coverage: context.coverage, problems,
    rows: rows.map(row => ({ story: row.story, title: row.title, test: row.test, ...(row.native_only?.length ? {native_only:row.native_only,note:row.note} : {}), ...resultOutcome(row), refusals: row.refusals, ...(row.unsent?{unsent:true}:{}), ...(row.not_checked?.length?{not_checked:row.not_checked}:{}), call_preflight: row.call_preflight ?? null, binding_plan: row.binding_plan, ...(row.binding_plan?{binding_diagnostics:bindingRefusals(row.binding_plan,row.compatibility)}:{}), compatibility: row.compatibility, client_advice: row.client_advice })), warnings: [...new Set([...(context.warnings ?? []), ...(context.unmatched ?? [])])] };
  result.call_preflight_context = answer?.result?.call_preflight_context ?? answer?.result?.report?.lint?.call_preflight_context ?? null;
  result.call_preflight_requested_cap = context.lint?.selected_cap ?? null;
  if (context.folder) context.store.write(join(context.folder, 'summary.json'), result);
  if (context.json) {
    line(ports.stdout, JSON.stringify(result));
    return exitCode;
  }
  const out = [];
  for (const row of rows.filter(row=>row.unsent)) for (const problem of row.refusals) out.push(
    `${row.test}: ${problem.message}`, problem.hint ?? 'Fix the named test file, then run the selection again.');
  for (const row of rows) for (const item of row.not_checked ?? []) out.push(`${row.test} ${item.criterion_id}: not checked: ${item.reason}`);
  if (problems.length) {
    out.push(context.localOnly ? 'Local lint problems:' : 'Lint problems (from the PDD interpreter):');
    for (const item of problems) out.push(`  ${[item.code, item.path, item.section, item.message].filter(Boolean).join('  ')}`, ...(item.hint ? [`    ${item.hint}`] : []));
  }
  for (const row of rows) out.push(`  ${row.test}  ${outcomeText(row)}${row.note ? `: ${row.note.message}` : ''}`);
  for (const row of rows.filter(row => row.state === 'refused' && row.native_only?.length)) out.push(`  Native-only: ${row.note?.message}`);
  for (const row of rows.filter(row=>row.binding_plan)) for (const detail of bindingRefusals(row.binding_plan,row.compatibility)) out.push(JSON.stringify(detail));
  for (const row of rows.filter(row => row.compatibility)) out.push(`Compatibility (${cleanText(row.story, context.secrets)} / ${cleanText(row.test, context.secrets)}): ${JSON.stringify(row.compatibility, null, 2)}`,
    `  Client advice: ${JSON.stringify(row.client_advice)}`);
  for (const row of rows) out.push(describeCallPreflight({ test: row.test, preflight: row.call_preflight ?? null,
    context: result.call_preflight_context, sourceSha256: context.capture?.sha256, requestedCap: result.call_preflight_requested_cap }).text);
  if (typeof capabilityCoverage === 'boolean') out.push(`Capability inventory complete: ${capabilityCoverage}.`);
  if (reportUrl) out.push(`Report: ${reportUrl}`);
  out.push(summary, coverageText(context.coverage), ...warnings);
  ports.stdout.write(`${out.join('\n')}\n`);
  return exitCode;
}

function runFillHash(root, cwd, words, ports, compact = false) {
  const scoped = words.length ? (ports.prepareHashSelection ?? (input => prepareHashSelection(input,{...ports,capture:ports.captureSource})))({root,cwd,words}) : null;
  const result = ports.fillHashes(scoped ? {root,files:scoped.files,targets:scoped.targets,...(compact ? {compact:true} : {})} : (compact ? {root,compact:true} : {root}));
  for (const { message } of result.warnings) line(ports.stdout, `Warning: ${message}`);
  for (const { path } of result.filled) line(ports.stdout, `Filled prose_sha256: ${path}`);
  for (const { path } of result.synced ?? []) line(ports.stdout, `Synced criteria: ${path}`);
  if (compact) for (const { path } of result.compacted) line(ports.stdout, `Compacted Runtime interface: ${path}`);
  for (const { message } of result.refused) line(ports.stdout, `Refused: ${message}`);
  for (const { path } of result.stale) line(ports.stdout, `Stale: ${path} is approved, but ${STALE_HINT}.`);
  if (compact) line(ports.stdout, `Interfaces: ${result.compacted.length} compacted.`);
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
  const held = rows.filter(row => runtimeLintRow(row) && !row.request_ids?.length && row.state === 'not_run' && (unresolved
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
  if (answer) { lint.note = null; delete lint.public_result; await finishReservation(context, lint, answer); }
  context.lintPending = false; context.lintUnknown = false;
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
  Object.assign(lint, { state: answer.state, pending: false, unknown: false });
  const sourceRecovered = recoverSourceContext(context);
  const judged = judgeLint(answer, held, context.root, context.visible, context.secrets, context.capture);
  for (const [row, outcome] of judged) {
    const [state, extra] = busy ? ['not_run', { refusals: [], note: { code: 'lint-busy', message: 'The saved lint could not get a slot. No checks ran. Run the same command again later.' } }]
      : outcome.state === 'passed' ? context.intent === 'lint-only' ? ['passed', { refusals: [], note: null }]
        : ['not_run', { refusals: [], note: { code: 'lint-finished', message: 'The saved lint finished. This check was not sent. Run a fresh pdd test command to start checks.' } }]
      : unsentByLint(outcome);
    // These rows already have unsent lint-held producer evidence. Failed source
    // reconstruction must retain it so later reads repeat the guarded source
    // check and its actionable explanation, rather than silently ending recovery.
    if (!busy && !sourceRecovered && state === 'not_run') extra.note = { code: 'lint-finished',
      message: 'The saved lint finished. This check was not sent because the saved source could not be verified.' };
    Object.assign(row, { state, calls: 0, phase: 'lint', why: lintView.why, next_step: lintView.next_step, ...extra });
    incompleteCriteria(row);
    if (!busy && outcome.state === 'unknown') context.lintUnknown = lint.unknown = true;
  }
  lint.public_result = resultOverall([...judged.values()]);
}

const runtimeLintRow = row => row.phase !== 'local' && !row.native_only?.length;
function heldForLint(row) {
  return runtimeLintRow(row) && !row.request_ids?.length && row.state === 'not_run' && !row.busy && !row.can_retry
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
  candidates = candidates.filter(row => runtimeLintRow(row) && !row.request_ids.length && !row.dispatchIncomplete);
  if (!candidates.length) return;
  if (saved.version !== 1 || (saved.intent !== undefined && saved.intent !== 'check')
    || !candidates.every(validSavedCallCeiling)
    || (saved.intent === undefined && !candidates.every(validSavedCheck))
    || candidates.some(row => Object.hasOwn(row, 'calls') && row.calls !== 0)) {
    context.continuationNotice = 'No checks were sent for the lint-held rows: the saved batch lacks valid original call ceilings, unambiguous Check intent or zero-call lint-held proof. Start a fresh selected pdd test.';
    return;
  }
  if (context.lintPending) return;
  const lintId = context.lint?.request_ids?.at(-1), lint = lintId && context.store.read(join(context.folder, `${lintId}.json`));
  let capture;
  try { capture = Array.isArray(context.capture.sources) ? context.capture : context.ports.captureSource(context.root, { tests: sentTests(saved.rows), appMap: null, excludeFixtureProjects: saved.exclude_fixture_projects === true }); }
  catch (error) {
    if (!(error instanceof PreflightError)) throw error;
    context.continuationNotice = `No checks were sent for the lint-held rows: the saved source cannot be verified. ${error.message}`;
    return;
  }
  if (capture.sha256 !== saved.source_sha256) { context.continuationNotice = 'No checks were sent for the lint-held rows: the saved source no longer matches: source changed. Start a fresh selected pdd test instead.'; return; }
  capture.stories = context.capture.stories;
  if (context.interrupted || context.ports.now() >= context.deadline) return;
  Object.assign(context, { capture });
  const admitted = sameJob(lint, lintId, 'lint') ? candidates.filter(row => lintAdmits(lint, row, capture)) : [];
  if (!admitted.length) return;
  const selected = admitted.filter(row => !row.request_ids.length && !row.dispatchIncomplete);
  if (selected.length) lintDiagnostics(context, lint, candidates);
  for (const row of selected) Object.assign(row, { state: 'ready', eligible: true, note: null });
  return selected;
}

function isLocalSavedBatchRead(context, saved) {
  if (!isObject(saved) || !Array.isArray(saved.rows)) return false;
  const lintId = saved.lint?.request_ids?.at(-1);
  if (lintId) {
    const lintAnswer = context.store.read(join(context.folder, `${lintId}.json`));
    if (!(sameJob(lintAnswer, lintId, 'lint') && ['passed', 'failed', 'refused'].includes(lintAnswer.state))) return false;
  }
  for (const rawRow of saved.rows) {
    const row = { ...rawRow, request_ids: [...(rawRow?.request_ids ?? [])] };
    if (heldForLint(row)) return false;
    const id = row.request_ids.at(-1);
    if (!id) continue;
    const admission = context.store.read(join(context.folder, `${id}.admission.json`));
    if (admissionCapacityCandidate(admission)) return false;
    const answer = context.store.read(join(context.folder, `${id}.json`));
    if (answer && confirmedEnd(answer) && sameJob(answer, id, 'check')) {
      if (!context.singleAttempt && (saved.intent === undefined || saved.intent === 'check') && !row.restart_used && !row.restart_pending && restarted(answer)) return false;
      continue;
    }
    const isFinalPost = !answer && (['refused', 'not_run', 'stop'].includes(row.post_verdict)
      || (!row.post_verdict && (row.state === 'refused' || (row.state === 'not_run' && !row.busy && !row.can_retry))));
    if (!isFinalPost) return false;
  }
  return true;
}

async function runRead(context, batchWord, quiet = false, options = {}) {
  context.cacheReadInvocation = true;
  const { store, ports, root } = context;
  const progress = context.checkProgress ??= { startedAt: ports.now(), shownAt: ports.now() };
  const timeout = options['--timeout'] === undefined ? quiet ? AGENT_WAIT_MIN : null : Number(options['--timeout']);
  context.deadline ??= timeout === null ? Infinity : ports.now() + timeout * 60_000;
  context.timeoutMin = timeout; context.agentLimit = false;
  const name = batchWord ?? store.read(join(store.dir,'repos',`${store.repoKey(root)}.json`))?.last_batch;
  if (!name || !BATCH.test(name)) throw new Stop(2, name ? 'BATCH looks like 20261027-092747-k3f9.' : 'No saved check for this repository. Run pdd test first.');
  context.folder = join(store.dir, 'batches', name);
  if (!statOrNull(join(context.folder, 'batch.json'))) throw new Stop(2, `No saved batch ${name}.`);
  const local = localLayoutResult(store.read(join(context.folder,'batch.json')),store.read(join(context.folder,'summary.json')));
  if (local) {
    if (local.repo !== root) throw new Stop(2,'This saved batch belongs to a different repository.');
    context.localLayout = local;
    if (quiet) return local.rows;
    return printLocalLayout(context,local);
  }
  await ownBatch(context, name);
  const saved = store.read(join(context.folder, 'batch.json'));
  if (!saved) throw new Stop(2, `No saved batch ${name}.`);
  for (const row of [...saved.rows, ...(saved.lint ? [saved.lint] : [])]) {
    if (row.recovery_state !== undefined) { row.state = row.recovery_state; delete row.reason; }
  }
  if (saved.root !== root) throw new Stop(2, 'This saved batch belongs to a different repository.');
  context.checkPlan = saved.check_plan ?? null;
  context.checkSelection = saved.check_selection; context.baselineReport = saved.baseline_report;
  if (saved.local_only === true && saved.rows.length && saved.rows.every(row => row.unsent && ['refused','not_run'].includes(row.state) && !row.request_ids?.length)) {
    Object.assign(context,{localOnly:true,batch:name,intent:saved.intent,coverage:saved.coverage,rows:saved.rows,warnings:saved.warnings ?? [],
      capture:{sha256:saved.source_sha256},startedAt:Date.parse(saved.created_at),lint:saved.lint});
    if (quiet) return saved.rows;
    return saved.intent === 'lint-only' ? printLintResult(context,saved.rows,saved.lint?.problems ?? []) : printResult(context,saved.rows);
  }
  if(loadRuntimeWorkspace({root}).configured)ports.captureSource(root,{tests:saved.rows.filter(row=>!row.unsent).map(row=>row.test),appMap:null,excludeFixtureProjects:saved.exclude_fixture_projects === true,...(saved.lazy_interfaces === true ? {allowMissingInterfaces:true} : {})});
  const identity = signIn(ports.gh, context.store, ports, {
    allowSavedLocalReadFallback: !quiet && isLocalSavedBatchRead(context, saved),
  });
  if (identity.login !== saved.login) throw new Stop(5, `These runs belong to ${saved.login}. Run: gh auth switch -u ${saved.login}`);
  Object.assign(context, { singleAttempt: context.singleAttempt || saved.single_attempt === true, allowMissingInterfaces: saved.lazy_interfaces === true, excludeFixtureProjects: saved.exclude_fixture_projects === true, batch: name, origin: saved.origin, sourceSelection:saved.source_selection, nativeSource:saved.native_source, coverage: saved.coverage, identity, intent: saved.intent, secrets: [identity.token], warnings: saved.warnings ?? [],
    capture: { sha256: saved.source_sha256, files: saved.files.map(path => ({ path })), bytes: saved.bytes, stories:saved.contract_snapshots }, lint: saved.lint, head: saved.head, startedAt: Date.parse(saved.created_at) });
  runtimeOrigin({ PDD_RUNTIME_URL: saved.origin });
  context.auth = authSession({
    identity,
    store: context.store,
    ports,
    secrets: context.secrets,
    expectedOwnerLogin: saved.login,
    ownerMismatchError: owner => new Stop(5, `These runs belong to ${owner}. Run: gh auth switch -u ${owner}`),
  });
  context.runtime = new Runtime({ origin: saved.origin, token: identity.token, ports, signal: context.signal, auth: context.auth });
  const rows = saved.rows.map(row => ({ ...row, why: ['refused', 'not_run', 'unknown'].includes(row.state) && row.why === 'Checks failed.' ? null : row.why, ...(row.request_ids?.length ? { calls: 'unknown' } : {}), request_ids: [...(row.request_ids ?? [])], checks: row.cached ? row.checks : null, failed_checks: [], all_checks: [] }));
  const candidates = rows.filter(row => heldForLint(row));
  // Preserve the producer's original evidence before refresh can normalize unsent usage.
  const evidence = candidates.map(row => ({ row, hadCalls: Object.hasOwn(row, 'calls'), calls: row.calls }));
  for (const row of rows) adoptClaims(context, row);
  Object.assign(context, { rows, visible: ports.findTests({ root, excludeFixtureProjects: context.excludeFixtureProjects }).visible, reading: true });
  const cache = context.cacheEnabled ? await openTestCache(context, root, false) : null;
  context.testCache = cache; context.savedTestCache = saved.test_cache;
  if (cache && !cache.disabled) {
    cache.tokens = new Map(Array.isArray(saved.test_cache?.tokens) ? saved.test_cache.tokens : []);
    // Reads may continue lint-held checks or resend restarted jobs below.
    await cacheTransaction(cache, data => markTestAttempt(cache, data));
  }
  // A pdd that was killed can leave rows that never got an answer: read them if they were posted.
  for (const row of rows) if (['ready', 'sending', 'waiting'].includes(row.state)) {
    if (row.request_ids.length) row.state = 'unknown';
    else Object.assign(row, { state: 'not_run', calls: 0, phase: 'local', busy: !row.dispatchIncomplete, can_retry: !row.dispatchIncomplete,
      note: { code: null, message: 'pdd stopped before sending this check.' } });
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
  await eachLimited(rows, MAX_READS, async row => {
    const id = row.request_ids.at(-1);
    if (!id) return;
    row.phase = 'server';
    const admission = store.read(join(context.folder, `${id}.admission.json`));
    if (admissionCapacityCandidate(admission)) {
      const wait = capacityDelay(admission.error);
      if (wait !== null && accountingProof(admission) && capacityRetryAllowed(context, row)) { markBusy(context, row, wait); return; }
      markCapacityUnknown(context, row);
    }
    const answer = store.read(join(context.folder, `${id}.json`));
    // Local terminal receipts remain available even when another row used the network wait.
    if (answer && confirmedEnd(answer) && sameJob(answer, id, 'check')) {
      await finishReservation(context, row, answer); applyAnswer(row, answer, context);
      if (!row.capacity_uncertain) return;
    }
    if (finalPost(row, answer)) return;
    if (row.final && (ports.now() >= (context.deadline ?? Infinity) || context.interrupted)) return;
    // A verified open receipt stays open when another row consumed this wait.
    if ((ports.now() >= (context.deadline ?? Infinity) || context.interrupted)
      && answer && sameJob(answer, id, 'check') && ['queued', 'running'].includes(answer.state)) { applyAnswer(row, answer, context); return; }
    // Polling an open cache is not evidence that its saved advice came from a lost read.
    if (!row.capacity_uncertain && !row.lost && (row.state !== 'unknown' || row.lost === false)) row.why = null;
    Object.assign(row, { state: 'unknown', calls: 'unknown', checks: null, criteria: null, failed_checks: [], all_checks: [], busy: false, can_retry: false, note: null, lost: true,
      progress: undefined, ahead: undefined,
      read_until: Number.isFinite(context.deadline) ? context.deadline : ports.now() + LOST_READ_MS });
    if (row.capacity_uncertain) { row.why = capacityUnknownReason; row.next_step = sameIdReadAdvice(context, row); }
    if (ports.now() >= (context.deadline ?? Infinity) || context.interrupted) return;
    if (!quiet) line(ports.stderr, 'Reading 1 result from the PDD interpreter…');
    await readRow(context, row, context.deadline);
    if (row.state === 'unknown' && row.lost) row.why ??= 'pdd could not read this run yet.';
  });
  while (context.lintPending && !context.interrupted && !context.readStop && ports.now() < context.deadline) {
    if (ports.now() - progress.shownAt >= PROGRESS_MS) {
      progress.shownAt = ports.now();
      line(ports.stderr, progressLine(rows, progress.shownAt - progress.startedAt));
    }
    await ports.sleep(Math.max(0, Math.min(ports.pollMs, context.deadline - ports.now())), context.signal);
    if (context.interrupted || ports.now() >= context.deadline) break;
    await readUnsentLint(context, rows);
    await eachLimited(rows.filter(isOpen), MAX_READS, row => readRow(context, row));
    saveBatch(context);
  }
  const continued = await continueHeld(context, candidates, saved) ?? [];
  const replacements = await recoverRestarts(context);
  if (continued.length || replacements.length || !quiet && rows.some(isOpen)) {
    if (continued.length) context.reading = false;
    await runScheduledChecks(context, rows, [...continued, ...replacements]);
  }
  context.savedTestCache = saved.test_cache;
  saveBatch(context);
  return quiet ? rows : () => printResult(context, rows);
}

async function recoverRestarts(context) {
  if (context.singleAttempt || context.intent !== undefined && context.intent !== 'check') return [];
  const eligible = context.rows.filter(row => {
    adoptClaims(context, row);
    const id = row.request_ids.at(-1), answer = id && context.store.read(join(context.folder, `${id}.json`));
    return !row.restart_used && !row.restart_pending && !row.admitting && !context.restartDecisions?.has(id) && sameJob(answer, id, 'check') && restarted(answer);
  });
  if (!eligible.length || context.interrupted || context.ports.now() >= context.deadline) return [];
  const lintId = context.lint?.request_ids?.at(-1), lint = lintId && context.store.read(join(context.folder, `${lintId}.json`));
  if (!recoverSourceContext(context)) {
    context.continuationNotice = 'The saved source changed or cannot be verified; no restarted check was sent again.';
    return [];
  }
  const admitted = sameJob(lint, lintId, 'lint') ? eligible.filter(row => lintAdmits(lint, row, context.capture)) : [];
  if (admitted.length < eligible.length) context.continuationNotice = `The interpreter restarted ${eligible.length - admitted.length === 1 ? 'a check' : `${eligible.length - admitted.length} checks`}, `
    + 'but the saved lint gives no pass of its own to that test, so pdd did not send it again. Start a fresh pdd test.';
  if (!admitted.length) return [];
  context.restartDecisions ??= new Set();
  for (const row of admitted) context.restartDecisions.add(row.request_ids.at(-1));
  const capture = context.recoveredSourceCapture ?? context.ports.captureSource(context.root, { tests: sentTests(context.rows), appMap: null, excludeFixtureProjects: context.excludeFixtureProjects });
  if (capture.sha256 !== context.capture.sha256) { context.continuationNotice = 'The saved source changed; no restarted check was sent again.'; return []; }
  capture.stories = context.capture.stories;
  context.capture = capture;
  lintDiagnostics(context, lint, context.rows);
  const selected = [];
  for (const row of admitted) {
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
  if (context.localLayout) {
    line(ports.stderr,'For new evidence, run a fresh pdd lint --local.');
    return () => printLocalLayout(context,context.localLayout);
  }
  if (context.intent !== undefined && context.intent !== 'check') throw new Stop(2, 'The saved batch has no Check intent. Start a fresh selected pdd test.');
  if (context.localOnly) return () => printResult(context, rows);
  if (context.interrupted || ports.now() >= context.deadline) return () => printResult(context, rows);
  const capture = Array.isArray(context.capture.sources) ? context.capture : context.ports.captureSource(context.root, { tests: sentTests(rows), appMap: null, excludeFixtureProjects: context.excludeFixtureProjects });
  if (capture.sha256 !== context.capture.sha256) throw new Stop(2, 'The saved source no longer matches: source changed. Start a fresh selected pdd test instead.');
  capture.stories = context.capture.stories;
  context.capture = capture;
  const lintId = context.lint?.request_ids?.at(-1), lint = lintId && context.store.read(join(context.folder, `${lintId}.json`));
  if (!lint || !sameJob(lint, lintId, 'lint') || context.lint.pending)
    throw new Stop(2, 'The saved lint cannot authorize recovery. Start a fresh selected pdd test.');
  const retryable = rows.filter(row => row.can_retry && row.eligible && (row.busy || !row.request_ids.length));
  const selected = retryable.filter(row => lintAdmits(lint, row, context.capture));
  if (retryable.length && !selected.length) throw new Stop(2, 'The saved lint cannot authorize recovery. Start a fresh selected pdd test.');
  if (selected.length) lintDiagnostics(context, lint, rows);
  Object.assign(context, { capture, reading: false, timeoutMin: timeout });
  for (const row of selected) row.state = row.retry_at > ports.now() ? 'waiting' : 'ready';
  if (selected.length) line(ports.stderr, `Retrying ${selected.length} unstarted check${selected.length === 1 ? '' : 's'}…`);
  await runScheduledChecks(context, rows, selected);
  saveBatch(context);
  return () => printResult(context, rows);
}

async function runRequest(context, id, cwd) {
  try { context.root=repoRoot(cwd); context.store=stateFor(context.ports.env,context.root); }
  catch (error) {
    if (error instanceof Stop && error.exitCode === 2 && error.message.includes('PDD_STATE_DIR')) throw error;
    /* An outside-repository request read has no owning local batch, but still uses PDD_STATE_DIR for github-user.json. */
    context.store = new StateStore(resolve(context.ports.env.PDD_STATE_DIR || join(context.ports.env.HOME || homedir(), '.pdd', 'runtime')));
  }
  if (!UUID.test(id)) throw new Stop(2, 'The request ID must be a UUID.');
  const { ports } = context, identity = signIn(ports.gh, context.store, ports), origin = runtimeOrigin(ports.env);
  Object.assign(context, { origin, identity, secrets: [identity.token] });
  context.auth = authSession({ identity, store: context.store, ports, secrets: context.secrets });
  const runtime = new Runtime({ origin, token: identity.token, ports, signal: context.signal, auth: context.auth });
  const row = { test: '-', story: '-', title: '-', phase: 'server', request_ids: [id], state: 'unknown', refusals: [], warnings: [] };
  const read = judgeGet(await runtime.get(id), id, 'check');
  if (read.kind === 'state') {
    const owner=owningCheckBatch(context,identity,origin,id);
    if(owner?.not_checked?.length) Object.assign(row,{not_checked:owner.not_checked,criteria_total:owner.criteria_total,criterion_texts:owner.criterion_texts,steps:owner.steps});
    applyAnswer(row, read.answer, context);
  }
  else {
    row.why = read.unreachable ?? read.why ?? (read.kind === 'auth' ? AUTH_TEXT : 'pdd could not read this run.');
    if (read.kind === 'auth') context.readStop = AUTH_TEXT;
  }
  return printResult(context, [row], { recovery: `pdd test --request '${id}'` });
}

// A read-only lookup for the hidden request route. Never refresh receipts or caches here.
function owningCheckBatch({root,store},identity,origin,id) {
  if(!root || !store)return null;
  const batches=join(store.dir,'batches');let names;
  try {names=readdirSync(batches);}catch{return null;}
  for(const name of names.filter(name=>BATCH.test(name)).sort().reverse()) {
    const saved=store.read(join(batches,name,'batch.json'));
    if(saved?.batch!==name || saved.root!==root || saved.origin!==origin || saved.login!==identity.login || String(saved.user_id)!==String(identity.userId) || !Array.isArray(saved.rows))continue;
    const row=saved.rows.find(row=>Array.isArray(row?.request_ids)&&row.request_ids.includes(id));
    if(row)return row;
  }
  return null;
}

// Refresh only caches owned by this exact repository, runtime and signed-in account.
async function refreshCheckBatches(context, identity, origin, id, answer) {
  const { store, root } = context, batches = join(store.dir, 'batches');
  let names, owner = null;
  try { names = readdirSync(batches); } catch { return; }
  for (const name of names.filter(name => BATCH.test(name))) {
    try {
      const folder = join(batches, name), saved = store.read(join(folder, 'batch.json'));
      if (!saved || saved.root !== root || saved.origin !== origin || saved.login !== identity.login
        || String(saved.user_id) !== String(identity.userId)) continue;
      const matchingRow = saved.rows?.find(row => row.request_ids?.includes(id));
      if (!matchingRow) continue;
      owner ??= { batch: name, folder, row: matchingRow };
      const cached = store.read(join(folder, `${id}.json`));
      if (sameJob(cached, id, 'check') && ['passed', 'failed', 'refused'].includes(cached.state)
        && !['passed', 'failed', 'refused'].includes(answer.state)) continue;
      saveAnswerAt(store, folder, id, answer);
      if (context.cacheEnabled && saved.version === 1 && saved.intent === 'check'
        && Array.isArray(saved.test_cache?.tokens) && saved.rows.some(row => row.request_ids?.at(-1) === id)) {
        const capture = context.ports.captureSource(root, { tests: sentTests(saved.rows), appMap: null, excludeFixtureProjects: saved.exclude_fixture_projects === true });
        if (capture.sha256 !== saved.source_sha256) continue;
        // Project receipts privately: UUID reads never rewrite saved batch/summary views.
        const projection = { ...context, cacheReadInvocation: true, startedAt: Date.parse(saved.created_at), reading: true, visible: context.ports.findTests({ root, excludeFixtureProjects: saved.exclude_fixture_projects === true }).visible, warnings: [] };
        const rows = saved.rows.map(savedRow => {
          const row = { ...savedRow, state: 'unknown', calls: 'unknown', request_ids: [...(savedRow.request_ids ?? [])], checks: null };
          const latest = row.request_ids.at(-1), receipt = latest && store.read(join(folder, `${latest}.json`));
          if (sameJob(receipt, latest, 'check')) applyAnswer(row, receipt, projection);
          return row;
        });
        const cache = await openTestCache(projection, root, false);
        cache.tokens = new Map(saved.test_cache.tokens);
        await finishTestAttempts(cache, rows, capture);
        for (const warning of projection.warnings) if (!context.warnings.includes(warning)) context.warnings.push(warning);
      }
    } catch (error) { if (error?.unboundPort) throw error; /* A cache failure must not hide an authoritative read or other caches. */ }
  }
  return owner;
}

// A read is observation only; it does not replay the call or settle backend accounting.
async function runCallRead(context, id) {
  const { ports, store } = context;
  const saved = store.read(join(store.dir, 'calls', `${id}.meta.json`));
  const identity = signIn(ports.gh, store, ports);
  if (saved && identity.login !== saved.login) throw new Stop(5, `These runs belong to ${saved.login}. Run: gh auth switch -u ${saved.login}`);
  const origin = runtimeOrigin(saved ? { PDD_RUNTIME_URL: saved.origin } : ports.env);
  const secrets = [identity.token];
  const auth = authSession({
    identity,
    store,
    ports,
    secrets,
    expectedOwnerLogin: saved?.login ?? null,
    ownerMismatchError: owner => new Stop(5, `These runs belong to ${owner}. Run: gh auth switch -u ${owner}`),
  });
  const runtime = new Runtime({ origin, token: identity.token, ports, signal: context.signal, auth });
  const reply = await runtime.get(id), blocked = blockingAnswer(reply);
  if (blocked) throw new Stop(5, blocked);
  const command = ['call', 'check'].includes(reply.json?.command) ? reply.json.command : null;
  const verified = [200, 202].includes(reply.status) && command && sameJob(reply.json, id, command)
    && !(saved?.session_id && reply.json.session_id && saved.session_id !== reply.json.session_id);
  const answer = verified && !(command === 'call' && reply.json.state === 'passed' && !isObject(reply.json.result?.program_result)) ? reply.json : null;
  if (answer?.command === 'check') {
    Object.assign(context, { origin, secrets });
    const row = { test: '-', story: '-', title: '-', phase: 'server', request_ids: [id], state: 'unknown', refusals: [], warnings: [] };
    const owner = await refreshCheckBatches(context, identity, origin, id, answer);
    if (owner?.row.not_checked?.length) Object.assign(row, {not_checked:owner.row.not_checked,criteria_total:owner.row.criteria_total,
      criterion_texts:owner.row.criterion_texts,steps:owner.row.steps});
    // Use the owning batch only to build the direct row's aggregate projection.
    // UUID reads must not turn a one-row view into a saved batch or summary write.
    applyAnswer(row, answer, owner ? { ...context, batch: owner.batch, folder: owner.folder } : context);
    return printResult(context, [row], { recovery: `pdd test --read ${id}` });
  }
  const state = answer?.state ?? 'unknown', exitCode = ports.exitCodeFor([{ state }]);
  const sanitize = value => typeof value === 'string' ? secrets.reduce((text, secret) => secret ? text.split(secret).join('[secret]') : text, value).replace(/\x1b\[[0-9;?]*[ -/]*[@-~]/g, '').replace(/[\x00-\x08\x0b\x0c\x0e-\x1f\x7f-\x9f]/g, '').replace(/\b(?:gh[pousr]_[A-Za-z0-9_]+|github_pat_[A-Za-z0-9_]+|sk-[A-Za-z0-9_-]{12,})\b/g, '[secret]')
    : Array.isArray(value) ? value.map(sanitize) : isObject(value) ? Object.fromEntries(Object.entries(value).map(([k, v]) => [sanitize(k), sanitize(v)])) : value;
  const out = sanitize({ request_id: id, command: 'call', state, exit_code: exitCode,
    calls: answer?.usage?.calls ?? 'unknown', usage: answer?.usage ?? null,
    program_result: answer?.result?.program_result ?? null, result: answer?.result ?? null,
    report_url: answer?.report_url ? validLink(answer.report_url, origin, 'report') : null,
    why: answer ? answer.why ?? null : reply.status === 401 ? AUTH_TEXT : reply.status === 410 ? 'The result expired.' : 'The call receipt could not be verified.' });
  if (answer) store.write(join(store.folder('calls'), `${id}.json`), answer);
  if (!answer && reply.status === 401) line(ports.stderr, AUTH_TEXT);
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

// All check POSTs use this one run-owned boundary, including sends after a read.
// Its lifetime covers scheduler waits, recovery and every phase of a retry.
async function withCheckRun(context, run) {
  let ownership;
  context.postCheck = async (request, row, timeoutMs) => {
    ownership ??= (async () => {
      if (!context.testCache) {
        const cache = context.testCache = await openTestCache(context, context.root, false);
        if (Array.isArray(context.savedTestCache?.tokens)) cache.tokens = new Map(context.savedTestCache.tokens);
        else await beginTestAttempts(cache, context.rows, null, {}, context.origin, true);
      }
      const cache = context.testCache;
      if (!cache.disabled && !cache.mark) await cacheTransaction(cache, data => markTestAttempt(cache, data));
    })();
    await ownership;
    return postJob(context, '/v1/check', 'check', request, row, timeoutMs, context.deadline);
  };
  let result;
  try { result = await run(); }
  catch (error) { context.checkRunFailed = true; throw error; }
  finally {
    const cache = context.testCache;
    if (cache && context.capture && context.rows) await finishTestAttempts(cache, context.rows, context.capture);
  }
  // Keep warnings and cache completion ahead of the final result rendering.
  return typeof result === 'function' ? result() : result;
}

// pdd test. Returns the exit code.
export async function runCheck({ words = [], options = {}, cwd = process.cwd(), cache = false, client, workflow } = {}, givenPorts = {}) {
  const ports = withDefaults(givenPorts);
  const context = { ports, clientVersion: client?.version ?? ports.clientVersion ?? null, workflow, singleAttempt: ports.env.PDD_CHECK_SINGLE_ATTEMPT === '1', cacheEnabled: cache || !!options['--lf'] || !!options['--cache-clear'], json: options['--json'] === true, details: options['--details'] === true, explicitTimeout: options['--timeout'] !== undefined, interrupted: false, warnings: [] };
  let release = () => {};
  try {
    if (options['--affected'] !== undefined && (options['--affected'] !== true || words.length || Object.keys(options).some(key => !['--affected','--json','--details','--timeout','--max-calls','--cache-clear'].includes(key))))
      throw new Stop(2, '--affected accepts no Stories and only --cache-clear, --json, --details, --timeout and --max-calls.');
    if(options['--journeys']!==undefined){
      if(options['--journeys']!==true||words.length>1||['--read','--retry','--fill-hash','--request','--screen','--drawing','--look'].some(key=>options[key]!==undefined))throw new Stop(2,'Use pdd test --journeys [JOURNEY] with normal test options.');
      const {root,found}=localSetup(cwd,[],ports);
      try { words=selectJourneys(found.tests.map(test=>({testPath:test.path,storyPath:test.storyPath})),words[0],ports); } catch(error) { if (error?.unboundPort) throw error; throw new Stop(2,error.message); }
      if(!words.length)throw new Stop(2,'No root product journeys found.');
      options={...options};delete options['--journeys'];
    }
    requestedCalls(options['--max-calls']);
    if (options['--local'] !== undefined && options['--max-calls'] !== undefined) throw new Stop(2, '--local does not accept --max-calls.');
    if (options['--lint'] === true && words.length && (options['--local'] === undefined || options['--local'] === true && !Object.hasOwn(options, '--timeout')) && Object.keys(options).every(key => ['--lint','--local','--json','--timeout'].includes(key))) {
      const {root,found,normalized} = localSetup(cwd,words,ports);
      const selection = ports.selectTests(found,normalized,{native:true});
      if (selection.nativeSelections?.length) {
        if(selection.untested.length)throw new Stop(2,selection.untested.join('\n'));
        if(selection.unknown.length)throw new Stop(2,[`Unknown story ${selection.unknown.map(word=>JSON.stringify(cleanText(word))).join(', ')}. Stories:`,...storyList(found,ports)].join('\n'));
        if (typeof ports.allRuns !== 'function' || typeof ports.assessNativeEvidence !== 'function' || typeof ports.usableResult !== 'function' || (!context.json && typeof ports.resultLines !== 'function')) {
          throw unboundPortError('Native Story assessment ports (allRuns, assessNativeEvidence, usableResult, resultLines) are not bound.');
        }
        const runs = ports.allRuns({cancelled:true},{env:ports.env}).filter(run => {
          try { return realpathSync(run.root) === realpathSync(root); } catch { return false; }
        });
        const eligibilityPort = ports.evidenceEligibility ?? ports.readEvidenceEligibility ?? (() => ({state:'unavailable',reason:'workflow evidence eligibility port is not bound'}));
        const native = [];
        for (const descriptor of selection.nativeSelections) {
          const owners = runs.filter(run => (run.evidence ?? []).some(entry => entry.native?.profileId === descriptor.profileId && entry.native?.storyPath === descriptor.storyPath));
          const run = owners.length === 1 ? owners[0] : null;
          const assessment = await ports.assessNativeEvidence({root,runDir:run?.runDir ?? null,runId:run?.runId ?? null,profileId:descriptor.profileId,storyPath:descriptor.storyPath},
            {workspace:input=>eligibilityPort(input,{env:ports.env})});
          if (descriptor.reason || owners.length !== 1) {
            assessment.profileNativeProof = assessment.storyNativeProof = 'none';
            assessment.limits.push(descriptor.reason ?? (owners.length ? 'Native evidence run association is ambiguous.' : 'No owned native evidence run/profile association.'));
          }
          native.push({...descriptor,assessment});
        }
        const missing = native.some(row=>!ports.usableResult({kind:'native evidence',assessment:row.assessment}));
        let exitCode = missing ? 1 : 0;
        const runtimeWords = selection.selected.map(test=>test.path);
        if (context.json) {
          let output = '';
          if (runtimeWords.length) exitCode = await runCheck({words:runtimeWords,options,cwd,cache,client,workflow},{...givenPorts,stdout:{write:chunk=>{output+=chunk;}}});
          if (exitCode === 0 && missing) exitCode = 1;
          let report = {};
          if (output.trim()) { try { report = JSON.parse(output); } catch { line(ports.stdout,output.trim()); } }
          line(ports.stdout,JSON.stringify({...report,repo:root,exit_code:exitCode,native_assessments:native,...(!runtimeWords.length?{rows:[],summary_line:'Native evidence assessment. 0 AI calls. No checks were sent.'}:{})}));
        } else {
          for (const row of native) {
            line(ports.stdout,`Native Story: ${row.storyPath}; profile ${row.profileId ?? 'unknown'}; owner ${row.promptPath ?? 'unknown'}`);
            for (const criterion of row.assessment.criteria) line(ports.stdout,`${criterion.id}: ${criterion.text}`);
            for (const value of ports.resultLines([{kind:'native evidence',assessment:row.assessment,source:row.assessment.sourceState,stage:row.assessment.identity.stage}])) line(ports.stdout,value);
          }
          if (runtimeWords.length) exitCode = await runCheck({words:runtimeWords,options,cwd,cache,client,workflow},givenPorts);
          if (exitCode === 0 && missing) exitCode = 1;
        }
        return exitCode;
      }
    }
    if (Object.hasOwn(options, '--compact') && (options['--compact'] !== true || options['--fill-hash'] !== true || words.length
      || Object.keys(options).some(name => !['--fill-hash', '--compact'].includes(name)))) throw new Stop(2, '--compact requires --fill-hash, without other options or Stories.');
    // Local modes dispatch before repository runtime state, origin or sign-in.
    if (options['--screen'] !== undefined || options['--drawing'] !== undefined || options['--look'] !== undefined) {
      if (!options['--screen'] || !options['--drawing'] || words.length || Object.keys(options).some(name => !['--screen', '--drawing', '--look', '--json'].includes(name))) throw new Stop(2, 'Use pdd test --screen URL --drawing PATH [--look] [--json], without other options or Stories.');
      if (typeof ports.compareScreen !== 'function' || (!context.json && typeof ports.formatScreenComparison !== 'function')) {
        throw unboundPortError('Screen comparison ports (compareScreen, formatScreenComparison) are not bound.');
      }
      try {
        const report = await ports.compareScreen({ url: options['--screen'], drawingPath: options['--drawing'], cwd, chromePath: ports.env.PDD_CHROME_PATH, look: options['--look'] === true }, { env: ports.env, browser: givenPorts.screenBrowser });
        const exitCode = report.passed ? 0 : 1;
        line(ports.stdout, context.json ? JSON.stringify({ ...report, exit_code: exitCode }) : ports.formatScreenComparison(report));
        return exitCode;
      } catch (error) {
        if (error.code === 'screen-not-ready' && error.exitCode === 6) {
          const result = { drawing: resolve(cwd, options['--drawing']), url: new URL(options['--screen']).href, outcome: 'not-ready', code: error.code, state: error.state, reason: error.reason, message: error.message, exit_code: 6 };
          line(ports.stdout, context.json ? JSON.stringify(result) : `Screen not ready (${result.state}; ${result.reason}): ${result.message}`);
          return 6;
        }
        throw new Stop(error.exitCode === 2 ? 2 : 5, `Screen comparison: ${causeText(error.message) || 'browser execution failed'}`);
      }
    }
    if (options['--local'] !== undefined) {
      if (options['--local'] !== true || options['--lint'] !== true || Object.keys(options).some(name => !['--lint', '--local', '--json'].includes(name))) throw new Stop(2, '--local requires --lint and accepts only Story words and --json.');
      if (typeof ports.lintSvgLayouts !== 'function') throw unboundPortError('SVG layout port (lintSvgLayouts) is not bound.');
      try {
        const root = repoRoot(cwd), workspace=loadRuntimeWorkspace({root}), files = gitFiles(root).filter(path=>allowsRuntimePath(workspace,path));
        const { found, normalized } = localSetup(cwd, words, ports);
        const selectedTests = words.length ? select(found, normalized, root, ports) : found.tests;
        const tests = words.length ? selectedTests.map(test => test.path) : [];
        const promptSet = new Set(), captureProblems = [];
        if (words.length) {
          // Capture each scenario independently: one malformed source must not hide
          // findings in the remaining selected scenarios.
          for (const test of selectedTests) {
            for (const path of entryPaths([test])) if (typeof path === 'string' && path.endsWith('.prompt.md')) promptSet.add(path);
            if (test.error) continue;
            try {
              for (const file of ports.captureSource(root, { tests:[test.path], appMap:null }).files) {
                if (file.path.endsWith('.prompt.md')) promptSet.add(file.path);
              }
            } catch (error) {
              if (error?.exitCode !== 4) throw error;
              captureProblems.push({code:error.code ?? 'source-unavailable',path:test.path,message:error.message,section:'source'});
            }
          }
        } else for (const path of found.discoveryVisible ?? found.visible) if (path.endsWith('.prompt.md')) promptSet.add(path);
        const promptPaths = [...promptSet];
        if (!localLayoutPaths([...new Set(tests)].sort()) || !localLayoutPaths([...new Set(promptPaths)].sort())) {
          throw new Stop(2, 'Could not save local lint result in PDD_STATE_DIR: Local lint record cannot satisfy the saved result contract, including safe inspected scope.');
        }
        const problems = [...captureProblems, ...interfaceFindings({root,paths:promptPaths}).filter(localInterfaceProblem)];
        const prompts = new Map(), seen = new Set();
        const {promptSchemaRefusals} = await import('./runtime-preflight.mjs');
        for (const path of promptPaths) {
          if (!prompts.has(path)) prompts.set(path, readPrompt(root, found.visible, path, workspace));
          for (const problem of promptSchemaRefusals(root, found, prompts.get(path), prompts, seen, {lint:true})) problems.push(problem);
        }
        for (const row of preflight({root,found,selected:selectedTests,workspace,lint:true}).rows) {
          for (const problem of row.refusals) problems.push({...problem,path:problem.path ?? row.test});
        }
        // Saved v1 diagnostics have a deliberately small, stable shape.
        const unique = new Map();
        for (const item of problems) {
          const problem = {code:String(item.code),path:String(item.path ?? ''),message:String(item.message),...(typeof item.section === 'string' ? {section:item.section} : {})};
          unique.set(JSON.stringify(problem),problem);
        }
        const advice = formatAdvice(root, found.visible, promptPaths, workspace);
        const hygiene = lintLocalHygiene({ root, files, promptPaths, tests: selectedTests, workspace }, ports);
        const warnings = [...new Set([...advice, ...ports.lintSvgLayouts({ root, files, promptPaths }), ...hygiene])], summary = `partial: checked static admission and SVG layout (local-only). ${warnings.length} warnings. 0 AI calls. No checks were sent.`;
        const result = saveLocalLayout(context,{root,tests,prompts:promptPaths,warnings,problems:[...unique.values()],summary});
        return printLocalLayout(context,result);
      } catch (error) { if (error?.unboundPort) throw error; throw new Stop(error?.exitCode === 4 ? 4 : 2, error.message); }
    }
    const modes = ['--read', '--retry', '--fill-hash', '--files', '--explain-bindings', '--request', '--lint'].filter(name => options[name] !== undefined);
    const others = Object.keys(options).filter(name => !modes.includes(name) && !(modes[0] === '--fill-hash' && name === '--compact') && !(modes[0] === '--retry' && ['--json', '--details', '--timeout'].includes(name)) && !(name === '--json' && ['--read', '--request', '--lint', '--files', '--explain-bindings'].includes(modes[0])) && !(name === '--timeout' && ['--read', '--lint'].includes(modes[0])) && !(name === '--max-calls' && modes[0] === '--lint') && !(name === '--app-map' && modes[0] === '--files'));
    if (modes.length > 1 || (modes.length && others.length) || (['--request', '--retry'].includes(modes[0]) && words.length)
      || (modes[0] === '--read' && words.length > 1) || (!modes.length && options['--app-map'] !== undefined)) throw new Stop(2, 'This mix of options does not work together. Run pdd test --help.');
    if (modes[0] === '--request') { release = interruptible(context); return await runRequest(context, options['--request'], cwd); }
    const root = repoRoot(cwd);
    if (modes[0] === '--fill-hash') return runFillHash(root, cwd, words, ports, options['--compact'] === true);
    if (modes[0] === '--explain-bindings') return runExplainBindings(cwd, words, options, ports);
    if (modes[0] === '--files') return runFiles(cwd, words, options, ports);
    context.root = root; context.store = stateFor(ports.env, root);
    return await withCheckRun(context, async () => {
      if (modes[0] === '--retry') { release = interruptible(context); return await runRetry(context, options['--retry'], options); }
      if (modes[0] === '--read') { release = interruptible(context); return UUID.test(words[0] ?? '') ? await runCallRead(context, words[0]) : await runRead(context, words[0], false, options); }
      if (modes[0] === '--lint') return await runLintOnly(context, cwd, words, options, value => { release = value; });
      return await runBatch(context, cwd, words, options, value => { release = value; });
    });
  } catch (error) {
    if (error instanceof Stop || error instanceof PreflightError || error instanceof RuntimeWorkspaceError) {
      line(ports.stderr, error.message);
      if (options['--affected'] === true && error.exitCode !== 2) line(ports.stderr,AFFECTED_DISCLAIMER);
      if (context.rows?.some(row=>row.unsent || row.not_checked?.length)) {
        const rows = context.rows.map(row=>['ready','sending','waiting'].includes(row.state)
          ? {...row,state:'not_run',note:{code:null,message:error.message}} : row);
        const summary = {...renderJson({batch:context.batch??null,repo:context.root,rows,coverage:context.coverage,
          exitCode:error.exitCode,warnings:context.warnings},ports),...(context.checkSelection?{check_selection:context.checkSelection,baseline_report:context.baselineReport,check_plan:context.checkPlan,check_scope:selectedCheckScope(context.checkPlan,rows,context.checkSelection)}:{}),message:error.message,lint_state:error.exitCode===3?'unknown':'not_run'};
        if (context.folder) context.store.write(join(context.folder,'summary.json'),summary);
        if (context.json) line(ports.stdout,JSON.stringify(summary));
        else ports.stdout.write(renderText({batch:context.batch,rows,coverage:context.coverage,warnings:context.warnings,exitCode:error.exitCode,secrets:context.secrets},ports));
      } else if (context.json && error.bindingInventory) line(ports.stdout, JSON.stringify({ batch: null, repo: context.root, exit_code: 4, lint_state: 'refused',
        coverage: { available: false, bound: null, total: null, modules: [] }, problems: [{ code: 'binding-invalid', path: 'pdd-bindings.json', message: error.message }], rows: [], warnings: [] }));
      else if (context.coverage && error.exitCode !== 5) {
        if (context.json) line(ports.stdout, JSON.stringify({ batch: context.batch ?? null, repo: context.root, exit_code: error.exitCode,
          coverage: context.coverage, lint_state: error.exitCode === 3 ? 'partial' : 'not run', ...resultOutcome({ state: error.exitCode === 3 ? 'partial' : 'not run', note: { code: error.exitCode === 3 && context.timeoutMin ? 'timeout-flag' : 'no-server-verdict', message: error.message } }), problems: [], rows: [], warnings: context.warnings, message: error.message }));
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

// The filesystem port keeps cache decisions testable without native disk effects.
const nativeCacheFiles = {
  nonce: randomUUID, lstat: lstatSync, mkdir: mkdirSync, write: writeFileSync,
  read(path, encoding = 'utf8', limit = CACHE_LIMIT) {
    const fd = openSync(path, constants.O_RDONLY | constants.O_NOFOLLOW);
    try {
      const stat = fstatSync(fd);
      if (!stat.isFile() || stat.size > limit) throw new Error('unsafe or oversized cache file');
      const buffer = Buffer.alloc(limit + 1);
      let size = 0, count;
      while (size < buffer.length && (count = readSync(fd, buffer, size, buffer.length - size, null))) size += count;
      if (size > limit) throw new Error('oversized cache file');
      return buffer.subarray(0, size).toString('utf8');
    } finally { closeSync(fd); }
  },
  list: readdirSync, rename: renameSync, unlink: unlinkSync, rmdir: rmdirSync,
  tracked(root) {
    const result = spawnSync('git', ['ls-files', '--', '.pdd/cache/test'], { cwd: root, encoding: 'utf8' });
    if (result.status !== 0) throw new Error('Git tracking unavailable');
    return !!result.stdout.trim();
  },
  exclude(root) {
    const result = spawnSync('git', ['rev-parse', '--path-format=absolute', '--git-common-dir'], { cwd: root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
    if (result.status !== 0 || !result.stdout.trim()) throw new Error('Git exclude unavailable');
    return join(realpathSync(result.stdout.trim()), 'info', 'exclude');
  }
};
const CACHE_LIMIT = 2 * 1024 * 1024;
const freshTestCache = cache => ({ schema_version: 1, generation: 0, epoch: cache.fs.nonce(), stories: {} });
function cacheStat(fs, path) { try { return fs.lstat(path); } catch (error) { if (error.code === 'ENOENT') return null; throw error; } }
function safeCachePath(fs, path, { directory = false, create = false } = {}) {
  const absolute = resolve(path), parts = absolute.split(sep).filter(Boolean);
  let at = sep;
  for (let index = 0; index < parts.length; index++) {
    at = join(at, parts[index]);
    const isDir = index < parts.length - 1 || directory;
    let stat = cacheStat(fs, at);
    if (!stat && create && isDir) { fs.mkdir(at, { mode: 0o700 }); stat = fs.lstat(at); }
    if (!stat) { if (index < parts.length - 1) throw new Error('missing cache parent'); continue; }
    if (stat.isSymbolicLink() || (isDir ? !stat.isDirectory() : !stat.isFile())) throw new Error('unsafe cache path');
  }
  return absolute;
}
function validTestCache(value) {
  const keys = (value, allowed) => isObject(value) && Object.keys(value).every(key => allowed.includes(key));
  const path = text => typeof text === 'string' && text.length > 0 && text.length <= 4096 && !text.startsWith('/') && !text.split('/').some(part => !part || part === '.' || part === '..');
  const hash = text => typeof text === 'string' && /^[a-f0-9]{64}$/.test(text);
  const counts = value => value == null || keys(value, ['passed', 'total']) && ['passed', 'total'].every(key => Number.isSafeInteger(value[key]) && value[key] >= 0) && value.passed <= value.total;
  const evidence = row => keys(row, ['checks', 'criteria', 'criteria_total', 'draft']) && counts(row.checks) && counts(row.criteria)
    && (row.criteria_total === undefined || Number.isSafeInteger(row.criteria_total) && row.criteria_total >= 0) && typeof row.draft === 'boolean';
  if (!keys(value, ['schema_version', 'generation', 'epoch', 'stories', 'latest_identity']) || typeof value.epoch !== 'string' || !UUID.test(value.epoch) || value.schema_version !== 1 || !Number.isSafeInteger(value.generation) || value.generation < 0 || !isObject(value.stories) || Object.keys(value.stories).length > 10000) return false;
  const latest = value.latest_identity;
  if (latest !== undefined && (!keys(latest, ['engine_sha', 'models', 'observed_at', 'sampled_at', 'engine_shas', 'conflict', 'clean', 'written_at', 'in_progress'])
    || !(latest.engine_sha === null || typeof latest.engine_sha === 'string' && latest.engine_sha.trim() && latest.engine_sha.trim().toLowerCase() !== 'unknown')
    || (latest.in_progress !== undefined && (!Array.isArray(latest.in_progress) || latest.in_progress.length > 10000
      || !latest.in_progress.every(mark => keys(mark, ['token', 'pid', 'started_at']) && typeof mark.token === 'string' && UUID.test(mark.token)
        && Number.isSafeInteger(mark.pid) && mark.pid > 0 && Number.isFinite(mark.started_at))))
    || (latest.clean !== undefined && typeof latest.clean !== 'boolean')
    || (latest.written_at !== undefined && (typeof latest.written_at !== 'string' || !Number.isFinite(Date.parse(latest.written_at))))
    || (latest.conflict !== undefined && typeof latest.conflict !== 'boolean')
    || (latest.engine_shas !== undefined && (!Array.isArray(latest.engine_shas) || latest.engine_shas.length > 10000
      || !latest.engine_shas.every(sha => typeof sha === 'string' && sha.trim() && sha.trim().toLowerCase() !== 'unknown')))
    || !Array.isArray(latest.models) || latest.models.length > 10000 || !latest.models.every(model => typeof model === 'string' && model.trim() && model.trim().toLowerCase() !== 'unknown')
    || ![latest.observed_at, latest.sampled_at].every(at => typeof at === 'string' && Number.isFinite(Date.parse(at)) && new Date(at).toISOString() === at))) return false;
  return Object.entries(value.stories).every(([name, row]) => path(name) && keys(row, ['generation', 'outcome', 'pass']) && Number.isSafeInteger(row.generation) && row.generation >= 0 && row.generation <= value.generation
    && ['passed', 'failed', 'refused', 'not_run', 'unknown'].includes(row.outcome)
    && (row.pass === undefined || (row.outcome === 'passed' && keys(row.pass, ['fingerprint', 'passed_at', 'tests', 'rows', 'engine_sha', 'requested_model']) && hash(row.pass.fingerprint)
      && typeof row.pass.passed_at === 'string' && Number.isFinite(Date.parse(row.pass.passed_at)) && new Date(row.pass.passed_at).toISOString() === row.pass.passed_at
      && Array.isArray(row.pass.tests) && row.pass.tests.length > 0 && row.pass.tests.every(path) && new Set(row.pass.tests).size === row.pass.tests.length
      && keys(row.pass.rows, row.pass.tests) && Object.keys(row.pass.rows).length === row.pass.tests.length && row.pass.tests.every(test => evidence(row.pass.rows[test])))));
}
function cacheWarning(cache, recovered = false) {
  const message = 'Warning: test cache unavailable or damaged; running selected Stories without reuse. To reset, run pdd test --cache-clear.';
  if (!cache.warned) cache.warningIndex = cache.context.warnings.push(message) - 1;
  else if (cache.recoveredWarning) cache.context.warnings[cache.warningIndex] = message;
  cache.recoveredWarning = false;
  if (!recovered) {
    if (!cache.disabled) recordCacheInvalidation(cache);
    cache.disabled = true;
  }
  cache.warned = true;
}
function cacheRecoveryWarning(cache) {
  if (cache.warned) return;
  cache.warningIndex = cache.context.warnings.push('Warning: recovered stale cache lock or claim; previous passes may remain eligible.') - 1;
  cache.warned = true;
  cache.recoveredWarning = true;
}
// Immutable markers let recovery retire observed failures without erasing a later one.
function cacheInvalidations(cache) {
  safeCachePath(cache.fs, cache.markerDir, { directory: true, create: true });
  const names = cache.fs.list(cache.markerDir);
  if (names.length > 64) throw new Error('oversized cache recovery state');
  for (const name of names) {
    if (!name.endsWith('.json') || !UUID.test(name.slice(0, -5))) throw new Error('unsafe cache recovery entry');
    const path = join(cache.markerDir, name);
    safeCachePath(cache.fs, path);
    const stat = cacheStat(cache.fs, path);
    if (!stat || stat.size > 128) throw new Error('unsafe cache recovery state');
    const marker = JSON.parse(cache.fs.read(path, 'utf8', 128));
    if (!isObject(marker) || Object.keys(marker).length !== 2 || marker.schema_version !== 1 || marker.invalid !== true) throw new Error('invalid cache recovery state');
  }
  return names;
}
function recordCacheInvalidation(cache) {
  try {
    safeCachePath(cache.fs, cache.markerDir, { directory: true, create: true });
    if (cache.fs.list(cache.markerDir).length >= 64) return;
    const path = join(cache.markerDir, `${cache.fs.nonce()}.json`);
    cache.fs.write(path, '{"schema_version":1,"invalid":true}\n', { flag: 'wx', mode: 0o600 });
  } catch { /* Both local stores may be unavailable; checks still fail open. */ }
}
function readTestCacheBinding(cache) {
  safeCachePath(cache.fs, cache.bindingPath);
  const binding = JSON.parse(cache.fs.read(cache.bindingPath, 'utf8', 128));
  if (binding.schema_version !== 1 || !UUID.test(binding.epoch)) throw new Error('invalid local binding');
  return binding.epoch;
}
function readTestCache(cache) {
  safeCachePath(cache.fs, cache.path);
  const stat = cacheStat(cache.fs, cache.path);
  if (!stat) return { data: freshTestCache(cache), history: false };
  if (stat.size > CACHE_LIMIT) throw new Error('oversized cache');
  const data = JSON.parse(cache.fs.read(cache.path, 'utf8'));
  if (!validTestCache(data)) throw new Error('invalid cache');
  if (data.epoch !== cache.epoch) return { data: freshTestCache(cache), history: false };
  safeCachePath(cache.fs, cache.failedPath);
  const failedStat = cacheStat(cache.fs, cache.failedPath);
  if (!failedStat || failedStat.size > CACHE_LIMIT) throw new Error('missing or oversized last-failed metadata');
  const failed = JSON.parse(cache.fs.read(cache.failedPath, 'utf8'));
  const expected = Object.fromEntries(Object.entries(data.stories).filter(([, row]) => row.outcome === 'failed').map(([story]) => [story, true]));
  if (!isObject(failed) || Object.keys(failed).length !== 4 || failed.schema_version !== 1 || failed.epoch !== data.epoch
    || failed.generation !== data.generation || !isDeepStrictEqual(failed.stories, expected)) throw new Error('invalid last-failed metadata');
  return { data, history: true, failed: failed.stories };
}
function replaceCacheFile(cache, path, text) {
  safeCachePath(cache.fs, path);
  const temporary = `${path}.${cache.fs.nonce()}.tmp`;
  try {
    cache.fs.write(temporary, text, { flag: 'wx', mode: 0o600 });
    safeCachePath(cache.fs, path);
    cache.fs.rename(temporary, path);
  } finally { try { cache.fs.unlink(temporary); } catch {} }
}
// Bakery tickets serialize acquisition, stale recovery and release together. Each
// attempt owns a never-reused directory, so reclaiming a dead claim cannot erase
// a successor claim. Publishing the directory first announces ticket selection.
async function acquireCacheGuard(cache) {
  const fs = cache.fs, folder = join(cache.dir, 'transaction-claims');
  try { fs.mkdir(folder, { mode: 0o700 }); } catch (error) { if (error.code !== 'EEXIST') throw error; }
  safeCachePath(fs, folder, { directory: true });
  const name = `${process.pid}.${fs.nonce()}`, own = join(folder, name);
  fs.mkdir(own, { mode: 0o700 });
  const remove = path => {
    for (const file of fs.list(path)) {
      if (!['ticket.json', 'ticket.tmp'].includes(file)) throw new Error('invalid cache claim');
      const entry = join(path, file); safeCachePath(fs, entry);
      try { fs.unlink(entry); } catch (error) { if (error.code !== 'ENOENT') throw error; }
    }
    try { fs.rmdir(path); } catch (error) { if (error.code !== 'ENOENT') throw error; }
  };
  const peers = () => {
    const names = fs.list(folder);
    if (names.length > 64) throw new Error('too many cache claims');
    const result = [];
    for (const peer of names) {
      if (peer === name) continue;
      const match = /^([1-9][0-9]*)\.([a-f0-9-]+)$/.exec(peer);
      if (!match || !UUID.test(match[2]) || !Number.isSafeInteger(Number(match[1]))) throw new Error('invalid cache claim');
      const path = join(folder, peer);
      try {
        safeCachePath(fs, path, { directory: true });
        if (!cacheStat(fs, path)) continue;
        let dead = false;
        try { process.kill(Number(match[1]), 0); } catch (error) { if (error.code === 'ESRCH') dead = true; }
        if (dead) { remove(path); cacheRecoveryWarning(cache); continue; }
        const ticketPath = join(path, 'ticket.json');
        safeCachePath(fs, ticketPath);
        let ticket = null;
        if (cacheStat(fs, ticketPath)) {
          ticket = JSON.parse(fs.read(ticketPath, 'utf8', 128));
          if (!Number.isSafeInteger(ticket) || ticket < 1) throw new Error('invalid cache ticket');
        }
        result.push({ name: peer, ticket });
      } catch (error) { if (error.code !== 'ENOENT') throw error; }
    }
    return result;
  };
  try {
    const ticket = Math.max(0, ...peers().map(peer => peer.ticket ?? 0)) + 1;
    if (!Number.isSafeInteger(ticket)) throw new Error('cache ticket overflow');
    fs.write(join(own, 'ticket.tmp'), JSON.stringify(ticket), { flag: 'wx', mode: 0o600 });
    fs.rename(join(own, 'ticket.tmp'), join(own, 'ticket.json'));
    for (let attempt = 0; attempt < 30; attempt++) {
      if (!peers().some(peer => peer.ticket === null || peer.ticket < ticket || peer.ticket === ticket && peer.name < name)) return () => remove(own);
      await cache.context.ports.sleep(10);
    }
    throw new Error('busy cache claims');
  } catch (error) { try { remove(own); } catch {} throw error; }
}
async function cacheTransaction(cache, operation, clear = false) {
  if (cache.disabled) return null;
  let locked = false, releaseGuard, owner;
  try {
    safeCachePath(cache.fs, cache.dir, { directory: true });
    releaseGuard = await acquireCacheGuard(cache);
    for (let attempt = 0; attempt < 30; attempt++) {
      try {
        cache.fs.mkdir(cache.lock); locked = true;
        owner = { pid: process.pid, token: cache.fs.nonce() };
        cache.fs.write(join(cache.lock, 'owner.json'), JSON.stringify(owner), { flag: 'wx', mode: 0o600 });
        break;
      } catch (error) {
        if (locked || error.code !== 'EEXIST') throw error;
        safeCachePath(cache.fs, cache.lock, { directory: true });
        const ownerPath = join(cache.lock, 'owner.json');
        safeCachePath(cache.fs, ownerPath);
        const ownerStat = cacheStat(cache.fs, ownerPath);
        let stale = false, previous;
        if (ownerStat) {
          previous = JSON.parse(cache.fs.read(ownerPath, 'utf8', 128));
          if (!Number.isSafeInteger(previous.pid) || previous.pid <= 0) throw new Error('invalid cache owner');
          try { process.kill(previous.pid, 0); } catch (cause) { if (cause.code === 'ESRCH') stale = true; }
        } else stale = Date.now() - cache.fs.lstat(cache.lock).mtimeMs > 60_000;
        if (stale) {
          // The guard excludes other protocol participants. Reread also rejects
          // a successor installed by an older process before guard acquisition.
          if (ownerStat) {
            const current = JSON.parse(cache.fs.read(ownerPath, 'utf8', 128));
            if (!isDeepStrictEqual(previous, current)) continue;
            cache.fs.unlink(ownerPath);
          }
          cache.fs.rmdir(cache.lock);
          cacheRecoveryWarning(cache);
          continue;
        }
        await cache.context.ports.sleep(10);
      }
    }
    if (!locked) throw new Error('busy cache');
    // Another command may have cleared or recovered the cache while this one ran.
    cache.epoch = readTestCacheBinding(cache);
    let snapshot;
    try { snapshot = readTestCache(cache); }
    catch (error) {
      safeCachePath(cache.fs, cache.path);
      cacheWarning(cache, true);
      // A new namespace prevents an earlier in-flight generation from matching.
      snapshot = { data: freshTestCache(cache), history: false };
    }
    const invalidations = cacheInvalidations(cache);
    if (invalidations.length) {
      snapshot = { data: { ...freshTestCache(cache), generation: snapshot.data.generation + 1 }, history: false };
    }
    const result = operation(snapshot.data, snapshot.history, snapshot.failed ?? {});
    if (snapshot.data.epoch !== cache.epoch) {
      replaceCacheFile(cache, cache.bindingPath, JSON.stringify({ schema_version: 1, epoch: snapshot.data.epoch }));
      cache.epoch = snapshot.data.epoch;
    }
    const text = JSON.stringify(snapshot.data) + '\n';
    if (Buffer.byteLength(text) > CACHE_LIMIT) throw new Error('oversized cache');
    const failed = Object.fromEntries(Object.entries(snapshot.data.stories).filter(([, row]) => row.outcome === 'failed').map(([story]) => [story, true]));
    replaceCacheFile(cache, cache.failedPath, JSON.stringify({ schema_version: 1, epoch: snapshot.data.epoch, generation: snapshot.data.generation, stories: failed }) + '\n');
    replaceCacheFile(cache, cache.path, text);
    cache.data = snapshot.data;
    for (const name of invalidations) {
      const path = join(cache.markerDir, name);
      safeCachePath(cache.fs, path);
      try { cache.fs.unlink(path); } catch (error) { if (error.code !== 'ENOENT') throw error; }
    }
    return result;
  } catch { cacheWarning(cache); return null; }
  finally {
    if (locked) try {
      const path = join(cache.lock, 'owner.json');
      safeCachePath(cache.fs, path);
      if (owner && isDeepStrictEqual(JSON.parse(cache.fs.read(path, 'utf8', 128)), owner)) {
        cache.fs.unlink(path); cache.fs.rmdir(cache.lock);
      } else cacheWarning(cache);
    } catch { cacheWarning(cache); }
    if (releaseGuard) try { releaseGuard(); } catch { cacheWarning(cache); }
  }
}
async function openTestCache(context, root, clear, visible) {
  const fs = context.ports.cacheFiles, dir = join(root, '.pdd', 'cache', 'test');
  const cache = { fs, context, dir, path: join(dir, 'stories.json'), failedPath: join(dir, 'lastfailed.json'), lock: join(dir, 'transaction.lock'), tokens: new Map(), data: null, history: false, markerDir: join(context.store.dir, 'test-cache-invalidations', sha256(Buffer.from(root))) };
  try {
    // Trust the canonical external root, but never its final symlink.
    if (cacheStat(fs, context.store.dir)?.isSymbolicLink()) throw new Error('unsafe state root');
    const stateRoot = realish(context.store.dir);
    const repoKey = sha256(Buffer.from(realpathSync(root)));
    cache.markerDir = join(stateRoot, 'test-cache-invalidations', repoKey);
    const bindingDir = join(stateRoot, 'test-cache-bindings');
    safeCachePath(fs, bindingDir, { directory: true, create: true });
    const bindingPath = cache.bindingPath = join(bindingDir, repoKey + '.json');
    safeCachePath(fs, bindingPath);
    if (!cacheStat(fs, bindingPath)) {
      try { fs.write(bindingPath, JSON.stringify({ schema_version: 1, epoch: fs.nonce() }), { flag: 'wx', mode: 0o600 }); }
      catch (error) { if (error.code !== 'EEXIST') throw error; }
    }
    cache.epoch = readTestCacheBinding(cache);
    if ((fs.tracked ?? nativeCacheFiles.tracked)(root)) throw new Error('tracked test cache');
    const marker = cacheStat(fs, join(root, '.git'));
    if (!marker || marker.isSymbolicLink() || (!marker.isFile() && !marker.isDirectory())) throw new Error('unsafe Git marker');
    safeCachePath(fs, dir, { directory: true, create: true });
    const exclude = fs.exclude(root);
    safeCachePath(fs, dirname(exclude), { directory: true, create: true });
    safeCachePath(fs, exclude);
    const stat = cacheStat(fs, exclude);
    if (stat?.size > CACHE_LIMIT) throw new Error('oversized exclude');
    const text = stat ? fs.read(exclude, 'utf8') : '';
    if (!text.split(/\r?\n/).includes('/.pdd/cache/test/')) replaceCacheFile(cache, exclude, `${text}${text.endsWith('\n') || !text ? '' : '\n'}/.pdd/cache/test/\n`);
    // Clearing replaces only known metadata; unsafe files and directories remain untouched.
    await cacheTransaction(cache, (data, history, failed) => {
      cache.history = history;
      cache.failed = { ...failed };
      if (visible) for (const story of Object.keys(data.stories)) {
        if (!visible.has(story)) { delete data.stories[story]; delete cache.failed[story]; }
      }
      if (clear) {
        const generation = data.generation + 1, marks = data.latest_identity?.in_progress ?? [];
        delete data.latest_identity;
        Object.assign(data, freshTestCache(cache), { generation });
        if (marks.length) data.latest_identity = { engine_sha: null, models: [], clean: false, conflict: true,
          sampled_at: new Date(0).toISOString(), observed_at: new Date(cache.context.ports.now()).toISOString(), in_progress: marks };
        cache.history = false;
      }
    }, clear);
  } catch { cacheWarning(cache); }
  return cache;
}
function storyFingerprint(cache, capture, story, options, origin) {
  const footprint = capture.stories?.find(item => item.story_path === story);
  if (!footprint || footprint.unavailable || !Array.isArray(footprint.files) || !Array.isArray(footprint.tests)) return null;
  const rawPaths = [...new Set([story, ...footprint.tests, ...footprint.files.filter(file => file.path.endsWith('.prompt.md')).map(file => file.path)])].sort();
  const raw = rawPaths.map(path => [path, capture.raw_file_hashes?.[path] ?? (path.endsWith('.prompt.md') ? capture.raw_prompt_hashes?.[path] : undefined)]);
  if (raw.some(([, hash]) => !hash)) return null;
  return cache.context.ports.cacheHash(Buffer.from(JSON.stringify({ footprint, raw, origin, max_calls: options['--max-calls'] ?? null, pdd_version: cache.context.clientVersion ?? null })));
}
// The captured footprint owns reachability; inspect its captured declarations without
// inventing another dependency graph or reading a later version of a source file.
function declarationCacheReason(capture, story, tests) {
  const footprint = capture.stories?.find(item => item.story_path === story);
  if (!footprint?.files || !Array.isArray(capture.sources)) return 'runs again: resource declarations unavailable';
  const sources = new Map(capture.sources.map(file => [file.path, Buffer.from(file.bytes).toString('utf8')]));
  const fake = name => `runs every time: uses an AI-played fake (${name})`;
  const deterministic = binding => {
    if (!isObject(binding)) return false;
    if (binding.action === 'fixture.lookup') return Array.isArray(binding.cases) && binding.cases.length > 0;
    if (binding.action === 'port.write') return Object.hasOwn(binding, 'result_template') || Object.hasOwn(binding, 'result');
    return /^(key-value\.(get|put)|collection\.(get|get-or-null|merge)|blob\.(read|write|stat)|sql\.execute|compute)$/.test(binding.action);
  };
  const prompts = [];
  for (const file of footprint.files.filter(file => sources.has(file.path))) {
    const match = /^prompts\/fakes\/(.+)\.prompt\.md$/.exec(file.path);
    if (match) return fake(match[1]);
    if (!file.path.endsWith('.prompt.md')) continue;
    try {
      const blocks = interfaceBlocks(sources.get(file.path));
      if (blocks.length) prompts.push(JSON.parse(blocks[0][1]));
    }
    catch { return 'runs again: resource declarations unavailable'; }
  }
  for (const path of tests) {
    let doc; try { doc = JSON.parse(sources.get(path)); } catch { return 'runs again: resource declarations unavailable'; }
    // A step override is part of that step's world, not evidence for other steps.
    const stepSimulation = (base, overrides) => {
      const result = { ...(base ?? {}) };
      if (Array.isArray(overrides)) {
        for (const row of overrides) {
          const name = isObject(row) && typeof row.operation === 'string' && row.operation.trim() ? row.operation : 'simulation_overrides';
          result[name] = isObject(row) && isObject(row.binding) ? row.binding : null;
        }
      } else if (isObject(overrides)) Object.assign(result, overrides);
      return result;
    };
    const steps = Array.isArray(doc.steps) ? doc.steps : [];
    const bindings = steps.length ? steps.map(step => stepSimulation(doc.simulation, step?.simulation_overrides)) : [doc.simulation ?? {}];
    for (const simulation of [doc.simulation ?? {}, ...bindings]) for (const [operation, binding] of Object.entries(simulation)) {
      if (!deterministic(binding)) return fake(operation.split('.')[0]);
    }
    for (const prompt of prompts) for (const resource of prompt.resources ?? []) {
      if (['key-value', 'collection', 'blob', 'sql', 'compute'].includes(resource.kind)) continue;
      if (!['http', 'command', 'model', 'port'].includes(resource.kind)) return fake(resource.name);
      const operations = resource.operations;
      if (!Array.isArray(operations) || !operations.length) return fake(resource.name);
      for (const operation of operations) {
        const bound = bindings.every(simulation => deterministic(simulation[`${resource.name}.${operation.name}`]));
        if (resource.kind === 'port' && resource.name === 'clock' && operation.name === 'now') {
          const value = doc.initial_world?.clock?.now;
          const fixed = typeof value === 'number' && Number.isFinite(value) || typeof value === 'string' && /^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}(?::\d{2}(?:\.\d+)?)?(?:Z|[+-]\d{2}:\d{2})?$/.test(value) && Number.isFinite(Date.parse(value));
          if (!fixed && !bound) return 'runs every time: uses the real clock';
        } else if (!bound) return fake(resource.name);
      }
    }
  }
  return null;
}
function eligibleCachePass(pass, now) {
  const age = now - Date.parse(pass?.passed_at);
  return !!pass && typeof pass.requested_model === 'string' && pass.requested_model.trim() && pass.requested_model.trim().toLowerCase() !== 'unknown'
    && typeof pass.engine_sha === 'string' && pass.engine_sha.trim() && pass.engine_sha.trim().toLowerCase() !== 'unknown'
    && Number.isFinite(age) && age >= 0 && age <= 7 * 86400000;
}

function identityFingerprint(cache, fingerprint, identity) {
  return cache.context.ports.cacheHash(Buffer.from(JSON.stringify({ fingerprint, engine_sha: identity?.engine_sha ?? null, requested_model: identity?.requested_model ?? null })));
}
// Call only while holding the cache transaction; normal and saved-read sends
// share ownership so another invocation cannot reuse evidence while either runs.
function markTestAttempt(cache, data) {
  if (cache.mark) return;
  cache.mark = { token: cache.fs.nonce(), pid: cache.context.ports.pid ?? process.pid, started_at: cache.context.ports.now() };
  const latest = data.latest_identity ?? { engine_sha: null, models: [], clean: false, conflict: true,
    sampled_at: new Date(0).toISOString(), observed_at: new Date(cache.context.ports.now()).toISOString() };
  const isAlive = cache.context.ports.isAlive ?? (pid => { try { process.kill(pid, 0); return true; } catch (error) { return error.code !== 'ESRCH'; } });
  // Eligibility already saw every mark, including dead owners. Only now retire
  // dead marks; live owners must survive another invocation's finish.
  latest.in_progress = [...(latest.in_progress ?? []).filter(mark => isAlive(mark.pid)), cache.mark];
  data.latest_identity = latest;
  cache.identitySnapshot = JSON.stringify(latest);
}
async function beginTestAttempts(cache, rows, capture, options, origin, force = false) {
  if (cache.disabled || !rows.length) return;
  const originals = rows.map(row => ({ ...row }));
  const grouped = new Map();
  for (const row of rows) grouped.set(row.story_path, [...(grouped.get(row.story_path) ?? []), row]);
  await cacheTransaction(cache, data => {
    for (const [story, own] of grouped) {
      if (!story) continue;
      const fingerprint = capture ? storyFingerprint(cache, capture, story, options, origin) : null;
      const pass = data.stories[story]?.pass;
      const reason = capture && declarationCacheReason(capture, story, own.map(row => row.test))
        || (Number.isFinite(Date.parse(pass?.passed_at)) && cache.context.ports.now() - Date.parse(pass.passed_at) > 7 * 86400000 ? 'runs again: saved pass is older than seven days' : null)
        || (pass && !cleanRecordMatches(data.latest_identity, pass) ? 'runs again: interpreter build or model changed' : null);
      if (reason) for (const row of own) row.cache_reason = reason;
      if (!force && !reason && [undefined, '', '0', 'false'].includes(cache.context.ports.env.CI) && eligibleCachePass(pass, cache.context.ports.now()) && fingerprint && pass?.fingerprint === identityFingerprint(cache, fingerprint, pass) && own.every(row => row.state === 'ready' && pass.tests.includes(row.test))) {
        for (const row of own) Object.assign(row, pass.rows[row.test], { state: 'passed', cached: true, cache_identity: { engine_sha: pass.engine_sha, requested_model: pass.requested_model }, passed_at: pass.passed_at, phase: 'cache', calls: 0, input_tokens: 0, cached_input_tokens: 0, output_tokens: 0, cached_input_share: null, seconds: 0, request_ids: [], report_url: null });
        continue;
      }
      const generation = ++data.generation;
      data.stories[story] = { generation, outcome: data.stories[story]?.outcome === 'failed' ? 'failed' : own.some(row => row.state === 'refused') ? 'refused' : 'unknown' };
      cache.tokens.set(story, { epoch: data.epoch, generation, fingerprint });
    }
    if (capture && rows.some(row => !row.cached && row.state === 'ready') && !cache.mark) {
      markTestAttempt(cache, data);
    }
  });
  if (cache.disabled) rows.forEach((row, index) => { for (const key of Object.keys(row)) delete row[key]; Object.assign(row, originals[index]); });
}
async function finishTestAttempts(cache, rows, capture) {
  if (cache.disabled) return;
  await cacheTransaction(cache, data => {
    const observations = cache.context.observedTestIdentities ?? [];
    const previous = data.latest_identity;
    const identity = { engine_sha: observations.find(item => item.engine_sha)?.engine_sha ?? null,
      requested_model: observations.flatMap(item => item.models).find(Boolean) ?? null };
    const terminalObservations = observations.filter(item => item.terminal);
    const complete = terminalObservations.length > 0 && terminalObservations.every(item => item.complete)
      && observations.every(item => observedIdentityMatches(item, identity));
    const marks = previous?.in_progress ?? [];
    const ownMark = mark => !!cache.mark && mark.token === cache.mark.token;
    const clean = marks.length === 1 && ownMark(marks[0]) && !cache.context.cacheReadInvocation && !cache.context.checkRunFailed && Number.isFinite(cache.context.startedAt)
      && (!previous || cache.context.startedAt > Date.parse(previous.sampled_at))
      && cache.identitySnapshot === JSON.stringify(previous ?? null) && complete;
    data.latest_identity = { engine_sha: identity.engine_sha, models: identity.requested_model ? [identity.requested_model] : [],
      in_progress: marks.filter(mark => !ownMark(mark)), clean, conflict: !clean, sampled_at: new Date(Number.isFinite(cache.context.startedAt) ? cache.context.startedAt : 0).toISOString(),
      written_at: new Date(cache.context.ports.now()).toISOString(), observed_at: new Date(cache.context.ports.now()).toISOString() };
    for (const [story, token] of cache.tokens) {
      if (data.epoch !== token.epoch || data.stories[story]?.generation !== token.generation) continue;
      const own = rows.filter(row => row.story_path === story && !row.cached), footprint = capture.stories?.find(item => item.story_path === story);
      const complete = footprint?.tests.length === own.length && footprint.tests.every(test => own.some(row => row.test === test));
      const outcome = own.some(row => row.state === 'failed') ? 'failed' : own.some(row => row.state === 'refused') ? 'refused' : own.some(row => row.state === 'not_run') ? 'not_run' : complete && own.length && own.every(row => row.state === 'passed' && typeof row.calls === 'number' && row.accounting_complete === true) && !cache.context.interrupted && !cache.context.lintUnknown ? 'passed' : 'unknown';
      const record = data.stories[story] = { generation: token.generation, outcome: outcome !== 'passed' && data.stories[story]?.outcome === 'failed' ? 'failed' : outcome };
      const identity = own[0]?.cache_identity;
      const consistent = identity && own.every(row => sameCacheIdentity(identity, row.cache_identity))
        && rows.filter(row => !row.cached && row.cache_identity).every(row => sameCacheIdentity(identity, row.cache_identity))
        && observations.every(observed => observedIdentityMatches(observed, identity));
      const sampledAt = Math.min(cache.context.startedAt, ...own.map(row => row.cache_sample_at).filter(Number.isFinite));
      if (outcome === 'passed' && token.fingerprint && consistent && Number.isFinite(sampledAt)) {
        record.pass = { ...identity, fingerprint: identityFingerprint(cache, token.fingerprint, identity), tests: footprint.tests, passed_at: new Date(sampledAt).toISOString(),
          rows: Object.fromEntries(own.map(row => [row.test, { checks: row.checks, criteria: row.criteria, criteria_total: row.criteria_total, draft: !!row.draft }])) };
      }
    }
  });
}

// Bind planning to the Git comparison and the exact permitted classification inputs.
// Git's binary diff also preserves link spelling and non-UTF-8 implementation bytes.
// The source reader admits each working path before Git reads its raw bytes.
function affectedPlanningAuthority(root, found, base, ports) {
  const git = args => {
    if (ports.checkPlanPorts?.git) return ports.checkPlanPorts.git(root,args);
    const result = spawnSync('git',args,{cwd:root,stdio:['ignore','pipe','pipe'],maxBuffer:512*1024*1024});
    if (result.status !== 0 && !(args.includes('--no-index') && result.status === 1)) throw Error('comparison unavailable');
    return result.stdout;
  };
  const permitted = path => allowsRuntimePath(found.workspace,path)
    && !(found.excludedFixtureProjects ?? []).some(prefix=>path === prefix || path.startsWith(`${prefix}/`));
  try {
    const revision = String(git(['rev-parse',`${base}^{tree}`])).trim();
    const tracked = String(git(['diff','--name-only','-z','--no-renames',base,'--'])).split('\0').filter(permitted).filter(Boolean).sort();
    const untracked = String(git(['ls-files','--others','--exclude-standard','-z'])).split('\0').filter(permitted).filter(Boolean).sort();
    // Validate working paths through the source authority before Git reads bytes.
    const source = sourceFilePort(root,found.visible,found.workspace);
    const content = [...new Set([...tracked,...untracked])].map(path=>{
      try { return [path,sha256(Buffer.from(source.read({path}).content))]; }
      catch { return [path,null]; }
    });
    const readable = new Set(content.filter(([,hash])=>hash !== null).map(([path])=>path));
    const paths = tracked.filter(path=>readable.has(path));
    const diff = paths.length ? sha256(Buffer.from(git(['diff','--no-ext-diff','--no-textconv','--no-renames','--binary',base,'--',...paths.map(path=>`:(literal)${path}`)]))) : null;
    const added = untracked.filter(path=>readable.has(path)).map(path=>[path,sha256(Buffer.from(git([
      'diff','--no-index','--no-ext-diff','--no-textconv','--binary','--','/dev/null',path])))]);
    return {revision,tracked,untracked,content,diff,added};
  } catch { return {unavailable:true}; }
}

async function runBatch(context, cwd, words, options, setRelease) {
  const { ports } = context;
  const origin = runtimeOrigin(ports.env);
  const { root, found, normalized } = localSetup(cwd, words, ports);
  context.visible = found.visible; context.origin = origin; context.excludeFixtureProjects = words.length === 0;
  // Ordinary Check waits for completion in every shell unless a limit is explicit.
  context.agentLimit = false;
  context.timeoutMin = options['--timeout'] !== undefined ? Number(options['--timeout']) : null;
  let selected = select(found, normalized, root, ports);
  const inventory = selected;
  const allowMissingInterfaces = hasMissingPromptInterface(root, found, entryPaths(inventory))
    ? await probeLazyInterfaces(context, origin, context.store) : false;
  const affected = options['--affected'] === true;
  const resolveWorkflowBase = () => {
    const workflowBase = context.workflow !== undefined
      ? context.workflow?.base_sha
      : ports.workflowBaseSha !== undefined && ports.workflowBaseSha !== null
        ? (typeof ports.workflowBaseSha === 'function'
            ? ports.workflowBaseSha({ root, env: ports.env })
            : ports.workflowBaseSha)
        : (() => {
            const runs = (ports.allRuns ?? (() => []))({ cancelled: true }, { env: ports.env }).filter(run => {
              try { return realpathSync(run.root) === realpathSync(root); } catch { return false; }
            });
            return runs.length === 1 ? runs[0].baseSha : null;
          })();
    return /^[a-f0-9]{40}$/.test(workflowBase ?? '') ? workflowBase : 'HEAD';
  };
  let base = affected ? resolveWorkflowBase() : null;
  const planningPorts = {
    headerPrompts: ports.headerPrompts,
    capture: ports.captureSource,
    isStoryPath: ports.isStoryPath,
    hasAcceptance: ports.hasAcceptance,
    matchTests: ports.matchTests,
    orphanSummary: ports.orphanSummary,
    ...ports.checkPlanPorts,
  };
  // Discovery is part of selection authority, including complete sibling variants.
  // Recheck after captures too: a capture can observe a newly created test that
  // was absent from the discovery result passed to the planner.
  const discoveryScope = current => ({tests:current.tests,visible:current.discoveryVisible ?? current.visible,workspace:current.workspace,
    authority:affected ? affectedPlanningAuthority(root,current,base,ports) : null});
  const initialDiscovery = discoveryScope(found);
  if (affected && initialDiscovery.authority.unavailable) context.forceAffectedFull = true;
  let discoveryChanged = false, cache = null;
  const discover = () => {
    const current = localSetup(cwd, words, ports);
    discoveryChanged ||= !isDeepStrictEqual(initialDiscovery,discoveryScope(current.found));
    return current;
  };
  const planFor = rows => {
    const current = discover();
    const plan = buildCheckPlan({root,found:current.found,selected:select(current.found,current.normalized,root,ports),rows,full:true,base,affected:!context.forceAffectedFull,allowMissingInterfaces},planningPorts);
    discover();
    return context.forceAffectedFull ? {...plan,stories:plan.stories.map(story=>({...story,role:'target',reason:'conservative: source selection changed during planning'}))} : plan;
  };
  const restartConservatively = async () => {
    // A late discovery change can follow provisional cache admission. Retire
    // only this attempt's mark, leaving its invalidations and other owners intact.
    if (cache?.mark) await cacheTransaction(cache, data => {
      if (data.latest_identity?.in_progress) {
        data.latest_identity.in_progress = data.latest_identity.in_progress.filter(mark=>mark.token!==cache.mark.token);
        Object.assign(data.latest_identity,{clean:false,conflict:true});
      }
    });
    if (context.testCache === cache) context.testCache = null;
    if ((context.affectedPlanningRestarts ?? 0) >= 3)
      throw new Stop(4,'Source selection kept changing during planning. No checks were sent. Run a fresh pdd test --affected once local source is stable.');
    context.affectedPlanningRestarts = (context.affectedPlanningRestarts ?? 0) + 1;
    context.forceAffectedFull = true;
    line(ports.stderr,'Source selection changed during planning; checking every Story conservatively before any paid Check.');
    return runBatch(context,cwd,words,options,setRelease);
  };
  let classification;
  if (affected) {
    classification = planFor([]);
    if (discoveryChanged) return restartConservatively();
    // Re-read local membership before any dispatch preflight or cache mutation.
    const revalidated = planFor([]);
    const first = selectCheckTests(classification,{affected:true}), second = selectCheckTests(revalidated,{affected:true});
    classification = revalidated;
    if (discoveryChanged || !isDeepStrictEqual(first.tests,second.tests)) return restartConservatively();
    context.checkSelection = selectCheckTests(classification,{affected:true});
    selected = inventory.filter(test=>context.checkSelection.tests.includes(test.path));
    context.baselineReport = await readBaselineReport(context,classification,ports.baselineIdentity ?? null);
    discover();
    if (discoveryChanged) return restartConservatively();
  }
  cache = context.cacheEnabled ? await openTestCache(context, root, !!options['--cache-clear'], found.visible) : null;
  if (cache && !cache.disabled && options['--lf'] && !options['--cache-clear'] && cache.history) {
    const failures = selected.filter(test => cache.failed[test.storyPath] === true);
    if (failures.length) selected = failures;
  }
  if (options['--cache-clear']) {
    const count = new Set(selected.map(test => test.storyPath ?? test.path)).size;
    line(ports.stderr, `pdd: test cache ${cache && !cache.disabled ? 'cleared' : 'unavailable'}. Running ${count} selected ${count === 1 ? 'Story' : 'Stories'}; the interpreter may reuse saved answers.`);
  }
  context.coverage = bindingCoverage({ root, found, selected, includeRuntime:true, allowMissingInterfaces });
  const checked = preflight({ root, found, selected, allowMissingInterfaces });
  const rows = localRows(checked.rows);
  context.rows = rows;
  for (const row of rows) {
    const test = selected.find(item => item.path === row.test);
    row.story_path = test?.storyPath;
    // A test that discovery cannot use (a conflict, unreadable, invalid or over the upload limit) is refused and never uploaded.
    if (test?.error) row.unsent = true;
    row.criterion_texts = Object.fromEntries([...(Array.isArray(test?.doc?.criteria) ? test.doc.criteria : []).filter(isObject).map(item => [item.id, item.text]),
      ...(row.not_checked??[]).map(item=>[item.criterion_id,item.text])]);
  }
  if (options['--max-calls'] !== undefined) for (const row of rows) row.max_calls = Number(options['--max-calls']);
  base ??= resolveWorkflowBase();
  context.checkPlan = affected ? planFor(rows) : buildCheckPlan({root,found,selected,rows,full:words.length === 0,base,allowMissingInterfaces},planningPorts);
  if (affected) {
    const finalSelection = selectCheckTests(context.checkPlan,{affected:true});
    if (discoveryChanged || !isDeepStrictEqual(finalSelection.tests,context.checkSelection.tests)) return restartConservatively();
    context.baselineReport = await readBaselineReport(context, context.checkPlan, ports.baselineIdentity ?? null);
    discover();
    if (discoveryChanged) return restartConservatively();
  }
  for (const value of checkPlanLines(context.checkPlan)) line(ports.stderr, value);
  if (!words.length && context.checkPlan.prerequisites.length) {
    const note = {code:'check-plan-prerequisite',message:checkPlanResults(context.checkPlan,rows).guidance};
    for (const row of rows) {
      if (row.state === 'ready') Object.assign(row,{state:'not_run',calls:0,phase:'local'});
      if (row.state !== 'passed') row.note = note;
    }
    context.warnings.push('Full check blocked by a check-plan prerequisite. 0 AI calls. No checks were sent.');
    saveLocalNativeResult(context,rows,'check');
    printResult(context,rows);
    return 4;
  }

  const scopedOwnership = words.length > 0 || affected || selected.length < found.tests.length;
  context.warnings.push(...found.warnings, ...checked.warnings, ...sharedSourceFiles(root, found.discoveryVisible ?? found.visible, { ...(scopedOwnership ? { tests: selected } : {}), workspace: found.workspace }, ports));
  context.unmatched = unmatchedLines(found);
  if (cache) await beginTestAttempts(cache, rows.filter(row => row.state !== 'ready'), null, options, origin);
  if (!rows.some(row => row.state === 'ready')) { if (rows.some(row => row.native_only?.length)) saveLocalNativeResult(context, rows, 'check'); return printResult(context, rows); }
  context.nativeSource = nativeSourceIdentity(context, rows);
  let capture;
  try { capture = captureIndependent(root, rows, ports, {appMap:null,excludeFixtureProjects:words.length === 0,...(allowMissingInterfaces ? {allowMissingInterfaces:true} : {})}); }
  catch (error) { if (cache) await beginTestAttempts(cache, rows, null, options, origin); throw error; }
  if (!capture || !rows.some(row=>row.state==='ready')) {
    if (cache) await beginTestAttempts(cache,rows,null,options,origin);
    return printResult(context,rows);
  }
  if (affected) {
    const validated = selectCheckTests(planFor([]),{affected:true});
    if (discoveryChanged || !isDeepStrictEqual(validated.tests,context.checkSelection.tests)) return restartConservatively();
  }
  context.sourceSelection = {tests:sentTests(rows),exclude_fixture_projects:words.length === 0};
  const svgWarnings = typeof ports.lintSvgLayouts === 'function'
    ? ports.lintSvgLayouts({ root, files: [...found.visible], promptPaths: capture.files.map(file => file.path).filter(path => path.endsWith('.prompt.md')) })
    : [];
  context.warnings.push(...svgWarnings, ...(capture.warnings ?? []));
  if (cache) await beginTestAttempts(cache, rows, capture, options, origin);
  context.testCache = cache;
  const fresh = rows.filter(row => !row.cached);
  if (!fresh.some(row => row.state === 'ready')) {
    if (affected) { discover(); if (discoveryChanged) return restartConservatively(); }
    return printResult(context, rows);
  }
  context.otherNote = otherNote(otherFiles(capture.files, found).length);
  let identity;
  try { identity = context.probedIdentity ?? signIn(ports.gh, context.store, ports); }
  catch (error) {
    if (cache?.mark) await cacheTransaction(cache, data => {
      if (data.latest_identity?.in_progress) {
        data.latest_identity.in_progress = data.latest_identity.in_progress.filter(mark => mark.token !== cache.mark.token);
        Object.assign(data.latest_identity, { clean: false, conflict: true });
      }
    });
    throw error;
  }
  if (affected) {
    context.baselineReport = await readBaselineReport(context, context.checkPlan, identity);
    const validated = selectCheckTests(planFor([]),{affected:true});
    if (discoveryChanged || !isDeepStrictEqual(validated.tests,context.checkSelection.tests)) return restartConservatively();
  }
  const startedAt = ports.now(), batch = batchId(startedAt, ports.randomUUID);
  const head = spawnSync('git', ['rev-parse', 'HEAD'], { cwd: root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  Object.assign(context, { capture, identity, batch, startedAt, deadline: Infinity, rows,
    intent: 'check', head: head.status === 0 ? head.stdout.trim() : null, secrets: [identity.token], lint: { request_ids: [], state: null } });
  context.folder = context.store.folder('batches', batch);
  setRelease(interruptible(context));
  await ownBatch(context, batch);
  saveBatch(context);
  const repoState = context.store.repo(root);
  context.store.saveRepo(root, { ...repoState, last_batch: batch });
  context.auth = authSession({ identity, store: context.store, ports, secrets: context.secrets, onRefresh: next => { context.identity = next; saveBatch(context); } });
  context.runtime = new Runtime({ origin, token: identity.token, ports, signal: context.signal, auth: context.auth });
  await checkBatch(context, fresh);
  if (cache) {
    const observed = context.observedTestIdentities ?? [];
    const rerun = rows.filter(row => row.cached && observed.some(identity =>
      identity.engine_sha && identity.engine_sha !== row.cache_identity?.engine_sha
      || identity.models.some(model => model !== row.cache_identity?.requested_model)));
    if (rerun.length) {
      // Restore the selected local rows, then invalidate their old generations before
      // sending. The same rows replace the provisional cache projection in output.
      const originals = new Map(localRows(checked.rows).map(row => [row.test, row]));
      for (const row of rerun) {
        const original = originals.get(row.test), storyPath = row.story_path, texts = row.criterion_texts;
        for (const key of Object.keys(row)) delete row[key];
        Object.assign(row, original, { story_path: storyPath, criterion_texts: texts, cache_reason: 'runs again: interpreter build or model changed' });
        if (options['--max-calls'] !== undefined) row.max_calls = Number(options['--max-calls']);
      }
      await beginTestAttempts(cache, rerun, capture, options, origin, true);
      const stopReason = context.interrupted ? 'interrupted' : context.readStop ? 'reading stopped'
        : ports.now() >= context.deadline ? 'time limit reached' : context.stopped ? 'stopped' : null;
      if (stopReason) {
        for (const row of rerun) Object.assign(row, { state: 'not_run', calls: 0, seconds: 0, phase: 'local', busy: false,
          note: { code: null, message: `not sent: ${stopReason}` }, why: `not sent: ${stopReason}` });
      } else await checkBatch(context, rerun, context.lastCheckLint);
      saveBatch(context);
    }
  }
  saveBatch(context);
  return () => printResult(context, rows);
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
  requireRuntimePath(loadRuntimeWorkspace({root}),{path:rel,from:'App map'});
  if (!found.visible.has(rel)) throw new Stop(2, `--app-map ${cleanText(given)} is not a Git-visible file in this repository.`);
  const problem = appMapProblem(root, rel);
  if (problem) throw new Stop(2, `--app-map ${cleanText(given)} is not an app map: ${problem}. An app map is a JSON file with "schema_version": "${APP_MAP_VERSION}". See RUNBOOK.md §13.`);
  return rel;
}

function oneTest(found, words, root, ports) {
  const selected = select(found, words, root, ports);
  if (selected.length !== 1) throw new Stop(2, ['pdd simulate needs one story. Choose one:', ...storyList({ tests: selected }, ports)].join('\n'));
  return selected[0];
}

function productTest(found, words, journey, root, ports) {
  if(journey===undefined && words.length)return oneTest(found,words,root,ports);
  const paths=selectJourneys(found.tests.map(test=>({testPath:test.path,storyPath:test.storyPath})),journey,ports);
  if(!paths.length && journey===undefined)return oneTest(found,words,root,ports);
  const requested=words.length?new Set(select(found,words,root,ports).map(test=>test.path)):null;
  const selected=found.tests.filter(test=>paths.includes(test.path)&&(!requested||requested.has(test.path)));
  if(selected.length!==1)throw new Stop(2,'Product Simulator needs one explicit Story or journey test.');
  return selected[0];
}
function captureProductTry(root,test,options,ports) {
  let composition, maxTapCalls;
  const capture=ports.captureSource(root,{tests:[test.path],appMap:null,prepareSource(snapshot){
    const adapters={root,statFile:(path,options)=>snapshot.statFile(relative(root,path).split(sep).join('/'),options),
      readFile:path=>snapshot.readFile(relative(root,path).split(sep).join('/')),
      parseProductDocuments:ports.parseProductDocuments,parseProductWorldWriters:ports.parseProductWorldWriters,selectTests:ports.selectTests};
    const journey=options['--journey']??(/^user_stories\/journeys\/[^/]+\.md$/.test(test.storyPath)?test.path:undefined);
    composition=composeProductTry({root,...(options['--parts']!==undefined?{parts:options['--parts'].split(',').map(part=>part.trim())}:{}),
      ...(journey!==undefined?{journey,testPath:test.path}:{})},adapters);
    maxTapCalls=productTapCallBound(parseJsonValue(composition.files[0].content),adapters);
    const output=new Map(composition.files.map(file=>[file.path,file.content]));
    const files={stat:({path})=>output.has(path)?{exists:true,is_symlink:false,size:Buffer.byteLength(output.get(path))}:snapshot.statFile(path),
      read:({path})=>({content:output.get(path)??snapshot.readFile(path).toString('utf8')})};
    const scenario=parseJsonValue(snapshot.readFile(test.path).toString('utf8'));
    if(options['--journey']!==undefined)selectJourneys([{testPath:test.path,storyPath:scenario.story_path}],options['--journey'],ports);
    scenario.initial_world={$seed:composition.seedPath};
    const expanded=expandSource({path:test.path,text:stringifyJsonValue(scenario),format:'scenario'},files);
    return [...composition.files.map(file=>({path:file.path,bytes:file.content,...(file.path===composition.appMapPath?{role:'app-map'}:{})})),{path:test.path,bytes:expanded.text}];
  }});
  return {capture,composition,maxTapCalls};
}
const productOptions = setup => setup ? {'--product':true,...(setup.parts?{'--parts':setup.parts.join(',')}:{}),...(setup.journey?{'--journey':setup.journey}:{})} : {};
function tryCommand(test, setup, suffix='', target=test.story) {
  const quote=value=>/^[A-Za-z0-9_./-]+$/.test(String(value))?String(value):"'"+String(value).replace(/'/g,"'\"'\"'")+"'";
  return `pdd simulate ${quote(target)}${setup?' --product'+(setup.parts?' --parts '+quote(setup.parts.join(',')):'')+(setup.journey?' --journey '+quote(setup.journey):''):''}${suffix}`;
}

// Read the authored interfaces, never scenario output, to choose an interaction.
function programEntries(root, found, test) {
  const cli = new Set(), http = new Set();
  for (const step of Array.isArray(test.doc?.steps) ? test.doc.steps : []) {
    if (!step || typeof step.entry_path !== 'string' || typeof step.operation !== 'string') continue;
    const prompt = readPrompt(root, found.visible, step.entry_path);
    const entries = Array.isArray(prompt.interface?.entries) ? prompt.interface.entries : [];
    const conventions = Array.isArray(prompt.interface?.conventions) ? prompt.interface.conventions : [];
    const index = entries.findIndex(entry => entry?.operation === step.operation);
    if (!(index >= 0)) continue;
    const entry = entries[index], key = `${step.entry_path}#${step.operation}`;
    if (['input_schema', 'result_schema'].every(name => conventions.some(c => c?.path === `/entries/${index}/${name}` && c.convention === 'cli'))) cli.add(key);
    if (typeof entry.input_schema?.title === 'string' && /^HTTP (GET|HEAD|POST|PUT|PATCH|DELETE|OPTIONS) \/\S*$/.test(entry.input_schema.title)) http.add(key);
  }
  return { test, cli, http };
}

function simulationSelection(root, found, words, appMap, options, ports) {
  const all = [...found.tests].sort((a, b) => a.path.localeCompare(b.path));
  if (!all.length) throw new Stop(2, 'No Stories are available to simulate.');
  const selected = words.length ? [oneTest(found, words, root, ports)] : all;
  const rows = selected.map(test => programEntries(root, found, test));
  const eligibleNames = predicate => [...new Set(all.flatMap(test => {
    const selectedRow = rows.find(row => row.test === test);
    // Selected source was read strictly above. Unselected failures cannot turn
    // advisory eligible-name discovery into a new source requirement.
    try { return predicate(selectedRow ?? programEntries(root, found, test)) ? [test.story] : []; }
    catch { return []; }
  }))].sort();
  const cli = new Set(rows.flatMap(row => [...row.cli]));
  const hasHttp = rows.some(row => row.http.size);
  const screens = appMap ? JSON.parse(readFileSync(join(root, appMap), 'utf8')).screens : [];
  const mapped = Array.isArray(screens) && selected.some(test => (Array.isArray(test.doc?.steps) ? test.doc.steps : []).some(step => step && screens.some(screen => screen?.source === 'operation' && screen.prompt_path === step.entry_path && screen.operation === step.operation)));
  const typed = words.length && !cli.size && !hasHttp && !mapped;
  const page = options['--page'] || options['--agent'] !== undefined || options['--tab'] !== undefined;
  const forcedCli = options['--cli'] || options['--shell'];
  if (forcedCli && cli.size !== 1) {
    const names = eligibleNames(row => row.cli.size === 1);
    const name = selected[0].story, target = /^[A-Za-z0-9_./-]+$/.test(name) ? name : "'" + name.replaceAll("'", "'\\''") + "'";
    const refusal = new Stop(125, `${cli.size ? 'This Story uses more than one command-line program.' : 'This Story is not a command-line program.'} ${names.length ? `These are: ${names.join(', ')}.` : 'No Stories are command-line programs.'}`);
    if (typed) refusal.formRecovery = `pdd simulate ${target} opens its Form tab.`;
    throw refusal;
  }
  if (options['--serve'] !== undefined && !hasHttp && !appMap) {
    const names = eligibleNames(row => row.http.size);
    throw new Stop(2, `This Story has no HTTP routes or screens. ${names.length ? `These are: ${names.join(', ')}.` : 'No Stories have HTTP routes or screens.'}`);
  }
  let seed = selected[0];
  if (!page && !forcedCli && options['--serve'] === undefined && !(appMap && !words.length)) {
    if (cli.size > 1) throw new Stop(2, `There is more than one command-line program. Name a Story: ${[...new Set(rows.filter(row => row.cli.size).map(row => row.test.story))].sort().join(', ')}.`);
    if (cli.size === 1) { options['--cli'] = true; options['--shell'] = true; }
    else if (hasHttp) options['--serve'] = 0;
  }
  if (forcedCli) options['--cli'] = true;
  // The seed establishes saved-case/session identity, not a preferred view.
  if (cli.size === 1) seed = rows.find(row => row.cli.size).test;
  else if (hasHttp) seed = rows.find(row => row.http.size).test;
  const tab = options['--tab'] ?? (options['--cli'] ? 'terminal' : appMap && (!words.length || mapped || !typed) ? 'screen' : 'call');
  return { test: seed, selected, tab, typed: typed && tab === 'call' && options['--serve'] === undefined };
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

function tryRecovery(context, test, id) {
  const target = /^[A-Za-z0-9_./-]+$/.test(test.path) ? test.path : "'" + test.path.replace(/'/g, "'\"'\"'") + "'";
  return new Stop(3, `The original Try ${id} is not confirmed running. Its saved setup is kept; no replacement was sent.\nRead-only status: GET ${context.origin}/v1/runs/${id} (authenticated).\nRead it again with: ${tryCommand(test,context.product_setup,' --no-open --no-wait')}\nUse --new only after reconciling the original outcome to start a separate Try.`);
}

async function reopenTry(context, record, test) {
  const target = /^[A-Za-z0-9_./-]+$/.test(test.path) ? test.path : "'" + test.path.replace(/'/g, "'\"'\"'") + "'";
  const again = tryCommand(test,record.product_setup,'',test.path);
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

function trySourceSelection(record, path) {
  const scope = record.simulation_scope;
  if (scope === undefined) return { tests: [path] };
  if (!isObject(scope) || !Array.isArray(scope.tests) || !scope.tests.length
    || !scope.tests.every(test => typeof test === 'string') || !scope.tests.includes(path)
    || !(scope.appMap === null || typeof scope.appMap === 'string')) {
    throw new Stop(4, 'The saved whole-project source scope is unavailable. Run pdd simulate --new.');
  }
  return { tests: scope.tests, appMap: scope.appMap };
}

function tryPromptProblem(root, found, test, record, capture, ports) {
  const hashes=record.prompt_hashes;
  if (!capture && record.simulation_scope?.appMap) capture = ports.captureSource(root, trySourceSelection(record, test?.path));
  if (!capture && isObject(hashes)) {
    const files=sourceFilePort(root,found.visible), sources=[], references=[], raw_prompt_hashes={};
    for (const path of Object.keys(hashes)) {
      const prepared=readPrompt(root,found.visible,path);
      if (!prepared.text) return 'A prompt changed or this Try has no source record.';
      sources.push({path,bytes:Buffer.from(executableInterfaceText(prepared.text),'utf8')});references.push(...(prepared.references??[]));
      raw_prompt_hashes[path]=sha256(Buffer.from(files.read({path}).content,'utf8'));
    }
    capture={sources,references,raw_prompt_hashes};
  }
  if (record.simulation_scope?.appMap != null) {
    const scope = record.simulation_scope, map = capture.sources.find(file => file.path === scope.appMap);
    if (!/^[a-f0-9]{64}$/.test(scope.appMapHash ?? '') || !map || sha256(map.bytes) !== scope.appMapHash) return 'The saved simulation app map changed or its source baseline is unavailable.';
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
  options = { ...options };
  const ports = withDefaults(givenPorts), context = { ports, interrupted: false, doorMode: false, warnings: [] };
  let release = () => {};
  try {
    const productMode=options['--product']===true;
    if(options['--product']!==undefined&&!productMode || !productMode&&['--parts','--journey'].some(key=>options[key]!==undefined))throw new Stop(2,'--parts and --journey require --product.');
    if(productMode&&options['--app-map']!==undefined)throw new Stop(2,'--product builds its map; omit --app-map.');
    const requestedBudget = requestedCalls(options['--max-calls']);
    if (options['--agent'] !== undefined && (typeof options['--agent'] !== 'string' || !options['--agent'].trim() || ['--no-wait','--stop','--save-last','--cli','--shell','--serve'].some(key => options[key] !== undefined))) throw new Stop(2, '--agent chooses a configured agent name for an ordinary connected pdd simulate; omit --no-wait and door modes.');
    const doorModes = [options['--cli'] || options['--shell'], options['--serve'] !== undefined, options['--page'] || options['--tab'] !== undefined || options['--agent'] !== undefined, options['--save-last']].filter(Boolean);
    if (doorModes.length > 1 || (doorModes.length && options['--stop'])
      || (options['--save-last'] && (words.length || Object.keys(options).length !== 1))) throw new Stop(2, 'Choose one of --cli (with optional --shell), --shell, --serve, --page, --save-last or --stop.');
    if (options['--save-last']) {
      const root = repoRoot(cwd), store = stateFor(ports.env, root);
      const pointer=store.repo(root).last_door,descriptor=pointer?.descriptor?store.read(pointer.descriptor):null;
      if(descriptor?.originalPath)ports.captureSource(root,{tests:[descriptor.originalPath]});
      const identity = signIn(ports.gh, store, ports);
      return await (await import('./try-doors.mjs')).saveLast({ root, store, identity, ports });
    }
    if (options['--stop'] && (options['--tab'] || options['--new'] || options['--no-open'] || options['--no-wait'] || options['--app-map'] !== undefined || productMode || requestedBudget !== null)) throw new Stop(2, 'pdd simulate --stop takes only a STORY. Run pdd simulate --help.');
    if (words.length > 1) throw new Stop(2, 'pdd simulate takes one STORY.');
    const origin = runtimeOrigin(ports.env);
    if (options['--stop']) return await stopByName(context, cwd, words, origin);
    const { root, found, normalized } = localSetup(cwd, words, ports), store = stateFor(ports.env, root);
    const repoState = store.repo(root);
    if (!productMode && normalized.length && !options['--new']) {
      const prior = repoState.tries?.[oneTest(found, normalized, root, ports).path];
      if (prior?.product_setup) options = { ...options, ...productOptions(prior.product_setup) };
    }
    const productSetup = options['--product'] ? { parts: options['--parts']?.split(',').map(p => p.trim()) ?? null, journey: options['--journey'] ?? null } : null;
    const localSelected = productSetup ? [productTest(found, normalized, options['--journey'], root, ports)]
      : normalized.length ? [oneTest(found, normalized, root, ports)] : [...found.tests].sort((a, b) => a.path.localeCompare(b.path));
    const allowMissingInterfaces = hasMissingPromptInterface(root, found, entryPaths(localSelected))
      ? await probeLazyInterfaces(context, origin, store) : false;
    const checked = preflight({ root, found, selected: localSelected, allowMissingInterfaces }), rows = localRows(checked.rows);
    const refused = rows.find(row => row.state === 'refused');
    if (refused) {
      if (options['--cli'] || options['--shell'] || options['--serve'] !== undefined) throw new Stop(125, refused.refusals?.map(r => r.message || r.code).join('; ') || 'The Story input was refused.');
      line(ports.stdout, renderText({ rows: [refused], exitCode: 4 }, ports)); return 4;
    }
    let appMap = productSetup ? null : appMapFor(found, options['--app-map'], cwd, root, ports.stderr);
    if (!productSetup && options['--serve'] !== undefined && normalized.length && !options['--new']) {
      const priorTest = oneTest(found, normalized, root, ports), prior = repoState.tries?.[priorTest.path];
      if (prior) {
        const problem = tryPromptProblem(root, found, priorTest, prior, undefined, ports);
        if (problem) throw new Stop(125, `${problem} Run pdd simulate STORY --serve --new.`);
      }
    }
    const captureExtra = allowMissingInterfaces ? { allowMissingInterfaces: true } : {};
    const boundedCapture = !productSetup && loadRuntimeWorkspace({root}).configured && localSelected.length ? ports.captureSource(root, { tests: localSelected.map(item => item.path), appMap, ...captureExtra }) : null;
    let { test, selected, tab, typed } = productSetup
      ? { test: localSelected[0], selected: localSelected, tab: options['--tab'] ?? (options['--cli'] || options['--shell'] ? 'terminal' : 'screen'), typed: false }
      : simulationSelection(root, found, normalized, appMap, options, ports);
    if (productSetup && options['--shell']) options['--cli'] = true;
    const wholeRecords = productSetup || normalized.length ? [] : Object.entries(repoState.tries ?? {}).filter(([, value]) => isObject(value.simulation_scope));
    if (wholeRecords.length > 1) throw new Stop(2, 'Several whole-project simulations are saved. Stop a named Try with pdd simulate --stop STORY before opening the whole project.');
    const [recordPath, record] = wholeRecords[0] ?? [test.path, repoState.tries?.[test.path]];
    if (record && !options['--new'] && productSetup && (!record.product_setup || JSON.stringify(productSetup.parts) !== JSON.stringify(record.product_setup.parts) || Boolean(productSetup.journey) !== Boolean(record.product_setup.journey))) throw new Stop(4, 'Product selection changed; use --new explicitly.');
    const simulationScope = productSetup || normalized.length ? null : { tests: selected.map(item => item.path), appMap, appMapHash: appMap ? sha256(readFileSync(join(root, appMap))) : null };
    if (record && simulationScope && !options['--new'] && !isDeepStrictEqual(record.simulation_scope, simulationScope)) throw new Stop(2, 'This saved simulation does not contain the current whole project. Run pdd simulate --new.');
    if (wholeRecords.length && !options['--new']) test = selected.find(item => item.path === recordPath) ?? test;
    if (record && options['--new'] && recordPath !== test.path && repoState.tries?.[test.path]) throw new Stop(2, `A different saved Try uses ${test.path}. Stop it with pdd simulate --stop ${test.path} before replacing the whole-project simulation.`);
    context.product_setup = productSetup;
    context.typedForm = typed;
    context.doorMode = !!(options['--cli'] || options['--serve'] !== undefined);
    context.agentConnection = !options['--no-wait'] && !context.doorMode && ports.agentBridge !== false
      && (ports.stdout.isTTY === true || options['--agent'] !== undefined);
    if (context.agentConnection) {
      const loadDefinitions = ports.loadAgentDefinitions ?? ports.agents?.loadDefinitions;
      if (typeof loadDefinitions !== 'function') throw unboundPortError('Agent configuration port (loadAgentDefinitions) is not bound.');
      try { context.agentDefinitions = loadDefinitions({cwd:root,env:ports.env}); }
      catch (error) { throw new Stop(2,error.message); }
      if (!context.agentDefinitions.length) throw new Stop(2,'No agents are configured. Add an agent or enable defaults in agents.json.');
      if (options['--agent'] !== undefined && !context.agentDefinitions.some(d => d.name === options['--agent'] || (['codex','claude','gemini'].includes(d.id) && d.id === options['--agent']))) throw new Stop(2,'Unknown agent name. Choose a name from agents.json or an enabled default.');
    }
    Object.assign(context, { root, store, origin, visible: found.visible, appMap, cwd: realpathSync(cwd), simulationTests: selected, seedTest: { path: test.path, storyPath: test.storyPath } });
    const row = rows.find(row => row.test === test.path) ?? rows[0];
    const prepared = productSetup ? captureProductTry(root, test, options, ports) : null;
    const capture = prepared?.capture ?? (record?.simulation_scope && !options['--new']
      ? ports.captureSource(root, { ...trySourceSelection(record, recordPath), ...captureExtra })
      : boundedCapture ?? ports.captureSource(root, { tests: selected.map(item => item.path), appMap, ...captureExtra }));
    if (prepared && record?.product_parts && !options['--new'] && JSON.stringify(prepared.composition.product_parts) !== JSON.stringify(record.product_parts)) throw new Stop(4, 'The product part ownership changed. The original session is kept; use --new explicitly.');
    if (prepared) appMap = capture.appMap;
    context.appMap = appMap;
    const note = otherNote(otherFiles(capture.files, found).length);
    for (const warning of capture.warnings ?? []) line(ports.stderr, warning);
    if (record?.simulation_scope && !options['--new']) {
      const problem = !isDeepStrictEqual(record.prompt_hashes, capture.raw_prompt_hashes)
        ? 'A prompt changed or this Try has no source record.' : tryPromptProblem(root, found, test, record, capture, ports);
      if (problem) throw new Stop(normalized.length ? context.doorMode ? 125 : 4 : 2,
        normalized.length ? `${problem} Run pdd simulate --new.` : 'This saved simulation does not contain the current whole project. Run pdd simulate --new.');
    }
    if(context.agentConnection&&loadRuntimeWorkspace({root}).configured)throw new Stop(5,'Bounded agent connection is unavailable: installed CLI controls do not establish packet-only context. Use the ordinary simulator without an agent connection.');
    const identity = context.probedIdentity ?? signIn(ports.gh, context.store, ports, { exitCode: context.doorMode ? 125 : 5 });
    Object.assign(context, { capture, identity, secrets: [identity.token], startedAt: ports.now(), deadline: ports.now() + TRY_MS, lint: { request_ids: [], state: null },
      batch: null, rows, timeoutMin: TRY_MS / 60_000, agentLimit: false, head: null });
    context.folder = store.folder('tries');
    release = interruptible(context);
    let activeOwner = record?.login ?? null;
    context.auth = authSession({
      identity,
      store: context.store,
      ports,
      secrets: context.secrets,
      signInExitCode: context.doorMode ? 125 : 5,
      expectedOwnerLogin: () => activeOwner,
      ownerMismatchError: owner => new Stop(context.doorMode ? 125 : 5, `This Try belongs to ${owner}. Run: gh auth switch -u ${owner}`),
      onRefresh: next => {
        context.identity = next;
        const latestRepo = store.repo(root), current = latestRepo.tries?.[test.path];
        if (current && (!record || options['--new'] || current.id !== record.id)) {
          store.saveRepo(root, { ...latestRepo, tries: { ...latestRepo.tries, [test.path]: { ...current, login: next.login } } });
        }
      },
    });
    context.runtime = new Runtime({ origin, token: identity.token, ports, signal: context.signal, auth: context.auth });
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
      // An unavailable or ended record does not authorize a replacement setup.
      const ended = read.kind === 'missing' || read.status === 410 || ['failed', 'refused', 'unknown'].includes(answer?.state)
        || (answer?.state === 'passed' && ['stopped', 'stopping', 'unknown'].includes(answer.result?.session?.state));
      if (ended && !options['--new']) throw tryRecovery(context, test, record.id);
      if (live && !options['--new'] && (options['--app-map'] !== undefined || options['--tab'])) {
        throw new Stop(2, `A Try for "${test.title}" is already open. --app-map and --tab apply only to a new Try: run pdd simulate ${test.story} --new (it stops the open Try first).`);
      }
      if (live && (context.doorMode || context.agentConnection) && !options['--new']) {
        const problem=tryPromptProblem(root,found,test,record,capture,ports);
        if (problem) throw new Stop(context.doorMode ? 125 : 4, `${problem} Run pdd simulate STORY${options['--serve'] !== undefined ? ' --serve' : ''} --new.`);
      }
      if (answer?.state === 'passed' && answer.result?.session?.state === 'paused' && !options['--new']) {
        if (!validLink(answer.result?.url, origin, 'try')) throw new Stop(3, refusedLink(answer, origin));
        answer = await reopenTry(context, record, test); link = tryLink(answer, origin);
      }
      if (link && !options['--new']) {
        if (!record.storyPath && record.story !== test.story) throw new Stop(4, 'The original Try story changed. Restore its test file, or use --new to start a new Try.');
        context.seedTest.storyPath = record.storyPath ?? test.storyPath;
        return await showTry(context, test, link, options, record.id, true, answer?.result?.session, answer, record);
      }
      if (!link && answer?.state === 'passed' && LIVE_SESSION.has(answer.result?.session?.state) && !options['--new']) throw new Stop(3, refusedLink(answer, origin));
      // A Try that may still start or run is never made twice by accident.
      if (!ended && !options['--new']) {
        throw new Stop(3, `The last Try for "${test.title}" is not ready or its state is unknown. Run pdd simulate ${test.story} again later, or pdd simulate ${test.story} --new to stop it and make a new one.`);
      }
      if (!ended) { line(ports.stderr, 'Stopping the old Try…'); await stopTry(context, record); }
      delete repoState.tries[recordPath];
      store.saveRepo(root, repoState);
      activeOwner = null;
    }
    if(prepared){
      const version=await context.runtime.send('/v1/version',{method:'GET',headers:{'X-PDD-Features':'product-parts-v1'}},GET_MS);
      const blocked=blockingAnswer(version);
      if(blocked)throw new Stop(5,blocked);
      if(version.status===401)throw new Stop(5,AUTH_TEXT);
      if(version.unreachable)throw new Stop(5,version.unreachable);
      if(version.status!==200)throw new Stop(5,`Product support could not be read (HTTP ${version.status ?? 'unknown'}). Nothing was uploaded.`);
      if(!Array.isArray(version.json?.features) || !version.json.features.includes('product-parts-v1'))throw new Stop(5,'This interpreter needs an upgrade for whole-product Simulator support (product-parts-v1). Nothing was uploaded.');
      line(ports.stderr,`Product parts: ${prepared.composition.parts.join(', ')}. One tap: up to ${prepared.maxTapCalls} AI calls.`);
      line(ports.stderr,`Product screens: ${prepared.composition.labels.map(label=>label.title).join(', ')}. Up to ${prepared.composition.tapOperations} handler/background operations per tap, before drawing.`);
    }
    await checkLint(context, rows);
    const failedRow = rows.find(item => item.state !== 'ready');
    if (failedRow && failedRow !== row) {
      if (context.doorMode) throw new Stop(125, failedRow.refusals?.map(r => r.message || r.code).join('; ') || 'A selected Story did not pass lint.');
      if (appMap && failedRow.state === 'refused' && isAppMapSetupRefusal(context, appMap, failedRow.raw_refusals ?? failedRow.refusals ?? []))
        return trySetupRefused(context, test, appMap, failedRow.raw_refusals ?? failedRow.refusals ?? [], failedRow.report_url);
      return printTryProblem(context, failedRow);
    }
    if (context.interrupted) throw new Stop(3, 'Stopped before the Try was made. Nothing new was sent.');
    if (row.state !== 'ready') {
      if (options['--cli'] || options['--serve'] !== undefined) throw new Stop(125, row.refusals?.map(r => r.message || r.code).join('; ') || 'The Story did not pass lint.');
      if (appMap && row.state === 'refused' && isAppMapSetupRefusal(context, appMap, row.raw_refusals ?? row.refusals ?? []))
        return trySetupRefused(context, test, appMap, row.raw_refusals ?? row.refusals ?? [], row.report_url);
      return printTryProblem(context, row);
    }
    let request, verdict, reply, done;
    const setup = { request_ids: [], reservation: null };
    for (;;) {
      if (!await admission(context, 'try', setup)) throw new Stop(context.interrupted ? 3 : 5, context.interrupted ? 'Stopped before sending.' : 'The interpreter stayed busy until the Try setup wait ended. No new Try was sent.');
      request = { requestId: ports.randomUUID(), source_sha256: capture.sha256, seed: test.path, max_calls: requestedBudget ?? 400, ...(appMap ? { app_map: appMap } : {}), ...(prepared ? {product_parts:prepared.composition.product_parts} : {}),
        ...(context.serverFeatures?.includes('lazy-interfaces') ? { lazy_interfaces: true } : {}),
        tab };
      setup.request_ids.push(request.requestId);
      const registered = await recordRuntimeRequest(setup.reservation, request.requestId, slotPorts(context));
      if (registered === false) { await finishReservation(context, setup, { state: 'not_run' }); throw new Stop(3, context.interrupted ? 'Stopped before sending.' : 'Stopped before the Try was sent.'); }
      if (context.interrupted || ports.now() >= context.deadline) { await finishReservation(context, setup, { state: 'not_run' }); throw new Stop(3, context.interrupted ? 'Stopped before sending.' : 'Stopped before the Try was sent.'); }
      const uploadedSeed=capture.sources.find(file=>file.path===test.path);
      const tryRecord = { id: request.requestId, ...setup, story: test.story, storyPath: test.storyPath, title: test.title, origin, login: identity.login, source_sha256: capture.sha256, ...(!productSetup && !words.length ? { simulation_scope: { tests: selected.map(item => item.path), appMap, appMapHash: appMap ? sha256(capture.sources.find(file => file.path === appMap).bytes) : null } } : {}), seed_scenario: uploadedSeed ? JSON.parse(uploadedSeed.bytes.toString('utf8')) : test.doc, story_sha256: createHash('sha256').update(readFileSync(join(root, test.storyPath))).digest('hex'), prompt_hashes: capture.raw_prompt_hashes,
        effective_prompt_hashes:Object.fromEntries(capture.sources.filter(file=>file.path.endsWith('.prompt.md')).map(file=>[file.path,sha256(file.bytes)])),contract_references:capture.references, ...(productSetup?{product_setup:productSetup,product_parts:prepared.composition.product_parts}:{}) };
      store.saveRepo(root, { ...repoState, tries: { ...repoState.tries, [test.path]: tryRecord } });
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
      const confirmedEngine = validEngineHex(done.answer?.engine_sha);
      if (confirmedEngine) {
        const currentRepo = store.repo(root);
        if (currentRepo.tries?.[test.path]?.id === request.requestId) {
          currentRepo.tries[test.path].engine_sha = confirmedEngine;
          store.saveRepo(root, currentRepo);
        }
      }
      return await showTry(context, test, link, options, request.requestId, false, done.answer?.result?.session, done.answer, store.repo(root).tries?.[test.path]);
    }
    if (stepTimeLimit(done.answer, { steps: row.steps, secrets: context.secrets })) { applyAnswer(row, done.answer, context); return printTryProblem(context, row); }
    if (done.answer?.state === 'unknown' || (done.answer?.state === 'passed'
      && ['unknown', 'stopped', 'stopping'].includes(done.answer.result?.session?.state))) throw tryRecovery(context, test, request.requestId);
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
    if (error?.unboundPort) throw error;
    if(options['--product'] && error.code && !error.exitCode){line(ports.stderr,`${error.code}: ${cleanText(error.message)}`);return 4;}
    if (options['--cli'] || options['--serve'] !== undefined || options['--save-last']) {
      line(ports.stderr, `pdd: ${cleanText(error.message || 'The Try could not start.', context.secrets ?? [])}`);
      if (error instanceof Stop && error.formRecovery) line(ports.stderr, cleanText(error.formRecovery, context.secrets ?? []));
      return error.exitCode === 2 ? 2 : 125;
    }
    if (error instanceof Stop || error instanceof PreflightError || error instanceof RuntimeWorkspaceError) {
      line(ports.stderr, error.message);
      if (error instanceof Stop && error.formRecovery) line(ports.stderr, cleanText(error.formRecovery, context.secrets ?? []));
      return error.exitCode;
    }
    throw error;
  } finally { release();for(const lease of context.caseWriteLeases?.values()??[])lease.release(); await Promise.all([...(context.reservations ?? [])].map(reservation => releaseRuntimeSlot(reservation, { ended: false }, slotPorts(context)))); }
}

// pdd simulate --stop [STORY]: find the Try by its story name in the state record, so it works on any branch (real-user issue 14).
async function stopByName(context, cwd, words, origin) {
  const { ports } = context, root = repoRoot(cwd), store = stateFor(ports.env, root), repoState = store.repo(root);
  const entries = Object.entries(repoState.tries ?? {}), word = words[0]?.replace(/^\.\//, '');
  const names = entries.map(([path, record]) => record.story ?? basename(path, '.json')).join(', ') || 'none';
  const hits = word === undefined ? entries : entries.filter(([path, record]) => [record.storyPath, record.story, path, basename(path, '.json')].includes(word));
  if (hits.length !== 1) {
    throw new Stop(2, word !== undefined ? `No open Try for "${cleanText(word)}". Open Try links: ${names}.`
      : entries.length ? `Name the Try to stop. Open Try links: ${names}.` : 'No open Try in this repository.');
  }
  const [path, record] = hits[0], title = record.title ?? record.story ?? path;
  Object.assign(context, { root, store, origin });
  const identity = signIn(ports.gh, store, ports);
  context.secrets = [identity.token];
  context.auth = authSession({
    identity,
    store,
    ports,
    secrets: context.secrets,
    expectedOwnerLogin: record.login ?? null,
    ownerMismatchError: owner => new Stop(5, `This Try belongs to ${owner}. Run: gh auth switch -u ${owner}`),
  });
  context.runtime = new Runtime({ origin: record.origin ?? origin, token: identity.token, ports, auth: context.auth });
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
  if (lint.kind === 'not_run' || lint.kind === 'stop') throw new Stop(5, `${lint.note.message}${lint.note.code ? ` (${lint.note.code})` : ''}`);
  if (lint.kind === 'refused') { Object.assign(rows[0], { state: 'refused', phase: 'lint', refusals: [lint.refusal], raw_refusals: [lint.refusal] }); return; }
  if (context.doorMode && lint.kind === 'answer' && lint.answer?.state === 'refused' && !isObject(lint.answer.result?.report?.program)) {
    const refusal = lint.answer.result?.refusals?.[0] ?? lint.answer.result?.report?.refusal;
    throw new Stop(125, refusal?.reason || refusal?.message || refusal?.code || 'The interpreter refused lint.');
  }
  // A Try uses AI calls, so it passes the same lint gate as a check.
  if (rows.every(row => lintAdmits(lint.answer, row, context.capture, context.appMap))) { for (const text of lintDiagnostics(context, lint.answer, rows)) line(context.ports.stderr, text); return; }
  const verdicts = judgeLint(lint.answer, rows, context.root, context.visible, context.secrets, context.capture, context.appMap);
  const report = isObject(lint.answer?.result?.report?.refusal) ? lint.answer.result.report.refusal : null;
  const reportUrl = validLink(cleanText(lint.answer?.report_url, context.secrets), context.origin, 'report');
  for (const [row, outcome] of verdicts) if (outcome.state === 'refused') {
    const rawRefusals = outcome.rawRefusals.map(item => ({
      ...item,
      ...(report?.code === item.code ? { reason: item.reason ?? report.reason, fix: item.fix ?? report.fix } : {}),
    }));
    Object.assign(row, { state: 'refused', phase: 'lint', refusals: outcome.refusals, raw_refusals: rawRefusals, report_url: reportUrl });
  }
  if ([...verdicts.values()].some(outcome => outcome.state === 'unknown')) throw new Stop(3, 'The lint result is unknown, so pdd made no Try link. Run pdd simulate again later.');
  // A lint that ended without a pass for the test is final: nothing changes by waiting.
  const ended = [...verdicts.values()].find(outcome => outcome.state === 'not_run');
  if (ended) {
    for (const row of rows.filter(row => row.compatibility)) {
      line(context.ports.stderr, `Compatibility (${cleanText(row.test, context.secrets)}): ${JSON.stringify(row.compatibility, null, 2)}`);
      line(context.ports.stderr, `Client advice: ${JSON.stringify(row.client_advice)}`);
    }
    throw new Stop(5, `No lint pass for this test (${ended.reason ?? ended.message}), so pdd made no Try link.`);
  }
}

// A refused Try setup is not a check (runtime team, Oct 27): two plain lines with what was refused, why and the fix; no table.
const APP_MAP_RULES = { 'ambiguous-handler': 'on one screen, all taps of one kind must match by the same key',
  'template-reference-schema': 'a field that gets a value from the screen ($ref) must be a plain {"type": "string"}',
  'invalid-after-step': 'an after step has the wrong fields' };
const AFTER_STEP_SHAPE_HELP = 'Write each after step as {"handler": {"prompt_path": "...", "operation": "..."}, "input": {...}, "bind": "/field"} (RUNBOOK §13).';
const GENERIC_REFUSAL = /^The runtime refused this (?:job|run)\b/;
const isAppMapCode = code => Object.hasOwn(APP_MAP_RULES, code) || code === 'invalid-clipboard-action' || /^(?:after|app-map|invalid-app-map)-/.test(code);
function normalizeTryRefusals(context, refusals) {
  const text = value => typeof value === 'string' ? cleanText(value, context.secrets) : '';
  const items = (refusals.length ? refusals : [{ code: 'refused' }]).map(item => {
    const code = text(item.code) || 'refused';
    const file = text(item.file) || text(item.path);
    const at = text(item.at) || text(item.pointer);
    const rawWhere = text(item.where);
    const where = !rawWhere ? [file, at].filter(Boolean).join(' ') : file && rawWhere === file && at ? `${file} ${at}` : rawWhere;
    return {
      code,
      file: text(item.file),
      path: text(item.path),
      section: text(item.section),
      reason: [text(item.reason), APP_MAP_RULES[code], text(item.engine_message), GENERIC_REFUSAL.test(text(item.message)) ? '' : text(item.message)].find(Boolean),
      fix: text(item.fix),
      where,
    };
  });
  const specificTargets = new Set(items.filter(item => item.code !== 'lint-refused').map(item => item.file || item.path).filter(Boolean));
  return items.filter(item => !(item.code === 'lint-refused' && specificTargets.has(item.file || item.path)));
}
function isAppMapSetupRefusal(context, appMap, refusals) {
  if (!appMap) return false;
  return normalizeTryRefusals(context, refusals).some(item => item.file === appMap || item.path === appMap || item.section === appMap
    || /app[-_]map/i.test(item.section) || isAppMapCode(item.code));
}
function trySetupRefused(context, test, appMap, refusals, reportUrl) {
  if (context.doorMode) throw new Stop(125, [...new Set(refusals.map(item => item.reason || item.engine_message || item.message || item.code).filter(Boolean))].join('; ') || 'The interpreter refused this Try.');
  const items = normalizeTryRefusals(context, refusals);
  const mapped = !!appMap && items.some(item => item.file === appMap || item.path === appMap || item.section === appMap
    || /app[-_]map/i.test(item.section) || isAppMapCode(item.code));
  const why = [...new Set(items.map(item => `${item.reason ? `${item.code}: ${item.reason}` : item.code}${item.where ? `; at ${item.where}` : ''}`))].join('; '), fix = items.find(item => item.fix)?.fix;
  const needsAfterHelp = items.some(item => item.code === 'invalid-after-step' && !/"handler"\s*:\s*\{|\bprompt_path\b/.test(`${item.reason ?? ''} ${item.fix ?? ''}`));
  const again = `run ${tryCommand(test,context.product_setup,' --new')}.`;
  const target = context.product_setup ? 'the authored part maps or product/plan.md' : appMap;
  line(context.ports.stdout, `The Try could not start: ${mapped ? 'the app map was refused' : 'the server refused it'} (${why}).`);
  line(context.ports.stdout, fix ? `${fix}${needsAfterHelp ? ` ${AFTER_STEP_SHAPE_HELP}` : ''} Then ${again}`
    : needsAfterHelp ? `${mapped ? `Fix ${target}. ` : ''}${AFTER_STEP_SHAPE_HELP} Then ${again}`
    : mapped ? `Fix ${target} (RUNBOOK §13), then ${again}`
    : `Fix what it names, then ${again}${reportUrl ? ` Details: ${reportUrl}` : ''}`);
  return 4;
}

function printTryProblem(context, row) {
  if (context.doorMode) throw new Stop(125, row.time_limit ? `${row.time_limit.message} ${row.time_limit.fix}` : row.refusals?.map(r => r.message || r.code).join('; ') || `The Try could not start (${row.state}).`);
  const exitCode = context.ports.exitCodeFor([row]);
  context.ports.stdout.write(renderText({ rows: [row], exitCode, secrets: context.secrets, recovery: `pdd simulate ${row.story}` }, context.ports));
  return exitCode;
}

const validSha256Hex = value => typeof value === 'string' && /^[0-9a-f]{64}$/i.test(value) ? value.toLowerCase() : null;
const validEngineHex = value => typeof value === 'string' && /^[0-9a-f]{8,40}$/i.test(value) ? value.toLowerCase() : null;

async function showTry(context, test, link, options, tryId, reused = false, session, answer = null, record = null) {
  if (context.typedForm) line(context.ports.stderr, "This Story's operation takes typed input, so it opens on the Form tab.");
  const budget = Number.isSafeInteger(session?.max_calls) && session.max_calls > 0 && Number.isSafeInteger(session?.remaining_calls)
    && session.remaining_calls >= 0 && session.remaining_calls <= session.max_calls
    ? `Try budget ${session.max_calls} calls; ${session.remaining_calls} remaining. You are charged only for calls that run.`
    : 'The interpreter did not report this Try’s budget.';
  const stream = options['--cli'] || options['--serve'] !== undefined ? context.ports.stderr : context.ports.stdout;
  line(stream, budget);
  const sourceSha = validSha256Hex(answer?.source_sha256) ?? validSha256Hex(record?.source_sha256) ?? (!reused ? validSha256Hex(context.capture?.sha256) : null);
  const engineSha = validEngineHex(answer?.engine_sha) ?? validEngineHex(record?.engine_sha);
  if (sourceSha) line(stream, `Try source: sha256:${sourceSha}${engineSha ? `; engine: ${engineSha}` : ''}`);
  if (options['--cli'] || options['--serve'] !== undefined) {
    const doors = await import('./try-doors.mjs');
    return options['--cli'] ? doors.openCli(context, test, tryId, options) : (await import('./try-http.mjs')).openServe(context, test, tryId, options);
  }
  const { ports } = context, ends = reused ? `It keeps its original 24-hour expiry; stop it with: pdd simulate --stop ${test.story}`
    : `It ends in 24 hours, or with: pdd simulate --stop ${test.story}`;
  let bridge = null, answers = null;
  try {
    if (context.agentConnection) {
      const finalRuntime = new Runtime({ origin: context.origin, token: context.identity.token, ports, auth: context.auth });
      context.agentFinalSend = finalRuntime.send.bind(finalRuntime);
      try {
        const seamPorts = {
          redaction: ports.redaction,
          redactSecrets: ports.redactSecrets,
          loadAgentDefinitions: ports.loadAgentDefinitions,
          discoverAgents: ports.discoverAgents,
          askAgent: ports.askAgent,
          evidenceEligibility: ports.evidenceEligibility ?? ports.readEvidenceEligibility,
          guidePorts: ports.guidePorts,
          findTests: ports.findTests,
          captureSource: ports.captureSource,
          isStoryPath: ports.isStoryPath,
          hasAcceptance: ports.hasAcceptance,
          matchTests: ports.matchTests,
          orphanSummary: ports.orphanSummary,
        };
        bridge = await (ports.agentBridge
          ? ports.agentBridge(context, test, tryId, options, link)
          : (await import('./agent-chat.mjs')).createAgentBridge(context, test, tryId, options, link, seamPorts));
      }
      catch (error) { if (error?.unboundPort) throw error; throw new Stop(5, cleanText(error.message || 'Your agent could not connect.', context.secrets)); }
    }
    if (!options['--no-open'] && await ports.openUrl(bridge?.url ?? link)) line(ports.stdout, `Try ready for "${test.title}": ${link} (open in your browser). ${ends}`);
    else {
      line(ports.stdout, `Try ready for "${test.title}": ${link}`);
      line(ports.stdout, `${options['--no-open'] ? '' : 'pdd could not open a browser. Open the link yourself. '}Anyone with the link can use it. ${ends}`);
      if (bridge) line(ports.stdout, `Owner agent chat link (private; do not share): ${bridge.url}`);
    }
    if (!bridge) { await watchSavedTests(context, tryId, !options['--no-wait'] && ports.interactive, test.story); return 0; }
    answers = ports.interactive ? ports.lineReader(ports.stdin) : null;
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
function stepsArray(text, arrayName = 'steps') {
  let depth = 0, key = null, index = 0;
  const skipString = at => { let i = at + 1; while (i < text.length && text[i] !== '"') i += text[i] === '\\' ? 2 : 1; return i + 1; };
  while (index < text.length) {
    const char = text[index];
    if (char === '"') {
      const end = skipString(index);
      if (depth === 1 && /^\s*:/.test(text.slice(end))) key = JSON.parse(text.slice(index, end));
      index = end; continue;
    }
    if (char === '[' && depth === 1 && key === arrayName) {
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

// Preserve each received object's exact JSON bytes independently of the envelope.
function receivedCaseBytes(text,index){
  const range=typeof text==='string'?stepsArray(text,'tests'):null;if(!range)return undefined;
  let start=range[0]+1,depth=0,quoted=false,escaped=false,atIndex=0;
  for(let i=start;i<range[1]-1;i++){const char=text[i];if(quoted){if(escaped)escaped=false;else if(char==='\\')escaped=true;else if(char==='"')quoted=false;continue;}if(char==='"'){quoted=true;continue;}if(char==='{'||char==='[')depth++;else if(char==='}'||char===']')depth--;else if(char===','&&depth===0){if(atIndex++===index)return text.slice(start,i).trim();start=i+1;}}
  return atIndex===index?text.slice(start,range[1]-1).trim():undefined;
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

const NOT_TEST_FILES = /^(?:\..*|package(?:-lock)?\.json|tsconfig(?:\..+)?\.json|jsconfig\.json|composer\.json|deno\.json|bower\.json|app-map\.json|.+\.config\.json)$/;
const inRepo = (realRoot, path) => { try { return realpathSync(join(realRoot, path)) === join(realRoot, path); } catch { return false; } };

// Received case custody and publication. All filesystem/process/time effects are
// bound here; tests may replace the same ports used by the native adapter.
const caseNativeFiles={lstat:lstatSync,read:readFileSync,open:openSync,write:writeFileSync,close:closeSync,sync:fsyncSync,stat:fstatSync,mkdir:mkdirSync,list:readdirSync,rename:renameSync,unlink:unlinkSync,link:linkSync,realpath:realpathSync};
const caseLeases=new WeakMap();
function casePorts(ports={}){const findTestsBound=ports.findTests??(input=>findTests(input,ports)),captureSourceBound=ports.captureSource??((root,options)=>captureSource(root,options,ports));return{files:ports.files??caseNativeFiles,env:ports.env??process.env,hash:ports.hash??sha256,nonce:ports.randomUUID??randomUUID,now:ports.now??Date.now,pid:ports.pid??process.pid,host:ports.host??hostname(),isAlive:ports.isAlive??(pid=>{try{process.kill(pid,0);return true;}catch(e){return e.code==='ESRCH'?false:null;}}),sleep:ports.sleep??((ms,signal)=>new Promise(done=>{if(signal?.aborted)return done();const finish=()=>{clearTimeout(timer);signal?.removeEventListener('abort',finish);done();};const timer=setTimeout(finish,ms);signal?.addEventListener('abort',finish,{once:true});})),fault:ports.fault??(()=>{}),findTests:findTestsBound,captureSource:captureSourceBound,isStoryPath:ports.isStoryPath,hasAcceptance:ports.hasAcceptance,matchTests:ports.matchTests,orphanSummary:ports.orphanSummary};}
function caseStat(p,path){try{return p.files.lstat(path);}catch(e){if(e.code==='ENOENT')return null;throw e;}}
function caseStateDirectory(env,root,p){
  const configured=resolve(env.PDD_STATE_DIR||join(env.HOME||homedir(),'.pdd','runtime'));
  if(caseStat(p,configured)?.isSymbolicLink())throw Error('unsafe or missing local path');
  const missing=[];let current=configured,canonical;
  for(;;){try{canonical=p.files.realpath(current);break;}catch(e){if(e.code!=='ENOENT')throw e;const parent=dirname(current);if(parent===current)throw e;missing.push(basename(current));current=parent;}}
  const directory=join(canonical,...missing.reverse());
  if(inside(directory,p.files.realpath(root)))throw new Stop(2,'PDD_STATE_DIR is inside this repository. pdd keeps run state outside the repo. Choose another folder.');
  return directory;
}
function caseSafe(p,path,{directory=false,create=false}={}){
  const full=resolve(path),parts=full.split(sep).filter(Boolean);let at=sep;
  for(let i=0;i<parts.length;i++){at=join(at,parts[i]);const dir=i<parts.length-1||directory;let st=caseStat(p,at);
    if(!st&&create&&dir){try{p.files.mkdir(at,{mode:0o700});}catch(e){if(e.code!=='EEXIST')throw e;}st=p.files.lstat(at);}
    if(!st||st.isSymbolicLink()||(dir?!st.isDirectory():!st.isFile()))throw Error('unsafe or missing local path');
  }return full;
}
function caseSyncDir(p,path){const fd=p.files.open(path,constants.O_RDONLY|constants.O_DIRECTORY|constants.O_NOFOLLOW);try{p.files.sync(fd);}finally{p.files.close(fd);}}
function caseRead(p,path){caseSafe(p,path);const fd=p.files.open(path,constants.O_RDONLY|constants.O_NOFOLLOW|constants.O_NONBLOCK);try{const st=p.files.stat(fd);if(!st.isFile()||st.size>32*1024*1024)throw Error('unsafe case record');return p.files.read(fd,'utf8');}finally{p.files.close(fd);}}
function caseWrite(p,path,text,{exclusive=false}={}){
  caseSafe(p,dirname(path),{directory:true,create:true});
  // Exclusive link publication refuses every existing destination. A separate
  // leaf probe races with normal owner release and cannot add write authority.
  if(!exclusive&&caseStat(p,path))caseSafe(p,path);
  const temp=`${path}.${p.pid}.${p.nonce()}.tmp`;let fd,owned;
  try{fd=p.files.open(temp,constants.O_WRONLY|constants.O_CREAT|constants.O_EXCL|constants.O_NOFOLLOW,0o600);p.files.write(fd,text);p.files.sync(fd);owned=p.files.stat(fd);p.files.close(fd);fd=undefined;
    if(exclusive)p.files.link(temp,path);else p.files.rename(temp,path);
    caseSyncDir(p,dirname(path));
  }finally{if(fd!==undefined)p.files.close(fd);try{const remaining=caseStat(p,temp);if(owned&&remaining?.ino===owned.ino&&remaining.dev===owned.dev)p.files.unlink(temp);}catch(e){if(e.code!=='ENOENT')throw e;}}
}
function caseArea(root,p,{create=true}={}){
  const dir=caseStateDirectory(p.env,root,p),area=join(dir,'case-import');
  if(create)caseSafe(p,area,{directory:true,create:true});else if(caseStat(p,area))caseSafe(p,area,{directory:true});
  return area;
}
const caseResult=(record,state,reason,extra={})=>({state,path:record.target??null,pendingId:record.pendingId,reason,recoveryPath:record.recoveryPath,...extra});
function caseMessage(result){return result.state==='committed'?`${result.duplicate?'already saved to':'added to'} ${result.path}${result.steps?.length?' as step '+result.steps.join(', '):''}`:`not added: ${result.reason}. Case retained at ${result.recoveryPath} (pending ${result.pendingId}).`;}
const caseOutcome=result=>({kind:'case',result,message:caseMessage(result)});
function retainCase(root,saved,options,p){
  const original=options.seedTest??{path:saved?.original_path,storyPath:saved?.story_path??saved?.test?.story_path};
  const identity={root,session:options.sessionId??saved?.session_id??null,action:saved?.id??null,original};
  const raw=options.rawBytes===undefined?JSON.stringify(saved):Buffer.from(options.rawBytes).toString('utf8');
  const unsafeNumbers=[];try{JSON.parse(raw,(_key,value,context)=>{if(typeof value==='number'&&context?.source&&(!Number.isFinite(value)||!Number.isSafeInteger(value)&&/^-?[0-9]+$/.test(context.source)))unsafeNumbers.push(context.source);return value;});}catch{}
  const payload=JSON.stringify({saved,identity,isolated:options.isolated===true,...(unsafeNumbers.length?{unsafeNumbers}:{})});
  const id=p.hash(Buffer.from(JSON.stringify(identity))),variant=p.hash(Buffer.from(payload));
  const area=caseArea(root,p),dir=join(area,id);caseSafe(p,dir,{directory:true,create:true});
  const recoveryPath=join(dir,`${variant}.received.json`),pendingId=`${id}.${variant}`;
  const record={schema_version:'pdd.case-import.v1',pendingId,recoveryPath,identity,saved,raw,target:original.path??null,isolated:options.isolated===true};
  try{caseWrite(p,recoveryPath,JSON.stringify(record),{exclusive:true});}catch(e){if(e.code!=='EEXIST')throw e;const previous=JSON.parse(caseRead(p,recoveryPath));if(!isDeepStrictEqual(previous.saved,saved)||!isDeepStrictEqual(previous.identity,identity))throw Error('received identity collision');if(previous.raw!==raw){const observation=join(dir,variant+'.raw-'+p.hash(Buffer.from(raw))+'.json');try{caseWrite(p,observation,raw,{exclusive:true});}catch(extra){if(extra.code!=='EEXIST')throw extra;}}}
  p.fault('received',record);return record;
}
function readPending(root,pendingId,p){
  if(typeof pendingId!=='string'||!/^([0-9a-f]{64})\.([0-9a-f]{64})$/.test(pendingId))throw Error('invalid pending case identity');
  const [id,variant]=pendingId.split('.'),path=join(caseArea(root,p,{create:false}),id,`${variant}.received.json`);
  const record=JSON.parse(caseRead(p,path));if(record.identity?.root!==root||record.pendingId!==pendingId||record.recoveryPath!==path)throw Error('pending case belongs to another repository');return record;
}
// A handoff is trusted local input. It is never derived from a received payload.
export async function acquireCaseWriteOwnership({root,testPath,handoff,signal},ports={}){
  const p=casePorts(ports);root=p.files.realpath(root);
  if(signal?.aborted)throw Error('case save cancelled');
  if(!handoff||!['closed-editor','editor-lease'].includes(handoff.kind)||handoff.testPath!==testPath||handoff.closed===false||handoff.kind==='editor-lease'&&typeof handoff.release!=='function')throw Error(`Close the editor for ${testPath} and explicitly hand over that file before applying its pending cases`);
  requireRuntimePath(loadRuntimeWorkspace({root}),{path:testPath,from:'Case destination'});
  const area=caseArea(root,p),path=join(area,`${p.hash(Buffer.from(root+'\0'+testPath))}.lock`),owner={pid:p.pid,host:p.host,token:p.nonce(),root,testPath};
  const started=p.now(),maxWait=ports.maxWaitMs??2000;let lockStat;
  for(;;){
    if(signal?.aborted)throw Error('case save cancelled');
    try{caseWrite(p,path,JSON.stringify(owner),{exclusive:true});lockStat=p.files.lstat(path);break;}
    catch(e){if(e.code!=='EEXIST')throw e;const before=caseStat(p,path);let other,disappeared=!before;
      if(before)try{other=JSON.parse(caseRead(p,path));}catch(readError){
        // A supported owner can release between the collision, stat and read.
        // Only a missing lock with safe ancestors permits another atomic try.
        if(readError.code!=='ENOENT'&&readError.message!=='unsafe or missing local path')throw Error('case ownership is uncertain; keep pending');
        caseSafe(p,dirname(path),{directory:true});
        if(caseStat(p,path))throw Error('case ownership is uncertain; keep pending');
        disappeared=true;
      }
      if(!disappeared&&other.host===p.host&&Number.isSafeInteger(other.pid)&&p.isAlive(other.pid)===false){
        // A separate exclusive recovery guard serializes abandoned-owner removal.
        const guard=path+'.recover';let owned=false;
        try{caseWrite(p,guard,JSON.stringify(owner),{exclusive:true});owned=true;const now=caseStat(p,path);if(now&&now.ino===before?.ino&&now.dev===before?.dev&&caseRead(p,path)===JSON.stringify(other))p.files.unlink(path);}
        catch(recovery){
          if(recovery.code!=='EEXIST')throw recovery;
          caseSafe(p,dirname(guard),{directory:true});
          const present=caseStat(p,guard);
          if(present&&(present.isSymbolicLink()||!present.isFile()))throw Error('unsafe or missing local path');
        }finally{if(owned)p.files.unlink(guard);}
        // Recovery contention must reach the same deadline and cancellable wait
        // as a live owner, even if the guard disappeared after the collision.
      }
      if(p.now()-started>=maxWait)throw Error('another saver or editor owns this file; keep pending');
      await p.sleep(Math.min(25,maxWait),signal);
    }
  }
  const record={root,testPath,p,path,owner,lockStat,released:false};
  const lease={release(){if(record.released)return;record.released=true;try{const now=caseStat(p,path);if(now?.ino===lockStat.ino&&now.dev===lockStat.dev&&caseRead(p,path)===JSON.stringify(owner)){p.files.unlink(path);caseSyncDir(p,dirname(path));}}finally{handoff.kind==='editor-lease'&&handoff.release();}}};
  caseLeases.set(lease,record);
  if(signal?.aborted){lease.release();throw Error('case save cancelled');}return Object.freeze(lease);
}
function ownedCaseLease(lease,root,path){const record=caseLeases.get(lease);if(!record||record.released||record.root!==root||record.testPath!==path)throw Error('supported ownership for the exact original test is required');const now=caseStat(record.p,record.path);if(!now||now.ino!==record.lockStat.ino||now.dev!==record.lockStat.dev||caseRead(record.p,record.path)!==JSON.stringify(record.owner))throw Error('case write ownership was lost');return record;}
function knownEndWorld(doc){
  if(!doc.steps.length)return doc.initial_world;
  const values=(doc.steps.at(-1)?.checks??[]).filter(c=>c.target==='world'&&c.path===''&&c.op==='equals').map(c=>c.value);
  if(!values.length||!values.every(v=>isDeepStrictEqual(v,values[0])))return undefined;
  if(JSON.stringify(values[0]).includes('"$step_result"'))return undefined;return values[0];
}
function prepareCase(root,record,p){
  const saved=record.saved,test=saved?.test,story=record.identity.original.storyPath,path=record.target;
  let unsafeNumber=false;const numeric=text=>{const match=/^(-?)([0-9]+)(?:\.([0-9]+))?(?:[eE]([+-]?[0-9]+))?$/.exec(text);if(!match)return text;let digits=(match[2]+(match[3]??'')).replace(/^0+/,'');if(!digits)return '0';const zeros=/0*$/.exec(digits)[0].length;return match[1]+digits.slice(0,digits.length-zeros)+'e'+(BigInt(match[4]??0)-BigInt((match[3]??'').length)+BigInt(zeros));};
  try{JSON.parse(record.raw,(_key,value,context)=>{if(typeof value==='number'&&(!Number.isFinite(value)||context?.source&&numeric(context.source)!==numeric(String(value))))unsafeNumber=true;return value;});}catch{}
  if(unsafeNumber)throw Error('received numeric expectation needs lossless handling; exact original bytes retained');
  if(!isObject(test)||test.schema_version!==TEST_SCHEMA||!Array.isArray(test.steps)||!test.steps.length||typeof story!=='string'||test.story_path!==story||typeof path!=='string')throw Error('the exact original test association or complete received scenario is unavailable');
  const workspace=loadRuntimeWorkspace({root});requireRuntimePath(workspace,{path,from:'Original selected test'});requireRuntimePath(workspace,{path:story,from:path});
  const found=p.findTests({root}),original=found.tests.find(t=>t.path===path&&t.storyPath===story&&t.doc?.story_path===story);
  if(!original?.doc||original.doc.schema_version!==TEST_SCHEMA||!Array.isArray(original.doc.steps)||NOT_TEST_FILES.test(basename(path)))throw Error(`the original test ${path} is missing or no longer belongs to ${story}. Restore it before importing the case`);
  if(original.criteriaRefusal)throw Error(original.criteriaRefusal.message);
  caseSafe(p,join(root,path));caseSafe(p,join(root,story));
  const text=caseRead(p,join(root,path)),doc=JSON.parse(text);
  if(!isDeepStrictEqual(doc,original.rawDoc??original.doc)||(original.storySource!==undefined&&caseRead(p,join(root,story))!==original.storySource))throw Error('the original test changed while being inspected');
  if(record.isolated){
    if(!isObject(test.initial_world)||test.steps.length!==1||(!isDeepStrictEqual(test.criteria,original.doc.criteria)&&!isDeepStrictEqual(test.criteria,doc.criteria))||!isDeepStrictEqual(test.simulation??{},doc.simulation??{})||!isDeepStrictEqual(test.context??[],doc.context??[]))throw Error('recorded case lacks original criteria, simulation, context or confirmed starting world');
    const id=slug(saved.id);if(!id)throw Error('case has no safe identity');
    const variant=`tests/${original.story}.try-${id}.json`;requireRuntimePath(workspace,{path:variant,from:path});
    const isolatedTest=Array.isArray(test.criteria)&&test.criteria.every(c=>isObject(c)&&typeof c.id==='string'&&typeof c.text==='string')?test:{...test,criteria:original.doc.criteria};
    return{path:variant,before:null,after:JSON.stringify(isolatedTest,null,2)+'\n',steps:[test.steps[0].step_id],isolated:true};
  }
  const beforeWorld=Object.hasOwn(saved,'world_before')?saved.world_before:Object.hasOwn(test,'initial_world')?test.initial_world:undefined;
  if(beforeWorld===undefined||!isDeepStrictEqual(knownEndWorld(doc),beforeWorld))throw Error('confirmed starting world does not match the original test continuation');
  const byText=new Map((original.doc.criteria??[]).map(c=>[c.text,c.id])),savedText=new Map((test.criteria??[]).map(c=>[c.id,c.text]));
  let after=text,current=doc;const steps=[];
  for(const raw of test.steps){if(!isObject(raw)||!Array.isArray(raw.checks)||!raw.checks.length)throw Error('case has no mapped checks');const checks=raw.checks.map(c=>({...c,criterion_id:byText.get(savedText.get(c.criterion_id))}));if(checks.some(c=>!c.criterion_id))throw Error(`"${cleanText(saved.name??saved.id)}" checks a criterion that ${path} does not have; keep expected values and repair the mapping`);const taken=new Set(current.steps.map(s=>s.step_id));let id=slug(raw.step_id)||slug(saved.id)||'saved-case';for(let n=2,base=id;taken.has(id);n++)id=`${base}-${n}`;const step={...raw,step_id:id,checks};after=appendStep(after,current,step);current={...current,steps:[...current.steps,step]};steps.push(id);}
  return{path,before:text,after,steps};
}
function caseImportState(root,record,p,{inspect=false,reconcile=false,reason='reconciled published case'}={}){
  if(p.files.list(dirname(record.recoveryPath)).filter(x=>x.endsWith('.received.json')).length!==1)
    return{result:caseResult(record,'conflict','this identity has different received payloads; both are retained')};
  const journal=record.recoveryPath.replace('.received.json','.transaction.json');
  if(!caseStat(p,journal))return{};
  const transaction=JSON.parse(caseRead(p,journal));
  if(transaction.state==='committed')return{result:caseResult(record,'committed','already applied',{path:transaction.path,duplicate:true})};
  // Only a conflict recorded before publication retains the observed baseline
  // in its history. Older conflicts lost their phase, so absence is uncertain.
  if(transaction.state==='conflict'&&!transaction.observed?.includes(transaction.before))
    return{result:caseResult(record,'conflict','authored revision changed after preparation; received and observed revisions retained')};
  if((inspect||reconcile)&&transaction.after!==undefined){
    requireRuntimePath(loadRuntimeWorkspace({root}),{path:transaction.path,from:'Case reconciliation'});
    const target=join(root,transaction.path),actual=caseStat(p,target)?caseRead(p,target):null;
    if(actual===transaction.after){
      if(!reconcile)return{transaction,published:true,reconciliationOnly:transaction.state==='publishing'};
      caseSyncDir(p,dirname(target));caseWrite(p,journal,JSON.stringify({...transaction,state:'committed'}));
      return{result:caseResult(record,'committed',reason,{path:transaction.path,steps:transaction.steps})};
    }
    if(reconcile&&actual!==transaction.before){
      caseWrite(p,journal,JSON.stringify({...transaction,state:'conflict',observed:[...(transaction.observed??[]),...(transaction.state==='prepared'?[transaction.before]:[]),actual]}));
      return{result:caseResult(record,'conflict','authored revision changed after preparation; received and observed revisions retained')};
    }
    if(transaction.state==='publishing'){
      if(!reconcile)return{transaction,reconciliationOnly:true};
      return{result:caseResult(record,'pending','publication outcome is uncertain; retain the case without reapplying it')};
    }
  }
  return{transaction};
}
function applyPendingCaseSync({root,pendingId,writeOwnership,signal},ports={},publicationGuard){
  const p=casePorts(ports);root=p.files.realpath(root);const record=readPending(root,pendingId,p),journal=record.recoveryPath.replace('.received.json','.transaction.json');
  let temp,tempOwned,lease,transaction;const persist=value=>caseWrite(p,journal,JSON.stringify(value));
  try{
    lease=ownedCaseLease(writeOwnership,root,record.target);
    const known=caseImportState(root,record,p,{reconcile:true});
    if(known.result)return known.result;
    transaction=known.transaction;
    if(signal?.aborted)return caseResult(record,'pending','case save cancelled');
    publicationGuard?.();
    const prepared=prepareCase(root,record,p);transaction={...prepared,state:'prepared',pendingId};persist(transaction);p.fault('prepared',record);
    if(signal?.aborted)return caseResult(record,'pending','case save cancelled');
    ownedCaseLease(writeOwnership,root,record.target);
    requireRuntimePath(loadRuntimeWorkspace({root}),{path:prepared.path,from:'Case publication'});
    const target=join(root,prepared.path);caseSafe(p,dirname(target),{directory:true,create:prepared.isolated});
    const st=caseStat(p,target),before=st?caseRead(p,target):null;
    if(before!==prepared.before){if(prepared.isolated&&before===prepared.after){persist({...transaction,state:'committed'});return caseResult(record,'committed','already saved',{path:prepared.path,duplicate:true});}persist({...transaction,state:'conflict',observed:[prepared.before,before]});return caseResult(record,'conflict','authored revision changed before publication');}
    temp=join(dirname(target),`.pdd-case-${p.nonce()}.tmp`);caseWrite(p,temp,prepared.after,{exclusive:true});tempOwned=caseStat(p,temp);p.fault('before-publication',record);
    ownedCaseLease(writeOwnership,root,record.target);
    const latest=caseStat(p,target)?caseRead(p,target):null;
    if(latest!==prepared.before){persist({...transaction,state:'conflict',observed:[prepared.before,latest]});return caseResult(record,'conflict','authored revision changed during preparation');}
    if(signal?.aborted)return caseResult(record,'pending','case save cancelled');
    publicationGuard?.();
    // From this boundary onward, reconcile while custody remains held even on abort.
    transaction={...transaction,state:'publishing'};persist(transaction);
    if(prepared.isolated)p.files.link(temp,target);else p.files.rename(temp,target);
    p.fault('published',record);caseSyncDir(p,dirname(target));
    if(caseRead(p,target)!==prepared.after)throw Error('published target changed; reconciliation required');
    p.fault('before-ledger',record);persist({...transaction,state:'committed'});p.fault('committed',record);
    return caseResult(record,'committed','applied',{path:prepared.path,steps:prepared.steps});
  }catch(error){
    if(error?.unboundPort)throw error;
    if(transaction?.state==='publishing'){
      try{const known=caseImportState(root,record,p,{reconcile:true,reason:'reconciled after publication'});if(known.result?.state==='committed')return known.result;}catch(reconcileError){if(reconcileError?.unboundPort)throw reconcileError;/* durable prepared record retains custody */}
    }
    return caseResult(record,'pending',cleanText(error.message??error));
  }finally{if(temp){try{const remaining=caseStat(p,temp);if(tempOwned&&remaining?.ino===tempOwned.ino&&remaining.dev===tempOwned.dev)p.files.unlink(temp);}catch(e){if(e.code!=='ENOENT'){} }} }
}
export async function applyPendingCase(input,ports={}){return applyPendingCaseSync(input,ports);}
export const saveDoorCaseResult=(root,saved,options={})=>{
  const p=casePorts(options.ports??{env:options.env});let record;
  try{root=p.files.realpath(root);record=retainCase(root,saved,options,p);
    const known=caseImportState(root,record,p);if(known.result)return caseOutcome(known.result);
    if(options.writeOwnership)return caseOutcome(applyPendingCaseSync({root,pendingId:record.pendingId,writeOwnership:options.writeOwnership,signal:options.signal},options.ports??{env:options.env}));
    let reason;try{prepareCase(root,record,p);}catch(error){if(error?.unboundPort)throw error;reason=error.message;}
    const result=caseResult(record,'pending',options.signal?.aborted?'case save cancelled':reason??'close the editor for the named original test and apply the retained case with supported ownership');return caseOutcome(result);}
  catch(error){if(error?.unboundPort)throw error;return{kind:'failure',message:`not added: durable case receipt failed (${cleanText(error.message??error)}).${record?' Recovery: '+record.recoveryPath:''}`};}
};
export const saveDoorCase=(root,saved,options={})=>saveDoorCaseResult(root,saved,options).message;

function retainedCaseAuthority(root,record,p){
  const action=record.identity.action;
  if(typeof action!=='string'||!UUID.test(action))throw Error('original local call authority is unavailable');
  const directory=caseStateDirectory(p.env,root,p),meta=JSON.parse(caseRead(p,join(directory,'calls',action+'.meta.json')));
  if(meta.id!==action||meta.root!==root||typeof meta.session_id!=='string'||!UUID.test(meta.session_id)
    ||record.identity.session!=null&&record.identity.session!==meta.session_id)throw Error('original local call authority does not match this receipt');
  const repo=JSON.parse(caseRead(p,join(directory,'repos',sha256(Buffer.from(root)).slice(0,16)+'.json')));
  if(repo.root!==root||!isObject(repo.tries))throw Error('original local Try authority is unavailable');
  const matches=Object.entries(repo.tries).filter(([,value])=>value?.id===meta.session_id);
  if(matches.length!==1)throw Error('original local Try authority is missing or ambiguous');
  const [path,original]=matches[0],story=record.identity.original.storyPath;
  if(path!==record.target||original.storyPath!==story)throw Error('original test or Story authority does not match this receipt');
  const hash=value=>typeof value==='string'&&/^[a-f0-9]{64}$/.test(value),raw=original.prompt_hashes,effective=original.effective_prompt_hashes;
  if(!hash(original.story_sha256)||!isObject(raw)||!Object.keys(raw).length||!isObject(effective)
    ||!Object.entries(raw).every(([path,value])=>hash(value)&&hash(effective[path]))
    ||!Object.keys(effective).every(path=>Object.hasOwn(raw,path)))throw Error('original Story/raw/effective source pins are unavailable');
  const workspace=loadRuntimeWorkspace({root});
  requireRuntimePath(workspace,{path,from:'Retained case original'});requireRuntimePath(workspace,{path:story,from:path});
  caseSafe(p,join(root,path));caseSafe(p,join(root,story));
  const found=p.findTests({root}),test=found.tests.find(test=>test.path===path&&test.storyPath===story);
  if(!test||test.doc?.story_path!==story||sha256(Buffer.from(caseRead(p,join(root,story))))!==original.story_sha256)throw Error('the original Story or test changed');
  const selection=trySourceSelection(original,path),capture=p.captureSource(root,selection);
  const references=capture.references??[];
  if((references.length||original.contract_references!==undefined)
    &&(!Array.isArray(original.contract_references)||!isDeepStrictEqual(original.contract_references,references)))throw Error('original reference baseline is unavailable or changed');
  const problem=tryPromptProblem(root,found,test,original,capture,p);if(problem)throw Error(problem);
  const seed=original.seed_scenario;
  if(!isObject(seed)||seed.schema_version!==TEST_SCHEMA||seed.story_path!==story||!Array.isArray(seed.steps)||!seed.steps.length)
    throw Error('original captured scenario context is unavailable');
  // Let the capture owner discover both closures. Current scenario edits cannot
  // hide required context from the original uploaded seed, and neither capture
  // may supply a missing original pin.
  const originalCapture=p.captureSource(root,{...selection,prepareSource:()=>[{path,bytes:JSON.stringify(seed)}]});
  for(const selected of [capture,originalCapture]){
    if(!selected.sources.filter(file=>file.path.endsWith('.prompt.md')).every(file=>hash(raw[file.path])&&hash(effective[file.path])))
      throw Error('complete original raw/effective source pins are unavailable');
    const problem=tryPromptProblem(root,found,{...test,doc:seed},original,selected,p);if(problem)throw Error(problem);
  }
  return JSON.stringify({id:meta.id,root:meta.root,session:meta.session_id,path,story,pins:{story:original.story_sha256,raw,effective,references:original.contract_references}});
}

function retainedCaseCoverage(record){
  const unavailable={scope:'unavailable',covered:null,total:null},doc=record.saved?.test;
  if(!Array.isArray(doc?.criteria)||!doc.criteria.length||!Array.isArray(doc.steps)||!doc.steps.length)return unavailable;
  const ids=new Set(),covered=new Set();
  for(const criterion of doc.criteria){
    if(!isObject(criterion)||typeof criterion.id!=='string'||!criterion.id||typeof criterion.text!=='string'||ids.has(criterion.id))return unavailable;
    ids.add(criterion.id);
  }
  for(const step of doc.steps){
    if(!isObject(step)||!Array.isArray(step.checks)||!step.checks.length)return unavailable;
    for(const check of step.checks){if(!isObject(check)||typeof check.criterion_id!=='string'||!ids.has(check.criterion_id))return unavailable;covered.add(check.criterion_id);}
  }
  // Existing persistence retains scenario criteria, not a complete original
  // Story inventory. A seed snapshot alone cannot promote this scope.
  return{scope:'retained-scenario',covered:covered.size,total:ids.size};
}

export async function applyPendingCaseWithHandoff({cwd=process.cwd(),pendingId,handoff,signal}={},ports={}){
  const p=casePorts(ports);let root,record,lease,unsubscribe;const removals=[];
  const outcome=result=>({...caseOutcome(result),coverage:retainedCaseCoverage(record)});
  try{
    root=p.files.realpath(repoRoot(cwd));const received=readPending(root,pendingId,p),original=received.identity?.original;
    if(received.schema_version!=='pdd.case-import.v1'||!isObject(received.saved)||!isObject(original)
      ||typeof received.target!=='string'||received.target!==original.path||typeof original.storyPath!=='string'||received.saved.id!==received.identity.action
      ||received.target.split(/[\\/]/).some(part=>!part||part==='.'||part==='..')||received.target.startsWith('/'))throw Error('invalid retained original case binding');
    record=received;
    if(!handoff||!['closed-editor','editor-lease'].includes(handoff.kind)||handoff.testPath!==record.target||handoff.closed===false
      ||handoff.kind==='editor-lease'&&typeof handoff.release!=='function')throw Error('explicit closed-file handoff for the exact original test is required');
    let known=caseImportState(root,record,p,{inspect:true});if(known.result)return outcome(known.result);
    const controller=new AbortController(),abort=()=>controller.abort();
    for(const external of new Set([signal,ports.signal].filter(Boolean))){if(external.aborted)abort();else{external.addEventListener('abort',abort,{once:true});removals.push(()=>external.removeEventListener('abort',abort));}}
    unsubscribe=withDefaults(ports).onInterrupt(abort);
    if(controller.signal.aborted)throw Error('case save cancelled');
    const authority=known.published||known.reconciliationOnly?null:retainedCaseAuthority(root,record,p);
    const guard=()=>{
      if(authority===null)throw Error('the established published target changed; keep the received case without reapplying it');
      if(retainedCaseAuthority(root,record,p)!==authority)throw Error('original local source authority changed while waiting');
    };
    lease=await acquireCaseWriteOwnership({root,testPath:record.target,handoff,signal:controller.signal},ports);
    known=caseImportState(root,record,p,{inspect:true});if(known.result)return outcome(known.result);
    if(!known.published&&!known.reconciliationOnly)guard();
    return outcome(applyPendingCaseSync({root,pendingId,writeOwnership:lease,signal:controller.signal},ports,guard));
  }catch(error){if(error?.unboundPort)throw error;return record?outcome(caseResult(record,'pending',cleanText(error.message??error))):{kind:'failure',message:`not added: retained case unavailable (${cleanText(error.message??error)}).`};}
  finally{try{lease?.release();}finally{unsubscribe?.();for(const remove of removals)remove();}}
}

async function caseHandoff(context,testPath){
  context.caseHandoffs??=new Map();if(context.caseHandoffs.has(testPath))return null;
  context.caseHandoffs.set(testPath,true);
  if(context.ports.caseHandoff)return context.ports.caseHandoff({root:context.root,testPath,signal:context.signal});
  if(!context.ports.interactive||context.signal?.aborted)return null;
  line(context.ports.stdout,`Close the editor for ${testPath}. Hand over this closed file for the pending case apply? y/N`);
  const answers=context.ports.lineReader(context.ports.stdin);try{const answer=await answers.ask();return /^y(?:es)?$/i.test(answer.trim())?{kind:'closed-editor',testPath}:null;}finally{answers.close();}
}

// Saved cases: add each new one once. Returns 'ok', 'missing' (no endpoint yet) or 'ended'.
async function collectSavedTests(context, tryId) {
  const { ports, store, root } = context, path = join(store.folder('tries'), `${tryId}.tests.json`);
  const reply = await context.runtime.send(`/v1/try/${tryId}/tests`, { method: 'GET' }, GET_MS);
  if ([401, 403, 410].includes(reply.status)) return 'ended';
  if (reply.status !== 200 || !Array.isArray(reply.json?.tests)) return reply.lost ? 'ok' : 'missing';
  const done = store.read(path) ?? {},writeLeases=context.caseWriteLeases??=new Map();
  for (const [receivedIndex,saved] of reply.json.tests.entries()) {
    const key = typeof saved?.id === 'string' ? saved.id : null;
    if (!key) continue;
    const caseSelectionPorts={env:ports.env,findTests:ports.findTests,captureSource:ports.captureSource,isStoryPath:ports.isStoryPath,hasAcceptance:ports.hasAcceptance,matchTests:ports.matchTests,orphanSummary:ports.orphanSummary};
    const p=casePorts(caseSelectionPorts),record=retainCase(root,saved,{seedTest:context.seedTest,sessionId:tryId,rawBytes:receivedCaseBytes(reply.text,receivedIndex)},p);
    let result=caseResult(record,'pending','close the editor for the named original test and explicitly hand over the file');
    let valid=true;try{prepareCase(root,record,p);}catch(error){if(error?.unboundPort)throw error;valid=false;result=caseResult(record,'pending',error.message);}
    const handoff=valid&&!writeLeases.has(record.target)?await caseHandoff(context,record.target):null;
    if(handoff||writeLeases.has(record.target)){try{let lease=writeLeases.get(record.target);if(!lease){lease=await acquireCaseWriteOwnership({root,testPath:record.target,handoff,signal:context.signal},caseSelectionPorts);writeLeases.set(record.target,lease);}result=await applyPendingCase({root,pendingId:record.pendingId,writeOwnership:lease,signal:context.signal},caseSelectionPorts);}catch(error){if(error?.unboundPort)throw error;result=caseResult(record,'pending',error.message);}}
    const said=caseMessage(result);
    if(result.duplicate&&done[key])continue;
    if(done[key]?.result===said)continue;
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
      if (typeof ports.promptPath !== 'function' || typeof ports.askApproval !== 'function') {
        throw unboundPortError('Try approval ports (promptPath, askApproval) are not bound.');
      }
      const real = realpathSync(root), prompt = typeof request.prompt_path === 'string' ? ports.promptPath(real, real, request.prompt_path) : null;
      const result = prompt ? await ports.askApproval({ root: real, path: prompt, stdout: ports.stdout, answers, expectedHash: request.prose_sha256 })
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
  const { ports } = context, answers = wait ? ports.lineReader(ports.stdin) : null;
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
export async function runDoorCall(descriptor, input, givenPorts = {}) {
  const ports = withDefaults(givenPorts), { root, origin, sessionId, login, prompt, operation } = descriptor;
  if(loadRuntimeWorkspace({root}).configured)ports.captureSource(root,{tests:descriptor.originalPath?[descriptor.originalPath]:[descriptor.prompt].filter(Boolean)});
  const store = stateFor(ports.env, root), identity = signIn(ports.gh, store, ports, { exitCode: 125 });
  if (identity.login !== login) throw new Stop(125, `This Try belongs to ${login}. Run: gh auth switch -u ${login}`);
  if (runtimeOrigin({ PDD_RUNTIME_URL: origin }) !== origin) throw new Stop(2, 'The saved interpreter address is invalid.');
  const repo=store.read(join(store.dir,'repos',`${store.repoKey(root)}.json`));
  const saved=Object.entries(repo?.tries ?? {}).find(([,record])=>record.id===sessionId);
  if (saved) {
    const found=ports.findTests({root}), test=found.tests.find(test=>test.path===saved[0]);
    const problem=tryPromptProblem(root,found,test,saved[1],undefined,ports);
    if (problem) throw new Stop(125,`${problem} Run pdd simulate STORY --new.`);
  }
  const secrets = [identity.token];
  if (ports.signal?.aborted) throw new Stop(125, 'The local server stopped before the command was sent.');
  const id = ports.randomUUID(), request = { requestId: id, prompt, operation, input };
  const recovery = ` Read the result with: pdd test --read ${id}`;
  store.write(join(store.folder('calls'), `${id}.meta.json`), { id, origin, root, login, user_id: identity.userId, session_id: sessionId });
  store.posted(store.folder('tries'), id);
  let knownOutcome = false, dispatched = false;
  const auth = authSession({
    identity,
    store,
    ports,
    secrets,
    signInExitCode: 125,
    expectedOwnerLogin: login,
    ownerMismatchError: owner => {
      if (!dispatched) knownOutcome = true;
      return new Stop(125, `This Try belongs to ${owner}. Run: gh auth switch -u ${owner}`);
    },
    onRefresh: next => {
      if (next.login === login) store.write(join(store.folder('calls'), `${id}.meta.json`), { id, origin, root, login, user_id: next.userId, session_id: sessionId });
    },
  });
  const runtime = new Runtime({ origin, token: identity.token, ports, signal: ports.signal, auth });
  try {
    const reply = await runtime.send(`/v1/try/${sessionId}/call`, { method: 'POST',
      headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(request) }, ports.postMs);
    if (reply.status && ![200, 202].includes(reply.status)) {
      knownOutcome = reply.status >= 400 && reply.status < 500 && reply.status != 408;
      throw new Stop(125, cleanText(reply.json?.error?.message || (reply.status === 401 ? AUTH_TEXT : reply.json?.error?.code) || `The interpreter refused the command (HTTP ${reply.status}).`, secrets) + recovery);
    }
    dispatched = true;
    const end = ports.now() + 900_000;
    let answer = null;
    for (;;) {
      if (ports.signal?.aborted) throw new Stop(125, 'The local server stopped; this command result is unknown. Do not repeat it automatically.' + recovery);
      if (answer && (!sameJob(answer, id, 'call') || (answer.session_id && answer.session_id !== sessionId))) throw new Stop(125, 'The interpreter returned a different command.' + recovery);
      if (answer && ENDED.has(answer.state)) {
        store.write(join(store.folder('tries'), `${id}.json`), answer);
        if (answer.state !== 'passed' || !isObject(answer.result?.program_result)) {
          knownOutcome = ['failed', 'refused', 'not_run'].includes(answer.state);
          const limit = stepTimeLimit(answer, { steps: [{ step_id: operation }], secrets });
          const why = answer.result?.refusals?.[0];
          if (limit) throw Object.assign(new Stop(125, `${limit.message} ${limit.fix}${recovery}`), { tryUsage: tryUsage(answer, { cap: descriptor.callCap }) });
          throw Object.assign(new Stop(125, cleanText(why?.engine_message || why?.message || why?.code || 'The command result is unknown. Do not repeat it automatically.', secrets) + (['failed', 'refused'].includes(answer.state) ? '' : recovery)), { tryUsage: tryUsage(answer, { cap: descriptor.callCap }) });
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
      if ([401, 403, 410].includes(read.status)) throw new Stop(125, cleanText(read.json?.error?.message || (read.status === 401 ? AUTH_TEXT : 'The command could not be read. Do not repeat it automatically.'), secrets) + recovery);
      answer = [200, 202].includes(read.status) ? read.json : null;
    }
  } catch (error) {
    if (!knownOutcome) error.unknownOutcome = true;
    throw error;
  }
}

export async function readTryOwner({ cwd = process.cwd(), story } = {}, givenPorts = {}) {
  const ports = withDefaults(givenPorts), root = repoRoot(cwd), found = ports.findTests({ root }), store = stateFor(ports.env, root);
  const repo = store.repo(root), open = found.tests.filter(test => repo.tries?.[test.path]);
  let selected = story === undefined ? (open.length === 1 ? open : found.tests) : ports.selectTests(found, [story]).selected;
  if (selected.length > 1) { const live = selected.filter(test => repo.tries?.[test.path]); if (live.length === 1) selected = live; }
  if (selected.length !== 1) throw new Error(`Choose one Story${story ? ` matching "${story}"` : ''}. Available: ${found.tests.map(test => `${test.story} (${test.path})`).join(', ') || 'none'}.`);
  const test = selected[0];
  ports.captureSource(root,{tests:[test.path]});
  async function openTry() {
    const code = await runTry({ cwd, words: [test.path], options: { '--page': true, ...productOptions(record?.product_setup), '--no-open': true, '--no-wait': true } }, { ...ports, stdout: ports.stderr, interactive: false, agentBridge: false });
    if (code !== 0) throw new Error('The Try could not open. Read the progress on stderr and fix the reported problem.');
  }
  let record = repo.tries?.[test.path];
  if (!record) { await openTry(); record = store.repo(root).tries?.[test.path]; }
  if (!record) throw new Error('No confirmed Try is recorded. Run pdd simulate STORY.');
  ports.captureSource(root,{tests:[test.path]});
  const identity = signIn(ports.gh, store, ports);
  if (record.login !== identity.login) throw new Error(`This Try belongs to ${record.login}. Run: gh auth switch -u ${record.login}`);
  if (runtimeOrigin({ PDD_RUNTIME_URL: record.origin }) !== record.origin) throw new Error('The saved interpreter address is invalid.');
  const promptProblem=tryPromptProblem(root,found,test,record,undefined,ports);
  if (record.storyPath !== test.storyPath || record.story_sha256 && createHash('sha256').update(readFileSync(join(root, test.storyPath))).digest('hex') !== record.story_sha256 || promptProblem)
    throw new Error(`${promptProblem ?? 'The Story changed.'} Run pdd simulate STORY --new.`);
  const secrets = [identity.token];
  const auth = authSession({
    identity,
    store,
    ports,
    secrets,
    expectedOwnerLogin: () => record.login,
    ownerMismatchError: owner => new Error(`This Try belongs to ${owner}. Run: gh auth switch -u ${owner}`),
  });
  let runtime = new Runtime({ origin: record.origin, token: identity.token, ports, signal: ports.signal, auth });
  let metadata = await runtime.send(`/v1/try/${record.id}/model`, { method: 'GET' }, GET_MS);
  let paused = false;
  if (metadata.status === 409 && metadata.json?.error?.code === 'session-stopped') {
    const saved = await runtime.get(record.id);
    paused = saved.status === 200 && sameJob(saved.json, record.id, 'try') && saved.json.state === 'passed'
      && saved.json.result?.session?.state === 'paused';
  }
  if (paused || [404, 410].includes(metadata.status)) {
    await openTry(); record = store.repo(root).tries?.[test.path];
    const refreshedIdentity = signIn(ports.gh, store, ports);
    Object.assign(identity, refreshedIdentity);
    if (!secrets.includes(identity.token)) secrets.push(identity.token);
    if (record.login !== identity.login) throw new Error(`This Try belongs to ${record.login}. Run: gh auth switch -u ${record.login}`);
    runtime = new Runtime({ origin: record.origin, token: identity.token, ports, signal: ports.signal, auth });
    metadata = await runtime.send(`/v1/try/${record.id}/model`, { method: 'GET' }, GET_MS);
  }
  if (metadata.status !== 200 || !Array.isArray(metadata.json?.entries)) throw new Error(cleanText(metadata.json?.error?.message || `The Try model could not be read${metadata.status ? ` (HTTP ${metadata.status})` : ''}. Read this Try again; no new run was sent.`, secrets));
  const state = await runtime.send(`/v1/try/${record.id}/state`, { method: 'GET' }, GET_MS);
  const source_sha256 = validSha256Hex(metadata.json?.source_sha256) ?? validSha256Hex(record?.source_sha256) ?? null;
  const engine_sha = validEngineHex(metadata.json?.engine_sha) ?? validEngineHex(record?.engine_sha) ?? null;
  return { root, test: record.seed_scenario ? { ...test, doc: record.seed_scenario } : test, record, model: metadata.json, source_sha256, engine_sha, actions: Array.isArray(state.json?.actions) ? state.json.actions : null,
    ...(state.status === 200 && Object.hasOwn(state.json ?? {}, 'world') ? { data: state.json.world } : { data_error: `Current saved data unavailable${state.status ? ` (HTTP ${state.status})` : ''}; no initial data was substituted.` }) };
}

// Local migration ports use the same private custody/publication boundary.
export function runtimeWorkspaceMigrationStore({root,projectionRoot,env=process.env},given={}){
  const p=casePorts({...given,env}),directory=caseStateDirectory(env,root,p),oldKey=p.hash(Buffer.from(projectionRoot)).slice(0,16);
  const readJson=path=>JSON.parse(caseRead(p,path));
  const list=path=>{try{caseSafe(p,path,{directory:true});return p.files.list(path);}catch(e){if(e.code==='ENOENT'||!caseStat(p,path))return[];throw e;}};
  const destinationRepo=join(directory,'repos',p.hash(Buffer.from(root)).slice(0,16)+'.json');
  function migrateDoor(pointer,record) {
    if(!pointer?.descriptor||!pointer?.last)throw Error('original last-door pointer is unavailable; retain the original recovery command');
    const descriptor=readJson(pointer.descriptor),lastRaw=caseRead(p,pointer.last),mapping=new Map(record.mappings.map(m=>[m.from,m.to]));
    if(descriptor.version!==1||descriptor.root!==projectionRoot||!UUID.test(descriptor.sessionId??'')||!descriptor.login||!descriptor.origin
      ||pointer.descriptor!==join(directory,'tries',descriptor.sessionId+'.door.json')||descriptor.repoState!==join(directory,'repos',oldKey+'.json')
      ||!Object.values(readJson(descriptor.repoState).tries??{}).some(row=>row.id===descriptor.sessionId))throw Error('original PDD-owned door identity is unavailable');
    const mapped=path=>{const target=mapping.get(path);if(!target)throw Error('door source has no exact destination mapping');return target;};
    const mapHashes=hashes=>Object.fromEntries(Object.entries(hashes??{}).map(([path,hash])=>[mapped(path),hash]));
    // The launcher derives its last-result path from this directory and the
    // original session ID. Give destination control files their own directory
    // so a later command cannot overwrite the original producer's last bytes.
    const stem=join(directory,'tries',`authored-${p.hash(Buffer.from(root)).slice(0,16)}`,descriptor.sessionId),descriptorPath=stem+'.door.json',lastPath=stem+'.last.json';
    const next={...descriptor,root,originalPath:mapped(descriptor.originalPath),storyPath:mapped(descriptor.storyPath),prompt:mapped(descriptor.prompt),promptHashes:mapHashes(descriptor.promptHashes),effectivePromptHashes:mapHashes(descriptor.effectivePromptHashes),repoState:destinationRepo,stateDir:directory,
      migration:{producerRoot:projectionRoot,originalDescriptor:pointer.descriptor,originalLast:pointer.last,readCommand:record.readCommand??null}};
    // This is a local destination descriptor. Original execution records and
    // their producer identity are immutable and remain at their original paths.
    caseWrite(p,descriptorPath,JSON.stringify(next));
    if(!caseStat(p,lastPath))caseWrite(p,lastPath,lastRaw,{exclusive:true});
    return {descriptor:descriptorPath,last:lastPath};
  }
  return{
    inventory(){
      const records=[],repoPath=join(directory,'repos',oldKey+'.json');let repo;
      if(caseStat(p,repoPath)){repo=readJson(repoPath);records.push({id:repoPath,kind:'repo',record:repo,raw:caseRead(p,repoPath)});}
      for(const batch of list(join(directory,'batches'))){if(!BATCH.test(batch))continue;const folder=join(directory,'batches',batch),path=join(folder,'batch.json');if(!caseStat(p,path))continue;const record=readJson(path);if(record.root!==projectionRoot)continue;records.push({id:path,kind:'batch',record,raw:caseRead(p,path),receipts:list(folder).filter(n=>UUID.test(n.replace(/\.json$/,''))).map(n=>({path:join(folder,n),raw:caseRead(p,join(folder,n))}))});}
      for(const id of new Set(Object.values(repo?.tries??{}).map(r=>r.id).filter(id=>UUID.test(id))))for(const suffix of ['.json','.door.json','.tests.json','.approvals.json']){const path=join(directory,'tries',id+suffix);if(caseStat(p,path))records.push({id:path,kind:'try',record:readJson(path),raw:caseRead(p,path)});}
      const area=join(directory,'case-import');for(const name of list(area).filter(n=>/^[a-f0-9]{64}$/.test(n)))for(const file of list(join(area,name)).filter(n=>n.endsWith('.received.json'))){const path=join(area,name,file),record=readJson(path);if(record.identity?.root!==projectionRoot)continue;const journal=path.replace('.received.json','.transaction.json');records.push({id:path,kind:'case',record,raw:caseRead(p,path),transaction:caseStat(p,journal)?readJson(journal):null});}
      return records;
    },
    readMapping(id){
      const folder=join(directory,'workspace-migrations',id),records=list(folder).filter(n=>/^[a-f0-9]{64}\.json$/.test(n)).map(n=>readJson(join(folder,n)));
      if(!records.length)return null;
      const items=Object.assign({},...records.map(r=>r.items));
      for(const item of Object.values(items))if(item.state==='applied'&&(item.kind==='repo'&&item.record.last_door||item.kind==='try'&&item.record.version===1&&item.record.originalPath)) {
        try {
          const pointer=readJson(destinationRepo).last_door,d=readJson(pointer.descriptor);caseRead(p,pointer.last);
          if(d.root!==root||d.repoState!==destinationRepo||d.migration?.producerRoot!==projectionRoot)throw Error('destination door is unavailable');
        }catch{item.state='prepared';}
      }
      return {...records[0],items};
    },
    publishMapping(id,record){
      const itemId=record.activeItem,item=record.items[itemId],folder=join(directory,'workspace-migrations',id),path=join(folder,p.hash(Buffer.from(itemId))+'.json');
      // Each item has its own atomic record; another item's update cannot be lost.
      if(item.state==='applied'&&item.kind==='repo'){
        const old=item.record,mapping=new Map(record.mappings.map(m=>[m.from,m.to])),target=join(directory,'repos',p.hash(Buffer.from(root)).slice(0,16)+'.json');
        const current=caseStat(p,target)?readJson(target):{root,tries:{}};const tries={...current.tries};
        for(const [from,value] of Object.entries(old.tries??{})){const to=mapping.get(from);if(!to)throw Error('original Try has no exact destination mapping');if(tries[to]&&tries[to].id!==value.id)throw Error('authored repository already has another Try at this test');tries[to]={...value,original_root:projectionRoot};}
        const last_door=old.last_door?migrateDoor(old.last_door,{...record,readCommand:item.readCommand}):current.last_door;
        const next={...old,...current,root,original_root:projectionRoot,tries,last_batch:current.last_batch??old.last_batch??null,...(last_door?{last_door}:{})};
        // Destination publication is separately prepared and recoverable. Original
        // receipts/state remain untouched and the selected lease guards this item.
        caseWrite(p,target,JSON.stringify(next));
      }
      if(item.state==='applied'&&item.kind==='try'&&itemId.endsWith('.door.json')) {
        const old=readJson(join(directory,'repos',oldKey+'.json'));
        if(old.last_door?.descriptor!==itemId)throw Error('door has no owned original last-result pointer; preserve its original recovery command');
        const last_door=migrateDoor(old.last_door,{...record,readCommand:item.readCommand});
        if(!caseStat(p,destinationRepo))throw Error('authored repository pointer is unavailable');
        caseWrite(p,destinationRepo,JSON.stringify({...readJson(destinationRepo),last_door}));
      }
      caseWrite(p,path,JSON.stringify({...record,items:{[itemId]:item}}));return path;
    },
    transferCase(item,target){const old=item.record;
      // Transfer every conflicting variant before any one variant can be applied.
      for(const name of list(dirname(item.id)).filter(n=>n.endsWith('.received.json'))){const sibling=readJson(join(dirname(item.id),name));if(sibling.pendingId===old.pendingId)continue;if(sibling.identity?.root!==projectionRoot||!isDeepStrictEqual(sibling.identity,old.identity))throw Error('conflicting original case association is uncertain');const copy=retainCase(root,sibling.saved,{seedTest:{path:target,storyPath:item.mappedStory},sessionId:sibling.identity.session,isolated:sibling.isolated,rawBytes:sibling.raw},p);const origin=copy.recoveryPath.replace('.received.json','.origin.json');if(!caseStat(p,origin))caseWrite(p,origin,JSON.stringify({originalReceipt:caseRead(p,join(dirname(item.id),name)),originalIdentity:sibling.identity}),{exclusive:true});}
      const retained=retainCase(root,old.saved,{seedTest:{path:target,storyPath:target?item.mappedStory:old.identity.original.storyPath},sessionId:old.identity.session,isolated:old.isolated,rawBytes:old.raw},p);
      const originalPath=retained.recoveryPath.replace('.received.json','.origin.json');if(!caseStat(p,originalPath))caseWrite(p,originalPath,JSON.stringify({originalReceipt:item.raw,originalIdentity:old.identity,transaction:item.transaction??null}),{exclusive:true});
      if(item.transaction?.after!==undefined){
        const path=item.transaction.isolated?item.mappedVariant:target;
        if(path&&caseStat(p,join(root,path))&&caseRead(p,join(root,path))===item.transaction.after&&caseStat(p,join(projectionRoot,item.transaction.path))&&caseRead(p,join(projectionRoot,item.transaction.path))===item.transaction.after)caseWrite(p,retained.recoveryPath.replace('.received.json','.transaction.json'),JSON.stringify({...item.transaction,path,state:'committed'}));
      }
      return retained;
    }
  };
}
