// Generated from prompts/cli/runtime-seam.prompt.md (sha256: a2a4553e541ab4f947da3a3d684735acd645c846ce3813c86b0fa04fb4781c3f).
import { AsyncLocalStorage } from 'node:async_hooks';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import fs, { realpathSync } from 'node:fs';
import { createRequire, syncBuiltinESMExports } from 'node:module';
import { basename, dirname, join, relative, resolve, sep } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import {
  CHECK_STATES,
  DRAFT_SERVER_TEXT,
  LIMITS,
  OPEN_STATES,
  PROVIDER_TEXT,
  PreflightError,
  STALE_HINT,
  TEST_SCHEMA,
  acquireCaseWriteOwnership as rawAcquireCaseWriteOwnership,
  acquireRuntimeBatchLock,
  allowsRuntimePath,
  applyPendingCase as rawApplyPendingCase,
  applyPendingCaseWithHandoff as rawApplyPendingCaseWithHandoff,
  askAgent as runtimeAskAgent,
  baselineReport,
  buildAgentInput,
  buildCheckPlan as runtimeBuildCheckPlan,
  buildProjectCard as runtimeBuildProjectCard,
  captureSource as rawCaptureSource,
  causeText,
  checkInput,
  checkPlanResultLines,
  checkPlanResults,
  checkRuntimeHealth as runtimeCheckHealth,
  cleanText,
  composeProductTry as runtimeComposeProductTry,
  coverageText,
  createAgentBridge as runtimeCreateAgentBridge,
  createSavedStoryEvidenceReader as rawCreateSavedStoryEvidenceReader,
  createStrictSourceAccess as rawCreateStrictSourceAccess,
  createTryGuide as runtimeCreateTryGuide,
  createTryTools as runtimeCreateTryTools,
  defaultLineReader,
  defaultMaxCalls,
  discoveryRefusal,
  discoveryVisibleFiles,
  estimateCheckCalls,
  evaluateCheckBudget,
  exactIntegerLeaves,
  exactNumberSpelling,
  exactValue,
  executableInterfaceText,
  fillHashes as rawFillHashes,
  findTests as rawFindTests,
  failedCheckCount,
  format,
  formatSize,
  formatWarningLines,
  gitFiles,
  hasProgress,
  hasPromptInterface,
  interfaceBlocks,
  interfaceFormatWarnings,
  interfaceKindProblems,
  interfaceSchemaProblems,
  isSecretPath,
  jsonRow,
  jsonSafe,
  loadRuntimeClient as runtimeLoadClient,
  loadRuntimeWorkspace,
  migrateRuntimeWorkspace as runtimeMigrateWorkspace,
  numberWarnings,
  observeTryCall as runtimeObserveTryCall,
  openCli as runtimeOpenCli,
  openServe as runtimeOpenServe,
  otherFiles,
  outcomeDone,
  outcomeFor,
  outcomeOverall,
  outcomeText,
  parsePromptFrontmatter,
  parseScenarioJson,
  preflight as rawPreflight,
  providerText,
  productTapCallBound,
  progressText,
  progressTicker,
  projectAnswer,
  promptMarkdownTargets,
  promptRefusal,
  promptSchemaRefusals,
  proseSha256,
  readAgentScenarios as rawReadAgentScenarios,
  readContractHistory as runtimeReadContractHistory,
  readPrompt,
  readTryOwner as runtimeReadTryOwner,
  refusalView as rawRefusalView,
  renderJson as rawRenderJson,
  renderText as rawRenderText,
  requireRuntimePath,
  resendableStoryChecks as rawResendableStoryChecks,
  resultOutcome,
  roundedNumberTokens,
  resultOverall,
  runCheck as runtimeRunCheck,
  runContracts as runtimeRunContracts,
  runDoorCall as runtimeRunDoorCall,
  runJobs as runtimeRunJobs,
  runMcp as runtimeRunMcp,
  runShim as runtimeRunShim,
  runTry as runtimeRunTry,
  runtimeAgentPacketSlice,
  runtimeCheckPlanSlice,
  runtimeClientSlice as rawRuntimeClientSlice,
  runtimeOrigin,
  runtimeOutcomeSlice as rawRuntimeOutcomeSlice,
  runtimeOutputSlice as rawRuntimeOutputSlice,
  runtimePreflightSlice as rawRuntimePreflightSlice,
  runtimeScenarioJsonSlice as rawRuntimeScenarioJsonSlice,
  runtimeWorkspaceMigrationStore as rawRuntimeWorkspaceMigrationStore,
  runtimeWorkspaceSlice,
  saveDoorCaseResult as rawSaveDoorCaseResult,
  saveLast as runtimeSaveLast,
  savedStoryEvidence as rawSavedStoryEvidence,
  scenarioShapeRefusal,
  schemaKeywordWarningLines,
  selectCheckTests,
  selectJourneys as rawSelectJourneys,
  sha256,
  sharedSourceFiles as rawSharedSourceFiles,
  sinceText,
  sourceFilePort,
  staleHint,
  stepTimeLimit,
  storyCriteria,
  storyLines as rawStoryLines,
  stringifyScenarioJson,
  summaryLine as rawSummaryLine,
  tarFiles,
  tryUsage,
  tryUsageHeaders,
  tryUsageLine,
  validLink,
  version,
  withExactIntegers,
  workspace,
} from '@promptdriven/runtime-client';

const req = createRequire(import.meta.url);
const initialReadFileSync = fs.readFileSync;
const initialOpenSync = fs.openSync;
const initialCloseSync = fs.closeSync;
const initialLstatSync = fs.lstatSync;
const initialStatSync = fs.statSync;
const initialFstatSync = fs.fstatSync;
const TRY_LAUNCHER_URL = pathToFileURL(join(dirname(fileURLToPath(import.meta.url)), 'try-doors.mjs')).href;

export const NO_TESTS =
  'No tests found. The test of Story user_stories/S.md is S.json in a test or tests folder. See RUNBOOK.md §2.';
export const STATE_EXIT_CODES = Object.freeze({
  passed: 0,
  failed: 1,
  unknown: 3,
  waiting: 3,
  sent: 3,
  partial: 3,
  queued: 3,
  running: 3,
  refused: 4,
  not_run: 5,
  'not run': 5,
});
export const COMMAND_EXIT_CODE = 2;
export const PROMPT_TESTS_LABEL = 'Prompt tests';
export const PROMPT_TESTS_WORDS = '(?:Prompt tests|Runtime check)';

let cachedVersion = null;
function clientVersion() {
  return (cachedVersion ??= JSON.parse(initialReadFileSync(new URL('../package.json', import.meta.url), 'utf8')).version);
}

let cachedRedaction = null;
function hostRedaction() {
  if (!cachedRedaction) {
    const { knownSecretValues, redactSecrets, rememberSecrets } = req('./secret-redaction.mjs');
    cachedRedaction = Object.freeze({ remember: rememberSecrets, redact: redactSecrets, known: knownSecretValues });
  }
  return cachedRedaction;
}

let cachedSelection = null;
function hostSelection() {
  return (cachedSelection ??= req('./test-selection.mjs'));
}

let cachedExit = null;
function hostExit() {
  return (cachedExit ??= req('./runtime-exit.mjs'));
}

let cachedScenarioCompiler = null;
function hostScenarioCompiler() {
  return (cachedScenarioCompiler ??= req('./scenario-compile.mjs'));
}

const scenarioOverlayStorage = new AsyncLocalStorage();
const scenarioOverlayOpenFds = new Map();
let scenarioFsHookInstalled = false;

function lookupScenarioOverlayVirtualText(store, rawPath) {
  if (!store || (typeof rawPath !== 'string' && !(rawPath instanceof URL))) return undefined;
  const strPath = rawPath instanceof URL ? fileURLToPath(rawPath) : rawPath;
  if (!strPath.endsWith('.json') || strPath.includes('/node_modules/') || strPath.endsWith('/package.json')) {
    return undefined;
  }
  if (store.map === undefined) {
    store.map = null;
    const root = store.root ?? repoTopRoot(store.cwd);
    store.map = (root ? buildScenarioOverlay(root, store.ports) : null) ?? new Map();
  }
  if (!store.map || store.map.size === 0) return undefined;
  return store.map.get(strPath) ?? store.map.get(resolve(strPath));
}

function statWithVirtualSize(statObj, byteLength) {
  if (!statObj || typeof statObj.isFile !== 'function' || !statObj.isFile()) return statObj;
  const size = typeof statObj.size === 'bigint' ? BigInt(byteLength) : byteLength;
  return Object.assign(Object.create(Object.getPrototypeOf(statObj)), statObj, { size });
}

function ensureScenarioFsOverlay() {
  if (scenarioFsHookInstalled) return;
  scenarioFsHookInstalled = true;
  fs.openSync = function pddScenarioOpenSync(path, flags, mode) {
    const fd = initialOpenSync(path, flags, mode);
    const store = scenarioOverlayStorage.getStore();
    if (store?.interceptFd && typeof fd === 'number' && (typeof path === 'string' || path instanceof URL)) {
      const writeMask =
        (fs.constants?.O_WRONLY ?? 1) |
        (fs.constants?.O_RDWR ?? 2) |
        (fs.constants?.O_CREAT ?? 0) |
        (fs.constants?.O_TRUNC ?? 0);
      const numericFlags = typeof flags === 'number' ? flags : 0;
      if ((numericFlags & writeMask) === 0 && (typeof flags !== 'string' || flags.startsWith('r'))) {
        const strPath = path instanceof URL ? fileURLToPath(path) : path;
        if (strPath.endsWith('.json')) scenarioOverlayOpenFds.set(fd, resolve(strPath));
      }
    }
    return fd;
  };
  fs.closeSync = function pddScenarioCloseSync(fd) {
    scenarioOverlayOpenFds.delete(fd);
    return initialCloseSync(fd);
  };
  fs.lstatSync = function pddScenarioLstatSync(path, options) {
    const stat = initialLstatSync(path, options);
    const store = scenarioOverlayStorage.getStore();
    if (store?.interceptFd && stat && !stat.isSymbolicLink?.()) {
      const virtualText = lookupScenarioOverlayVirtualText(store, path);
      if (virtualText !== undefined) return statWithVirtualSize(stat, Buffer.byteLength(virtualText, 'utf8'));
    }
    return stat;
  };
  fs.statSync = function pddScenarioStatSync(path, options) {
    const stat = initialStatSync(path, options);
    const store = scenarioOverlayStorage.getStore();
    if (store?.interceptFd && stat) {
      const virtualText = lookupScenarioOverlayVirtualText(store, path);
      if (virtualText !== undefined) return statWithVirtualSize(stat, Buffer.byteLength(virtualText, 'utf8'));
    }
    return stat;
  };
  fs.fstatSync = function pddScenarioFstatSync(fd, options) {
    const stat = initialFstatSync(fd, options);
    const store = scenarioOverlayStorage.getStore();
    if (store?.interceptFd && stat) {
      const fdPath = scenarioOverlayOpenFds.get(fd);
      if (fdPath) {
        const virtualText = lookupScenarioOverlayVirtualText(store, fdPath);
        if (virtualText !== undefined) return statWithVirtualSize(stat, Buffer.byteLength(virtualText, 'utf8'));
      }
    }
    return stat;
  };
  fs.readFileSync = function pddScenarioReadFileSync(pathOrFd, options) {
    const store = scenarioOverlayStorage.getStore();
    if (store) {
      const targetPath =
        typeof pathOrFd === 'string' || pathOrFd instanceof URL
          ? pathOrFd
          : store.interceptFd && typeof pathOrFd === 'number'
            ? scenarioOverlayOpenFds.get(pathOrFd)
            : undefined;
      if (targetPath !== undefined) {
        const virtualText = lookupScenarioOverlayVirtualText(store, targetPath);
        if (virtualText !== undefined) {
          if (typeof options === 'string') return Buffer.from(virtualText, 'utf8').toString(options);
          if (options && typeof options === 'object' && options.encoding) {
            return Buffer.from(virtualText, 'utf8').toString(options.encoding);
          }
          return Buffer.from(virtualText, 'utf8');
        }
      }
    }
    return initialReadFileSync(pathOrFd, options);
  };
  syncBuiltinESMExports();
}

function withScenarioOverlay(lazyStore, fn) {
  if (!lazyStore) return fn();
  ensureScenarioFsOverlay();
  return scenarioOverlayStorage.run(lazyStore, fn);
}

function repoTopRoot(cwd = process.cwd()) {
  if (typeof cwd !== 'string' || !cwd) return null;
  const res = spawnSync('git', ['rev-parse', '--show-toplevel'], {
    cwd,
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  return res.status === 0 && res.stdout.trim() ? res.stdout.trim() : null;
}

function gitHeadBlobOids(root, commit, paths) {
  if (!commit || !paths.length) return new Map();
  const res = spawnSync('git', ['ls-tree', '-z', commit, '--', ...paths], {
    cwd: root,
    maxBuffer: 64 * 1024 * 1024,
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  if (res.status !== 0) return new Map();
  const map = new Map();
  for (const rec of res.stdout.toString('utf8').split('\0')) {
    if (!rec) continue;
    const tab = rec.indexOf('\t');
    if (tab < 0) continue;
    const [mode, type, oid] = rec.slice(0, tab).trim().split(/\s+/);
    const p = rec.slice(tab + 1);
    if (p && oid && type === 'blob' && mode !== '120000') map.set(p, oid.toLowerCase());
  }
  return map;
}

function gitBlobHash(buf, commit) {
  const algo = typeof commit === 'string' && commit.length === 64 ? 'sha256' : 'sha1';
  return createHash(algo).update(`blob ${buf.length}\0`).update(buf).digest('hex');
}

function seamRedaction(ports = {}) {
  if (ports.redaction !== undefined && ports.redaction !== null) return ports.redaction;
  const host = hostRedaction();
  if (
    (ports.rememberSecrets === undefined || ports.rememberSecrets === null) &&
    (ports.redactSecrets === undefined || ports.redactSecrets === null)
  ) {
    return host;
  }
  return Object.freeze({
    remember: ports.rememberSecrets ?? host.remember,
    redact: ports.redactSecrets ?? host.redact,
    known: host.known,
  });
}

function withPortDefaults(ports = {}, defaults = {}) {
  const merged = { ...ports };
  for (const [key, fallback] of Object.entries(defaults)) {
    if (merged[key] === undefined || merged[key] === null) {
      merged[key] = fallback;
    }
  }
  return merged;
}

function loadPreflightWorkspacePolicy(input) {
  try {
    return loadRuntimeWorkspace(input);
  } catch (error) {
    if (error?.code?.startsWith('workspace-')) {
      throw Object.assign(new PreflightError(4, error.message), { code: error.code });
    }
    throw error;
  }
}

function seamSelectionPorts(ports = {}) {
  const sel = hostSelection();
  return withPortDefaults(ports, {
    isStoryPath: sel.isStoryPath,
    hasAcceptance: sel.hasAcceptance,
    expectedTestPath: sel.expectedTestPath,
    matchTests: sel.matchTests,
    orphanSummary: sel.orphanSummary,
    selectTests: sel.selectTests,
    whyNoTests: sel.whyNoTests,
    NO_TESTS: sel.NO_TESTS,
    noTestsMessage: sel.NO_TESTS,
    findTests,
    captureSource,
  });
}

const IMPOSSIBLE_RVP_HINT = 'Port result_schema excluded simulation result_value_pointer (for example, synthesized {"type":"array"} instead of {"type":"object","properties":{"value":...}}). Set result_value_pointer to "" when the port returns the value directly, or state the exact returned JSON object keys in the prompt\'s Ports section so result_schema includes that pointer.';

function refusalView(item, secrets) {
  const view = rawRefusalView(item, secrets);
  if (view && view.code === 'impossible-result-value-pointer' && !String(view.hint ?? '').includes('result_value_pointer')) {
    return { ...view, hint: [view.hint, IMPOSSIBLE_RVP_HINT].filter(Boolean).join(' ') };
  }
  return view;
}

function normalizeRuntimeHints(text) {
  if (typeof text !== 'string') return text;
  let out = text.includes('--fill-hash')
    ? text.replace(/pdd\s+test\s+--fill-hash\b/g, 'pdd test').replace(/(?<!\s)\s+--fill-hash\b/g, '')
    : text;
  if (out.includes('impossible-result-value-pointer') && !out.includes('result_value_pointer to ""')) {
    out = out.replace(/impossible-result-value-pointer(?![^\n]*result_value_pointer to "")/g, `impossible-result-value-pointer (${IMPOSSIBLE_RVP_HINT})`);
  }
  return out;
}

function normalizeHintStream(stream) {
  if (!stream || typeof stream.write !== 'function' || stream.__pddHintNormalized) return stream;
  return Object.assign(Object.create(stream), {
    __pddHintNormalized: true,
    ...(stream.isTTY !== undefined ? { isTTY: stream.isTTY } : {}),
    write(chunk, ...rest) {
      const text =
        typeof chunk === 'string'
          ? chunk
          : Buffer.isBuffer(chunk) || chunk instanceof Uint8Array
            ? Buffer.from(chunk).toString('utf8')
            : String(chunk);
      return stream.write(normalizeRuntimeHints(text), ...rest);
    },
  });
}

function buildLegacyCriterionBindingLookup(root, ports = {}) {
  let cachedMap = null;
  const loadMap = () => {
    if (cachedMap !== null) return cachedMap;
    cachedMap = new Map();
    if (!root) return cachedMap;
    let realRoot;
    try {
      realRoot = realpathSync(root);
    } catch {
      return cachedMap;
    }
    const sel = hostSelection();
    const compiler = hostScenarioCompiler();
    const names = visibleStoryAndTestPaths(realRoot, { excludeFixtureProjects: false });
    const storyPaths = names.filter(p => sel.isStoryPath(p));
    const basenameCounts = new Map();
    for (const sp of storyPaths) {
      const stem = basename(sp, '.md');
      basenameCounts.set(stem, (basenameCounts.get(stem) ?? 0) + 1);
    }
    const matched = sel.matchTests(storyPaths, names).tests.filter(t => !t.problem);
    for (const entry of matched) {
      for (const testPath of entry.files ?? [entry.path]) {
        let rawText;
        try {
          const full = realpathSync(join(realRoot, testPath));
          if (full !== realRoot && !full.startsWith(realRoot + sep)) continue;
          rawText = initialReadFileSync(full, 'utf8');
        } catch {
          continue;
        }
        let parsed;
        try {
          parsed = compiler.parseExactScenarioJson(rawText);
        } catch {
          continue;
        }
        const effectiveStoryPath = typeof parsed?.story_path === 'string' && parsed.story_path
          ? parsed.story_path
          : entry.storyPath;
        if (!effectiveStoryPath) continue;
        let storySource;
        try {
          const fullStory = realpathSync(join(realRoot, effectiveStoryPath));
          if (fullStory !== realRoot && !fullStory.startsWith(realRoot + sep)) continue;
          storySource = initialReadFileSync(fullStory, 'utf8');
        } catch {
          continue;
        }
        const classification = compiler.classifyExplicitCriteriaBinding(parsed, {
          storyPath: effectiveStoryPath,
          storySource,
        });
        if (classification.kind !== 'legacy-unbound') continue;
        const stem = basename(effectiveStoryPath, '.md');
        const storyArg = (basenameCounts.get(stem) ?? 0) === 1 ? stem : effectiveStoryPath;
        const legacyLabel =
          classification.legacyIds.length === 1
            ? `legacy criterion ID ${JSON.stringify(classification.legacyIds[0])}`
            : `legacy criterion IDs ${classification.legacyIds.map(id => JSON.stringify(id)).join(', ')}`;
        const reason = `The test's criterion text already matches ${effectiveStoryPath}'s Acceptance criteria word for word, but ${legacyLabel} has no current ac-sha256-... content binding.`;
        const fix = `Bind matching criteria and checks on disk for review with: pdd lint --bind-criteria ${storyArg}`;
        cachedMap.set(testPath, {
          testPath,
          storyPath: effectiveStoryPath,
          reason,
          fix,
          message: `${reason} ${fix}`,
        });
      }
    }
    return cachedMap;
  };
  return testPathHint => {
    const map = loadMap();
    if (typeof testPathHint === 'string' && testPathHint) return map.get(testPathHint) ?? null;
    if (map.size === 1) return [...map.values()][0];
    return null;
  };
}

function rewriteMismatchList(items, lookup, fallbackPath = null) {
  if (!Array.isArray(items) || !items.length) return { items, changed: false };
  let changed = false;
  const emittedForPath = new Set();
  const next = [];
  for (const item of items) {
    if (!item || typeof item !== 'object' || item.code !== 'story-criterion-mismatch') {
      next.push(item);
      continue;
    }
    const candidatePath = item.file ?? item.path ?? fallbackPath;
    const info = lookup(candidatePath);
    if (!info) {
      next.push(item);
      continue;
    }
    changed = true;
    if (emittedForPath.has(info.testPath)) continue;
    emittedForPath.add(info.testPath);
    next.push({
      ...item,
      code: 'story-criterion-mismatch',
      ...(Object.hasOwn(item, 'file') ? { file: info.testPath } : { path: info.testPath }),
      ...(Object.hasOwn(item, 'at') ? { at: 'criteria' } : {}),
      section: 'criteria',
      reason: info.reason,
      fix: info.fix,
      hint: info.fix,
      message: info.message,
    });
  }
  return { items: changed ? next : items, changed };
}

function rewriteLegacyCriterionMismatchPayload(payload, lookup) {
  const result = payload?.result;
  if (!result || typeof result !== 'object') return false;
  let mutated = false;
  let singleResultTestPath = null;
  const listedTests = Array.isArray(result.tests)
    ? result.tests
    : Array.isArray(result.report?.lint?.tests)
      ? result.report.lint.tests
      : null;
  if (Array.isArray(listedTests) && listedTests.length === 1 && typeof listedTests[0]?.path === 'string') {
    singleResultTestPath = listedTests[0].path;
  }

  if (Array.isArray(result.problems)) {
    const r = rewriteMismatchList(result.problems, lookup, singleResultTestPath);
    if (r.changed) {
      result.problems = r.items;
      mutated = true;
    }
  }
  if (Array.isArray(result.refusals)) {
    const r = rewriteMismatchList(result.refusals, lookup, singleResultTestPath);
    if (r.changed) {
      result.refusals = r.items;
      mutated = true;
    }
  }
  if (result.report && typeof result.report === 'object') {
    if (Array.isArray(result.report.problems)) {
      const r = rewriteMismatchList(result.report.problems, lookup, singleResultTestPath);
      if (r.changed) {
        result.report.problems = r.items;
        mutated = true;
      }
    }
    if (result.report.refusal && typeof result.report.refusal === 'object') {
      const r = rewriteMismatchList([result.report.refusal], lookup, singleResultTestPath);
      if (r.changed && r.items[0]) {
        result.report.refusal = r.items[0];
        mutated = true;
      }
    }
    if (Array.isArray(result.report.lint?.tests)) {
      for (const t of result.report.lint.tests) {
        if (t && typeof t === 'object' && Array.isArray(t.refusals)) {
          const r = rewriteMismatchList(t.refusals, lookup, t.path ?? singleResultTestPath);
          if (r.changed) {
            t.refusals = r.items;
            if (typeof t.reason === 'string' && t.reason.includes('criteria')) t.reason = r.items[0]?.message ?? t.reason;
            mutated = true;
          }
        }
      }
    }
  }
  if (Array.isArray(result.tests)) {
    for (const t of result.tests) {
      if (t && typeof t === 'object' && Array.isArray(t.refusals)) {
        const r = rewriteMismatchList(t.refusals, lookup, t.path ?? singleResultTestPath);
        if (r.changed) {
          t.refusals = r.items;
          if (typeof t.reason === 'string' && t.reason.includes('criteria')) t.reason = r.items[0]?.message ?? t.reason;
          mutated = true;
        }
      }
    }
  }
  return mutated;
}

function wrapFetchForLegacyCriteriaDiagnostic(baseFetch, cwd, ports) {
  if (typeof baseFetch !== 'function' || baseFetch.__pddLegacyCriteriaWrapped) return baseFetch;
  const wrapped = async (url, init) => {
    const res = await baseFetch(url, init);
    if (!res || typeof res.clone !== 'function') return res;
    const contentType = String(res.headers?.get?.('content-type') ?? '');
    if (contentType && !contentType.includes('json')) return res;
    let bodyText;
    try {
      bodyText = await res.clone().text();
    } catch {
      return res;
    }
    if (!bodyText || !bodyText.includes('story-criterion-mismatch')) return res;
    let parsed;
    try {
      parsed = JSON.parse(bodyText);
    } catch {
      return res;
    }
    const activeCwd = cwd ?? scenarioOverlayStorage.getStore()?.cwd ?? process.cwd();
    const root = repoTopRoot(activeCwd);
    if (!root) return res;
    const lookup = buildLegacyCriterionBindingLookup(root, ports);
    if (!rewriteLegacyCriterionMismatchPayload(parsed, lookup)) return res;
    const headers = new Headers(res.headers);
    headers.delete('content-length');
    headers.delete('content-encoding');
    return new Response(JSON.stringify(parsed), {
      status: res.status,
      statusText: res.statusText,
      headers,
    });
  };
  Object.defineProperty(wrapped, '__pddLegacyCriteriaWrapped', { value: true });
  return wrapped;
}

function seamRuntimePorts(ports = {}, { cwd = null } = {}) {
  const exit = hostExit();
  const baseFetch = ports.fetch ?? globalThis.fetch;
  const merged = withPortDefaults(seamSelectionPorts(ports), {
    exitFor: exit.exitFor,
    exitCodeFor: exit.exitCodeFor,
    promptTestsLabel: PROMPT_TESTS_LABEL,
  });
  if (typeof baseFetch === 'function') {
    merged.fetch = wrapFetchForLegacyCriteriaDiagnostic(baseFetch, cwd, merged);
  }
  if (merged.stdout) merged.stdout = normalizeHintStream(merged.stdout);
  if (merged.stderr) merged.stderr = normalizeHintStream(merged.stderr);
  return merged;
}

function withEligibilityDefault(ports = {}, defaultEligibility) {
  const chosen = ports.evidenceEligibility ?? ports.readEvidenceEligibility ?? defaultEligibility;
  return {
    ...ports,
    evidenceEligibility: chosen,
    readEvidenceEligibility: chosen,
  };
}

function resolveWorkflowBaseSha({ root, env = process.env, allRunsPort } = {}) {
  if (!root) return null;
  const readAllRuns = allRunsPort ?? req('./workflow-runs.mjs').allRuns;
  let realRoot;
  try {
    realRoot = realpathSync(root);
  } catch {
    return null;
  }
  const matching = readAllRuns({ cancelled: true }, { env }).filter(run => {
    try {
      return realpathSync(run.root) === realRoot;
    } catch {
      return false;
    }
  });
  return matching.length === 1 && /^[a-f0-9]{40}$/.test(matching[0].baseSha ?? '') ? matching[0].baseSha : null;
}

export function isStoryPath(...args) {
  return hostSelection().isStoryPath(...args);
}

export function hasAcceptance(...args) {
  return hostSelection().hasAcceptance(...args);
}

export function expectedTestPath(...args) {
  return hostSelection().expectedTestPath(...args);
}

export function matchTests(...args) {
  return hostSelection().matchTests(...args);
}

export function orphanSummary(...args) {
  return hostSelection().orphanSummary(...args);
}

function enrichFoundWithCompiledScenarios(found, readText) {
  if (!found || !Array.isArray(found.tests) || !found.root) return found;
  const compiler = hostScenarioCompiler();
  let anyCompiled = false;
  const compiledTests = found.tests.map(test => {
    if (test.error || !test.doc || typeof test.doc !== 'object' || Array.isArray(test.doc)) return test;
    let rawText;
    try {
      rawText = readText(test.path);
    } catch {
      return test;
    }
    if (typeof rawText !== 'string') return test;
    let rawParsed;
    try {
      rawParsed = compiler.parseExactScenarioJson(rawText);
    } catch {
      return test;
    }
    if (!compiler.needsScenarioCompile(rawParsed)) return test;
    const targetStoryPath = typeof rawParsed.story_path === 'string' && rawParsed.story_path
      ? rawParsed.story_path
      : test.storyPath;
    let storySource = test.storySource ?? null;
    if (storySource == null && typeof targetStoryPath === 'string' && targetStoryPath && (!found.visible || found.visible.has(targetStoryPath))) {
      try {
        storySource = readText(targetStoryPath);
      } catch {
        storySource = null;
      }
    }
    const compiled = compiler.compileScenarioText(rawText, {
      path: test.path,
      storyPath: test.storyPath,
      storySource,
    });
    if (compiled.refusal) {
      anyCompiled = true;
      const item = {
        ...test,
        error: `${test.path}: ${compiled.refusal.section}: ${compiled.refusal.message}`,
      };
      Object.defineProperty(item, 'rawDoc', { value: test.rawDoc ?? test.doc });
      Object.defineProperty(item, 'shortRefusal', { value: compiled.refusal });
      return item;
    }
    if (!compiled.changed) return test;
    anyCompiled = true;
    const item = { ...test, doc: compiled.doc };
    Object.defineProperty(item, 'rawDoc', { value: compiled.doc });
    Object.defineProperty(item, 'compiledText', { value: compiled.text });
    if (storySource !== null && storySource !== undefined) {
      Object.defineProperty(item, 'storySource', { value: storySource });
    }
    return item;
  });
  if (!anyCompiled) return found;
  const next = { ...found, tests: compiledTests };
  if (found.workspace !== undefined) Object.defineProperty(next, 'workspace', { value: found.workspace });
  return next;
}

export function findTests(input, ports = {}) {
  const found = rawFindTests(input, seamSelectionPorts(ports));
  if (!found || !Array.isArray(found.tests) || !found.root) return found;
  return enrichFoundWithCompiledScenarios(found, relPath => initialReadFileSync(join(found.root, relPath), 'utf8'));
}

function buildScenarioOverlay(root, ports = {}) {
  if (typeof root !== 'string' || !root) return null;
  let found;
  try {
    found = findTests({ root, excludeFixtureProjects: false }, ports);
  } catch {
    return null;
  }
  let realRoot = null;
  try {
    realRoot = realpathSync(root);
  } catch {
    realRoot = null;
  }
  const overlay = new Map();
  for (const test of found?.tests ?? []) {
    if (test.error || typeof test.compiledText !== 'string') continue;
    overlay.set(resolve(root, test.path), test.compiledText);
    if (realRoot) overlay.set(join(realRoot, test.path), test.compiledText);
  }
  return overlay.size ? overlay : null;
}

export function preflight(input) {
  if (!input?.root) return rawPreflight(input);
  const directTests = Array.isArray(input.selected) ? input.selected : input.found?.tests;
  if (Array.isArray(directTests)) {
    const map = new Map();
    for (const test of directTests) {
      if (test && !test.error && typeof test.compiledText === 'string') {
        map.set(resolve(input.root, test.path), test.compiledText);
      }
    }
    if (map.size === 0) return rawPreflight(input);
    return withScenarioOverlay({ root: input.root, map }, () => rawPreflight(input));
  }
  return withScenarioOverlay({ root: input.root, map: undefined }, () => rawPreflight(input));
}

function scanStoryAndTestPathsOnDisk(root) {
  const names = [];
  let realRoot;
  try {
    realRoot = realpathSync(root);
  } catch {
    return names;
  }
  const visitedDirs = new Set([realRoot]);
  const walk = (absDir, relPrefix, inStoryDir, inTestDir) => {
    let entries;
    try {
      entries = fs.readdirSync(absDir, { withFileTypes: true });
    } catch {
      return;
    }
    for (const ent of entries) {
      if (ent.name.startsWith('.') || ent.name === 'node_modules') continue;
      const rel = relPrefix ? `${relPrefix}/${ent.name}` : ent.name;
      const abs = join(absDir, ent.name);
      if (ent.isDirectory()) {
        walk(abs, rel, inStoryDir || ent.name === 'user_stories', inTestDir || ent.name === 'test' || ent.name === 'tests');
      } else if (ent.isFile()) {
        if ((inStoryDir && ent.name.endsWith('.md')) || (inTestDir && ent.name.endsWith('.json'))) {
          names.push(rel);
        }
      } else if (ent.isSymbolicLink()) {
        try {
          const realTarget = realpathSync(abs);
          if (realTarget !== realRoot && !realTarget.startsWith(realRoot + sep)) continue;
          const st = fs.statSync(realTarget);
          if (st.isDirectory() && !visitedDirs.has(realTarget)) {
            visitedDirs.add(realTarget);
            walk(
              realTarget,
              rel,
              inStoryDir || ent.name === 'user_stories',
              inTestDir || ent.name === 'test' || ent.name === 'tests',
            );
          } else if (st.isFile()) {
            if ((inStoryDir && ent.name.endsWith('.md')) || (inTestDir && ent.name.endsWith('.json'))) {
              names.push(rel);
            }
          }
        } catch {
          // Ignore broken or outside-root links here; strict captureSource enforces link rules on selected files.
        }
      }
    }
  };
  walk(realRoot, '', false, false);
  return names;
}

function visibleStoryAndTestPaths(root, { excludeFixtureProjects = false } = {}) {
  try {
    return [...discoveryVisibleFiles({ root, excludeFixtureProjects })];
  } catch (err) {
    if (err?.code?.startsWith?.('workspace-')) return [];
    return scanStoryAndTestPathsOnDisk(root);
  }
}

function captureWithScenarioCompile(runCapture, root, options, selPorts) {
  const callerPrepare = options?.prepareSource;
  const compiledDiskBytes = new Map();
  const siblingOverlayMap = new Map();
  const explicitRequested = Array.isArray(options?.tests) ? new Set(options.tests) : null;
  let realRoot = null;
  try {
    realRoot = realpathSync(root);
  } catch {
    realRoot = null;
  }

  const mergedPrepare = prepPorts => {
    const emptyTestsSelection = explicitRequested !== null && explicitRequested.size === 0;
    const precompiledByPath = new Map();
    const precompiledSelectedByPath = new Map();

    if (!emptyTestsSelection) {
      const excludeFixtureProjects = options?.excludeFixtureProjects ?? (options?.tests === undefined);
      const scanned = scanStoryAndTestPathsOnDisk(root).filter(p => {
        try {
          return Boolean(prepPorts.statFile(p)?.exists);
        } catch {
          return false;
        }
      });
      let names;
      try {
        names = scanned.length ? [...discoveryVisibleFiles({ root, files: scanned, excludeFixtureProjects })] : [];
      } catch (err) {
        names = err?.code?.startsWith?.('workspace-') ? [] : scanned;
      }
      if (names.length) {
        const storyPaths = names.filter(p => selPorts.isStoryPath(p));
        const matched = selPorts.matchTests(storyPaths, names).tests.filter(t => !t.problem);
        let candidates;
        if (explicitRequested !== null) {
          const selectedStories = new Set(
            matched
              .filter(
                t =>
                  (t.files ?? [t.path]).some(f => explicitRequested.has(f)) ||
                  explicitRequested.has(t.path) ||
                  (t.storyPath && explicitRequested.has(t.storyPath)),
              )
              .map(t => t.storyPath)
              .filter(Boolean),
          );
          candidates = matched.filter(
            t => explicitRequested.has(t.path) || (t.storyPath && selectedStories.has(t.storyPath)),
          );
        } else {
          candidates = matched;
        }

        const compiler = hostScenarioCompiler();
        for (const entry of candidates) {
          for (const testPath of entry.files ?? [entry.path]) {
            let probeText;
            try {
              const full = realpathSync(join(root, testPath));
              const checkRoot = realRoot ?? realpathSync(root);
              if (full !== checkRoot && !full.startsWith(checkRoot + sep)) continue;
              probeText = initialReadFileSync(full, 'utf8');
            } catch {
              continue;
            }
            let probeParsed;
            try {
              probeParsed = compiler.parseExactScenarioJson(probeText);
            } catch {
              continue;
            }
            if (!compiler.needsScenarioCompile(probeParsed)) continue;

            let rawBuf;
            try {
              if (!prepPorts.statFile(testPath, { presenceOnly: true })?.exists) continue;
              rawBuf = prepPorts.readFile(testPath);
            } catch {
              continue;
            }
            const rawText = rawBuf.toString('utf8');
            let rawParsed;
            try {
              rawParsed = compiler.parseExactScenarioJson(rawText);
            } catch {
              continue;
            }
            if (!compiler.needsScenarioCompile(rawParsed)) continue;
            const targetStoryPath = typeof rawParsed.story_path === 'string' && rawParsed.story_path
              ? rawParsed.story_path
              : entry.storyPath;
            let storySource = null;
            if (typeof targetStoryPath === 'string' && targetStoryPath) {
              try {
                if (prepPorts.statFile(targetStoryPath, { presenceOnly: true })?.exists) {
                  storySource = prepPorts.readFile(targetStoryPath).toString('utf8');
                }
              } catch {
                storySource = null;
              }
            }
            const compiled = compiler.compileScenarioText(rawText, {
              path: testPath,
              storyPath: entry.storyPath,
              storySource,
            });
            const isExplicitlySelected =
              explicitRequested === null ||
              explicitRequested.has(testPath) ||
              Boolean(entry.storyPath && explicitRequested.has(entry.storyPath));
            if (compiled.refusal) {
              if (isExplicitlySelected) {
                throw Object.assign(
                  new PreflightError(4, `${testPath}: ${compiled.refusal.section}: ${compiled.refusal.message}`),
                  { code: compiled.refusal.code, section: compiled.refusal.section },
                );
              }
              continue;
            }
            if (compiled.changed) {
              const item = {
                diskBuf: rawBuf,
                compiledBuf: Buffer.from(compiled.text, 'utf8'),
                compiledText: compiled.text,
              };
              precompiledByPath.set(testPath, item);
              if (isExplicitlySelected) {
                precompiledSelectedByPath.set(testPath, item);
              } else {
                compiledDiskBytes.set(testPath, rawBuf);
                siblingOverlayMap.set(resolve(root, testPath), compiled.text);
                if (realRoot) siblingOverlayMap.set(join(realRoot, testPath), compiled.text);
              }
            }
          }
        }
      }
    }

    const wrappedPrepPorts =
      callerPrepare !== undefined && precompiledByPath.size > 0
        ? {
            ...prepPorts,
            readFile(p, ...rest) {
              if (precompiledByPath.has(p)) {
                const entry = precompiledByPath.get(p);
                compiledDiskBytes.set(p, entry.diskBuf);
                return Buffer.from(entry.compiledBuf);
              }
              return prepPorts.readFile(p, ...rest);
            },
          }
        : prepPorts;

    const callerItems = callerPrepare !== undefined ? callerPrepare(wrappedPrepPorts) : [];
    if (!Array.isArray(callerItems) || precompiledSelectedByPath.size === 0) return callerItems;

    const callerSet = new Set(
      callerItems.map(item => (item && typeof item.path === 'string' ? item.path : null)).filter(Boolean),
    );
    const extraItems = [];
    for (const [testPath, entry] of precompiledSelectedByPath.entries()) {
      if (callerSet.has(testPath)) continue;
      compiledDiskBytes.set(testPath, entry.diskBuf);
      extraItems.push({ path: testPath, bytes: entry.compiledBuf });
    }
    return extraItems.length ? [...callerItems, ...extraItems] : callerItems;
  };

  const nextOptions = options === undefined
    ? { prepareSource: mergedPrepare }
    : { ...options, prepareSource: mergedPrepare };

  const captured = withScenarioOverlay(
    { map: siblingOverlayMap, interceptFd: true },
    () => runCapture(nextOptions),
  );
  if (captured && compiledDiskBytes.size > 0 && captured.source_commit && Array.isArray(captured.dirty_files)) {
    const headBlobs = gitHeadBlobOids(root, captured.source_commit, [...compiledDiskBytes.keys()]);
    const filteredDirty = captured.dirty_files.filter(p => {
      if (!compiledDiskBytes.has(p)) return true;
      const headOid = headBlobs.get(p);
      if (!headOid) return true;
      return gitBlobHash(compiledDiskBytes.get(p), captured.source_commit) !== headOid;
    });
    return {
      ...captured,
      dirty_files: filteredDirty,
      source_dirty: filteredDirty.length > 0,
    };
  }
  return captured;
}

export function captureSource(root, options, ports = {}) {
  const selPorts = seamSelectionPorts(ports);
  return captureWithScenarioCompile(nextOpts => rawCaptureSource(root, nextOpts, selPorts), root, options, selPorts);
}
captureSource.isDefaultCapture = true;

export function fillHashes(input, ports = {}) {
  return rawFillHashes(input, seamSelectionPorts(ports));
}

export function createStrictSourceAccess(root, workspace, ports = {}) {
  const selPorts = seamSelectionPorts(ports);
  const rawAccess = rawCreateStrictSourceAccess(root, workspace, selPorts);
  const wrapStrictFilePort = (rawPort, visSet) => {
    let storyByTest = null;
    const compiledCache = new Map();
    const resolveStoryMap = () => {
      if (storyByTest !== null) return storyByTest;
      storyByTest = new Map();
      const visArr = [...visSet];
      const matched = selPorts.matchTests(visArr.filter(p => selPorts.isStoryPath(p)), visArr).tests.filter(t => !t.problem);
      for (const entry of matched) {
        for (const testPath of entry.files ?? [entry.path]) {
          if (entry.storyPath) storyByTest.set(testPath, entry.storyPath);
        }
      }
      return storyByTest;
    };
    const maybeCompile = path => {
      if (typeof path !== 'string' || !path.endsWith('.json')) return null;
      const parts = path.split('/').slice(0, -1);
      if (!parts.some(part => part === 'test' || part === 'tests')) return null;
      if (compiledCache.has(path)) return compiledCache.get(path);
      compiledCache.set(path, null);
      let rawText;
      try {
        rawText = rawPort.read({ path }).content;
      } catch {
        return null;
      }
      const compiler = hostScenarioCompiler();
      let parsed;
      try {
        parsed = compiler.parseExactScenarioJson(rawText);
      } catch {
        return null;
      }
      if (!compiler.needsScenarioCompile(parsed)) return null;
      const storyMap = resolveStoryMap();
      const inferredStory = storyMap.get(path) ?? null;
      const targetStoryPath = typeof parsed.story_path === 'string' && parsed.story_path ? parsed.story_path : inferredStory;
      let storySource = null;
      if (typeof targetStoryPath === 'string' && targetStoryPath && visSet.has(targetStoryPath)) {
        try {
          storySource = rawPort.read({ path: targetStoryPath }).content;
        } catch {
          storySource = null;
        }
      }
      const compiled = compiler.compileScenarioText(rawText, {
        path,
        storyPath: inferredStory,
        storySource,
      });
      if (compiled.refusal || !compiled.changed) return null;
      const entry = { text: compiled.text, size: Buffer.byteLength(compiled.text, 'utf8') };
      compiledCache.set(path, entry);
      return entry;
    };
    return {
      ...rawPort,
      stat(arg) {
        const base = rawPort.stat(arg);
        if (!base?.exists) return base;
        const compiled = maybeCompile(arg?.path);
        return compiled ? { ...base, size: compiled.size } : base;
      },
      read(arg) {
        const raw = rawPort.read(arg);
        const compiled = maybeCompile(arg?.path);
        return compiled ? { ...raw, content: compiled.text } : raw;
      },
    };
  };
  return {
    sourceFilePort(visible) {
      const visSet = visible instanceof Set ? visible : new Set(visible ?? gitFiles(root));
      return wrapStrictFilePort(rawAccess.sourceFilePort(visSet), visSet);
    },
    findTests(opts = {}) {
      const rawFound = rawAccess.findTests(opts);
      if (!rawFound || !Array.isArray(rawFound.tests) || !rawFound.root) return rawFound;
      let strictPort = null;
      const getPort = () => (strictPort ??= rawAccess.sourceFilePort(rawFound.visible));
      return enrichFoundWithCompiledScenarios(rawFound, relPath => getPort().read({ path: relPath }).content);
    },
    captureSource(opts = {}) {
      return captureWithScenarioCompile(nextOpts => rawAccess.captureSource(nextOpts), root, opts, selPorts);
    },
  };
}

export function sharedSourceFiles(root, visible, options = {}, ports = {}) {
  const { resolveOwners } = req('./file-owner.mjs');
  return rawSharedSourceFiles(root, visible, options, withPortDefaults(seamSelectionPorts(ports), { resolveOwners }));
}

export function selectTests(found, words, options = {}) {
  return hostSelection().selectTests(found, words, {
    ...options,
    captureSource: options?.captureSource ?? captureSource,
  });
}

export function whyNoTests(root, visible, found, ports = {}) {
  return hostSelection().whyNoTests(
    root,
    visible,
    found,
    withPortDefaults(ports, {
      allowsPath: (r, p) => allowsRuntimePath(loadPreflightWorkspacePolicy({ root: r }), p),
      discoverTests: (r, files) => findTests({ root: r, files }),
    }),
  );
}

export function exitFor(value) {
  return hostExit().exitFor(value);
}

export function outcomeExitCode(outcomes, options, ports = {}) {
  return hostExit().outcomeExitCode(outcomes, options, withPortDefaults(ports, { outcomeOverall }));
}

export const exitCodeFor = outcomeExitCode;

export function summaryLine(rows, story = null, ports = {}) {
  return rawSummaryLine(rows, story, withPortDefaults(ports, { promptTestsLabel: PROMPT_TESTS_LABEL }));
}

export function storyLines(rows, ports = {}) {
  return rawStoryLines(rows, withPortDefaults(ports, { promptTestsLabel: PROMPT_TESTS_LABEL }));
}

export function renderJson(input, ports = {}) {
  return normalizeRuntimeHints(rawRenderJson(input, withPortDefaults(ports, { promptTestsLabel: PROMPT_TESTS_LABEL })));
}

export function renderText(input, ports = {}) {
  return normalizeRuntimeHints(rawRenderText(input, withPortDefaults(ports, { promptTestsLabel: PROMPT_TESTS_LABEL })));
}

function lintShortScenarioFiles(root, ports = {}) {
  if (typeof root !== 'string' || !root) return [];
  try {
    const found = findTests({ root, excludeFixtureProjects: true }, ports);
    return (found?.tests ?? [])
      .filter(test => test.shortRefusal && typeof test.error === 'string' && test.error.length > 0)
      .map(test => test.error);
  } catch {
    return [];
  }
}

function normalizeSelectionWords(rawWords, cwd, root, found) {
  let realCwd = cwd;
  let realRoot = root;
  try {
    realCwd = realpathSync(cwd);
    realRoot = realpathSync(root);
  } catch {}
  return rawWords.map(word => {
    if (typeof word !== 'string' || !word) return word;
    const abs = resolve(realCwd, word);
    const rel = relative(realRoot, abs).split(sep).join('/');
    const inside = rel !== '..' && !rel.startsWith('../');
    let isDir = false;
    try {
      isDir = inside && fs.statSync(abs).isDirectory();
    } catch {}
    return word.includes('/') || found.visible?.has(rel) || isDir ? (rel || '.') : word;
  });
}

function runEmitV1(input = {}, ports = {}) {
  const stdout = ports.stdout ?? process.stdout;
  const stderr = ports.stderr ?? process.stderr;
  const options = input?.options ?? {};
  const jsonMode = options['--json'] === true;
  const badKey = Object.keys(options).find(key => !['--lint', '--emit-v1', '--json'].includes(key));
  if (badKey) {
    stderr.write('pdd lint --emit-v1 accepts only --json and Story selections.\n');
    return 2;
  }
  const cwd = input?.cwd ?? process.cwd();
  const root = repoTopRoot(cwd);
  if (!root) {
    stderr.write('No Git project root is available.\n');
    return 2;
  }
  const rawWords = commandWords(input);
  const found = findTests({ root, excludeFixtureProjects: rawWords.length === 0 }, ports);
  const normalizedWords = normalizeSelectionWords(rawWords, cwd, root, found);
  const selection = selectTests(found, normalizedWords);
  if (selection.unknown?.length || selection.untested?.length || !selection.selected?.length) {
    const missingNames = [...(selection.unknown ?? []), ...(selection.untested ?? [])];
    stderr.write(
      missingNames.length
        ? `No selected Story tests: ${missingNames.join(', ')}\n`
        : 'No selected Story tests.\n',
    );
    return 2;
  }
  const compiler = hostScenarioCompiler();
  const sourcePort = createStrictSourceAccess(root, found.workspace, ports).sourceFilePort(found.visible);
  const errors = [];
  const emitted = [];
  for (const test of selection.selected) {
    if (test.error) {
      errors.push({
        path: test.path,
        story_path: test.storyPath ?? null,
        code: test.shortRefusal?.code ?? 'invalid-scenario',
        section: test.shortRefusal?.section ?? 'document',
        message: test.error,
      });
      continue;
    }
    let rawText;
    try {
      rawText = sourcePort.read({ path: test.path }).content;
    } catch (err) {
      errors.push({
        path: test.path,
        story_path: test.storyPath ?? null,
        code: 'unreadable-scenario',
        section: 'document',
        message: `${test.path}: ${err?.message ?? String(err)}`,
      });
      continue;
    }
    let storySource = test.storySource ?? null;
    if (storySource === null && typeof test.storyPath === 'string' && test.storyPath) {
      try {
        storySource = sourcePort.read({ path: test.storyPath }).content;
      } catch {
        storySource = null;
      }
    }
    const compiled = compiler.compileScenarioText(rawText, {
      path: test.path,
      storyPath: test.storyPath,
      storySource,
      space: 2,
    });
    if (compiled.refusal) {
      errors.push({
        path: test.path,
        story_path: test.storyPath ?? null,
        code: compiled.refusal.code,
        section: compiled.refusal.section,
        message: `${test.path}: ${compiled.refusal.section}: ${compiled.refusal.message}`,
      });
      continue;
    }
    const finalExact = compiled.exactDoc;
    emitted.push({
      path: test.path,
      story_path: test.storyPath ?? finalExact?.story_path ?? null,
      changed: compiled.changed,
      text: compiler.stringifyExactScenarioJson(finalExact, 2) + '\n',
      scenario: finalExact,
    });
  }
  if (errors.length > 0) {
    if (jsonMode) {
      stdout.write(compiler.stringifyExactScenarioJson({ ok: false, errors }, 2) + '\n');
    } else {
      for (const err of errors) stderr.write(`${err.message}\n`);
    }
    return 4;
  }
  if (jsonMode) {
    stdout.write(
      compiler.stringifyExactScenarioJson(
        {
          ok: true,
          scenarios: emitted.map(({ path, story_path, changed, scenario }) => ({
            path,
            story_path,
            changed,
            scenario,
          })),
        },
        2,
      ) + '\n',
    );
    return 0;
  }
  if (emitted.length === 1) {
    stdout.write(emitted[0].text);
    return 0;
  }
  stdout.write(compiler.stringifyExactScenarioJson(emitted.map(item => item.scenario), 2) + '\n');
  return 0;
}

function runBindCriteria(input = {}, ports = {}) {
  const stdout = ports.stdout ?? process.stdout;
  const stderr = ports.stderr ?? process.stderr;
  const options = input?.options ?? {};
  const jsonMode = options['--json'] === true;
  const badKey = Object.keys(options).find(key => !['--lint', '--bind-criteria', '--json'].includes(key));
  if (badKey) {
    stderr.write('pdd lint --bind-criteria accepts only --json and Story selections.\n');
    return 2;
  }
  const cwd = input?.cwd ?? process.cwd();
  const root = repoTopRoot(cwd);
  if (!root) {
    stderr.write('No Git project root is available.\n');
    return 2;
  }
  let realRoot;
  try {
    realRoot = realpathSync(root);
  } catch {
    stderr.write('No Git project root is available.\n');
    return 2;
  }

  const rawWords = commandWords(input);
  const found = findTests({ root, excludeFixtureProjects: rawWords.length === 0 }, ports);
  const normalizedWords = normalizeSelectionWords(rawWords, cwd, root, found);
  const selection = selectTests(found, normalizedWords);
  if (selection.unknown?.length || selection.untested?.length || !selection.selected?.length) {
    const missingNames = [...(selection.unknown ?? []), ...(selection.untested ?? [])];
    stderr.write(
      missingNames.length
        ? `No selected Story tests: ${missingNames.join(', ')}\n`
        : 'No selected Story tests.\n',
    );
    return 2;
  }

  const compiler = hostScenarioCompiler();
  const errors = [];
  const plannedWrites = [];
  const seenTestPaths = new Set();

  for (const test of selection.selected) {
    const filePaths = Array.isArray(test.files) && test.files.length ? test.files : [test.path];
    for (const testPath of filePaths) {
      if (seenTestPaths.has(testPath)) continue;
      seenTestPaths.add(testPath);
      if (found.workspace && !allowsRuntimePath(found.workspace, testPath)) {
        errors.push({
          path: testPath,
          story_path: test.storyPath ?? null,
          code: 'workspace-excluded',
          section: 'document',
          message: `${testPath}: excluded by workspace policy.`,
        });
        continue;
      }
      let fullTestPath;
      let rawText;
      try {
        fullTestPath = realpathSync(join(realRoot, testPath));
        if (fullTestPath !== realRoot && !fullTestPath.startsWith(realRoot + sep)) {
          throw new Error('Test file resolves outside repository root.');
        }
        rawText = initialReadFileSync(fullTestPath, 'utf8');
      } catch (err) {
        errors.push({
          path: testPath,
          story_path: test.storyPath ?? null,
          code: 'unreadable-scenario',
          section: 'document',
          message: `${testPath}: ${err?.message ?? String(err)}`,
        });
        continue;
      }

      let targetStoryPath = test.storyPath ?? null;
      try {
        const parsed = compiler.parseExactScenarioJson(rawText);
        if (typeof parsed?.story_path === 'string' && parsed.story_path) {
          targetStoryPath = parsed.story_path;
        }
      } catch {}

      let storySource = null;
      if (typeof targetStoryPath === 'string' && targetStoryPath) {
        try {
          const fullStory = realpathSync(join(realRoot, targetStoryPath));
          if (fullStory === realRoot || fullStory.startsWith(realRoot + sep)) {
            storySource = initialReadFileSync(fullStory, 'utf8');
          }
        } catch {
          storySource = null;
        }
      }

      const bound = compiler.bindScenarioCriteriaText(rawText, {
        path: testPath,
        storyPath: targetStoryPath,
        storySource,
        space: 2,
      });
      if (bound.refusal) {
        errors.push({
          path: testPath,
          story_path: targetStoryPath,
          code: bound.refusal.code,
          section: bound.refusal.section,
          message: bound.refusal.message,
          ...(bound.refusal.hint ? { hint: bound.refusal.hint } : {}),
        });
        continue;
      }
      plannedWrites.push({
        path: testPath,
        fullPath: fullTestPath,
        story_path: targetStoryPath,
        changed: bound.changed,
        nextText: bound.text,
        bound_ids: bound.boundIds ?? [],
      });
    }
  }

  if (errors.length > 0) {
    if (jsonMode) {
      stdout.write(JSON.stringify({ ok: false, exit_code: 4, refusals: errors }, null, 2) + '\n');
    } else {
      for (const err of errors) {
        stderr.write(`${err.message}\n`);
        if (err.hint) stderr.write(`${err.hint}\n`);
      }
    }
    return 4;
  }

  for (const item of plannedWrites) {
    if (!item.changed) continue;
    fs.writeFileSync(item.fullPath, item.nextText, 'utf8');
  }

  if (jsonMode) {
    stdout.write(
      JSON.stringify(
        {
          ok: true,
          exit_code: 0,
          updated: plannedWrites.filter(r => r.changed).map(r => r.path),
          unchanged: plannedWrites.filter(r => !r.changed).map(r => r.path),
          files: plannedWrites.map(({ path, story_path, changed, bound_ids }) => ({
            path,
            story_path,
            changed,
            bound_ids,
          })),
        },
        null,
        2,
      ) + '\n',
    );
    return 0;
  }

  for (const item of plannedWrites) {
    if (item.changed) {
      stdout.write(
        `Bound ${item.bound_ids.length} criterion ID${item.bound_ids.length === 1 ? '' : 's'} in ${item.path} (${item.story_path}). Review with git diff.\n`,
      );
    } else {
      stdout.write(`${item.path}: criteria already bound to ${item.story_path}.\n`);
    }
  }
  return 0;
}

const DERIVATION_MAX_LENGTH = 10_000;
const DERIVATION_MAX_DEPTH = 128;
const DERIVATION_MAX_EXP = 10_000;
const DERIVATION_MAX_DIGITS = 10_001;
const DERIVATION_MAX_DEC_PLACES = 10_000;
const DERIVATION_MAX_OUTPUT_LENGTH = 20_004;
const NUMERIC_DERIVATION_OPS = new Set(['equals', 'not_equals', 'gt', 'lt', 'gte', 'lte', 'at_least', 'at_most']);
const UNARY_DERIVATION_FNS = new Set(['floor', 'ceil', 'trunc', 'round_half_up', 'round_half_even']);
const VARIADIC_DERIVATION_FNS = new Set(['min', 'max']);

let cachedMaxComponent = null;
const maxComponentLimit = () => (cachedMaxComponent ??= 10n ** BigInt(DERIVATION_MAX_DIGITS));

function derivationSyntaxError(message) {
  const err = new SyntaxError(message);
  err.code = 'scenario-derivation-invalid';
  return err;
}

const bigAbs = value => (value < 0n ? -value : value);

function bigGcd(a, b) {
  let x = bigAbs(a);
  let y = bigAbs(b);
  while (y !== 0n) {
    const t = x % y;
    x = y;
    y = t;
  }
  return x;
}

function makeRational(n, d = 1n) {
  if (d === 0n) throw derivationSyntaxError('Division by zero');
  if (n === 0n) return { n: 0n, d: 1n };
  let num = n;
  let den = d;
  if (den < 0n) {
    num = -num;
    den = -den;
  }
  const g = bigGcd(num, den);
  num /= g;
  den /= g;
  const limit = maxComponentLimit();
  if (bigAbs(num) >= limit || den >= limit) {
    throw derivationSyntaxError(`Value exceeds ${DERIVATION_MAX_DIGITS}-digit rational limit`);
  }
  return { n: num, d: den };
}

const intRational = n => makeRational(n, 1n);
const addRat = (a, b) => makeRational(a.n * b.d + b.n * a.d, a.d * b.d);
const subRat = (a, b) => makeRational(a.n * b.d - b.n * a.d, a.d * b.d);
const mulRat = (a, b) => makeRational(a.n * b.n, a.d * b.d);
const divRat = (a, b) => {
  if (b.n === 0n) throw derivationSyntaxError('Division by zero');
  return makeRational(a.n * b.d, a.d * b.n);
};
const cmpRat = (a, b) => {
  const diff = a.n * b.d - b.n * a.d;
  return diff < 0n ? -1 : diff > 0n ? 1 : 0;
};

function truncQuotient(a, b) {
  const q = divRat(a, b);
  return q.n / q.d;
}

function floorRat(r) {
  let q = r.n / r.d;
  if (r.n % r.d < 0n) q -= 1n;
  return intRational(q);
}

function ceilRat(r) {
  let q = r.n / r.d;
  if (r.n % r.d > 0n) q += 1n;
  return intRational(q);
}

function roundHalfRat(r, toEven) {
  const neg = r.n < 0n;
  const absN = neg ? -r.n : r.n;
  let q = absN / r.d;
  const twice = (absN % r.d) * 2n;
  if (twice > r.d || (twice === r.d && (!toEven || (q & 1n) === 1n))) q += 1n;
  return intRational(neg ? -q : q);
}

function applyDerivationFn(name, args) {
  if (VARIADIC_DERIVATION_FNS.has(name)) {
    if (!args.length) throw derivationSyntaxError(`${name}() requires at least one argument`);
    let best = args[0];
    for (let i = 1; i < args.length; i++) {
      const cmp = cmpRat(args[i], best);
      if ((name === 'min' && cmp < 0) || (name === 'max' && cmp > 0)) best = args[i];
    }
    return best;
  }
  if (!UNARY_DERIVATION_FNS.has(name)) throw derivationSyntaxError(`Unknown function "${name}"`);
  if (args.length !== 1) throw derivationSyntaxError(`${name}() expects exactly 1 argument`);
  const value = args[0];
  if (name === 'floor') return floorRat(value);
  if (name === 'ceil') return ceilRat(value);
  if (name === 'trunc') return intRational(value.n / value.d);
  if (name === 'round_half_up') return roundHalfRat(value, false);
  return roundHalfRat(value, true);
}

function parseDecimalLiteral(raw) {
  const match = /^(?:(\d+)(?:\.(\d+))?|\.(\d+))(?:[eE]([+-]?\d+))?$/.exec(raw);
  if (!match) throw derivationSyntaxError(`Invalid numeric literal "${raw}"`);
  const intPart = match[1] ?? '';
  const fracPart = match[2] ?? match[3] ?? '';
  const expText = match[4] ?? '';
  let exp = 0;
  if (expText) {
    if (expText.replace(/^[+-]/, '').length > 6) throw derivationSyntaxError(`Exponent exceeds limit of ${DERIVATION_MAX_EXP}`);
    exp = Number.parseInt(expText, 10);
    if (!Number.isFinite(exp) || Math.abs(exp) > DERIVATION_MAX_EXP) {
      throw derivationSyntaxError(`Exponent exceeds limit of ${DERIVATION_MAX_EXP}`);
    }
  }
  const combined = `${intPart}${fracPart}`.replace(/^0+/, '');
  if (!combined) return { n: 0n, d: 1n };
  const shift = exp - fracPart.length;
  if (shift >= 0) {
    if (combined.length + shift > DERIVATION_MAX_DIGITS) {
      throw derivationSyntaxError(`Numeric literal exceeds ${DERIVATION_MAX_DIGITS}-digit limit`);
    }
    return makeRational(BigInt(combined) * (10n ** BigInt(shift)), 1n);
  }
  let trimZeros = 0;
  while (trimZeros < combined.length && combined[combined.length - 1 - trimZeros] === '0') trimZeros += 1;
  const trimmed = combined.slice(0, combined.length - trimZeros);
  const netShift = shift + trimZeros;
  if (netShift >= 0) {
    if (trimmed.length + netShift > DERIVATION_MAX_DIGITS) {
      throw derivationSyntaxError(`Numeric literal exceeds ${DERIVATION_MAX_DIGITS}-digit limit`);
    }
    return makeRational(BigInt(trimmed) * (10n ** BigInt(netShift)), 1n);
  }
  const negShift = -netShift;
  if (negShift > DERIVATION_MAX_DIGITS) {
    throw derivationSyntaxError(`Numeric literal exceeds ${DERIVATION_MAX_DIGITS}-digit limit`);
  }
  return makeRational(BigInt(trimmed), 10n ** BigInt(negShift));
}

function tokenizeDerivation(source) {
  const tokens = [];
  let i = 0;
  while (i < source.length) {
    const ch = source[i];
    if (ch === ' ' || ch === '\t' || ch === '\r' || ch === '\n') { i += 1; continue; }
    if ((ch >= '0' && ch <= '9') || ch === '.') {
      const start = i;
      while (i < source.length && source[i] >= '0' && source[i] <= '9') i += 1;
      if (i < source.length && source[i] === '.') {
        i += 1;
        const fracStart = i;
        while (i < source.length && source[i] >= '0' && source[i] <= '9') i += 1;
        if (i === fracStart) throw derivationSyntaxError(`Invalid numeric literal "${source.slice(start, i)}"`);
      }
      if (i < source.length && (source[i] === 'e' || source[i] === 'E')) {
        i += 1;
        if (i < source.length && (source[i] === '+' || source[i] === '-')) i += 1;
        const expStart = i;
        while (i < source.length && source[i] >= '0' && source[i] <= '9') i += 1;
        if (i === expStart) throw derivationSyntaxError(`Invalid exponent in "${source.slice(start, i)}"`);
      }
      if (i < source.length && /[A-Za-z_.]/.test(source[i])) {
        throw derivationSyntaxError(`Unexpected character "${source[i]}" after number`);
      }
      tokens.push({ type: 'num', value: parseDecimalLiteral(source.slice(start, i)) });
      continue;
    }
    if ((ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z') || ch === '_') {
      const start = i;
      while (i < source.length && /[A-Za-z0-9_]/.test(source[i])) i += 1;
      const word = source.slice(start, i);
      if (word === 'div' || word === 'mod') tokens.push({ type: 'op', value: word });
      else tokens.push({ type: 'ident', value: word });
      continue;
    }
    if ('+-*/(),'.includes(ch)) {
      tokens.push({ type: ch === '(' || ch === ')' || ch === ',' ? ch : 'op', value: ch });
      i += 1;
      continue;
    }
    throw derivationSyntaxError(`Unexpected character "${ch}"`);
  }
  return tokens;
}

function formatRational(r) {
  let out;
  if (r.n === 0n) out = '0';
  else if (r.d === 1n) out = r.n.toString();
  else {
    let rem = r.d;
    let c2 = 0;
    let c5 = 0;
    while (rem % 2n === 0n) { rem /= 2n; c2 += 1; }
    while (rem % 5n === 0n) { rem /= 5n; c5 += 1; }
    const places = Math.max(c2, c5);
    if (rem === 1n && places <= DERIVATION_MAX_DEC_PLACES) {
      const scale = (2n ** BigInt(places - c2)) * (5n ** BigInt(places - c5));
      const digits = (bigAbs(r.n) * scale).toString().padStart(places + 1, '0');
      const intPart = digits.slice(0, digits.length - places);
      const fracPart = digits.slice(digits.length - places).replace(/0+$/, '');
      out = `${r.n < 0n ? '-' : ''}${fracPart ? `${intPart}.${fracPart}` : intPart}`;
    } else {
      out = `${r.n.toString()}/${r.d.toString()}`;
    }
  }
  if (out.length > DERIVATION_MAX_OUTPUT_LENGTH) {
    throw derivationSyntaxError(`Result exceeds ${DERIVATION_MAX_OUTPUT_LENGTH}-character output limit`);
  }
  return out;
}

function evaluateDerivationRational(expression) {
  if (typeof expression !== 'string' || !expression.trim()) {
    throw derivationSyntaxError('Derivation expression must be a nonblank string');
  }
  if (expression.length > DERIVATION_MAX_LENGTH) {
    throw derivationSyntaxError(`Derivation expression exceeds ${DERIVATION_MAX_LENGTH}-character limit`);
  }
  const tokens = tokenizeDerivation(expression);
  if (!tokens.length) throw derivationSyntaxError('Derivation expression is empty');
  let pos = 0;
  let depth = 0;
  const peek = () => tokens[pos];
  const enterDepth = () => {
    depth += 1;
    if (depth > DERIVATION_MAX_DEPTH) throw derivationSyntaxError(`Nesting depth exceeds limit of ${DERIVATION_MAX_DEPTH}`);
  };
  const leaveDepth = () => { depth -= 1; };

  function parseAdd() {
    let left = parseMul();
    while (peek()?.type === 'op' && (peek().value === '+' || peek().value === '-')) {
      const op = tokens[pos++].value;
      const right = parseMul();
      left = op === '+' ? addRat(left, right) : subRat(left, right);
    }
    return left;
  }

  function parseMul() {
    let left = parseUnary();
    while (peek()?.type === 'op' && (peek().value === '*' || peek().value === '/' || peek().value === 'div' || peek().value === 'mod')) {
      const op = tokens[pos++].value;
      const right = parseUnary();
      if (op === '*') left = mulRat(left, right);
      else if (op === '/') left = divRat(left, right);
      else if (op === 'div') left = intRational(truncQuotient(left, right));
      else left = subRat(left, mulRat(intRational(truncQuotient(left, right)), right));
    }
    return left;
  }

  function parseUnary() {
    if (peek()?.type === 'op' && (peek().value === '+' || peek().value === '-')) {
      const op = tokens[pos++].value;
      enterDepth();
      try {
        const inner = parseUnary();
        return op === '-' ? makeRational(-inner.n, inner.d) : inner;
      } finally {
        leaveDepth();
      }
    }
    return parsePrimary();
  }

  function parsePrimary() {
    const tok = peek();
    if (!tok) throw derivationSyntaxError('Unexpected end of expression');
    if (tok.type === 'num') { pos += 1; return tok.value; }
    if (tok.type === '(') {
      pos += 1;
      enterDepth();
      try {
        const value = parseAdd();
        if (peek()?.type !== ')') throw derivationSyntaxError('Missing closing parenthesis ")"');
        pos += 1;
        return value;
      } finally {
        leaveDepth();
      }
    }
    if (tok.type === 'ident') {
      pos += 1;
      if (peek()?.type !== '(') throw derivationSyntaxError(`Unknown identifier "${tok.value}"`);
      pos += 1;
      enterDepth();
      try {
        const args = [];
        if (peek()?.type !== ')') {
          args.push(parseAdd());
          while (peek()?.type === ',') {
            pos += 1;
            args.push(parseAdd());
          }
        }
        if (peek()?.type !== ')') throw derivationSyntaxError(`Missing closing parenthesis in ${tok.value}()`);
        pos += 1;
        return applyDerivationFn(tok.value, args);
      } finally {
        leaveDepth();
      }
    }
    throw derivationSyntaxError(`Unexpected token "${tok.value}"`);
  }

  const value = parseAdd();
  if (pos < tokens.length) throw derivationSyntaxError(`Unexpected trailing token "${tokens[pos].value}"`);
  return value;
}

function evaluateDerivationFallback(expression) {
  return formatRational(evaluateDerivationRational(expression));
}

function expectedNumericRational(value) {
  if (typeof value === 'bigint') {
    const text = value.toString();
    return { text, rat: intRational(value) };
  }
  if (typeof value === 'number' && Number.isFinite(value)) {
    const spelling = exactNumberSpelling(value);
    const text = typeof spelling === 'string' && spelling.length > 0 ? spelling : (Object.is(value, -0) ? '0' : String(value));
    return { text, rat: evaluateDerivationRational(text) };
  }
  return null;
}

function checkDerivationFallback(check) {
  if (!check || typeof check !== 'object' || !Object.hasOwn(check, 'derivation') || check.derivation === undefined) {
    return null;
  }
  if (typeof check.derivation !== 'string' || !check.derivation.trim()) {
    return { code: 'scenario-derivation-invalid', message: 'Check "derivation" must be a nonblank string.' };
  }
  if (!NUMERIC_DERIVATION_OPS.has(check.op)) {
    return { code: 'scenario-derivation-invalid', message: `Check "derivation" is only allowed on numeric comparison checks, not "${String(check.op)}".` };
  }
  if (Object.hasOwn(check, 'ref_target') || Object.hasOwn(check, 'ref_path')) {
    return { code: 'scenario-derivation-invalid', message: 'Check "derivation" requires a literal numeric "value", not a relational reference.' };
  }
  const expected = expectedNumericRational(check.value);
  if (!expected) {
    return { code: 'scenario-derivation-invalid', message: 'Check "derivation" requires a finite numeric "value".' };
  }
  let actualRat;
  let actualText;
  try {
    actualRat = evaluateDerivationRational(check.derivation);
    actualText = formatRational(actualRat);
  } catch (error) {
    return { code: 'scenario-derivation-invalid', message: error?.message || 'Invalid derivation expression.' };
  }
  if (cmpRat(actualRat, expected.rat) !== 0) {
    return {
      code: 'scenario-derivation-mismatch',
      message: `Derivation "${check.derivation}" evaluated to ${actualText}, which does not match expected value ${expected.text}.`,
    };
  }
  return null;
}

function scenarioDerivationRefusalFallback(doc) {
  const steps = Array.isArray(doc?.steps) ? doc.steps : [];
  for (let i = 0; i < steps.length; i++) {
    const checks = Array.isArray(steps[i]?.checks) ? steps[i].checks : [];
    for (let j = 0; j < checks.length; j++) {
      const refusal = checkDerivation(checks[j]);
      if (refusal) {
        return {
          code: refusal.code,
          section: `steps[${i}].checks[${j}].derivation`,
          message: refusal.message,
          step: i + 1,
        };
      }
    }
  }
  return null;
}

export function evaluateDerivation(expression) {
  const fn = rawRuntimeScenarioJsonSlice()?.evaluateDerivation;
  return typeof fn === 'function' ? fn(expression) : evaluateDerivationFallback(expression);
}

export function checkDerivation(check) {
  const fn = rawRuntimeScenarioJsonSlice()?.checkDerivation;
  return typeof fn === 'function' ? fn(check) : checkDerivationFallback(check);
}

export function scenarioDerivationRefusal(doc) {
  const fn = rawRuntimePreflightSlice()?.scenarioDerivationRefusal;
  return typeof fn === 'function' ? fn(doc) : scenarioDerivationRefusalFallback(doc);
}

export function runtimeScenarioJsonSlice() {
  return {
    ...rawRuntimeScenarioJsonSlice(),
    checkDerivation,
    evaluateDerivation,
  };
}

export function runtimePreflightSlice() {
  const mod = rawRuntimePreflightSlice();
  return {
    ...mod,
    NO_TESTS,
    captureSource,
    createStrictSourceAccess,
    expectedTestPath,
    fillHashes,
    findTests,
    hasAcceptance,
    isStoryPath,
    lintLocalHygiene: (input, ports = {}) => {
      const { isTestOwnedPath, promptClaims, resolveOwners } = req('./file-owner.mjs');
      const { lintRepoAntiPatterns } = req('./repo-hygiene-lint.mjs');
      const baseWarnings = mod.lintLocalHygiene(
        input,
        withPortDefaults(seamSelectionPorts(ports), { isTestOwnedPath, promptClaims, resolveOwners }),
      );
      return [
        ...new Set([
          ...baseWarnings,
          ...lintRepoAntiPatterns(input),
          ...lintShortScenarioFiles(input?.root, ports),
        ]),
      ];
    },
    matchTests,
    orphanSummary,
    preflight,
    prepareHashSelection: (input, ports = {}) => mod.prepareHashSelection(input, seamSelectionPorts(ports)),
    scenarioDerivationRefusal,
    selectTests,
    sharedSourceFiles,
    whyNoTests,
  };
}

export function runtimeOutcomeSlice() {
  const mod = rawRuntimeOutcomeSlice();
  return {
    ...mod,
    COMMAND_EXIT_CODE,
    STATE_EXIT_CODES,
    exitFor,
    outcomeExitCode,
  };
}

export function runtimeOutputSlice() {
  const mod = rawRuntimeOutputSlice();
  return {
    ...mod,
    PROMPT_TESTS_LABEL,
    PROMPT_TESTS_WORDS,
    exitCodeFor,
    outcomeExitCode,
    renderJson,
    renderText,
    storyLines,
    summaryLine,
  };
}

export function runtimeClientSlice() {
  const mod = rawRuntimeClientSlice();
  return {
    ...mod,
    acquireCaseWriteOwnership,
    applyPendingCase,
    applyPendingCaseWithHandoff,
    checkRuntimeHealth,
    createSavedStoryEvidenceReader,
    health,
    readContractHistory,
    runtimeOrigin,
    runtimeWorkspaceMigrationStore,
    resendableStoryChecks,
    saveDoorCase,
    saveDoorCaseResult,
    savedStoryEvidence,
  };
}

export function buildCheckPlan(input, ports = {}) {
  const { headerPrompts } = req('./file-owner.mjs');
  return runtimeBuildCheckPlan(input, withPortDefaults(seamSelectionPorts(ports), { headerPrompts }));
}

export function selectJourneys(tests, selector, ports = {}) {
  return rawSelectJourneys(tests, selector, seamSelectionPorts(ports));
}

export function composeProductTry(input, ports = {}) {
  const { parseProductDocuments, parseProductWorldWriters } = req('./product-documents.mjs');
  const compiler = hostScenarioCompiler();
  let effectivePorts = withPortDefaults(seamSelectionPorts(ports), { parseProductDocuments, parseProductWorldWriters });
  if (
    input &&
    typeof input === 'object' &&
    typeof input.root === 'string' &&
    typeof input.testPath === 'string' &&
    input.testPath &&
    typeof effectivePorts.readFile === 'function'
  ) {
    const targetAbs = join(input.root, input.testPath);
    const baseRead = effectivePorts.readFile;
    const baseStat = effectivePorts.statFile;
    effectivePorts = {
      ...effectivePorts,
      readFile(fullPath, ...rest) {
        const raw = baseRead(fullPath, ...rest);
        if (fullPath !== targetAbs) return raw;
        const rawText = typeof raw === 'string' ? raw : Buffer.isBuffer(raw) ? raw.toString('utf8') : null;
        if (rawText === null) return raw;
        let parsed;
        try {
          parsed = compiler.parseExactScenarioJson(rawText);
        } catch {
          return raw;
        }
        if (!compiler.needsScenarioCompile(parsed)) return raw;
        let pairedStoryPath = typeof parsed.story_path === 'string' && parsed.story_path ? parsed.story_path : null;
        if (!pairedStoryPath) {
          const base = basename(input.testPath, '.json');
          const stems = [base];
          for (let at = base.lastIndexOf('.'); at > 0; at = base.lastIndexOf('.', at - 1)) {
            stems.push(base.slice(0, at));
          }
          for (const cand of stems.flatMap(stem => [`user_stories/journeys/${stem}.md`, `user_stories/${stem}.md`])) {
            try {
              if (typeof baseStat === 'function' && baseStat(join(input.root, cand), { presenceOnly: true })?.exists) {
                pairedStoryPath = cand;
                break;
              }
            } catch {}
          }
          if (!pairedStoryPath && typeof input.journey === 'string' && input.journey) {
            pairedStoryPath = `user_stories/journeys/${base}.md`;
          }
        }
        let storySource = null;
        if (pairedStoryPath) {
          try {
            if (typeof baseStat === 'function' && baseStat(join(input.root, pairedStoryPath), { presenceOnly: true })?.exists) {
              const sRaw = baseRead(join(input.root, pairedStoryPath));
              storySource = typeof sRaw === 'string' ? sRaw : Buffer.isBuffer(sRaw) ? sRaw.toString('utf8') : null;
            }
          } catch {
            storySource = null;
          }
        }
        const compiled = compiler.compileScenarioText(rawText, {
          path: input.testPath,
          storyPath: pairedStoryPath,
          storySource,
        });
        if (compiled.refusal || !compiled.changed) return raw;
        return Buffer.isBuffer(raw) ? Buffer.from(compiled.text, 'utf8') : compiled.text;
      },
    };
  }
  return runtimeComposeProductTry(input, effectivePorts);
}

export function readAgentScenarios(input, ports = {}) {
  return rawReadAgentScenarios(input, seamSelectionPorts(ports));
}

export function createTryGuide(options = {}) {
  const givenPorts = options.ports ?? {};
  const lazyEligibility = (...args) => req('./workflow-eligibility.mjs').readEvidenceEligibility(...args);
  return runtimeCreateTryGuide({
    ...options,
    ports: withPortDefaults(seamSelectionPorts(withEligibilityDefault(givenPorts, lazyEligibility)), {
      redaction: seamRedaction(givenPorts),
    }),
  });
}

export function buildProjectCard(input = {}) {
  const lazyEligibility = (...args) => req('./workflow-eligibility.mjs').readEvidenceEligibility(...args);
  return runtimeBuildProjectCard(withEligibilityDefault(input, lazyEligibility));
}

export function readContractHistory(input, ports = {}) {
  const lazyEligibility = (...args) => req('./workflow-eligibility.mjs').readEvidenceEligibility(...args);
  const cwd = input?.root ?? input?.cwd ?? process.cwd();
  return withScenarioOverlay(
    { cwd, ports, interceptFd: true },
    () => runtimeReadContractHistory(input, seamSelectionPorts(withEligibilityDefault(ports, lazyEligibility))),
  );
}

export function runContracts(input, ports = {}) {
  runtimeClientSlice();
  const lazyEligibility = (...args) => req('./workflow-eligibility.mjs').readEvidenceEligibility(...args);
  const cwd = input?.cwd ?? process.cwd();
  return withScenarioOverlay(
    { cwd, ports, interceptFd: true },
    () => runtimeRunContracts(input, seamSelectionPorts(withEligibilityDefault(ports, lazyEligibility))),
  );
}

export async function runJobs(input = {}, ports = {}) {
  const { NAMES } = await import('./command-catalog.mjs');
  const commands = input?.client?.commands ?? { test: NAMES.test, lint: NAMES.lint, simulate: NAMES.simulate };
  const client = { ...(input?.client ?? {}), commands };
  return runtimeRunJobs({ ...input, client }, ports);
}

export async function checkRuntimeHealth(input, ports = {}) {
  await import('./secret-redaction.mjs');
  return runtimeCheckHealth(input, withPortDefaults(ports, { redaction: seamRedaction(ports) }));
}

export async function loadRuntimeClient() {
  const [{ DEFAULT_RUNTIME_URL: defaultUrl, checkRuntimeHealth: rawCheckHealth, runtimeOrigin: rawOrigin }] =
    await Promise.all([runtimeLoadClient(), import('./secret-redaction.mjs')]);
  const boundHealth = (input, ports = {}) =>
    rawCheckHealth(input, withPortDefaults(ports, { redaction: seamRedaction(ports) }));
  return {
    DEFAULT_RUNTIME_URL: defaultUrl,
    runtimeOrigin: rawOrigin,
    checkRuntimeHealth: boundHealth,
    health: boundHealth,
  };
}

const NON_EXEC_CHECK_FLAGS = [
  '--lint', '--local', '--files', '--explain-bindings',
  '--read', '--retry', '--request', '--screen', '--drawing', '--look', '--emit-v1', '--bind-criteria',
];
const PROMPT_DEP_LINK_RE = /\[[^\[\]\r\n]*\]\(([^()\s#\r\n]+\.prompt\.md)(?:#[^()\s\r\n]*)?\)/g;
const PORT_CALL_TOKEN_RE = /\b[A-Za-z][A-Za-z0-9_-]*\.[A-Za-z][A-Za-z0-9_-]*\b/;

function stripInlineCodeAndPromptLinks(text) {
  let out = '';
  let i = 0;
  const len = text.length;
  while (i < len) {
    const ch = text[i];
    if (ch === '`') {
      const close = text.indexOf('`', i + 1);
      if (close >= 0) {
        out += ' ';
        i = close + 1;
        continue;
      }
      out += text.slice(i);
      break;
    }
    if (ch === '(') {
      let j = i + 1;
      while (j < len && text[j] !== ')' && text[j] !== '(' && text[j] !== '\r' && text[j] !== '\n') {
        j += 1;
      }
      if (j < len && text[j] === ')') {
        const inner = text.slice(i + 1, j);
        out += inner.includes('.prompt.md') ? ' ' : text.slice(i, j + 1);
        i = j + 1;
        continue;
      }
      out += text.slice(i, j);
      i = j;
      continue;
    }
    out += ch;
    i += 1;
  }
  return out;
}

function extractDepsSection(markdown) {
  const lines = markdown.split(/\r?\n/);
  let inDeps = false;
  let inFence = false;
  const out = [];
  for (const line of lines) {
    if (/^\s*(?:```|~~~)/.test(line)) {
      inFence = !inFence;
      continue;
    }
    if (!inFence && /^##\s+/.test(line)) {
      inDeps = /^##\s+Dependencies\s*$/i.test(line.trim());
      continue;
    }
    if (inDeps && !inFence) out.push(line);
  }
  return out.join('\n');
}

function computeGraphAwareDefaultMaxCalls(input, ports) {
  const opts = input?.options ?? {};
  if (opts['--max-calls'] !== undefined) return undefined;
  if (NON_EXEC_CHECK_FLAGS.some(flag => opts[flag] !== undefined)) return undefined;
  const cwd = input?.cwd ?? process.cwd();
  const root = repoTopRoot(cwd);
  if (!root) return undefined;
  const rawWords = commandWords(input);
  let found;
  try {
    found = findTests({ root, excludeFixtureProjects: rawWords.length === 0 }, ports);
  } catch {
    return undefined;
  }
  if (!found?.tests?.length) return undefined;
  let candidates = found.tests;
  if (!opts['--affected'] && rawWords.length > 0) {
    const normalizedWords = normalizeSelectionWords(rawWords, cwd, root, found);
    try {
      const sel = selectTests(found, normalizedWords);
      if (sel?.selected?.length) candidates = sel.selected;
    } catch {
      return undefined;
    }
  }
  const readyTests = candidates.filter(
    t => t && !t.error && Array.isArray(t.doc?.steps) && t.doc.steps.length > 0,
  );
  if (!readyTests.length) return undefined;

  const promptCache = new Map();
  const inspectPrompt = relPath => {
    if (promptCache.has(relPath)) return promptCache.get(relPath);
    const info = { deps: [], extraCallWeight: 0, hasPortToken: false, isNativeOnly: false };
    promptCache.set(relPath, info);
    if (found.visible && !found.visible.has(relPath)) return info;
    let text;
    try {
      text = initialReadFileSync(join(root, relPath), 'utf8');
    } catch {
      return info;
    }
    try {
      const fm = parsePromptFrontmatter(text);
      if (fm?.frontmatter?.kind === 'native-only') info.isNativeOnly = true;
    } catch {}
    const promptDir = dirname(relPath);
    const resolveRel = target => {
      const joined = relative('.', join(promptDir === '.' ? '' : promptDir, target)).split(sep).join('/');
      return joined && !joined.startsWith('..') ? joined : null;
    };
    const depsText = extractDepsSection(text);
    for (const match of depsText.matchAll(PROMPT_DEP_LINK_RE)) {
      const depPath = resolveRel(match[1]);
      if (depPath && depPath !== relPath) info.deps.push(depPath);
    }
    for (const block of interfaceBlocks(text)) {
      try {
        const iface = JSON.parse(text.slice(block.indices[1][0], block.indices[1][1]));
        if (iface?.kind === 'native-only') info.isNativeOnly = true;
        if (Array.isArray(iface?.calls)) {
          for (const call of iface.calls) {
            if (typeof call?.target === 'string' && call.target.endsWith('.prompt.md')) {
              const depPath = call.target.startsWith('prompts/') ? call.target : (resolveRel(call.target) ?? call.target);
              if (depPath && depPath !== relPath) info.deps.push(depPath);
              if (Number.isInteger(call.max_calls) && call.max_calls > 1) {
                info.extraCallWeight += Math.min(8, call.max_calls - 1);
              }
            }
          }
        }
        if (Array.isArray(iface?.resources) && iface.resources.some(r => r?.kind === 'port')) {
          info.hasPortToken = true;
        }
      } catch {}
    }
    const stripped = stripInlineCodeAndPromptLinks(text);
    if (PORT_CALL_TOKEN_RE.test(stripped)) info.hasPortToken = true;
    info.deps = [...new Set(info.deps)];
    return info;
  };

  let maxCap = 0;
  let maxFallback = 0;
  let sumFallbacks = 0;
  for (const test of readyTests) {
    const doc = test.doc;
    const steps = doc.steps.length;
    const fallback = defaultMaxCalls(doc);
    maxFallback = Math.max(maxFallback, fallback);
    sumFallbacks += fallback;
    if (steps <= 2) {
      maxCap = Math.max(maxCap, fallback);
      continue;
    }
    const entryPrompts = new Set(
      doc.steps.map(s => s?.entry_path).filter(p => typeof p === 'string' && p.endsWith('.prompt.md')),
    );
    const visited = new Set();
    const queue = [...entryPrompts];
    let childPrompts = 0;
    let extraWeight = 0;
    let promptHasPorts = false;
    while (queue.length > 0 && visited.size < 64) {
      const cur = queue.shift();
      if (visited.has(cur)) continue;
      visited.add(cur);
      const info = inspectPrompt(cur);
      if (info.isNativeOnly) continue;
      if (!entryPrompts.has(cur)) childPrompts += 1;
      extraWeight += info.extraCallWeight;
      if (info.hasPortToken) promptHasPorts = true;
      for (const dep of info.deps) {
        if (!visited.has(dep)) queue.push(dep);
      }
    }
    const hasScenarioWorldOrPorts =
      (doc.initial_world && typeof doc.initial_world === 'object' && Object.keys(doc.initial_world).length > 0) ||
      (doc.simulation && typeof doc.simulation === 'object' && Object.keys(doc.simulation).length > 0) ||
      doc.steps.some(s => Array.isArray(s?.simulation_overrides) && s.simulation_overrides.length > 0) ||
      promptHasPorts;
    const perStep = 4 + (hasScenarioWorldOrPorts ? 1 : 0) + Math.min(8, childPrompts * 3 + extraWeight);
    const cap = Math.min(fallback, Math.max(24, steps * perStep + 6));
    maxCap = Math.max(maxCap, cap);
  }
  if (maxCap > 0 && maxCap < maxFallback && maxCap * readyTests.length < sumFallbacks) {
    return maxCap;
  }
  return undefined;
}

export async function runCheck(input = {}, ports = {}) {
  const [
    ,
    { headerPrompts, isTestOwnedPath, promptClaims, resolveOwners },
    { readEvidenceEligibility },
    { allRuns },
    { assessNativeEvidence, resultLines, usableResult },
    { lintSvgLayouts },
    { lintRepoAntiPatterns },
    { compareScreen, formatScreenComparison },
  ] = await Promise.all([
    import('./secret-redaction.mjs'),
    import('./file-owner.mjs'),
    import('./workflow-eligibility.mjs'),
    import('./workflow-runs.mjs'),
    import('./workflow-results.mjs'),
    import('./svg-layout.mjs'),
    import('./repo-hygiene-lint.mjs'),
    import('./screen-compare.mjs'),
  ]);
  if (input?.options?.['--emit-v1'] && input?.options?.['--bind-criteria']) {
    const stderr = ports.stderr ?? process.stderr;
    stderr.write('Use either --emit-v1 or --bind-criteria, not both.\n');
    return 2;
  }
  if (input?.options?.['--emit-v1']) {
    return runEmitV1(input, ports);
  }
  if (input?.options?.['--bind-criteria']) {
    return runBindCriteria(input, ports);
  }
  const env = ports.env ?? process.env;
  const client = input?.client
    ? { ...input.client, version: input.client.version ?? clientVersion() }
    : { version: clientVersion() };
  const graphCap = computeGraphAwareDefaultMaxCalls(input, ports);
  const effectiveInput =
    graphCap !== undefined
      ? { ...input, options: { ...(input.options ?? {}), '--max-calls': graphCap }, client }
      : { ...input, client };
  const cwd = effectiveInput?.cwd ?? process.cwd();
  const lazyOverlay = { cwd, ports, map: undefined };

  return withScenarioOverlay(lazyOverlay, () =>
    runtimeRunCheck(
      effectiveInput,
      seamRuntimePorts(
        withPortDefaults(withEligibilityDefault(ports, readEvidenceEligibility), {
          headerPrompts,
          isTestOwnedPath,
          promptClaims,
          resolveOwners,
          allRuns,
          workflowBaseSha: ({ root, env: runEnv }) =>
            resolveWorkflowBaseSha({ root, env: runEnv ?? env, allRunsPort: ports.allRuns ?? allRuns }),
          assessNativeEvidence,
          usableResult,
          resultLines,
          lintSvgLayouts: arg => [
            ...lintSvgLayouts(arg),
            ...lintRepoAntiPatterns(arg),
            ...lintShortScenarioFiles(arg?.root, ports),
          ],
          compareScreen,
          formatScreenComparison,
          redaction: seamRedaction(ports),
        }),
        { cwd },
      ),
    ),
  );
}

export async function askAgent(input = {}, ports = {}) {
  const explicitRun = input?.run ?? ports.run ?? ports.runAgentProcess ?? ports.agents?.run;
  const run = explicitRun ?? (await import('./agent-adapters.mjs')).runAgentProcess;
  return runtimeAskAgent({ ...input, run }, ports);
}

export async function runTry(input = {}, ports = {}) {
  const [
    ,
    { loadAgentDefinitions },
    { readEvidenceEligibility },
    { parseProductDocuments, parseProductWorldWriters },
    { askApproval, lineReader, promptPath },
  ] = await Promise.all([
    import('./secret-redaction.mjs'),
    import('./agent-config.mjs'),
    import('./workflow-eligibility.mjs'),
    import('./product-documents.mjs'),
    import('./prompt-approve.mjs'),
  ]);
  const defaultDiscoverAgents = async (...args) => (await import('./agent-adapters.mjs')).discoverAgents(...args);
  const defaultAskAgent = async (turnInput, ...rest) => askAgent(turnInput, ...rest);
  const cwd = input?.cwd ?? process.cwd();
  const defaultAgentBridge = (context, test, tryId, opts, link) =>
    createAgentBridge(context, test, tryId, opts, link, {
      redaction: ports.redaction ?? seamRedaction(ports),
      redactSecrets: ports.redactSecrets,
      loadAgentDefinitions: ports.loadAgentDefinitions ?? ports.agents?.loadDefinitions ?? loadAgentDefinitions,
      discoverAgents: ports.discoverAgents ?? ports.agents?.list,
      runAgentProcess: ports.runAgentProcess ?? ports.agents?.run,
      askAgent: ports.askAgent ?? ports.agents?.ask,
      evidenceEligibility: ports.evidenceEligibility ?? ports.readEvidenceEligibility ?? readEvidenceEligibility,
      guidePorts: ports.guidePorts,
    });
  const lazyOverlay = { cwd, ports, map: undefined };
  return withScenarioOverlay(lazyOverlay, () =>
    runtimeRunTry(
      input,
      seamRuntimePorts(
        withPortDefaults(withEligibilityDefault(ports, readEvidenceEligibility), {
          tryLauncherUrl: TRY_LAUNCHER_URL,
          agentBridge: defaultAgentBridge,
          loadAgentDefinitions: ports.loadAgentDefinitions ?? ports.agents?.loadDefinitions ?? loadAgentDefinitions,
          discoverAgents: ports.discoverAgents ?? ports.agents?.list ?? defaultDiscoverAgents,
          askAgent: ports.askAgent ?? ports.agents?.ask ?? defaultAskAgent,
          parseProductDocuments,
          parseProductWorldWriters,
          askApproval,
          lineReader,
          promptPath,
          files: wrapCaseFilesForShortJson(ports.files, ports),
          redaction: seamRedaction(ports),
        }),
        { cwd },
      ),
    ),
  );
}

export async function createAgentBridge(context, test, tryId, options, link, seamPorts = {}) {
  const [, { loadAgentDefinitions }, { discoverAgents, runAgentProcess }, { readEvidenceEligibility }] = await Promise.all([
    import('./secret-redaction.mjs'),
    import('./agent-config.mjs'),
    import('./agent-adapters.mjs'),
    import('./workflow-eligibility.mjs'),
  ]);
  const boundRun = seamPorts.runAgentProcess ?? seamPorts.agents?.run ?? runAgentProcess;
  const defaultAsk = turnInput =>
    runtimeAskAgent({ ...turnInput, run: turnInput?.run ?? boundRun }, seamPorts);
  return runtimeCreateAgentBridge(
    context,
    test,
    tryId,
    options,
    link,
    seamRuntimePorts(
      withPortDefaults(withEligibilityDefault(seamPorts, readEvidenceEligibility), {
        loadAgentDefinitions:
          seamPorts.loadAgentDefinitions ?? seamPorts.agents?.loadDefinitions ?? loadAgentDefinitions,
        discoverAgents: seamPorts.discoverAgents ?? seamPorts.agents?.list ?? discoverAgents,
        runAgentProcess: boundRun,
        askAgent: seamPorts.askAgent ?? seamPorts.agents?.ask ?? defaultAsk,
        redaction: seamRedaction(seamPorts),
      }),
    ),
  );
}

export async function openCli(context, test, sessionId, options) {
  const nextContext =
    context && typeof context.ports === 'object' && context.ports !== null
      ? { ...context, ports: seamRuntimePorts(withPortDefaults(context.ports, { tryLauncherUrl: TRY_LAUNCHER_URL })) }
      : context;
  return runtimeOpenCli(nextContext, test, sessionId, options);
}

export async function openServe(context, test, sessionId, options) {
  const nextContext =
    context && typeof context.ports === 'object' && context.ports !== null
      ? { ...context, ports: seamRuntimePorts(context.ports) }
      : context;
  return runtimeOpenServe(nextContext, test, sessionId, options);
}

export async function runShim(descriptorPath, argv, ports = {}) {
  const [, { lineReader }] = await Promise.all([
    import('./secret-redaction.mjs'),
    import('./prompt-approve.mjs'),
  ]);
  return runtimeRunShim(
    descriptorPath,
    argv,
    seamRuntimePorts(
      withPortDefaults(ports, {
        lineReader,
        redaction: seamRedaction(ports),
        files: wrapCaseFilesForShortJson(ports.files, ports),
      }),
    ),
  );
}

export async function saveLast(input) {
  const { lineReader } = await import('./prompt-approve.mjs');
  const nextInput =
    input && typeof input === 'object'
      ? {
          ...input,
          ports: seamRuntimePorts(seamCasePorts(withPortDefaults(input.ports ?? {}, { lineReader }))),
        }
      : input;
  return runtimeSaveLast(nextInput);
}

export async function runDoorCall(descriptor, input, ports = {}) {
  await import('./secret-redaction.mjs');
  return runtimeRunDoorCall(descriptor, input, seamRuntimePorts(withPortDefaults(ports, { redaction: seamRedaction(ports) })));
}

export async function readTryOwner(input = {}, ports = {}) {
  const [, { readEvidenceEligibility }, { parseProductDocuments, parseProductWorldWriters }] = await Promise.all([
    import('./secret-redaction.mjs'),
    import('./workflow-eligibility.mjs'),
    import('./product-documents.mjs'),
  ]);
  return runtimeReadTryOwner(
    input,
    seamRuntimePorts(
      withPortDefaults(withEligibilityDefault(ports, readEvidenceEligibility), {
        tryLauncherUrl: TRY_LAUNCHER_URL,
        parseProductDocuments,
        parseProductWorldWriters,
        redaction: seamRedaction(ports),
      }),
    ),
  );
}

export async function observeTryCall(input = {}, ports = {}) {
  await import('./secret-redaction.mjs');
  return runtimeObserveTryCall(
    input,
    seamSelectionPorts(withPortDefaults(ports, { redaction: seamRedaction(ports) })),
  );
}

export function createTryTools(input, ports = {}) {
  const lazyEligibility = (...args) => req('./workflow-eligibility.mjs').readEvidenceEligibility(...args);
  const lazyParseProductDocuments = (...args) => req('./product-documents.mjs').parseProductDocuments(...args);
  const lazyParseProductWorldWriters = (...args) => req('./product-documents.mjs').parseProductWorldWriters(...args);
  return runtimeCreateTryTools(
    input,
    seamRuntimePorts(
      withPortDefaults(withEligibilityDefault(ports, lazyEligibility), {
        tryLauncherUrl: TRY_LAUNCHER_URL,
        parseProductDocuments: lazyParseProductDocuments,
        parseProductWorldWriters: lazyParseProductWorldWriters,
        redaction: seamRedaction(ports),
      }),
    ),
  );
}

export async function runMcp(input, ports = {}) {
  const [, { readEvidenceEligibility }, { parseProductDocuments, parseProductWorldWriters }] = await Promise.all([
    import('./secret-redaction.mjs'),
    import('./workflow-eligibility.mjs'),
    import('./product-documents.mjs'),
  ]);
  return runtimeRunMcp(
    input,
    seamRuntimePorts(
      withPortDefaults(withEligibilityDefault(ports, readEvidenceEligibility), {
        clientVersion: clientVersion(),
        tryLauncherUrl: TRY_LAUNCHER_URL,
        parseProductDocuments,
        parseProductWorldWriters,
        applyPendingCaseWithHandoff,
        redaction: seamRedaction(ports),
      }),
    ),
  );
}

function createDefaultCaseFiles() {
  return {
    lstat: fs.lstatSync,
    read: initialReadFileSync,
    open: fs.openSync,
    write: fs.writeFileSync,
    close: fs.closeSync,
    sync: fs.fsyncSync,
    stat: fs.fstatSync,
    mkdir: fs.mkdirSync,
    list: fs.readdirSync,
    rename: fs.renameSync,
    unlink: fs.unlinkSync,
    link: fs.linkSync,
    realpath: realpathSync,
  };
}

function wrapCaseFilesForShortJson(baseFiles, ports = {}) {
  if (baseFiles?.__pddShortCaseFiles) return baseFiles;
  const rawFiles = baseFiles ?? createDefaultCaseFiles();
  const openReadPaths = new Map();

  const convertShortText = (filePath, rawResult, options) => {
    if (
      typeof filePath !== 'string' ||
      !filePath.endsWith('.json') ||
      filePath.includes(`${sep}node_modules${sep}`) ||
      filePath.includes(`${sep}.pdd${sep}`) ||
      filePath.endsWith('.received.json') ||
      filePath.endsWith('.transaction.json') ||
      filePath.endsWith('.meta.json') ||
      filePath.endsWith('.origin.json')
    ) {
      return rawResult;
    }
    const rawText = Buffer.isBuffer(rawResult) ? rawResult.toString('utf8') : String(rawResult);
    const compiler = hostScenarioCompiler();
    let parsed;
    try {
      parsed = compiler.parseExactScenarioJson(rawText);
    } catch {
      return rawResult;
    }
    if (!compiler.needsScenarioCompile(parsed)) return rawResult;
    const root = repoTopRoot(dirname(filePath));
    if (!root) return rawResult;
    let realRoot = root;
    let realFile = filePath;
    try {
      realRoot = rawFiles.realpath(root);
      realFile = rawFiles.realpath(filePath);
    } catch {}
    if (realFile !== realRoot && !realFile.startsWith(realRoot + sep)) return rawResult;
    const relPath = relative(realRoot, realFile).split(sep).join('/');
    const formatOut = outText => {
      if (typeof options === 'string') return Buffer.from(outText, 'utf8').toString(options);
      if (options && typeof options === 'object' && options.encoding) {
        return Buffer.from(outText, 'utf8').toString(options.encoding);
      }
      return Buffer.isBuffer(rawResult) ? Buffer.from(outText, 'utf8') : outText;
    };
    let storySource = null;
    let inferredStoryPath = typeof parsed.story_path === 'string' && parsed.story_path ? parsed.story_path : null;
    try {
      const found = findTests({ root: realRoot, excludeFixtureProjects: false }, ports);
      const matched = (found?.tests ?? []).find(t => t.path === relPath);
      if (matched && !matched.error && typeof matched.compiledText === 'string') {
        return formatOut(matched.compiledText);
      }
      if (matched?.storyPath && !inferredStoryPath) inferredStoryPath = matched.storyPath;
      if (typeof matched?.storySource === 'string') storySource = matched.storySource;
    } catch {}
    if (!storySource && inferredStoryPath) {
      try {
        const fullStory = rawFiles.realpath(join(realRoot, inferredStoryPath));
        if (fullStory === realRoot || fullStory.startsWith(realRoot + sep)) {
          storySource = initialReadFileSync(fullStory, 'utf8');
        }
      } catch {}
    }
    const compiled = compiler.compileScenarioText(rawText, {
      path: relPath,
      storyPath: inferredStoryPath,
      storySource,
    });
    if (compiled.refusal || !compiled.changed) return rawResult;
    return formatOut(compiled.text);
  };

  const wrapped = {
    ...rawFiles,
    open(filePath, flags, mode) {
      const fd = rawFiles.open(filePath, flags, mode);
      const writeMask =
        (fs.constants?.O_WRONLY ?? 1) |
        (fs.constants?.O_RDWR ?? 2) |
        (fs.constants?.O_CREAT ?? 0) |
        (fs.constants?.O_TRUNC ?? 0);
      if (typeof fd === 'number' && typeof filePath === 'string' && (Number(flags) & writeMask) === 0) {
        openReadPaths.set(fd, resolve(filePath));
      }
      return fd;
    },
    close(fd) {
      openReadPaths.delete(fd);
      return rawFiles.close(fd);
    },
    read(fdOrPath, options) {
      const rawResult = rawFiles.read(fdOrPath, options);
      const filePath =
        typeof fdOrPath === 'number'
          ? openReadPaths.get(fdOrPath)
          : typeof fdOrPath === 'string'
            ? resolve(fdOrPath)
            : null;
      return filePath ? convertShortText(filePath, rawResult, options) : rawResult;
    },
  };
  Object.defineProperty(wrapped, '__pddShortCaseFiles', { value: true });
  return wrapped;
}

function seamCasePorts(ports = {}) {
  const base = seamSelectionPorts(ports);
  return {
    ...base,
    files: wrapCaseFilesForShortJson(ports.files, ports),
  };
}

export async function migrateRuntimeWorkspace(input, ports = {}) {
  const { readEvidenceEligibility } = await import('./workflow-eligibility.mjs');
  return runtimeMigrateWorkspace(input, seamCasePorts(withEligibilityDefault(ports, readEvidenceEligibility)));
}

export function runtimeWorkspaceMigrationStore(input, given = {}) {
  return rawRuntimeWorkspaceMigrationStore(input, seamCasePorts(given));
}

function normalizeSavedCaseCriteria(root, saved, options, ports) {
  if (
    options?.rawBytes !== undefined ||
    !saved ||
    typeof saved !== 'object' ||
    !saved.test ||
    typeof saved.test !== 'object' ||
    !Array.isArray(saved.test.criteria) ||
    !saved.test.criteria.some(c => typeof c?.id === 'string' && c.id.startsWith('ac-sha256-'))
  ) {
    return saved;
  }
  const targetPath = options?.seedTest?.path ?? saved.original_path;
  const storyPath = options?.seedTest?.storyPath ?? saved.story_path ?? saved.test.story_path;
  if (typeof root !== 'string' || typeof targetPath !== 'string') return saved;
  try {
    const found = findTests({ root, excludeFixtureProjects: false }, ports);
    const orig = (found?.tests ?? []).find(t => t.path === targetPath && (!storyPath || t.storyPath === storyPath));
    if (!Array.isArray(orig?.doc?.criteria) || !orig.doc.criteria.length) return saved;
    if (orig.doc.criteria.some(c => typeof c?.id === 'string' && c.id.startsWith('ac-sha256-'))) return saved;
    const localIdByText = new Map(
      orig.doc.criteria
        .filter(c => c && typeof c.id === 'string' && typeof c.text === 'string')
        .map(c => [c.text, c.id]),
    );
    const idMap = new Map();
    const mappedCriteria = saved.test.criteria.map(c => {
      if (!c || typeof c !== 'object' || typeof c.id !== 'string' || typeof c.text !== 'string') return c;
      const localId = localIdByText.get(c.text);
      if (!localId) return c;
      idMap.set(c.id, localId);
      return { ...c, id: localId };
    });
    if (!idMap.size) return saved;
    const mapId = id => (typeof id === 'string' && idMap.has(id) ? idMap.get(id) : id);
    const mappedSteps = Array.isArray(saved.test.steps)
      ? saved.test.steps.map(step =>
          !step || typeof step !== 'object'
            ? step
            : {
                ...step,
                ...(Array.isArray(step.checks)
                  ? {
                      checks: step.checks.map(chk =>
                        chk && typeof chk === 'object' && Object.hasOwn(chk, 'criterion_id')
                          ? { ...chk, criterion_id: mapId(chk.criterion_id) }
                          : chk,
                      ),
                    }
                  : {}),
                ...(Array.isArray(step.simulation_overrides)
                  ? {
                      simulation_overrides: step.simulation_overrides.map(ov =>
                        ov && typeof ov === 'object' && Object.hasOwn(ov, 'criterion_id')
                          ? { ...ov, criterion_id: mapId(ov.criterion_id) }
                          : ov,
                      ),
                    }
                  : {}),
              },
        )
      : saved.test.steps;
    return {
      ...saved,
      test: {
        ...saved.test,
        criteria: mappedCriteria,
        steps: mappedSteps,
      },
    };
  } catch {
    return saved;
  }
}

export function saveDoorCaseResult(root, saved, options = {}) {
  const basePorts = options?.ports ?? (options?.env ? { env: options.env } : {});
  const casePortsBound = seamCasePorts(basePorts);
  const normalizedSaved = normalizeSavedCaseCriteria(root, saved, options, casePortsBound);
  return rawSaveDoorCaseResult(root, normalizedSaved, { ...options, ports: casePortsBound });
}

export function saveDoorCase(root, saved, options = {}) {
  return saveDoorCaseResult(root, saved, options).message;
}

export async function acquireCaseWriteOwnership(input, ports = {}) {
  return rawAcquireCaseWriteOwnership(input, seamCasePorts(ports));
}

export async function applyPendingCase(input, ports = {}) {
  return rawApplyPendingCase(input, seamCasePorts(ports));
}

export async function applyPendingCaseWithHandoff(input, ports = {}) {
  return rawApplyPendingCaseWithHandoff(input, seamCasePorts(ports));
}

export function createSavedStoryEvidenceReader(ports = {}) {
  return rawCreateSavedStoryEvidenceReader(seamSelectionPorts(ports));
}

export async function resendableStoryChecks(input, ports = {}) {
  return rawResendableStoryChecks(input, seamSelectionPorts(ports));
}

export async function savedStoryEvidence(input, ports = {}) {
  return rawSavedStoryEvidence(input, seamSelectionPorts(ports));
}

function commandWords(input = {}) {
  if (Array.isArray(input?.words)) return [...input.words];
  if (Array.isArray(input?.tests)) {
    return input.tests
      .map(item => (typeof item === 'string' ? item : item?.path ?? item?.story))
      .filter(item => typeof item === 'string' && item.length > 0);
  }
  return [];
}

function buildCheckInput(input = {}, { defaultCache = false, extraOptions = {} } = {}) {
  const cwd = input?.cwd ?? input?.root;
  const options = { ...(input?.options ?? {}), ...extraOptions };
  return {
    ...(cwd !== undefined ? { cwd } : {}),
    words: commandWords(input),
    options,
    cache: input?.cache ?? defaultCache,
    ...(input?.client !== undefined ? { client: input.client } : {}),
    ...(input?.workflow !== undefined ? { workflow: input.workflow } : {}),
  };
}

const LOCAL_WHAT_FLAGS = Object.freeze({
  files: '--files',
  'explain-bindings': '--explain-bindings',
});

const SIMULATE_MODES = new Set(['open', 'cli', 'serve', 'save-last', 'stop']);

export async function check(input = {}, ports = {}) {
  const extraOptions =
    input?.affected === true && input?.options?.['--affected'] === undefined ? { '--affected': true } : {};
  return runCheck(buildCheckInput(input, { defaultCache: true, extraOptions }), ports);
}

export async function lint(input = {}, ports = {}) {
  const extraOptions = {
    '--lint': true,
    ...(input?.local === true && input?.options?.['--local'] === undefined ? { '--local': true } : {}),
    ...(input?.emitV1 === true && input?.options?.['--emit-v1'] === undefined ? { '--emit-v1': true } : {}),
    ...(input?.bindCriteria === true && input?.options?.['--bind-criteria'] === undefined ? { '--bind-criteria': true } : {}),
  };
  return runCheck(buildCheckInput(input, { defaultCache: true, extraOptions }), ports);
}

export async function read(input = {}, ports = {}) {
  const cwd = input?.cwd ?? input?.root;
  const target = input?.call_id ?? input?.batch;
  const words = Array.isArray(input?.words)
    ? [...input.words]
    : target !== undefined && target !== null && target !== ''
      ? [String(target)]
      : [];
  return runCheck(
    {
      ...(cwd !== undefined ? { cwd } : {}),
      words,
      options: { ...(input?.options ?? {}), '--read': true },
      cache: input?.cache ?? false,
      ...(input?.client !== undefined ? { client: input.client } : {}),
      ...(input?.workflow !== undefined ? { workflow: input.workflow } : {}),
    },
    ports,
  );
}

export async function retry(input = {}, ports = {}) {
  const cwd = input?.cwd ?? input?.root;
  const words = Array.isArray(input?.words) ? [...input.words] : [];
  const retryTarget = input?.batch ?? input?.options?.['--retry'];
  return runCheck(
    {
      ...(cwd !== undefined ? { cwd } : {}),
      words,
      options: {
        ...(input?.options ?? {}),
        ...(retryTarget !== undefined ? { '--retry': retryTarget } : {}),
      },
      cache: input?.cache ?? false,
      ...(input?.client !== undefined ? { client: input.client } : {}),
      ...(input?.workflow !== undefined ? { workflow: input.workflow } : {}),
    },
    ports,
  );
}

export async function local(input = {}, ports = {}) {
  const flag = LOCAL_WHAT_FLAGS[input?.what];
  if (!flag) {
    throw new RangeError(`Unsupported local inspection mode: ${String(input?.what)}`);
  }
  const extraOptions = { [flag]: true };
  return runCheck({ ...buildCheckInput(input, { defaultCache: false, extraOptions }), cache: false }, ports);
}

export async function simulate(input = {}, ports = {}) {
  if (input?.mode !== undefined && !SIMULATE_MODES.has(input.mode)) {
    throw new RangeError(`Unsupported simulate mode: ${String(input.mode)}`);
  }
  const cwd = input?.cwd ?? input?.root;
  const options = { ...(input?.options ?? {}) };
  if (input?.mode === 'cli') options['--cli'] = true;
  else if (input?.mode === 'serve' && options['--serve'] === undefined) options['--serve'] = input?.port ?? true;
  else if (input?.mode === 'save-last') options['--save-last'] = true;
  else if (input?.mode === 'stop') options['--stop'] = true;
  const testWord =
    typeof input?.test === 'string' && input.test.length > 0
      ? input.test
      : input?.test && typeof input.test === 'object' && typeof (input.test.path ?? input.test.story) === 'string'
        ? input.test.path ?? input.test.story
        : null;
  const words = Array.isArray(input?.words)
    ? [...input.words]
    : testWord !== null
      ? [testWord]
      : commandWords(input);
  return runTry({ ...(cwd !== undefined ? { cwd } : {}), words, options }, ports);
}

export async function jobs(input = {}, ports = {}) {
  const env = input?.env ?? ports?.env;
  return runJobs({ ...(input ?? {}), ...(env !== undefined ? { env } : {}) }, ports);
}

export async function health(input = {}, ports = {}) {
  const env = input?.env ?? ports?.env;
  return checkRuntimeHealth({ ...(input ?? {}), ...(env !== undefined ? { env } : {}) }, ports);
}

export async function mcp(input = {}, ports = {}) {
  const cwd = input?.cwd ?? input?.root;
  const words = Array.isArray(input?.words) ? [...input.words] : input?.story ? [input.story] : [];
  const env = input?.env ?? ports?.env;
  return runMcp(
    {
      ...(cwd !== undefined ? { cwd } : {}),
      words,
      ...(env !== undefined ? { env } : {}),
    },
    ports,
  );
}

export function contracts(input = {}, ports = {}) {
  const cwd = input?.cwd ?? input?.root;
  const words = Array.isArray(input?.words) ? [...input.words] : input?.sync ? ['sync'] : [];
  const options =
    input?.options !== undefined
      ? {
          ...input.options,
          ...(input?.write !== undefined && input.options['--write'] === undefined ? { '--write': input.write } : {}),
        }
      : input?.write !== undefined
        ? { '--write': input.write }
        : {};
  return runContracts({ ...(cwd !== undefined ? { cwd } : {}), words, options }, ports);
}

export const source = Object.freeze({
  identity({ root, tests, ...options } = {}, ports = {}) {
    const normalizedTests = Array.isArray(tests)
      ? tests
          .map(item => (typeof item === 'string' ? item : item?.path ?? item?.story))
          .filter(item => typeof item === 'string')
      : tests;
    return captureSource(
      root,
      { ...(normalizedTests !== undefined ? { tests: normalizedTests } : {}), ...options },
      ports,
    );
  },
});

export const saved = Object.freeze({
  results(input = {}, ports = {}) {
    return savedStoryEvidence(input, ports);
  },
});

export function render(result, { as = 'table' } = {}, ports = {}) {
  if (as === 'table') return renderText(result, ports);
  if (as === 'json') return renderJson(result, ports);
  if (as === 'story-lines') return storyLines(Array.isArray(result) ? result : result?.rows ?? [], ports);
  if (as === 'summary') {
    return summaryLine(
      Array.isArray(result) ? result : result?.rows ?? [],
      Array.isArray(result) ? null : result?.story ?? null,
      ports,
    );
  }
  throw new RangeError(`Unsupported render format: ${String(as)}`);
}

export {
  CHECK_STATES,
  DRAFT_SERVER_TEXT,
  LIMITS,
  OPEN_STATES,
  PROVIDER_TEXT,
  PreflightError,
  STALE_HINT,
  TEST_SCHEMA,
  acquireRuntimeBatchLock,
  allowsRuntimePath,
  baselineReport,
  buildAgentInput,
  causeText,
  checkInput,
  checkPlanResultLines,
  checkPlanResults,
  cleanText,
  coverageText,
  defaultLineReader,
  defaultMaxCalls,
  discoveryRefusal,
  discoveryVisibleFiles,
  estimateCheckCalls,
  evaluateCheckBudget,
  exactIntegerLeaves,
  exactNumberSpelling,
  exactValue,
  executableInterfaceText,
  failedCheckCount,
  format,
  formatSize,
  formatWarningLines,
  gitFiles,
  hasProgress,
  hasPromptInterface,
  interfaceBlocks,
  interfaceFormatWarnings,
  interfaceKindProblems,
  interfaceSchemaProblems,
  isSecretPath,
  jsonRow,
  jsonSafe,
  loadRuntimeWorkspace,
  numberWarnings,
  otherFiles,
  outcomeDone,
  outcomeFor,
  outcomeOverall,
  outcomeText,
  parsePromptFrontmatter,
  parseScenarioJson,
  providerText,
  productTapCallBound,
  progressText,
  progressTicker,
  projectAnswer,
  promptMarkdownTargets,
  promptRefusal,
  promptSchemaRefusals,
  proseSha256,
  readPrompt,
  refusalView,
  requireRuntimePath,
  resultOutcome,
  resultOverall,
  roundedNumberTokens,
  runtimeAgentPacketSlice,
  runtimeCheckPlanSlice,
  runtimeOrigin,
  runtimeWorkspaceSlice,
  scenarioShapeRefusal,
  schemaKeywordWarningLines,
  selectCheckTests,
  sha256,
  sinceText,
  sourceFilePort,
  staleHint,
  stepTimeLimit,
  storyCriteria,
  stringifyScenarioJson,
  tarFiles,
  tryUsage,
  tryUsageHeaders,
  tryUsageLine,
  validLink,
  version,
  withExactIntegers,
  workspace,
};
