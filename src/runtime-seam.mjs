// Generated from prompts/cli/runtime-seam.prompt.md (sha256: c21f2aa1c7c74040e153f53509529f0a4a8d35b0c3d30036f30f68d3a8ea1b30).
import { AsyncLocalStorage } from 'node:async_hooks';
import { spawnSync } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import fs, { realpathSync } from 'node:fs';
import { createRequire, syncBuiltinESMExports } from 'node:module';
import { homedir } from 'node:os';
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
  compileLocalManifest,
  composeProductTry as runtimeComposeProductTry,
  coverageText,
  createAgentBridge as runtimeCreateAgentBridge,
  createLocalCommandBridge,
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
  executeLocalCommand,
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
  planProgramCase,
  planProgramSession,
  preflight as rawPreflight,
  prepareProgramInvocation,
  providerText,
  productTapCallBound,
  progressText,
  progressTicker,
  projectAnswer,
  projectCheckReconciliation as rawProjectCheckReconciliation,
  promptMarkdownTargets,
  promptRefusal,
  promptSchemaRefusals,
  proseSha256,
  readAgentScenarios as rawReadAgentScenarios,
  readContractHistory as runtimeReadContractHistory,
  readPrompt,
  readTryOwner as runtimeReadTryOwner,
  reconcileCheckReceipt as rawReconcileCheckReceipt,
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
  runProgram as runtimeRunProgram,
  runShim as runtimeRunShim,
  runTry as runtimeRunTry,
  runtimeAgentPacketSlice,
  runtimeCheckPlanSlice,
  runtimeClientSlice as rawRuntimeClientSlice,
  runtimeOrigin,
  runtimeOutcomeSlice as rawRuntimeOutcomeSlice,
  runtimeOutputSlice as rawRuntimeOutputSlice,
  runtimePreflightSlice as rawRuntimePreflightSlice,
  runtimeScenarioJsonSlice,
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
  validateLocalManifest,
  validateLocalRequest,
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
  'No tests found. The test of Story user_stories/S.md is S.json in a test or tests folder. Run `pdd help prompting` for the Story and scenario guide.';
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

let cachedFileOwner = null;
function hostFileOwner() {
  return (cachedFileOwner ??= req('./file-owner.mjs'));
}

function lazyEvidenceEligibility({ root, producerRoot, tests, source_sha256, runId = null, stage = null } = {}, ports = {}) {
  const canonicalPath = ports.realpath ?? realpathSync;
  const runCapture = ports.captureSource ?? ((dir, options) => captureSource(dir, { ...options, allowMissingInterfaces: true }));
  const listGitFiles = ports.gitFiles ?? (dir => gitFiles(dir));
  let result = {
    state: 'unavailable',
    reason: 'source or ownership unavailable',
    runId: null,
    repo: null,
    producerRoot: null,
    tests: [],
    stage: null,
    sourceAnchor: null,
    source_sha256: source_sha256 ?? null,
  };
  try {
    const realRoot = canonicalPath(root);
    const realProducer = canonicalPath(producerRoot);
    if (
      !Array.isArray(tests)
      || !tests.length
      || tests.some(p => typeof p !== 'string' || !p || /[\\\x00-\x1f\x7f]/.test(p)
        || p.startsWith('/') || /^[A-Za-z]:/.test(p)
        || p.split('/').some(seg => !seg || seg === '.' || seg === '..' || seg.toLowerCase() === '.git'))
      || new Set(tests).size !== tests.length
    ) {
      return { ...result, state: 'unavailable', reason: 'Select nonempty unique safe authored-relative test paths.' };
    }
    const sortedTests = [...tests].sort();
    result = { ...result, producerRoot: realProducer, tests: sortedTests };
    if (!/^[a-f0-9]{64}$/.test(source_sha256 ?? '')) {
      return { ...result, state: 'ineligible', reason: 'original selected source identity is missing' };
    }
    if (runId !== null || (stage !== null && stage !== 'current')) {
      return { ...result, state: 'ineligible', reason: 'saved run/stage has no matching owned association' };
    }
    if (realRoot !== realProducer) {
      return { ...result, state: 'ineligible', reason: 'alternate producer has no owned workspace association' };
    }
    const visible = new Set(listGitFiles(realRoot));
    if (sortedTests.some(p => !visible.has(p))) {
      return { ...result, state: 'unavailable', reason: 'A selected authored source is missing or unavailable.' };
    }
    if (runCapture(realRoot, { tests: sortedTests, appMap: null }).sha256 !== source_sha256) {
      return { ...result, state: 'ineligible', reason: 'the exact selected source has changed' };
    }
    return {
      state: 'eligible',
      reason: null,
      runId: null,
      repo: null,
      producerRoot: realProducer,
      tests: sortedTests,
      stage: 'current',
      sourceAnchor: { root: realRoot, head: null },
      source_sha256,
    };
  } catch (error) {
    return { ...result, reason: String(error?.message ?? error).replace(/\s+/g, ' ').trim() };
  }
}

function lazyAllRuns() {
  return [];
}

let cachedProductDocuments = null;
function hostProductDocuments() {
  return (cachedProductDocuments ??= req('./product-documents.mjs'));
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
    store.map = (root ? buildScenarioOverlay(root, store.ports, { preserveRawLineCount: !store.interceptFd }) : null) ?? new Map();
  }
  if (!store.map || store.map.size === 0) return undefined;
  const direct = store.map.get(strPath) ?? store.map.get(resolve(strPath));
  if (direct !== undefined) return direct;
  try {
    return store.map.get(realpathSync(strPath));
  } catch {
    return undefined;
  }
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
  if (out.includes('checked SVG layout only')) {
    out = out
      .replace(/partial: checked SVG layout only; prompts not checked \(local-only\)\./g, 'local-only: offline structural, scenario, and SVG checks completed; run pdd lint --remote for hosted cross-prompt checks (0 AI calls).')
      .replace(/checked SVG layout only; prompts not checked/g, 'offline structural, scenario, and SVG checks completed; hosted cross-prompt checks not run');
  }
  if (out.includes('RUNBOOK')) {
    out = out
      .replace(/\bRUNBOOK(?:\.md)?\s*§\s*13\b/g, 'the pdd skill reference ui-and-screens.md')
      .replace(/\bRUNBOOK(?:\.md)?\s*§\s*(?:4|5|6|17)\b/g, 'the pdd skill reference stories.md')
      .replace(/\bRUNBOOK(?:\.md)?\s*§\s*(?:18|19|20|21)\b/g, 'the pdd skill reference ports-and-cli.md')
      .replace(/\bRUNBOOK(?:\.md)?(?:\s*§\s*\d+[a-z]?)?/g, 'pdd help prompting');
  }
  return out;
}

function normalizeRuntimeHintsValue(value) {
  if (typeof value === 'string') return normalizeRuntimeHints(value);
  if (Array.isArray(value)) return value.map(normalizeRuntimeHintsValue);
  if (value && typeof value === 'object') {
    const out = {};
    for (const [k, v] of Object.entries(value)) out[k] = normalizeRuntimeHintsValue(v);
    return out;
  }
  return value;
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

function sleepWithSignal(ms, signal) {
  return new Promise(done => {
    if (signal?.aborted || ms <= 0) {
      done();
      return;
    }
    const finish = () => {
      clearTimeout(timer);
      signal?.removeEventListener('abort', finish);
      done();
    };
    const timer = setTimeout(finish, ms);
    signal?.addEventListener('abort', finish, { once: true });
  });
}

/** Honor 429/5xx/Retry-After floor without setting pollMs (preserving 1.1.1 native SSE, Prefer: wait, and adaptivePollMs). */
function attachRunCheckThrottleBackoff(merged, rawPorts) {
  if (rawPorts?.pollMs !== undefined || rawPorts?.sleep !== undefined || typeof merged.fetch !== 'function') return;
  let backoffFloorMs = 0;
  merged.sleep = (ms, signal) => {
    const waitMs = backoffFloorMs > 0 ? Math.max(Number(ms) || 0, backoffFloorMs) : Number(ms) || 0;
    backoffFloorMs = 0;
    return sleepWithSignal(waitMs, signal);
  };
  const wrappedFetch = merged.fetch;
  const observedFetch = async (url, init) => {
    let res;
    try {
      res = await wrappedFetch(url, init);
    } catch (err) {
      backoffFloorMs = 1000;
      throw err;
    }
    const status = Number(res?.status ?? 0);
    const retryAfterSec = Number(res?.headers?.get?.('retry-after'));
    if (status === 429 || status >= 500 || (Number.isFinite(retryAfterSec) && retryAfterSec > 0)) {
      backoffFloorMs = Number.isFinite(retryAfterSec) && retryAfterSec > 0 ? Math.min(300_000, Math.round(retryAfterSec * 1000)) : 1000;
    }
    return res;
  };
  if (wrappedFetch.__pddLegacyCriteriaWrapped) {
    Object.defineProperty(observedFetch, '__pddLegacyCriteriaWrapped', { value: true });
  }
  merged.fetch = observedFetch;
}

function seamRuntimePorts(ports = {}, { cwd = null, wrapStdout = true } = {}) {
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
  if (wrapStdout && merged.stdout) merged.stdout = normalizeHintStream(merged.stdout);
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
  const readAllRuns = allRunsPort ?? lazyAllRuns;
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

const STORY_STEP_LIMIT = 15;
const STORY_LINE_LIMIT = 1000;

function countTextLines(text) {
  if (typeof text !== 'string' || !text.length) return 0;
  const trimmed = text.replace(/\r?\n$/, '');
  return trimmed ? trimmed.split(/\r?\n/).length : 0;
}

function formatPreflightOverlayText(exactDoc, rawText, compiler) {
  const compact = compiler.stringifyExactScenarioJson(exactDoc);
  const rawLines = Math.max(1, countTextLines(rawText));
  return `${compact}${'\n'.repeat(rawLines)}`;
}

function rawShortStoryComplexityWarning({ path, storyPath, doc }, rawLines) {
  if (!doc || typeof doc !== 'object' || Array.isArray(doc)) return null;
  const steps = Array.isArray(doc.steps) ? doc.steps.length : 0;
  const lines = Number.isInteger(rawLines) ? rawLines : 0;
  const reasons = [];
  if (steps > STORY_STEP_LIMIT) reasons.push(`${steps} scenario steps (limit: ${STORY_STEP_LIMIT})`);
  if (lines > STORY_LINE_LIMIT) reasons.push(`${lines} lines (limit: ${STORY_LINE_LIMIT})`);
  if (!reasons.length) return null;
  const storyLabel = storyPath ?? (typeof doc.story_path === 'string' && doc.story_path.trim() ? doc.story_path.trim() : null) ?? path;
  return `Warning: oversized Story: ${storyLabel} (${path}) has ${reasons.join(' and ')}. Keep prompt scenarios focused on policy and authority boundaries and move multi-step state-machine or wire-protocol sequences to native tests (see the pdd skill references stories.md and verification.md, or run pdd help prompting).`;
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
    const rawLineCount = countTextLines(rawText);
    const preflightText = formatPreflightOverlayText(compiled.exactDoc ?? compiled.doc, rawText, compiler);
    const item = { ...test, doc: compiled.doc };
    Object.defineProperty(item, 'rawDoc', { value: compiled.doc });
    Object.defineProperty(item, 'compiledText', { value: compiled.text });
    Object.defineProperty(item, 'compiledPreflightText', { value: preflightText });
    Object.defineProperty(item, 'rawLineCount', { value: rawLineCount });
    if (Object.hasOwn(rawParsed, 'schema_version') && rawParsed.schema_version !== TEST_SCHEMA) {
      Object.defineProperty(item, 'rawHadNonV1Schema', { value: true });
    }
    if (Array.isArray(compiled.warnings) && compiled.warnings.length > 0) {
      Object.defineProperty(item, 'shortWarnings', { value: compiled.warnings });
    }
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

function buildScenarioOverlay(root, ports = {}, { preserveRawLineCount = false } = {}) {
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
    const overlayText = preserveRawLineCount ? (test?.compiledPreflightText ?? test?.compiledText) : test?.compiledText;
    if (test.error || typeof overlayText !== 'string') continue;
    overlay.set(resolve(root, test.path), overlayText);
    if (realRoot) overlay.set(join(realRoot, test.path), overlayText);
  }
  return overlay.size ? overlay : null;
}

export function preflight(input) {
  if (!input?.root) return rawPreflight(input);
  const directTests = Array.isArray(input.selected) ? input.selected : input.found?.tests;
  if (Array.isArray(directTests)) {
    const map = new Map();
    let realRoot = null;
    try {
      realRoot = realpathSync(input.root);
    } catch {
      realRoot = null;
    }
    for (const test of directTests) {
      const overlayText = test?.compiledPreflightText ?? test?.compiledText;
      if (test && !test.error && typeof overlayText === 'string') {
        map.set(resolve(input.root, test.path), overlayText);
        if (realRoot) map.set(join(realRoot, test.path), overlayText);
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
  const { resolveOwners } = hostFileOwner();
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
  return normalizeRuntimeHintsValue(rawRenderJson(input, withPortDefaults(ports, { promptTestsLabel: PROMPT_TESTS_LABEL })));
}

export function renderText(input, ports = {}) {
  return normalizeRuntimeHints(rawRenderText(input, withPortDefaults(ports, { promptTestsLabel: PROMPT_TESTS_LABEL })));
}

/** Format a local-lint story-criterion-mismatch diagnostic for stale or mismatched explicit criteria. */
function formatLocalCriteriaWarning(testPath, storyPath, classification) {
  if (classification.kind === 'stale-content-id') {
    return `${testPath}: story-criterion-mismatch: criterion ${JSON.stringify(classification.criterionId)} has a stale content-bound ID after ${storyPath} changed. Review ${storyPath} and update ${testPath} before rebinding.`;
  }
  if (classification.kind === 'text-mismatch') {
    return `${testPath}: story-criterion-mismatch: ${classification.difference}`;
  }
  if (classification.kind === 'duplicate-criterion') {
    return `${testPath}: story-criterion-mismatch: duplicate criterion ${JSON.stringify(classification.criterionId)} in ${testPath}.`;
  }
  return null;
}

function lintShortScenarioFiles(
  root,
  ports = {},
  { checkCriteriaBindings = false, includeRawComplexity = true, tests = undefined, words = [], cwd = null } = {},
) {
  if (typeof root !== 'string' || !root) return [];
  try {
    const rawWords = Array.isArray(words) ? words : [];
    const found = findTests({ root, excludeFixtureProjects: rawWords.length === 0 && tests === undefined }, ports);
    let scopedTests = found?.tests ?? [];
    if (Array.isArray(tests)) {
      const wanted = new Set(
        tests
          .map(entry => (typeof entry === 'string' ? entry : entry?.path))
          .filter(p => typeof p === 'string' && p.length > 0)
          .map(p => p.replace(/^\.\//, '')),
      );
      scopedTests = wanted.size > 0 ? scopedTests.filter(test => wanted.has(test.path)) : [];
    } else if (rawWords.length > 0) {
      const normalized = normalizeSelectionWords(rawWords, cwd ?? root, root, found);
      if (normalized.every(word => word.endsWith('.prompt.md') && found?.visible?.has(word))) {
        scopedTests = [];
      } else {
        const selection = selectTests(found, normalized);
        scopedTests = selection?.selected ?? [];
      }
    }
    const warnings = [];
    for (const test of scopedTests) {
      if (test.shortRefusal && typeof test.error === 'string' && test.error.length > 0) {
        warnings.push(test.error);
      }
      if (includeRawComplexity && !test.shortRefusal && test.rawHadNonV1Schema) {
        const complexityWarning = rawShortStoryComplexityWarning(test, test.rawLineCount);
        if (complexityWarning) warnings.push(complexityWarning);
      }
      if (Array.isArray(test.shortWarnings)) {
        for (const warning of test.shortWarnings) {
          if (typeof warning?.message === 'string' && warning.message.length > 0) {
            warnings.push(warning.message);
          }
        }
      }
    }
    if (!checkCriteriaBindings) return warnings;

    let realRoot;
    try {
      realRoot = realpathSync(root);
    } catch {
      return warnings;
    }
    const compiler = hostScenarioCompiler();
    const seen = new Set();
    for (const test of scopedTests) {
      if (test.shortRefusal) continue;
      for (const testPath of Array.isArray(test.files) && test.files.length ? test.files : [test.path]) {
        if (!testPath || seen.has(testPath)) continue;
        seen.add(testPath);
        let rawText;
        let parsed;
        try {
          const full = realpathSync(join(realRoot, testPath));
          if (full !== realRoot && !full.startsWith(realRoot + sep)) continue;
          rawText = initialReadFileSync(full, 'utf8');
          parsed = compiler.parseExactScenarioJson(rawText);
        } catch {
          continue;
        }
        const effectiveStoryPath =
          typeof parsed?.story_path === 'string' && parsed.story_path ? parsed.story_path : test.storyPath;
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
          allowSubset: true,
        });
        const msg = formatLocalCriteriaWarning(testPath, effectiveStoryPath, classification);
        if (msg) warnings.push(msg);
      }
    }
    return warnings;
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

/** Resolve a repo-relative regular file path, refusing symlinks on any path segment or escapes outside realRoot. */
function resolveWritableRepoFile(realRoot, relPath) {
  if (typeof relPath !== 'string' || !relPath || relPath.startsWith('/') || relPath.includes('\0')) {
    throw new Error('Test file path must be a safe repository-relative path.');
  }
  const parts = relPath.split(/[\\/]+/).filter(Boolean);
  if (!parts.length || parts.some(part => part === '.' || part === '..')) {
    throw new Error('Test file resolves outside repository root.');
  }
  let cur = realRoot;
  for (const part of parts) {
    cur = join(cur, part);
    const st = fs.lstatSync(cur);
    if (st.isSymbolicLink()) {
      throw new Error('Symlink test file cannot be overwritten in place.');
    }
  }
  const finalStat = fs.lstatSync(cur);
  if (!finalStat.isFile()) {
    throw new Error('Test file is not a regular file.');
  }
  const resolved = realpathSync(cur);
  if (resolved !== cur || (resolved !== realRoot && !resolved.startsWith(realRoot + sep))) {
    throw new Error('Test file resolves outside repository root.');
  }
  return resolved;
}

/** Write UTF-8 content atomically via a unique sibling temp file and rename. */
function writeFileAtomically(fullPath, content) {
  const tmpPath = join(dirname(fullPath), `.${basename(fullPath)}.pdd-tmp-${process.pid}-${randomUUID()}`);
  try {
    fs.writeFileSync(tmpPath, content, { encoding: 'utf8', flag: 'wx' });
    fs.renameSync(tmpPath, fullPath);
  } catch (err) {
    try {
      fs.unlinkSync(tmpPath);
    } catch {}
    throw err;
  }
}

function runEmitV1(input = {}, ports = {}) {
  const stdout = ports.stdout ?? process.stdout;
  const stderr = ports.stderr ?? process.stderr;
  const options = input?.options ?? {};
  const jsonMode = options['--json'] === true;
  const writeMode = options['--write'] === true;
  const badKey = Object.keys(options).find(key => !['--lint', '--emit-v1', '--write', '--json'].includes(key));
  if (badKey) {
    stderr.write('pdd lint --emit-v1 accepts only --write, --json and Story selections.\n');
    return 2;
  }
  const cwd = input?.cwd ?? process.cwd();
  const root = repoTopRoot(cwd);
  if (!root) {
    stderr.write('No Git project root is available.\n');
    return 2;
  }
  let realRoot = null;
  if (writeMode) {
    try {
      realRoot = realpathSync(root);
    } catch {
      stderr.write('No Git project root is available.\n');
      return 2;
    }
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
  const sourcePort = rawCreateStrictSourceAccess(root, found.workspace, seamSelectionPorts(ports)).sourceFilePort(found.visible);
  const errors = [];
  const emitted = [];
  const seenTestPaths = new Set();
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
    const filePaths = Array.isArray(test.files) && test.files.length ? test.files : [test.path];
    for (const testPath of filePaths) {
      if (!testPath || seenTestPaths.has(testPath)) continue;
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
      let fullTestPath = null;
      if (writeMode) {
        try {
          fullTestPath = resolveWritableRepoFile(realRoot, testPath);
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
      }
      let rawText;
      try {
        // Validate strict source access (visibility, workspace policy, size) before reading raw authored bytes.
        const strictEntry = sourcePort.read({ path: testPath });
        rawText = writeMode ? initialReadFileSync(fullTestPath, 'utf8') : strictEntry.content;
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
      let rawStoryPath = test.storyPath ?? null;
      let explicitStoryPath = null;
      try {
        const parsedRaw = compiler.parseExactScenarioJson(rawText);
        if (typeof parsedRaw?.story_path === 'string' && parsedRaw.story_path) {
          explicitStoryPath = parsedRaw.story_path;
          rawStoryPath = parsedRaw.story_path;
        }
      } catch {}
      let storySource =
        explicitStoryPath && explicitStoryPath !== test.storyPath ? null : (test.storySource ?? null);
      if (storySource === null && typeof rawStoryPath === 'string' && rawStoryPath) {
        try {
          storySource = sourcePort.read({ path: rawStoryPath }).content;
        } catch {
          storySource = null;
        }
      }
      const compiled = compiler.compileScenarioText(rawText, {
        path: testPath,
        storyPath: rawStoryPath,
        storySource,
        space: 2,
      });
      if (compiled.refusal) {
        errors.push({
          path: testPath,
          story_path: rawStoryPath ?? null,
          code: compiled.refusal.code,
          section: compiled.refusal.section,
          message: `${testPath}: ${compiled.refusal.section}: ${compiled.refusal.message}`,
        });
        continue;
      }
      let finalExact = compiled.exactDoc;
      let text = compiler.stringifyExactScenarioJson(finalExact, 2) + '\n';
      let changed = compiled.changed;
      const effectiveStoryPath = rawStoryPath ?? (typeof finalExact?.story_path === 'string' ? finalExact.story_path : null);
      if (storySource === null && typeof effectiveStoryPath === 'string' && effectiveStoryPath) {
        try {
          storySource = sourcePort.read({ path: effectiveStoryPath }).content;
        } catch {
          storySource = null;
        }
      }
      if (writeMode && effectiveStoryPath) {
        if (storySource === null) {
          errors.push({
            path: testPath,
            story_path: effectiveStoryPath,
            code: 'story-missing',
            section: 'story_path',
            message: `${testPath}: story_path: ${effectiveStoryPath} is not a Git-visible file.`,
          });
          continue;
        }
        const hasNumberedCriteria = compiler.numberedStoryCriteria(storySource, { requireHeading: true }).length > 0;
        if (hasNumberedCriteria) {
          const bound = compiler.bindScenarioCriteriaText(text, {
            path: testPath,
            storyPath: effectiveStoryPath,
            storySource,
            space: 2,
          });
          if (bound.refusal) {
            errors.push({
              path: testPath,
              story_path: effectiveStoryPath,
              code: bound.refusal.code,
              section: bound.refusal.section,
              message: `${testPath}: ${bound.refusal.section}: ${bound.refusal.message}`,
            });
            continue;
          }
          if (bound.changed) {
            text = bound.text;
            finalExact = compiler.parseExactScenarioJson(text);
            changed = true;
          }
        } else if (compiler.extractStoryCriteria(storySource).length === 0) {
          errors.push({
            path: testPath,
            story_path: effectiveStoryPath,
            code: 'story-criteria-missing',
            section: 'story_path',
            message: `${testPath}: story_path: ${effectiveStoryPath} has no numbered "## Acceptance criteria" list.`,
          });
          continue;
        }
      }
      emitted.push({
        path: testPath,
        fullPath: fullTestPath,
        story_path: effectiveStoryPath,
        changed,
        written: writeMode && changed && text !== rawText,
        text,
        scenario: finalExact,
        warnings: Array.isArray(compiled.warnings) ? compiled.warnings : [],
      });
    }
  }
  if (errors.length > 0) {
    if (jsonMode) {
      stdout.write(compiler.stringifyExactScenarioJson({ ok: false, ...(writeMode ? { exit_code: 4 } : {}), errors }, 2) + '\n');
    } else {
      for (const err of errors) stderr.write(`${err.message}\n`);
    }
    return 4;
  }
  const allWarnings = emitted.flatMap(item => item.warnings.map(w => w.message));
  if (writeMode) {
    for (const item of emitted) {
      if (!item.written) continue;
      writeFileAtomically(item.fullPath, item.text);
    }
    if (jsonMode) {
      stdout.write(
        compiler.stringifyExactScenarioJson(
          {
            ok: true,
            exit_code: 0,
            wrote: true,
            updated: emitted.filter(item => item.written).map(item => item.path),
            unchanged: emitted.filter(item => !item.written).map(item => item.path),
            warnings: allWarnings,
            files: emitted.map(({ path, story_path, changed, written, warnings }) => ({
              path,
              story_path,
              changed,
              written,
              warnings: warnings.map(w => w.message),
            })),
          },
          2,
        ) + '\n',
      );
      return 0;
    }
    for (const msg of allWarnings) stderr.write(`${msg}\n`);
    for (const item of emitted) {
      if (item.written) {
        stdout.write(`Wrote ${item.path} (prompt-runtime.program-scenario.v1).\n`);
      } else {
        stdout.write(`${item.path}: already canonical prompt-runtime.program-scenario.v1.\n`);
      }
    }
    return 0;
  }
  if (jsonMode) {
    stdout.write(
      compiler.stringifyExactScenarioJson(
        {
          ok: true,
          warnings: allWarnings,
          scenarios: emitted.map(({ path, story_path, changed, warnings, scenario }) => ({
            path,
            story_path,
            changed,
            warnings: warnings.map(w => w.message),
            scenario,
          })),
        },
        2,
      ) + '\n',
    );
    return 0;
  }
  for (const msg of allWarnings) stderr.write(`${msg}\n`);
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
      const { isTestOwnedPath, promptClaims, resolveOwners } = hostFileOwner();
      const { lintRepoAntiPatterns } = req('./repo-hygiene-lint.mjs');
      const baseWarnings = mod.lintLocalHygiene(
        input,
        withPortDefaults(seamSelectionPorts(ports), { isTestOwnedPath, promptClaims, resolveOwners }),
      );
      return [
        ...new Set([
          ...baseWarnings,
          ...lintRepoAntiPatterns(input),
          ...lintShortScenarioFiles(input?.root, ports, {
            tests: input?.tests,
          }),
        ]),
      ];
    },
    matchTests,
    orphanSummary,
    preflight,
    prepareHashSelection: (input, ports = {}) => mod.prepareHashSelection(input, seamSelectionPorts(ports)),
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
  const { headerPrompts } = hostFileOwner();
  return runtimeBuildCheckPlan(input, withPortDefaults(seamSelectionPorts(ports), { headerPrompts }));
}

export function selectJourneys(tests, selector, ports = {}) {
  return rawSelectJourneys(tests, selector, seamSelectionPorts(ports));
}

export function composeProductTry(input, ports = {}) {
  const { parseProductDocuments, parseProductWorldWriters } = hostProductDocuments();
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
  return runtimeCreateTryGuide({
    ...options,
    ports: withPortDefaults(seamSelectionPorts(withEligibilityDefault(givenPorts, lazyEvidenceEligibility)), {
      redaction: seamRedaction(givenPorts),
    }),
  });
}

export function buildProjectCard(input = {}) {
  return runtimeBuildProjectCard(withEligibilityDefault(input, lazyEvidenceEligibility));
}

export function readContractHistory(input, ports = {}) {
  const cwd = input?.root ?? input?.cwd ?? process.cwd();
  return withScenarioOverlay(
    { cwd, ports, interceptFd: true },
    () => runtimeReadContractHistory(input, seamSelectionPorts(withEligibilityDefault(ports, lazyEvidenceEligibility))),
  );
}

export function runContracts(input, ports = {}) {
  runtimeClientSlice();
  const cwd = input?.cwd ?? process.cwd();
  return withScenarioOverlay(
    { cwd, ports, interceptFd: true },
    () => runtimeRunContracts(input, seamSelectionPorts(withEligibilityDefault(ports, lazyEvidenceEligibility))),
  );
}

export async function runJobs(input = {}, ports = {}) {
  const { NAMES } = await import('./shared/command-names.mjs');
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
  '--read', '--retry', '--reconcile', '--request', '--screen', '--drawing', '--look', '--emit-v1', '--write', '--bind-criteria',
];
const FRESH_INCOMPATIBLE_CHECK_FLAGS = [
  '--read', '--retry', '--reconcile', '--files', '--explain-bindings',
  '--request', '--lint', '--local', '--screen', '--drawing', '--look',
  '--emit-v1', '--write', '--bind-criteria',
];
const UUID_RE = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;

function isPlainObject(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function wrapFetchForFresh(baseFetch, matchPathname) {
  if (typeof baseFetch !== 'function') return baseFetch;
  const wrapped = async (url, init) => {
    const method = String(init?.method ?? 'GET').toUpperCase();
    let pathname = '';
    try {
      pathname = new URL(String(url), 'http://localhost').pathname;
    } catch {
      return baseFetch(url, init);
    }
    if (method !== 'POST' || !matchPathname(pathname)) return baseFetch(url, init);
    if (init?.body instanceof FormData) {
      const reqPart = init.body.get('request');
      if (reqPart && typeof reqPart.text === 'function') {
        try {
          const parsed = JSON.parse(await reqPart.text());
          if (isPlainObject(parsed) && parsed.fresh !== true) {
            const nextForm = new FormData();
            for (const [key, value] of init.body.entries()) {
              if (key === 'request') {
                nextForm.set(
                  'request',
                  new Blob([JSON.stringify({ ...parsed, fresh: true })], { type: 'application/json' }),
                  'request.json',
                );
              } else if (typeof File !== 'undefined' && value instanceof File) {
                nextForm.append(key, value, value.name);
              } else {
                nextForm.append(key, value);
              }
            }
            return baseFetch(url, { ...init, body: nextForm });
          }
        } catch {
          /* Preserve original body on malformed payload. */
        }
      }
      return baseFetch(url, init);
    }
    if (typeof init?.body === 'string') {
      try {
        const parsed = JSON.parse(init.body);
        if (isPlainObject(parsed) && parsed.fresh === undefined) {
          return baseFetch(url, { ...init, body: JSON.stringify({ ...parsed, fresh: true }) });
        }
      } catch {
        /* Preserve original body on malformed payload. */
      }
    }
    return baseFetch(url, init);
  };
  if (baseFetch.__pddLegacyCriteriaWrapped) {
    Object.defineProperty(wrapped, '__pddLegacyCriteriaWrapped', { value: true });
  }
  return wrapped;
}

function isSafeRegularJsonFile(filePath, maxBytes = 4 * 1024 * 1024) {
  if (typeof filePath !== 'string' || !filePath) return false;
  try {
    const stat = fs.lstatSync(filePath);
    return !stat.isSymbolicLink() && stat.isFile() && stat.nlink === 1 && stat.size <= maxBytes;
  } catch {
    return false;
  }
}

function safeRequestIdDisplay(value) {
  if (typeof value === 'string') return value;
  if (value === undefined || value === null) return '';
  try {
    return String(value);
  } catch {
    return `[${typeof value}]`;
  }
}

function findExistingTryForFresh(cwd, words, rawOptions = {}, env = process.env, ports = {}) {
  try {
    const root = repoTopRoot(cwd);
    if (!root) return null;
    const realRoot = realpathSync(root);
    const home = env?.HOME || process.env.HOME || homedir();
    const stateRoot = resolve(env?.PDD_STATE_DIR || join(home, '.pdd', 'runtime'));
    const repoKey = createHash('sha256').update(realRoot).digest('hex').slice(0, 16);
    const repoStatePath = join(stateRoot, 'repos', `${repoKey}.json`);
    if (!isSafeRegularJsonFile(repoStatePath, 4 * 1024 * 1024)) return null;
    const repoState = JSON.parse(initialReadFileSync(repoStatePath, 'utf8'));
    const tries = repoState?.tries;
    if (!isPlainObject(tries) || Object.keys(tries).length === 0) return null;
    const found = findTests({ root: realRoot }, ports);
    if (rawOptions?.['--product'] === true) {
      const journey = rawOptions['--journey'];
      let target = null;
      if (journey === undefined && words.length === 1) {
        const normalized = normalizeSelectionWords(words, cwd, realRoot, found);
        const selection = selectTests(found, normalized);
        if (selection?.selected?.length === 1) target = selection.selected[0];
      } else {
        let journeyPaths = [];
        try {
          journeyPaths = selectJourneys(
            (found.tests ?? []).map(test => ({ testPath: test.path, storyPath: test.storyPath })),
            journey,
            ports,
          );
        } catch {
          journeyPaths = [];
        }
        if (!journeyPaths.length && journey === undefined) {
          if (found.tests?.length === 1) {
            target = found.tests[0];
          }
        } else {
          const requested =
            words.length > 0
              ? new Set(selectTests(found, normalizeSelectionWords(words, cwd, realRoot, found))?.selected?.map(t => t.path) ?? [])
              : null;
          const matched = (found.tests ?? []).filter(
            test => journeyPaths.includes(test.path) && (!requested || requested.has(test.path)),
          );
          if (matched.length === 1) target = matched[0];
        }
      }
      if (target) {
        return isPlainObject(tries[target.path])
          ? { story: words.length === 1 ? words[0] : null, product: true, title: target.title || target.story || 'this product' }
          : null;
      }
      if (journey === undefined && words.length === 0) {
        const productEntries = Object.entries(tries).filter(([, value]) => isPlainObject(value?.product_setup));
        if (productEntries.length === 1) {
          return { story: null, product: true, title: 'this product' };
        }
      }
      return null;
    }
    if (words.length === 1) {
      const normalized = normalizeSelectionWords(words, cwd, realRoot, found);
      const selection = selectTests(found, normalized);
      const target = selection?.selected?.length === 1 ? selection.selected[0] : null;
      if (!target) return null;
      const existing = tries[target.path];
      if (!isPlainObject(existing)) return null;
      return { story: target.story, title: target.title || target.story };
    }
    if (words.length === 0) {
      const wholeEntry = Object.entries(tries).find(([, value]) => isPlainObject(value?.simulation_scope));
      if (wholeEntry) return { story: null, title: 'this project' };
      const sorted = [...(found.tests ?? [])].sort((a, b) => a.path.localeCompare(b.path));
      const first = sorted[0];
      if (first && isPlainObject(tries[first.path])) {
        return { story: first.story, title: first.title || first.story };
      }
    }
  } catch {
    /* Let runtimeRunTry report selection or repository errors. */
  }
  return null;
}

async function runCheckReconcileCommand(input = {}, ports = {}) {
  const stdout = ports.stdout ?? process.stdout;
  const stderr = ports.stderr ?? process.stderr;
  const rawOptions = input?.options ?? {};
  const words = commandWords(input);
  if (words.length > 0 || Object.keys(rawOptions).some(key => !['--reconcile', '--json'].includes(key))) {
    stderr.write('Use pdd test --reconcile REQUEST_ID [--json] without other options or Stories.\n');
    return 2;
  }
  const requestId = rawOptions['--reconcile'];
  if (typeof requestId !== 'string' || !UUID_RE.test(requestId)) {
    stderr.write(`Invalid CHECK request UUID "${cleanText(safeRequestIdDisplay(requestId))}". Pass the original external request UUID.\n`);
    return 2;
  }
  try {
    const result = await reconcileCheckReceipt(
      { cwd: input?.cwd ?? process.cwd(), requestId },
      ports,
    );
    if (rawOptions['--json'] === true) {
      stdout.write(`${JSON.stringify(result)}\n`);
    } else {
      const { formatCheckReconciliation } = await import('./core/reconcile-format.mjs');
      stdout.write(`${formatCheckReconciliation(result)}\n`);
    }
    return result?.available === true ? 0 : 3;
  } catch (error) {
    if (error?.code === 'invalid-request-id' || error?.exitCode === 2) {
      stderr.write(`${causeText(error.message) || 'Invalid CHECK request UUID.'}\n`);
      return 2;
    }
    if (error?.code === 'reconciliation-unsupported' || error?.exitCode === 5) {
      stderr.write(`${causeText(error.message) || 'CHECK receipt reconciliation is unavailable.'}\n`);
      return 5;
    }
    const detail = causeText(error?.message ?? error);
    stderr.write(`CHECK receipt reconciliation failed.${detail ? ` Reason: ${detail}` : ''}\n`);
    return 3;
  }
}
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
  const rawOptions = input?.options ?? {};
  if (rawOptions['--emit-v1'] && rawOptions['--bind-criteria']) {
    const stderr = ports.stderr ?? process.stderr;
    stderr.write('Use either --emit-v1 or --bind-criteria, not both.\n');
    return 2;
  }
  if (rawOptions['--write'] && !rawOptions['--emit-v1']) {
    const stderr = ports.stderr ?? process.stderr;
    stderr.write('--write is only accepted with pdd lint --emit-v1.\n');
    return 2;
  }
  if (rawOptions['--emit-v1']) {
    return runEmitV1(input, ports);
  }
  if (rawOptions['--bind-criteria']) {
    return runBindCriteria(input, ports);
  }
  if (rawOptions['--reconcile'] !== undefined) {
    return runCheckReconcileCommand(input, ports);
  }
  const freshRequested = rawOptions['--fresh'] !== undefined;
  if (freshRequested) {
    const stderr = ports.stderr ?? process.stderr;
    if (rawOptions['--fresh'] !== true) {
      stderr.write('--fresh takes no value.\n');
      return 2;
    }
    if (FRESH_INCOMPATIBLE_CHECK_FLAGS.some(flag => rawOptions[flag] !== undefined)) {
      stderr.write('This mix of options does not work together. Run pdd test --help.\n');
      return 2;
    }
  }
  const words = commandWords(input);
  const screenRequested = rawOptions['--screen'] !== undefined;
  const nativeLintRequested = rawOptions['--lint'] === true && words.length > 0;
  const skipLintModules =
    screenRequested ||
    rawOptions['--read'] !== undefined ||
    rawOptions['--retry'] !== undefined ||
    rawOptions['--request'] !== undefined ||
    rawOptions['--explain-bindings'] !== undefined;

  const [
    ,
    { headerPrompts, isTestOwnedPath, promptClaims, resolveOwners },
    lintMods,
    screenMod,
  ] = await Promise.all([
    import('./secret-redaction.mjs'),
    import('./file-owner.mjs'),
    skipLintModules
      ? Promise.resolve(null)
      : Promise.all([import('./svg-layout.mjs'), import('./repo-hygiene-lint.mjs')]),
    screenRequested ? import('./screen-compare.mjs') : Promise.resolve(null),
  ]);
  const env = ports.env ?? process.env;
  const client = input?.client
    ? { ...input.client, version: input.client.version ?? clientVersion() }
    : { version: clientVersion() };
  const graphCap = computeGraphAwareDefaultMaxCalls(input, ports);
  const effectiveOptions = {
    ...rawOptions,
    ...(graphCap !== undefined ? { '--max-calls': graphCap } : {}),
  };
  if (freshRequested && effectiveOptions['--affected'] === true) {
    delete effectiveOptions['--fresh'];
  }
  const effectiveInput = {
    ...input,
    options: effectiveOptions,
    client,
  };
  const cwd = effectiveInput?.cwd ?? process.cwd();
  const lazyOverlay = { cwd, ports, map: undefined };

  const { onProjectLintResult, ...forwardPorts } = ports;
  const defaultLintSvgLayouts = lintMods
    ? arg => {
        const [{ lintSvgLayouts }, { lintRepoProject }] = lintMods;
        const project = lintRepoProject(arg);
        if (typeof onProjectLintResult === 'function' && arg?.promptPaths === undefined && arg?.tests === undefined) {
          onProjectLintResult(project);
        }
        return [
          ...lintSvgLayouts(arg),
          ...project.warnings,
          ...lintShortScenarioFiles(arg?.root, forwardPorts, {
            checkCriteriaBindings: rawOptions['--local'] === true,
            includeRawComplexity: rawOptions['--lint'] === true,
            words,
            cwd,
          }),
        ];
      }
    : undefined;
  return withScenarioOverlay(lazyOverlay, () => {
    const checkPorts = seamRuntimePorts(
      withPortDefaults(withEligibilityDefault(forwardPorts, lazyEvidenceEligibility), {
        headerPrompts,
        isTestOwnedPath,
        promptClaims,
        resolveOwners,
        allRuns: lazyAllRuns,
        workflowBaseSha: ({ root, env: runEnv }) =>
          resolveWorkflowBaseSha({ root, env: runEnv ?? env, allRunsPort: forwardPorts.allRuns ?? lazyAllRuns }),
        ...(nativeLintRequested
          ? {
              assessNativeEvidence: () => ({ ok: false, state: 'unavailable', storyNativeProof: 'none', reason: 'Verify native Stories locally with `pdd prove`.' }),
              usableResult: () => false,
              resultLines: () => [],
            }
          : {}),
        ...(defaultLintSvgLayouts ? { lintSvgLayouts: defaultLintSvgLayouts } : {}),
        ...(screenMod
          ? {
              compareScreen: screenMod.compareScreen,
              formatScreenComparison: screenMod.formatScreenComparison,
            }
          : {}),
        redaction: seamRedaction(forwardPorts),
      }),
      { cwd },
    );
    if (freshRequested) {
      // Bypass local pass cache reuse across all modes (including --lf --fresh, --affected --fresh,
      // --journeys --fresh) while preserving --lf failure lookup, unselected cached passes, and fresh writeback.
      checkPorts.env = { ...(checkPorts.env ?? env), CI: '1' };
      if (typeof checkPorts.fetch === 'function') {
        checkPorts.fetch = wrapFetchForFresh(checkPorts.fetch, pathname => pathname === '/v1/check');
      }
    }
    attachRunCheckThrottleBackoff(checkPorts, forwardPorts);
    return runtimeRunCheck(effectiveInput, checkPorts);
  });
}

export async function askAgent(input = {}, ports = {}) {
  const explicitRun = input?.run ?? ports.run ?? ports.runAgentProcess ?? ports.agents?.run;
  const run = explicitRun ?? (await import('./shared/agent-process.mjs')).runAgentProcess;
  return runtimeAskAgent({ ...input, run }, ports);
}

const PLAIN_PROSE_UI_MAX_BYTES = 2 * 1024 * 1024;
const DIRECT_PROMPT_STDERR_LIMIT = 4096;
const REOPEN_FALLBACK_LINE_LIMIT = 64;
const PLAIN_PROSE_RENDER_RE = /(?:\brender\s*\(|`(?:(?:sync|async)\s+)?render(?:\s*\([^)]*\))?`|^#{2,4}\s+render\b)/im;
const PLAIN_PROSE_HANDLE_EVENT_RE = /(?:\bhandle_event\s*\(|`(?:(?:sync|async)\s+)?handle_event(?:\s*\([^)]*\))?`|^#{2,4}\s+handle_event\b)/im;
const PLAIN_PROSE_CLI_ARGV_RE = /\bargv\b/;
const PLAIN_PROSE_CLI_EXIT_RE = /\bexit_code\b/;
const PLAIN_PROSE_HTTP_RE = /\bHTTP\s+(?:GET|HEAD|POST|PUT|PATCH|DELETE|OPTIONS)\s+\//;
const HTTP_TITLE_RE = /^HTTP (?:GET|HEAD|POST|PUT|PATCH|DELETE|OPTIONS) \/\S*$/;
const REOPEN_TAB_CONFLICT_RE = /--tab\b[^\n]*new/i;
const TRY_STARTUP_DONE_RE = /https?:\/\/\S+\/s\/\S+|Try budget \d+|Connecting your agent to the Try page/i;
const FORM_TAB_NOTICE = "This Story's operation takes typed input, so it opens on the Form tab.";

let cachedNativePlainProseUiSupport;
function runtimeClientSupportsPlainProseUi() {
  if (cachedNativePlainProseUiSupport !== undefined) return cachedNativePlainProseUiSupport;
  try {
    const info = typeof version === 'function' ? version() : null;
    cachedNativePlainProseUiSupport = Boolean(
      (Array.isArray(info?.features) &&
        info.features.some(f =>
          ['plain-prose-ui', 'plain-prose-ui-screen', 'single-prompt-try', 'single-prompt-simulate', 'hybrid-ui'].includes(f),
        )) ||
        info?.capabilities?.plainProseUi === true ||
        info?.capabilities?.plainProseUiScreen === true ||
        info?.capabilities?.singlePromptTry === true,
    );
    return cachedNativePlainProseUiSupport;
  } catch {
    cachedNativePlainProseUiSupport = false;
    return false;
  }
}

function isPlainProseHybridUiPrompt(source) {
  if (typeof source !== 'string' || !source || interfaceBlocks(source).length > 0) return false;
  return PLAIN_PROSE_RENDER_RE.test(source) && PLAIN_PROSE_HANDLE_EVENT_RE.test(source);
}

function promptEntryHasCliOrHttpDoor(realRoot, visible, entryPath, promptSource, operation) {
  const blocks = interfaceBlocks(promptSource);
  if (!blocks.length) {
    if (operation === 'main' && PLAIN_PROSE_CLI_ARGV_RE.test(promptSource) && PLAIN_PROSE_CLI_EXIT_RE.test(promptSource)) {
      return true;
    }
    if (PLAIN_PROSE_HTTP_RE.test(promptSource)) {
      return true;
    }
    return false;
  }
  let iface = null;
  try {
    iface = readPrompt(realRoot, visible, entryPath)?.interface ?? null;
  } catch {
    iface = null;
  }
  if (!iface) {
    try {
      iface = JSON.parse(blocks[0][1]);
    } catch {
      return false;
    }
  }
  const entries = Array.isArray(iface?.entries) ? iface.entries : [];
  const conventions = Array.isArray(iface?.conventions) ? iface.conventions : [];
  const index = entries.findIndex(entry => entry?.operation === operation);
  if (index < 0) return false;
  const entry = entries[index];
  if (
    ['input_schema', 'result_schema'].every(name =>
      conventions.some(c => c?.path === `/entries/${index}/${name}` && c.convention === 'cli'),
    )
  ) {
    return true;
  }
  if (typeof entry?.input_schema?.title === 'string' && HTTP_TITLE_RE.test(entry.input_schema.title)) {
    return true;
  }
  return false;
}

function hasSavedTryRecord(realRoot, tests, rawWords, env = process.env) {
  try {
    const stateDir = resolve(env?.PDD_STATE_DIR || join(env?.HOME || homedir(), '.pdd', 'runtime'));
    const repoKey = createHash('sha256').update(realRoot).digest('hex').slice(0, 16);
    const repoFile = join(stateDir, 'repos', `${repoKey}.json`);
    const st = initialLstatSync(repoFile);
    if (st.isSymbolicLink() || !st.isFile()) return false;
    const saved = JSON.parse(initialReadFileSync(repoFile, 'utf8'));
    const tries = saved?.tries;
    if (!tries || typeof tries !== 'object' || Array.isArray(tries)) return false;
    if (!rawWords.length) {
      if (
        Object.values(tries).some(
          v => v && typeof v === 'object' && v.simulation_scope && typeof v.simulation_scope === 'object' && !Array.isArray(v.simulation_scope),
        )
      ) {
        return true;
      }
      const seed = [...tests].sort((a, b) => String(a?.path ?? '').localeCompare(String(b?.path ?? '')))[0];
      return typeof seed?.path === 'string' && Boolean(tries[seed.path]);
    }
    return tests.some(item => typeof item?.path === 'string' && Boolean(tries[item.path]));
  } catch {
    return false;
  }
}

function wrapFilteredStream(baseStream, shouldSuppress) {
  const target = baseStream;
  return Object.assign(Object.create(target), {
    ...(target.isTTY !== undefined ? { isTTY: target.isTTY } : {}),
    write(chunk, ...rest) {
      const text =
        typeof chunk === 'string'
          ? chunk
          : Buffer.isBuffer(chunk) || chunk instanceof Uint8Array
            ? Buffer.from(chunk).toString('utf8')
            : String(chunk);
      if (shouldSuppress(text)) {
        const cb = rest.find(arg => typeof arg === 'function');
        if (cb) cb();
        return true;
      }
      return target.write(chunk, ...rest);
    },
  });
}

function classifyPlainProseScreenTab(input, cwd, ports, lazyOverlay) {
  const opts = input?.options ?? {};
  if (
    opts['--tab'] !== undefined ||
    opts['--cli'] ||
    opts['--shell'] ||
    opts['--serve'] !== undefined ||
    opts['--stop'] ||
    opts['--save-last'] ||
    opts['--product'] ||
    opts['--app-map'] !== undefined
  ) {
    return 'none';
  }
  try {
    const root = repoTopRoot(cwd);
    if (!root) return 'none';
    const rawWords = Array.isArray(input?.words) ? input.words : [];
    const found = withScenarioOverlay(lazyOverlay, () =>
      findTests({ root, cwd, excludeFixtureProjects: rawWords.length === 0 }, ports),
    );
    if (!found?.visible || found.visible.has('app-map.json') || found.visible.has('app/app-map.json')) {
      return 'none';
    }
    const realRoot = realpathSync(root);
    const realCwd = realpathSync(cwd);
    const normalizedWords = rawWords.map(word => {
      if (typeof word !== 'string' || !word) return word;
      if (realCwd === realRoot && !word.startsWith('/') && !word.includes('\\')) return word;
      const candidate = resolve(realCwd, word);
      const rel = relative(realRoot, candidate).split(sep).join('/');
      const withinRepo = rel !== '..' && !rel.startsWith('../');
      if (!withinRepo) return word;
      if (rel && (found.visible.has(rel) || found.tests?.some(t => t.path === rel || t.storyPath === rel))) {
        return rel;
      }
      try {
        if (initialStatSync(candidate).isDirectory()) return rel || '.';
      } catch { /* keep original word */ }
      return word;
    });
    const selectedResult = normalizedWords.length ? selectTests(found, normalizedWords) : null;
    const tests = normalizedWords.length
      ? (Array.isArray(selectedResult) ? selectedResult : selectedResult?.selected ?? [])
      : (found.tests ?? []);
    if (!tests.length) return 'none';

    const promptCache = new Map();
    const readSafeVisiblePrompt = rel => {
      if (promptCache.has(rel)) return promptCache.get(rel);
      let text = null;
      try {
        if (
          typeof rel === 'string' &&
          rel.endsWith('.prompt.md') &&
          !rel.startsWith('/') &&
          !rel.includes('\\') &&
          found.visible.has(rel)
        ) {
          const full = resolve(realRoot, rel);
          if (full.startsWith(`${realRoot}${sep}`)) {
            const lst = initialLstatSync(full);
            if (!lst.isSymbolicLink() && lst.isFile() && lst.size <= PLAIN_PROSE_UI_MAX_BYTES) {
              const realFull = realpathSync(full);
              if (realFull.startsWith(`${realRoot}${sep}`)) {
                text = initialReadFileSync(realFull, 'utf8');
              }
            }
          }
        }
      } catch {
        text = null;
      }
      promptCache.set(rel, text);
      return text;
    };

    let sawPlainProseUiStep = false;
    for (const item of tests) {
      if (Array.isArray(item?.doc?.app_maps) && item.doc.app_maps.length > 0) return 'none';
      const steps = Array.isArray(item?.doc?.steps) ? item.doc.steps : [];
      for (const step of steps) {
        const entryPath = typeof step?.entry_path === 'string' ? step.entry_path : '';
        const op = typeof step?.operation === 'string' ? step.operation : '';
        if (!entryPath || !op) continue;
        const promptSource = readSafeVisiblePrompt(entryPath);
        if (promptSource === null) continue;
        if (promptEntryHasCliOrHttpDoor(realRoot, found.visible, entryPath, promptSource, op)) return 'none';
        if ((op === 'render' || op === 'handle_event') && isPlainProseHybridUiPrompt(promptSource)) {
          sawPlainProseUiStep = true;
        }
      }
    }
    if (!sawPlainProseUiStep) return 'none';
    if (!opts['--new'] && hasSavedTryRecord(realRoot, tests, rawWords, ports?.env ?? process.env)) {
      return 'reopen';
    }
    return 'inject';
  } catch {
    return 'none';
  }
}

export async function runTry(input = {}, ports = {}) {
  const { runTry: rawTryOverride, ...forwardPorts } = ports;
  const opts = input?.options ?? {};
  const freshRequested = opts['--fresh'] !== undefined;
  const cwd = input?.cwd ?? process.cwd();
  const words = commandWords(input);
  const isDirectProgramTarget =
    words.length >= 1 &&
    typeof words[0] === 'string' &&
    (words[0].endsWith('.prompt.md') || basename(words[0]) === 'app-map.json');
  if (freshRequested) {
    const stderr = forwardPorts.stderr ?? process.stderr;
    if (opts['--fresh'] !== true) {
      stderr.write('--fresh takes no value.\n');
      return 2;
    }
    if (opts['--stop']) {
      stderr.write('pdd simulate --stop takes only a STORY. Run pdd simulate --help.\n');
      return 2;
    }
    if (opts['--save-last']) {
      stderr.write('Choose one of --cli (with optional --shell), --shell, --serve, --page, --save-last or --stop.\n');
      return 2;
    }
    if (!opts['--new'] && !isDirectProgramTarget) {
      const existing = findExistingTryForFresh(cwd, words, opts, forwardPorts.env ?? process.env, forwardPorts);
      if (existing) {
        const productArgs = [
          '--product',
          ...(existing.story ? [existing.story] : []),
          ...(typeof opts['--journey'] === 'string' && opts['--journey'] ? ['--journey', opts['--journey']] : []),
        ].join(' ');
        const targetCmd = existing.product
          ? `pdd simulate ${productArgs} --fresh --new`
          : `pdd simulate${existing.story ? ` ${existing.story}` : ''} --fresh --new`;
        stderr.write(
          `A Try for "${existing.title}" is already open. --fresh applies only to a new Try: run ${targetCmd} (it stops the open Try first).\n`,
        );
        return 2;
      }
    }
  }
  const [
    ,
    { loadAgentDefinitions },
    { parseProductDocuments, parseProductWorldWriters },
    { lineReader },
    { createPromptApproval },
    { createHumanBoundaryCard },
  ] = await Promise.all([
    import('./secret-redaction.mjs'),
    import('./agent-config.mjs'),
    import('./product-documents.mjs'),
    import('./shared/line-reader.mjs'),
    import('./core/approve-prompt.mjs'),
    import('./core/human-boundary-card-core.mjs'),
  ]);
  const { buildHumanBoundaryCard, formatApproveBoundaryCard } = createHumanBoundaryCard({
    TEST_SCHEMA,
    findTests,
    gitFiles,
    interfaceBlocks,
    parseScenarioJson,
    promptMarkdownTargets,
    readPrompt,
    storyCriteria,
  });
  const { askApproval, promptPath } = createPromptApproval({
    ...runtimePreflightSlice(),
    defaultEnv: forwardPorts.env ?? process.env,
    formatBoundaryCardLines: ({ root: cardRoot, focusPrompt, env: cardEnv }) =>
      formatApproveBoundaryCard(buildHumanBoundaryCard({ root: cardRoot, focusPrompt, env: cardEnv ?? forwardPorts.env ?? process.env })),
  });
  const defaultDiscoverAgents = async (...args) => (await import('./shared/agent-process.mjs')).discoverAgents(...args);
  const defaultAskAgent = async (turnInput, ...rest) => askAgent(turnInput, ...rest);
  const defaultAgentBridge = (context, test, tryId, opts, link) =>
    createAgentBridge(context, test, tryId, opts, link, {
      redaction: forwardPorts.redaction ?? seamRedaction(forwardPorts),
      redactSecrets: forwardPorts.redactSecrets,
      loadAgentDefinitions: forwardPorts.loadAgentDefinitions ?? forwardPorts.agents?.loadDefinitions ?? loadAgentDefinitions,
      discoverAgents: forwardPorts.discoverAgents ?? forwardPorts.agents?.list,
      runAgentProcess: forwardPorts.runAgentProcess ?? forwardPorts.agents?.run,
      askAgent: forwardPorts.askAgent ?? forwardPorts.agents?.ask,
      evidenceEligibility: forwardPorts.evidenceEligibility ?? forwardPorts.readEvidenceEligibility ?? lazyEvidenceEligibility,
      guidePorts: forwardPorts.guidePorts,
    });
  const invokeRunTry = typeof rawTryOverride === 'function' ? rawTryOverride : runtimeRunTry;
  const lazyOverlay = { cwd, ports: forwardPorts, map: undefined };
  const invoke = (tryInput, tryPorts) =>
    withScenarioOverlay(lazyOverlay, () => {
      const boundPorts = seamRuntimePorts(
        withPortDefaults(withEligibilityDefault(tryPorts, lazyEvidenceEligibility), {
          tryLauncherUrl: TRY_LAUNCHER_URL,
          agentBridge: defaultAgentBridge,
          loadAgentDefinitions: tryPorts.loadAgentDefinitions ?? tryPorts.agents?.loadDefinitions ?? loadAgentDefinitions,
          discoverAgents: tryPorts.discoverAgents ?? tryPorts.agents?.list ?? defaultDiscoverAgents,
          askAgent: tryPorts.askAgent ?? tryPorts.agents?.ask ?? defaultAskAgent,
          parseProductDocuments,
          parseProductWorldWriters,
          askApproval,
          lineReader,
          promptPath,
          files: wrapCaseFilesForShortJson(tryPorts.files, tryPorts),
          redaction: seamRedaction(tryPorts),
        }),
        { cwd },
      );
      return invokeRunTry(tryInput, boundPorts);
    });

  const skipSeamAutoScreenTab = typeof rawTryOverride !== 'function' && runtimeClientSupportsPlainProseUi();
  const screenTabMode = skipSeamAutoScreenTab
    ? 'none'
    : classifyPlainProseScreenTab(input, cwd, forwardPorts, lazyOverlay);
  if (screenTabMode === 'reopen') {
    const baseStderr = forwardPorts.stderr ?? process.stderr;
    const reopenStderr = wrapFilteredStream(baseStderr, text => text.includes(FORM_TAB_NOTICE));
    return invoke(input, { ...forwardPorts, stderr: reopenStderr });
  }
  const effectiveInput =
    screenTabMode === 'inject'
      ? { ...input, options: { ...opts, '--tab': 'screen' } }
      : input;
  if (screenTabMode === 'inject' && !opts['--new']) {
    let reopenAutoTabConflict = false;
    let startupSucceeded = false;
    const emittedBeforeFallback = new Set();
    const baseStdout = forwardPorts.stdout ?? process.stdout;
    const baseStderr = forwardPorts.stderr ?? process.stderr;
    const observedStdout = wrapFilteredStream(baseStdout, text => {
      if (!startupSucceeded && TRY_STARTUP_DONE_RE.test(text)) {
        startupSucceeded = true;
        emittedBeforeFallback.clear();
      }
      return false;
    });
    const filteredStderr = wrapFilteredStream(baseStderr, text => {
      if (!startupSucceeded) {
        if (REOPEN_TAB_CONFLICT_RE.test(text)) {
          reopenAutoTabConflict = true;
          return true;
        }
        if (TRY_STARTUP_DONE_RE.test(text)) {
          startupSucceeded = true;
          emittedBeforeFallback.clear();
        } else if (emittedBeforeFallback.size < REOPEN_FALLBACK_LINE_LIMIT && text.length <= DIRECT_PROMPT_STDERR_LIMIT) {
          emittedBeforeFallback.add(text);
        }
      }
      return false;
    });
    const code = await invoke(effectiveInput, { ...forwardPorts, stdout: observedStdout, stderr: filteredStderr });
    if (!startupSucceeded && code === 2 && reopenAutoTabConflict) {
      const reopenStderr = wrapFilteredStream(baseStderr, text => {
        if (emittedBeforeFallback.has(text)) {
          emittedBeforeFallback.delete(text);
          return true;
        }
        return text.includes(FORM_TAB_NOTICE);
      });
      return invoke(input, { ...forwardPorts, stderr: reopenStderr });
    }
    return code;
  }
  return invoke(effectiveInput, forwardPorts);
}

export async function createAgentBridge(context, test, tryId, options, link, seamPorts = {}) {
  const [, { loadAgentDefinitions }, { discoverAgents, runAgentProcess }] = await Promise.all([
    import('./secret-redaction.mjs'),
    import('./agent-config.mjs'),
    import('./shared/agent-process.mjs'),
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
      withPortDefaults(withEligibilityDefault(seamPorts, lazyEvidenceEligibility), {
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
    import('./shared/line-reader.mjs'),
  ]);
  const shimPorts = seamRuntimePorts(
    withPortDefaults(ports, {
      lineReader,
      redaction: seamRedaction(ports),
      files: wrapCaseFilesForShortJson(ports.files, ports),
    }),
  );
  return runtimeRunShim(descriptorPath, argv, shimPorts);
}

export async function saveLast(input) {
  const { lineReader } = await import('./shared/line-reader.mjs');
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
  const doorPorts = seamRuntimePorts(withPortDefaults(ports, { redaction: seamRedaction(ports) }));
  return runtimeRunDoorCall(descriptor, input, doorPorts);
}

export async function readTryOwner(input = {}, ports = {}) {
  const [, { parseProductDocuments, parseProductWorldWriters }] = await Promise.all([
    import('./secret-redaction.mjs'),
    import('./product-documents.mjs'),
  ]);
  return runtimeReadTryOwner(
    input,
    seamRuntimePorts(
      withPortDefaults(withEligibilityDefault(ports, lazyEvidenceEligibility), {
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

export function projectCheckReconciliation(input, ports = {}) {
  const impl =
    typeof ports?.projectCheckReconciliation === 'function'
      ? ports.projectCheckReconciliation
      : rawProjectCheckReconciliation;
  return impl(input);
}

export async function reconcileCheckReceipt(input = {}, ports = {}) {
  const rawRequestId = input?.requestId;
  if (typeof rawRequestId !== 'string' || !UUID_RE.test(rawRequestId)) {
    throw Object.assign(
      new Error(`Invalid CHECK request UUID "${cleanText(safeRequestIdDisplay(rawRequestId))}". Pass the original external request UUID.`),
      { code: 'invalid-request-id', exitCode: 2 },
    );
  }
  const { reconcileCheckReceipt: injectedReconcile, ...forwardPorts } = ports ?? {};
  const impl = typeof injectedReconcile === 'function' ? injectedReconcile : rawReconcileCheckReceipt;
  await import('./secret-redaction.mjs');
  return impl(
    input,
    seamRuntimePorts(withPortDefaults(forwardPorts, { redaction: seamRedaction(forwardPorts) }), {
      cwd: input?.cwd ?? process.cwd(),
    }),
  );
}

export async function runProgram(input = {}, ports = {}) {
  const [, { lineReader }] = await Promise.all([
    import('./secret-redaction.mjs'),
    import('./shared/line-reader.mjs'),
  ]);
  const cwd = input?.cwd ?? process.cwd();
  return runtimeRunProgram(
    input,
    seamRuntimePorts(
      withPortDefaults(ports, {
        lineReader,
        redaction: seamRedaction(ports),
        files: wrapCaseFilesForShortJson(ports.files, ports),
      }),
      { cwd },
    ),
  );
}

export async function run(input = {}, ports = {}) {
  return runProgram(input, ports);
}

export function createTryTools(input, ports = {}) {
  const lazyParseProductDocuments = (...args) => hostProductDocuments().parseProductDocuments(...args);
  const lazyParseProductWorldWriters = (...args) => hostProductDocuments().parseProductWorldWriters(...args);
  return runtimeCreateTryTools(
    input,
    seamRuntimePorts(
      withPortDefaults(withEligibilityDefault(ports, lazyEvidenceEligibility), {
        tryLauncherUrl: TRY_LAUNCHER_URL,
        parseProductDocuments: lazyParseProductDocuments,
        parseProductWorldWriters: lazyParseProductWorldWriters,
        saveDoorCase,
        applyPendingCaseWithHandoff,
        redaction: seamRedaction(ports),
      }),
      { wrapStdout: false },
    ),
  );
}

export async function runMcp(input, ports = {}) {
  const [, { parseProductDocuments, parseProductWorldWriters }] = await Promise.all([
    import('./secret-redaction.mjs'),
    import('./product-documents.mjs'),
  ]);
  return runtimeRunMcp(
    input,
    seamRuntimePorts(
      withPortDefaults(withEligibilityDefault(ports, lazyEvidenceEligibility), {
        clientVersion: clientVersion(),
        tryLauncherUrl: TRY_LAUNCHER_URL,
        parseProductDocuments,
        parseProductWorldWriters,
        saveDoorCase,
        applyPendingCaseWithHandoff,
        redaction: seamRedaction(ports),
      }),
      { wrapStdout: false },
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
  return runtimeMigrateWorkspace(input, seamCasePorts(withEligibilityDefault(ports, lazyEvidenceEligibility)));
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
  const extraOptions = {
    ...(input?.affected === true && input?.options?.['--affected'] === undefined ? { '--affected': true } : {}),
    ...(input?.fresh === true && input?.options?.['--fresh'] === undefined ? { '--fresh': true } : {}),
  };
  return runCheck(buildCheckInput(input, { defaultCache: true, extraOptions }), ports);
}

export async function lint(input = {}, ports = {}) {
  const extraOptions = {
    '--lint': true,
    ...(input?.local === true && input?.options?.['--local'] === undefined ? { '--local': true } : {}),
    ...(input?.emitV1 === true && input?.options?.['--emit-v1'] === undefined ? { '--emit-v1': true } : {}),
    ...(input?.write === true && input?.options?.['--write'] === undefined ? { '--write': true } : {}),
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
      options: {
        ...(input?.options ?? {}),
        ...(input?.details === true && input?.options?.['--details'] === undefined ? { '--details': true } : {}),
        '--read': true,
      },
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
  if (input?.fresh === true && options['--fresh'] === undefined) options['--fresh'] = true;
  if (input?.mode === 'cli') options['--cli'] = true;
  else if (input?.mode === 'serve' && options['--serve'] === undefined) options['--serve'] = input?.port ?? true;
  else if (input?.mode === 'save-last') options['--save-last'] = true;
  else if (input?.mode === 'stop') options['--stop'] = true;
  const testWord =
    typeof input?.test === 'string' && input.test.length > 0
      ? input.test
      : input?.test && typeof input.test === 'object' && typeof (input.test.path ?? input.test.story) === 'string'
        ? input.test.path ?? input.test.story
        : typeof input?.prompt === 'string' && input.prompt.length > 0
          ? input.prompt
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
  compileLocalManifest,
  coverageText,
  createLocalCommandBridge,
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
  executeLocalCommand,
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
  planProgramCase,
  planProgramSession,
  prepareProgramInvocation,
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
  runtimeScenarioJsonSlice,
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
  validateLocalManifest,
  validateLocalRequest,
  version,
  withExactIntegers,
  workspace,
};
