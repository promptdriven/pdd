// Generated from prompts/cli/runtime-seam.prompt.md (sha256: 143d47191a91e9e6ba0dc1d5cea15b2061365963a73a737c03751d4fd904237e).
import { AsyncLocalStorage } from 'node:async_hooks';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import fs, { realpathSync } from 'node:fs';
import { createRequire, syncBuiltinESMExports } from 'node:module';
import { dirname, join, relative, resolve, sep } from 'node:path';
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
  refusalView,
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
  version,
  withExactIntegers,
  workspace,
} from '@promptdriven/runtime-client';

const req = createRequire(import.meta.url);
const initialReadFileSync = fs.readFileSync;
const readFileSync = initialReadFileSync;
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
let scenarioFsHookInstalled = false;

function ensureScenarioFsOverlay() {
  if (scenarioFsHookInstalled) return;
  scenarioFsHookInstalled = true;
  fs.readFileSync = function pddScenarioReadFileSync(pathOrFd, options) {
    const store = scenarioOverlayStorage.getStore();
    if (store && (typeof pathOrFd === 'string' || pathOrFd instanceof URL)) {
      const strPath = pathOrFd instanceof URL ? fileURLToPath(pathOrFd) : pathOrFd;
      if (strPath.endsWith('.json') && !strPath.includes('/node_modules/') && !strPath.endsWith('/package.json')) {
        if (store.map === undefined) {
          store.map = null;
          const root = store.root ?? repoTopRoot(store.cwd);
          store.map = (root ? buildScenarioOverlay(root, store.ports) : null) ?? new Map();
        }
        if (store.map && store.map.size > 0) {
          const virtualText = store.map.get(strPath) ?? store.map.get(resolve(strPath));
          if (virtualText !== undefined) {
            if (typeof options === 'string') return Buffer.from(virtualText, 'utf8').toString(options);
            if (options && typeof options === 'object' && options.encoding) {
              return Buffer.from(virtualText, 'utf8').toString(options.encoding);
            }
            return Buffer.from(virtualText, 'utf8');
          }
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

function seamRuntimePorts(ports = {}) {
  const exit = hostExit();
  return withPortDefaults(seamSelectionPorts(ports), {
    exitFor: exit.exitFor,
    exitCodeFor: exit.exitCodeFor,
    promptTestsLabel: PROMPT_TESTS_LABEL,
  });
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

function readStoryForTest(root, visible, storyPath) {
  if (typeof storyPath !== 'string' || !storyPath || (visible && !visible.has(storyPath))) return null;
  try {
    return initialReadFileSync(join(root, storyPath), 'utf8');
  } catch {
    return null;
  }
}

export function findTests(input, ports = {}) {
  const found = rawFindTests(input, seamSelectionPorts(ports));
  if (!found || !Array.isArray(found.tests) || !found.root) return found;
  const compiler = hostScenarioCompiler();
  let anyCompiled = false;
  const compiledTests = found.tests.map(test => {
    if (test.error || !test.doc || typeof test.doc !== 'object' || Array.isArray(test.doc)) return test;
    let rawText;
    try {
      rawText = initialReadFileSync(join(found.root, test.path), 'utf8');
    } catch {
      return test;
    }
    let rawParsed;
    try {
      rawParsed = compiler.parseExactScenarioJson(rawText);
    } catch {
      return test;
    }
    if (!compiler.isShortScenarioDoc(rawParsed)) return test;
    anyCompiled = true;
    const targetStoryPath = typeof rawParsed.story_path === 'string' && rawParsed.story_path
      ? rawParsed.story_path
      : test.storyPath;
    const storySource = test.storySource ?? readStoryForTest(found.root, found.visible, targetStoryPath);
    const compiled = compiler.compileScenarioText(rawText, {
      path: test.path,
      storyPath: test.storyPath,
      storySource,
    });
    if (compiled.refusal) {
      const item = {
        ...test,
        error: `${test.path}: ${compiled.refusal.section}: ${compiled.refusal.message}`,
      };
      Object.defineProperty(item, 'rawDoc', { value: test.rawDoc ?? test.doc });
      Object.defineProperty(item, 'shortRefusal', { value: compiled.refusal });
      return item;
    }
    const item = { ...test, doc: compiled.doc };
    Object.defineProperty(item, 'rawDoc', { value: test.rawDoc ?? test.doc });
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
      if (ent.name === '.git' || ent.name === 'node_modules') continue;
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

export function captureSource(root, options, ports = {}) {
  const selPorts = seamSelectionPorts(ports);
  const callerPrepare = options?.prepareSource;
  const compiledDiskBytes = new Map();

  const mergedPrepare = prepPorts => {
    const callerItems = callerPrepare !== undefined ? callerPrepare(prepPorts) : [];
    if (!Array.isArray(callerItems)) return callerItems;
    if (Array.isArray(options?.tests) && options.tests.length === 0) return callerItems;

    const names = scanStoryAndTestPathsOnDisk(root);
    if (!names.length) return callerItems;
    const storyPaths = names.filter(p => selPorts.isStoryPath(p));
    const matched = selPorts.matchTests(storyPaths, names).tests.filter(t => !t.problem);
    const callerSet = new Set(
      callerItems.map(item => (item && typeof item.path === 'string' ? item.path : null)).filter(Boolean),
    );

    let candidates;
    if (Array.isArray(options?.tests)) {
      const requested = new Set(options.tests);
      const selectedStories = new Set(
        matched
          .filter(t => (t.files ?? [t.path]).some(f => requested.has(f)) || requested.has(t.path))
          .map(t => t.storyPath)
          .filter(Boolean),
      );
      candidates = matched.filter(
        t => requested.has(t.path) || (t.storyPath && selectedStories.has(t.storyPath)),
      );
    } else {
      candidates = matched;
    }

    const compiler = hostScenarioCompiler();
    const extraItems = [];
    for (const entry of candidates) {
      for (const testPath of entry.files ?? [entry.path]) {
        if (callerSet.has(testPath)) continue;
        // Fast host read first: skip all standard v1 JSON files without touching prepPorts!
        let probeText;
        try {
          const full = realpathSync(join(root, testPath));
          const realRoot = realpathSync(root);
          if (full !== realRoot && !full.startsWith(realRoot + sep)) continue;
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
        if (!compiler.isShortScenarioDoc(probeParsed)) continue;

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
        if (!compiler.isShortScenarioDoc(rawParsed)) continue;
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
        if (compiled.refusal) {
          throw Object.assign(
            new PreflightError(4, `${testPath}: ${compiled.refusal.section}: ${compiled.refusal.message}`),
            { code: compiled.refusal.code, section: compiled.refusal.section },
          );
        }
        if (compiled.changed) {
          compiledDiskBytes.set(testPath, rawBuf);
          extraItems.push({ path: testPath, bytes: Buffer.from(compiled.text, 'utf8') });
        }
      }
    }
    return extraItems.length ? [...callerItems, ...extraItems] : callerItems;
  };

  const nextOptions = options === undefined
    ? { prepareSource: mergedPrepare }
    : { ...options, prepareSource: mergedPrepare };

  const captured = rawCaptureSource(root, nextOptions, selPorts);
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
captureSource.isDefaultCapture = true;

export function fillHashes(input, ports = {}) {
  return rawFillHashes(input, seamSelectionPorts(ports));
}

export function createStrictSourceAccess(root, workspace, ports = {}) {
  return rawCreateStrictSourceAccess(root, workspace, seamSelectionPorts(ports));
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
  return rawRenderJson(input, withPortDefaults(ports, { promptTestsLabel: PROMPT_TESTS_LABEL }));
}

export function renderText(input, ports = {}) {
  return rawRenderText(input, withPortDefaults(ports, { promptTestsLabel: PROMPT_TESTS_LABEL }));
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
  let realCwd = cwd;
  let realRoot = root;
  try {
    realCwd = realpathSync(cwd);
    realRoot = realpathSync(root);
  } catch {}
  const normalizedWords = rawWords.map(word => {
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
    let finalExact = compiled.exactDoc;
    if (
      finalExact &&
      typeof finalExact === 'object' &&
      !Array.isArray(finalExact) &&
      !Object.hasOwn(finalExact, 'criteria') &&
      typeof storySource === 'string'
    ) {
      const storyTexts = compiler.extractStoryCriteria(storySource);
      if (storyTexts.length > 0) {
        const criteria = storyTexts.map((text, idx) => ({ id: `AC${idx + 1}`, text }));
        const { schema_version, story_path, ...rest } = finalExact;
        finalExact = {
          schema_version: schema_version ?? compiler.V1_SCENARIO_SCHEMA,
          ...(story_path !== undefined ? { story_path } : test.storyPath ? { story_path: test.storyPath } : {}),
          criteria,
          ...rest,
        };
      }
    }
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
  return runtimeComposeProductTry(
    input,
    withPortDefaults(seamSelectionPorts(ports), { parseProductDocuments, parseProductWorldWriters }),
  );
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
  return runtimeReadContractHistory(input, seamSelectionPorts(withEligibilityDefault(ports, lazyEligibility)));
}

export function runContracts(input, ports = {}) {
  runtimeClientSlice();
  const lazyEligibility = (...args) => req('./workflow-eligibility.mjs').readEvidenceEligibility(...args);
  return runtimeRunContracts(input, seamSelectionPorts(withEligibilityDefault(ports, lazyEligibility)));
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
  if (input?.options?.['--emit-v1']) {
    return runEmitV1(input, ports);
  }
  const env = ports.env ?? process.env;
  const client = input?.client
    ? { ...input.client, version: input.client.version ?? clientVersion() }
    : { version: clientVersion() };
  const lazyOverlay = { cwd: input?.cwd ?? process.cwd(), ports, map: undefined };
  return withScenarioOverlay(lazyOverlay, () =>
    runtimeRunCheck(
      {
        ...input,
        client,
      },
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
  const lazyOverlay = { cwd: input?.cwd ?? process.cwd(), ports, map: undefined };
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
          redaction: seamRedaction(ports),
        }),
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
    seamRuntimePorts(withPortDefaults(ports, { lineReader, redaction: seamRedaction(ports) })),
  );
}

export async function saveLast(input) {
  const { lineReader } = await import('./prompt-approve.mjs');
  const nextInput =
    input && typeof input === 'object'
      ? {
          ...input,
          ports: seamRuntimePorts(withPortDefaults(input.ports ?? {}, { lineReader })),
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
        redaction: seamRedaction(ports),
      }),
    ),
  );
}

export async function migrateRuntimeWorkspace(input, ports = {}) {
  const { readEvidenceEligibility } = await import('./workflow-eligibility.mjs');
  return runtimeMigrateWorkspace(input, seamSelectionPorts(withEligibilityDefault(ports, readEvidenceEligibility)));
}

export function runtimeWorkspaceMigrationStore(input, given = {}) {
  return rawRuntimeWorkspaceMigrationStore(input, seamSelectionPorts(given));
}

export function saveDoorCaseResult(root, saved, options = {}) {
  const basePorts = options?.ports ?? (options?.env ? { env: options.env } : {});
  return rawSaveDoorCaseResult(root, saved, { ...options, ports: seamSelectionPorts(basePorts) });
}

export function saveDoorCase(root, saved, options = {}) {
  return saveDoorCaseResult(root, saved, options).message;
}

export async function acquireCaseWriteOwnership(input, ports = {}) {
  return rawAcquireCaseWriteOwnership(input, seamSelectionPorts(ports));
}

export async function applyPendingCase(input, ports = {}) {
  return rawApplyPendingCase(input, seamSelectionPorts(ports));
}

export async function applyPendingCaseWithHandoff(input, ports = {}) {
  return rawApplyPendingCaseWithHandoff(input, seamSelectionPorts(ports));
}

export function createSavedStoryEvidenceReader(ports = {}) {
  return rawCreateSavedStoryEvidenceReader(seamSelectionPorts(ports));
}

export async function resendableStoryChecks(input, ports = {}) {
  return rawResendableStoryChecks(input, ports);
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
  version,
  withExactIntegers,
  workspace,
};
