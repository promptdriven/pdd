// Generated from prompts/cli/runtime-seam.prompt.md (sha256: 6a722862aec1bf1a2ad5cc886c9922e50a45975f9bdddba9b72a450e5e980263).
import { readFileSync, realpathSync } from 'node:fs';
import { createRequire } from 'node:module';
import { dirname, join } from 'node:path';
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
  exactIntegerLeaves,
  exactNumberSpelling,
  exactValue,
  executableInterfaceText,
  fillHashes,
  findTests as rawFindTests,
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
  loadInterfaceDraft,
  loadRuntimeClient as runtimeLoadClient,
  loadRuntimeWorkspace,
  migrateRuntimeWorkspace as runtimeMigrateWorkspace,
  numberWarnings,
  openCli as runtimeOpenCli,
  openServe as runtimeOpenServe,
  otherFiles,
  outcomeDone,
  outcomeFor,
  outcomeOverall,
  outcomeText,
  parseScenarioJson,
  preflight,
  productTapCallBound,
  progressText,
  progressTicker,
  projectAnswer,
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
  runAutomaticApproval as runtimeRunAutomaticApproval,
  runCheck as runtimeRunCheck,
  runContracts as runtimeRunContracts,
  runDoorCall as runtimeRunDoorCall,
  runInterfaceDraft as runtimeRunInterfaceDraft,
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
  sharedSourceFiles,
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
} from './runtime/index.mjs';

const req = createRequire(import.meta.url);
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
  return (cachedVersion ??= JSON.parse(readFileSync(new URL('../package.json', import.meta.url), 'utf8')).version);
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

export function findTests(input, ports = {}) {
  return rawFindTests(input, seamSelectionPorts(ports));
}

export function captureSource(root, options, ports = {}) {
  return rawCaptureSource(root, options, seamSelectionPorts(ports));
}

export function createStrictSourceAccess(root, workspace, ports = {}) {
  return rawCreateStrictSourceAccess(root, workspace, seamSelectionPorts(ports));
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
      hasInterfaceBlock: hasPromptInterface,
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

export function runtimePreflightSlice() {
  const mod = rawRuntimePreflightSlice();
  return {
    ...mod,
    NO_TESTS,
    captureSource,
    createStrictSourceAccess,
    expectedTestPath,
    findTests,
    hasAcceptance,
    isStoryPath,
    matchTests,
    orphanSummary,
    selectTests,
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
  const [{ NAMES }] = await Promise.all([import('./command-catalog.mjs'), import('./product.mjs')]);
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

export async function runInterfaceDraft(input = {}, ports = {}) {
  return runtimeRunInterfaceDraft(input, seamSelectionPorts(ports));
}

export async function runAutomaticApproval(input = {}, ports = {}) {
  const stderr = ports.stderr ?? process.stderr;
  try {
    const [
      { approvalActor, readApprovalPolicy, readPromptApprovals, recordPromptApproval },
      { approvePromptText, promptPath },
      ,
      ,
      { headerPrompts },
      { readEvidenceEligibility },
      { allRuns },
      { assessNativeEvidence, resultLines, usableResult },
      ,
      { lintSvgLayouts },
      { compareScreen, formatScreenComparison },
    ] = await Promise.all([
      import('./approval-policy.mjs'),
      import('./prompt-approve.mjs'),
      import('./product.mjs'),
      import('./secret-redaction.mjs'),
      import('./file-owner.mjs'),
      import('./workflow-runner.mjs'),
      import('./workflow-runs.mjs'),
      import('./workflow-results.mjs'),
      import('./agent-config.mjs'),
      import('./svg-layout.mjs'),
      import('./screen-compare.mjs'),
    ]);
    const env = ports.env ?? process.env;
    const client =
      ports.client ??
      (input?.client
        ? { ...input.client, version: input.client.version ?? clientVersion() }
        : { version: clientVersion() });
    const explicitWorkflow = ports.workflow ?? input?.workflow;
    return await runtimeRunAutomaticApproval(
      input,
      seamRuntimePorts(
        withPortDefaults(withEligibilityDefault(ports, readEvidenceEligibility), {
          approvalActor,
          readApprovalPolicy,
          readPromptApprovals,
          recordPromptApproval,
          approvePromptText,
          promptPath,
          headerPrompts,
          allRuns,
          workflowBaseSha: ({ root, env: runEnv }) =>
            resolveWorkflowBaseSha({ root, env: runEnv ?? env, allRunsPort: ports.allRuns ?? allRuns }),
          assessNativeEvidence,
          usableResult,
          resultLines,
          lintSvgLayouts,
          compareScreen,
          formatScreenComparison,
          client,
          ...(explicitWorkflow !== undefined ? { workflow: explicitWorkflow } : {}),
          redaction: seamRedaction(ports),
        }),
      ),
    );
  } catch (error) {
    stderr.write(`${error?.message || 'Approval failed.'}\n`);
    return 4;
  }
}

export async function runCheck(input = {}, ports = {}) {
  const [
    ,
    { headerPrompts },
    { readEvidenceEligibility },
    { allRuns },
    { assessNativeEvidence, resultLines, usableResult },
    { lintSvgLayouts },
    { compareScreen, formatScreenComparison },
  ] = await Promise.all([
    import('./secret-redaction.mjs'),
    import('./file-owner.mjs'),
    import('./workflow-runner.mjs'),
    import('./workflow-runs.mjs'),
    import('./workflow-results.mjs'),
    import('./svg-layout.mjs'),
    import('./screen-compare.mjs'),
    import('./product.mjs'),
  ]);
  const env = ports.env ?? process.env;
  const client = input?.client
    ? { ...input.client, version: input.client.version ?? clientVersion() }
    : { version: clientVersion() };
  return runtimeRunCheck(
    {
      ...input,
      client,
    },
    seamRuntimePorts(
      withPortDefaults(withEligibilityDefault(ports, readEvidenceEligibility), {
        headerPrompts,
        allRuns,
        workflowBaseSha: ({ root, env: runEnv }) =>
          resolveWorkflowBaseSha({ root, env: runEnv ?? env, allRunsPort: ports.allRuns ?? allRuns }),
        assessNativeEvidence,
        usableResult,
        resultLines,
        lintSvgLayouts,
        compareScreen,
        formatScreenComparison,
        redaction: seamRedaction(ports),
      }),
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
    import('./workflow-runner.mjs'),
    import('./product.mjs'),
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
  return runtimeRunTry(
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
  );
}

export async function createAgentBridge(context, test, tryId, options, link, seamPorts = {}) {
  const [, { loadAgentDefinitions }, { discoverAgents, runAgentProcess }, { readEvidenceEligibility }] = await Promise.all([
    import('./secret-redaction.mjs'),
    import('./agent-config.mjs'),
    import('./agent-adapters.mjs'),
    import('./workflow-runner.mjs'),
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
    import('./product.mjs'),
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
    import('./workflow-runner.mjs'),
    import('./product.mjs'),
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
    import('./workflow-runner.mjs'),
    import('./product.mjs'),
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
  const { readEvidenceEligibility } = await import('./workflow-runner.mjs');
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
  'fill-hash': '--fill-hash',
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
  const extraOptions = {
    [flag]: true,
    ...(input?.compact === true && input?.options?.['--compact'] === undefined ? { '--compact': true } : {}),
  };
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

export async function draftInterfaces(input = {}, ports = {}) {
  const cwd = input?.cwd ?? input?.root;
  const words = Array.isArray(input?.words) ? [...input.words] : Array.isArray(input?.paths) ? [...input.paths] : [];
  return runInterfaceDraft(
    {
      ...(cwd !== undefined ? { cwd } : {}),
      words,
      all: Boolean(input?.all),
      json: Boolean(input?.json),
      contract: input?.contract,
      extend: Boolean(input?.extend),
      refresh: Boolean(input?.refresh),
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
  exactIntegerLeaves,
  exactNumberSpelling,
  exactValue,
  executableInterfaceText,
  fillHashes,
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
  loadInterfaceDraft,
  loadRuntimeWorkspace,
  numberWarnings,
  otherFiles,
  outcomeDone,
  outcomeFor,
  outcomeOverall,
  outcomeText,
  parseScenarioJson,
  preflight,
  productTapCallBound,
  progressText,
  progressTicker,
  projectAnswer,
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
  sharedSourceFiles,
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
