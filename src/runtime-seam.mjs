// Generated from prompts/cli/runtime-seam.prompt.md (sha256: eda9c8d03d871d6de695d5a0ac9a0d3e0a4592aa8431a40b156efc94f3abc57a).
import { spawnSync } from 'node:child_process';
import { realpathSync } from 'node:fs';
import { createRequire } from 'node:module';
import { dirname, join } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import {
  buildCheckPlan as runtimeBuildCheckPlan,
  checkRuntimeHealth as runtimeCheckHealth,
  composeProductTry as runtimeComposeProductTry,
  createAgentBridge as runtimeCreateAgentBridge,
  createTryGuide as runtimeCreateTryGuide,
  loadRuntimeClient as runtimeLoadClient,
  migrateRuntimeWorkspace as runtimeMigrateWorkspace,
  readTryOwner as runtimeReadTryOwner,
  runAutomaticApproval as runtimeRunAutomaticApproval,
  runCheck as runtimeRunCheck,
  runContracts as runtimeRunContracts,
  runJobs as runtimeRunJobs,
  runMcp as runtimeRunMcp,
  runShim as runtimeRunShim,
  runTry as runtimeRunTry,
} from './runtime/index.mjs';

const req = createRequire(import.meta.url);
const TRY_LAUNCHER_URL = pathToFileURL(join(dirname(fileURLToPath(import.meta.url)), 'try-doors.mjs')).href;
const NON_BATCH_MODES = ['--read', '--retry', '--fill-hash', '--files', '--explain-bindings', '--request', '--lint', '--screen', '--drawing', '--local'];

let cachedVersion = null;
function clientVersion() {
  return (cachedVersion ??= req('../package.json').version);
}

let cachedRedaction = null;
function hostRedaction() {
  if (!cachedRedaction) {
    const { knownSecretValues, redactSecrets, rememberSecrets } = req('./secret-redaction.mjs');
    cachedRedaction = Object.freeze({ remember: rememberSecrets, redact: redactSecrets, known: knownSecretValues });
  }
  return cachedRedaction;
}

function seamRedaction(ports = {}) {
  if (ports.redaction !== undefined) return ports.redaction;
  const host = hostRedaction();
  if (ports.rememberSecrets === undefined && ports.redactSecrets === undefined) return host;
  return Object.freeze({
    remember: ports.rememberSecrets ?? host.remember,
    redact: ports.redactSecrets ?? host.redact,
    known: host.known,
  });
}

function resolveWorkflowBaseSha(cwd = process.cwd(), env = process.env) {
  const { allRuns } = req('./workflow-runs.mjs');
  const runs = allRuns({ cancelled: true }, { env });
  if (!runs.length) return null;
  const found = spawnSync('git', ['rev-parse', '--show-toplevel'], { cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  if (found.status !== 0 || !found.stdout.trim()) return null;
  let realRoot;
  try { realRoot = realpathSync(found.stdout.trim()); } catch { return null; }
  const matching = runs.filter(run => {
    try { return realpathSync(run.root) === realRoot; } catch { return false; }
  });
  return matching.length === 1 && /^[a-f0-9]{40}$/.test(matching[0].baseSha ?? '') ? matching[0].baseSha : null;
}

export function buildCheckPlan(input, ports = {}) {
  const { headerPrompts } = req('./file-owner.mjs');
  return runtimeBuildCheckPlan(input, { headerPrompts, ...ports });
}

export function composeProductTry(input, ports = {}) {
  const { parseProductDocuments, parseProductWorldWriters } = req('./product.mjs');
  return runtimeComposeProductTry(input, { parseProductDocuments, parseProductWorldWriters, ...ports });
}

export function createTryGuide(options = {}) {
  const givenPorts = options.ports ?? {};
  return runtimeCreateTryGuide({
    ...options,
    ports: {
      ...givenPorts,
      redaction: seamRedaction(givenPorts),
      ...(givenPorts.evidenceEligibility === undefined && givenPorts.readEvidenceEligibility === undefined
        ? { evidenceEligibility: (...args) => req('./workflow-runner.mjs').readEvidenceEligibility(...args) }
        : {}),
    },
  });
}

export async function runContracts(input, ports = {}) {
  const { readEvidenceEligibility } = await import('./workflow-runner.mjs');
  return runtimeRunContracts(input, { evidenceEligibility: readEvidenceEligibility, ...ports });
}

export async function runJobs(input = {}, ports = {}) {
  const { NAMES } = await import('./command-catalog.mjs');
  return runtimeRunJobs({ ...input, client: input?.client ?? { commands: { test: NAMES.test, lint: NAMES.lint, simulate: NAMES.simulate } } }, ports);
}

export async function checkRuntimeHealth(input, ports = {}) {
  await import('./secret-redaction.mjs');
  return runtimeCheckHealth(input, { ...ports, redaction: seamRedaction(ports) });
}

export async function loadRuntimeClient() {
  const [{ DEFAULT_RUNTIME_URL, checkRuntimeHealth: rawCheckHealth, runtimeOrigin }] = await Promise.all([
    runtimeLoadClient(),
    import('./secret-redaction.mjs'),
  ]);
  return {
    DEFAULT_RUNTIME_URL,
    runtimeOrigin,
    checkRuntimeHealth: (input, ports = {}) => rawCheckHealth(input, { ...ports, redaction: seamRedaction(ports) }),
  };
}

export async function runAutomaticApproval(input = {}, ports = {}) {
  const [
    { approvalActor, readApprovalPolicy, readPromptApprovals, recordPromptApproval },
    { approvePromptText, promptPath },
    ,
    { headerPrompts },
    { lintSvgLayouts },
  ] = await Promise.all([
    import('./approval-policy.mjs'),
    import('./prompt-approve.mjs'),
    import('./secret-redaction.mjs'),
    import('./file-owner.mjs'),
    import('./svg-layout.mjs'),
  ]);
  const env = ports.env ?? process.env;
  const client = ports.client ?? input?.client ?? { version: clientVersion() };
  const workflow = ports.workflow ?? input?.workflow ?? { base_sha: resolveWorkflowBaseSha(input?.root ?? input?.cwd, env) };
  return runtimeRunAutomaticApproval(input, {
    approvalActor,
    readApprovalPolicy,
    readPromptApprovals,
    recordPromptApproval,
    approvePromptText,
    promptPath,
    headerPrompts,
    lintSvgLayouts,
    client,
    workflow,
    ...ports,
    redaction: seamRedaction(ports),
  });
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
  ]);
  const env = ports.env ?? process.env;
  const needsBatchPlan = !NON_BATCH_MODES.some(flag => input?.options?.[flag] !== undefined);
  const workflow = input?.workflow !== undefined
    ? input.workflow
    : (needsBatchPlan ? { base_sha: resolveWorkflowBaseSha(input?.cwd, env) } : undefined);
  return runtimeRunCheck(
    {
      ...input,
      client: input?.client ?? { version: clientVersion() },
      ...(workflow !== undefined ? { workflow } : {}),
    },
    {
      headerPrompts,
      evidenceEligibility: readEvidenceEligibility,
      allRuns,
      assessNativeEvidence,
      usableResult,
      resultLines,
      lintSvgLayouts,
      compareScreen,
      formatScreenComparison,
      ...ports,
      redaction: seamRedaction(ports),
    },
  );
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
  return runtimeRunTry(input, {
    tryLauncherUrl: TRY_LAUNCHER_URL,
    loadAgentDefinitions,
    discoverAgents: async (...args) => (await import('./agent-adapters.mjs')).discoverAgents(...args),
    askAgent: async (...args) => (await import('./agent-adapters.mjs')).askAgent(...args),
    evidenceEligibility: readEvidenceEligibility,
    parseProductDocuments,
    parseProductWorldWriters,
    askApproval,
    lineReader,
    promptPath,
    ...ports,
    redaction: seamRedaction(ports),
  });
}

export async function createAgentBridge(context, test, tryId, options, link, seamPorts = {}) {
  const [
    ,
    { loadAgentDefinitions },
    { askAgent, discoverAgents },
    { readEvidenceEligibility },
  ] = await Promise.all([
    import('./secret-redaction.mjs'),
    import('./agent-config.mjs'),
    import('./agent-adapters.mjs'),
    import('./workflow-runner.mjs'),
  ]);
  return runtimeCreateAgentBridge(context, test, tryId, options, link, {
    loadAgentDefinitions,
    discoverAgents,
    askAgent,
    evidenceEligibility: readEvidenceEligibility,
    ...seamPorts,
    redaction: seamRedaction(seamPorts),
  });
}

export async function runShim(descriptorPath, argv, ports = {}) {
  const [, { lineReader }] = await Promise.all([
    import('./secret-redaction.mjs'),
    import('./prompt-approve.mjs'),
  ]);
  return runtimeRunShim(descriptorPath, argv, { lineReader, ...ports, redaction: ports.redaction ?? hostRedaction() });
}

export async function readTryOwner(input = {}, ports = {}) {
  const [
    ,
    { readEvidenceEligibility },
    { parseProductDocuments, parseProductWorldWriters },
  ] = await Promise.all([
    import('./secret-redaction.mjs'),
    import('./workflow-runner.mjs'),
    import('./product.mjs'),
  ]);
  return runtimeReadTryOwner(input, {
    tryLauncherUrl: TRY_LAUNCHER_URL,
    evidenceEligibility: readEvidenceEligibility,
    parseProductDocuments,
    parseProductWorldWriters,
    ...ports,
    redaction: seamRedaction(ports),
  });
}

export async function runMcp(input, ports = {}) {
  const [
    ,
    { readEvidenceEligibility },
    { parseProductDocuments, parseProductWorldWriters },
  ] = await Promise.all([
    import('./secret-redaction.mjs'),
    import('./workflow-runner.mjs'),
    import('./product.mjs'),
  ]);
  return runtimeRunMcp(input, {
    tryLauncherUrl: TRY_LAUNCHER_URL,
    evidenceEligibility: readEvidenceEligibility,
    parseProductDocuments,
    parseProductWorldWriters,
    ...ports,
    redaction: seamRedaction(ports),
  });
}

export async function migrateRuntimeWorkspace(input, ports = {}) {
  const { readEvidenceEligibility } = await import('./workflow-runner.mjs');
  return runtimeMigrateWorkspace(input, { evidenceEligibility: readEvidenceEligibility, ...ports });
}

export {
  LIMITS,
  PROMPT_TESTS_LABEL,
  PROMPT_TESTS_WORDS,
  allowsRuntimePath,
  buildAgentInput,
  captureSource,
  causeText,
  checkInput,
  checkPlanResultLines,
  checkPlanResults,
  cleanText,
  createSavedStoryEvidenceReader,
  exactIntegerLeaves,
  findTests,
  gitFiles,
  interfaceBlocks,
  interfaceSchemaProblems,
  isSecretPath,
  isStoryPath,
  jsonSafe,
  loadInterfaceDraft,
  loadRuntimeWorkspace,
  outcomeText,
  parseScenarioJson,
  preflight,
  productTapCallBound,
  promptRefusal,
  promptSchemaRefusals,
  proseSha256,
  readPrompt,
  requireRuntimePath,
  resultOutcome,
  runInterfaceDraft,
  selectJourneys,
  sha256,
  sourceFilePort,
  storyLines,
  stringifyScenarioJson,
  withExactIntegers,
} from './runtime/index.mjs';
