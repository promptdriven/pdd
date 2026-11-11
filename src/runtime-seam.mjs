// Generated from prompts/cli/runtime-seam.prompt.md (sha256: c0992a6a707221d813d73cad123282d3b27bdb73b1db930ea4c703965040f611).
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
  try { realRoot = realpathSync(root); } catch { return null; }
  const matching = readAllRuns({ cancelled: true }, { env }).filter(run => {
    try { return realpathSync(run.root) === realRoot; } catch { return false; }
  });
  return matching.length === 1 && /^[a-f0-9]{40}$/.test(matching[0].baseSha ?? '') ? matching[0].baseSha : null;
}

export function buildCheckPlan(input, ports = {}) {
  const { headerPrompts } = req('./file-owner.mjs');
  return runtimeBuildCheckPlan(input, withPortDefaults(ports, { headerPrompts }));
}

export function composeProductTry(input, ports = {}) {
  const { parseProductDocuments, parseProductWorldWriters } = req('./product.mjs');
  return runtimeComposeProductTry(input, withPortDefaults(ports, { parseProductDocuments, parseProductWorldWriters }));
}

export function createTryGuide(options = {}) {
  const givenPorts = options.ports ?? {};
  const lazyEligibility = (...args) => req('./workflow-runner.mjs').readEvidenceEligibility(...args);
  return runtimeCreateTryGuide({
    ...options,
    ports: withPortDefaults(withEligibilityDefault(givenPorts, lazyEligibility), {
      redaction: seamRedaction(givenPorts),
    }),
  });
}

export function runContracts(input, ports = {}) {
  const lazyEligibility = (...args) => req('./workflow-runner.mjs').readEvidenceEligibility(...args);
  return runtimeRunContracts(input, withEligibilityDefault(ports, lazyEligibility));
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
  const [{ DEFAULT_RUNTIME_URL, checkRuntimeHealth: rawCheckHealth, runtimeOrigin }] = await Promise.all([
    runtimeLoadClient(),
    import('./secret-redaction.mjs'),
  ]);
  return {
    DEFAULT_RUNTIME_URL,
    runtimeOrigin,
    checkRuntimeHealth: (input, ports = {}) =>
      rawCheckHealth(input, withPortDefaults(ports, { redaction: seamRedaction(ports) })),
  };
}

export async function runAutomaticApproval(input = {}, ports = {}) {
  const [
    { approvalActor, readApprovalPolicy, readPromptApprovals, recordPromptApproval },
    { approvePromptText, promptPath },
    ,
    { headerPrompts },
    { readEvidenceEligibility },
    { allRuns },
    { lintSvgLayouts },
  ] = await Promise.all([
    import('./approval-policy.mjs'),
    import('./prompt-approve.mjs'),
    import('./secret-redaction.mjs'),
    import('./file-owner.mjs'),
    import('./workflow-runner.mjs'),
    import('./workflow-runs.mjs'),
    import('./svg-layout.mjs'),
  ]);
  const env = ports.env ?? process.env;
  const client = ports.client ?? (input?.client ? { ...input.client, version: input.client.version ?? clientVersion() } : { version: clientVersion() });
  const explicitWorkflow = ports.workflow ?? input?.workflow;
  return runtimeRunAutomaticApproval(
    input,
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
      lintSvgLayouts,
      client,
      ...(explicitWorkflow !== undefined ? { workflow: explicitWorkflow } : {}),
      redaction: seamRedaction(ports),
    }),
  );
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
  const client = input?.client ? { ...input.client, version: input.client.version ?? clientVersion() } : { version: clientVersion() };
  return runtimeRunCheck(
    {
      ...input,
      client,
    },
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
  const defaultDiscoverAgents = async (...args) => (await import('./agent-adapters.mjs')).discoverAgents(...args);
  const defaultAskAgent = async (...args) => (await import('./agent-adapters.mjs')).askAgent(...args);
  return runtimeRunTry(
    input,
    withPortDefaults(withEligibilityDefault(ports, readEvidenceEligibility), {
      tryLauncherUrl: TRY_LAUNCHER_URL,
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
  );
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
  return runtimeCreateAgentBridge(
    context,
    test,
    tryId,
    options,
    link,
    withPortDefaults(withEligibilityDefault(seamPorts, readEvidenceEligibility), {
      loadAgentDefinitions: seamPorts.loadAgentDefinitions ?? seamPorts.agents?.loadDefinitions ?? loadAgentDefinitions,
      discoverAgents: seamPorts.discoverAgents ?? seamPorts.agents?.list ?? discoverAgents,
      askAgent: seamPorts.askAgent ?? seamPorts.agents?.ask ?? askAgent,
      redaction: seamRedaction(seamPorts),
    }),
  );
}

export async function runShim(descriptorPath, argv, ports = {}) {
  const [, { lineReader }] = await Promise.all([
    import('./secret-redaction.mjs'),
    import('./prompt-approve.mjs'),
  ]);
  return runtimeRunShim(descriptorPath, argv, withPortDefaults(ports, { lineReader, redaction: seamRedaction(ports) }));
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
  return runtimeReadTryOwner(
    input,
    withPortDefaults(withEligibilityDefault(ports, readEvidenceEligibility), {
      tryLauncherUrl: TRY_LAUNCHER_URL,
      parseProductDocuments,
      parseProductWorldWriters,
      redaction: seamRedaction(ports),
    }),
  );
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
  return runtimeRunMcp(
    input,
    withPortDefaults(withEligibilityDefault(ports, readEvidenceEligibility), {
      tryLauncherUrl: TRY_LAUNCHER_URL,
      parseProductDocuments,
      parseProductWorldWriters,
      redaction: seamRedaction(ports),
    }),
  );
}

export async function migrateRuntimeWorkspace(input, ports = {}) {
  const { readEvidenceEligibility } = await import('./workflow-runner.mjs');
  return runtimeMigrateWorkspace(input, withEligibilityDefault(ports, readEvidenceEligibility));
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
