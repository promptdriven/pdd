// Generated from prompts/cli/runtime-entry.prompt.md (sha256: da72903fa15d679b31aee8a3af6f041ac59a718e97072d30c73d165095bbf0fa).
import { createRequire } from 'node:module';

export {
  exactIntegerLeaves,
  jsonSafe,
  parseScenarioJson,
  stringifyScenarioJson,
  withExactIntegers,
} from './scenario-json.mjs';

export {
  allowsRuntimePath,
  loadRuntimeWorkspace,
  requireRuntimePath,
} from './runtime-workspace.mjs';

export {
  outcomeText,
  resultOutcome,
} from './runtime-outcome.mjs';

export {
  PROMPT_TESTS_LABEL,
  PROMPT_TESTS_WORDS,
  causeText,
  cleanText,
  storyLines,
} from './runtime-output.mjs';

export {
  LIMITS,
  captureSource,
  checkInput,
  findTests,
  gitFiles,
  interfaceBlocks,
  interfaceSchemaProblems,
  isSecretPath,
  isStoryPath,
  preflight,
  promptRefusal,
  promptSchemaRefusals,
  proseSha256,
  readPrompt,
  sha256,
  sourceFilePort,
} from './runtime-preflight.mjs';

export { buildAgentInput } from './agent-packet.mjs';

let checkPlanModule = null;
function loadCheckPlan() {
  return (checkPlanModule ??= createRequire(import.meta.url)('./runtime-check-plan.mjs'));
}

export function buildCheckPlan(input, ports) {
  return loadCheckPlan().buildCheckPlan(input, ports);
}

export function checkPlanResults(plan, rows) {
  return loadCheckPlan().checkPlanResults(plan, rows);
}

export function checkPlanResultLines(result) {
  return loadCheckPlan().checkPlanResultLines(result);
}

let productCompositionModule = null;
function loadProductComposition() {
  return (productCompositionModule ??= createRequire(import.meta.url)('./product-composition.mjs'));
}

export function composeProductTry(input, ports) {
  return loadProductComposition().composeProductTry(input, ports);
}

export function productTapCallBound(map, ports) {
  return loadProductComposition().productTapCallBound(map, ports);
}

export function selectJourneys(tests, selector) {
  return loadProductComposition().selectJourneys(tests, selector);
}

let agentGuideModule = null;
function loadAgentGuide() {
  return (agentGuideModule ??= createRequire(import.meta.url)('./agent-guide.mjs'));
}

export function createTryGuide(options) {
  return loadAgentGuide().createTryGuide(options);
}

export async function runJobs(input, ports) {
  const { runJobs: run } = await import('./runtime-slots.mjs');
  return run(input, ports);
}

export async function runContracts(input, ports) {
  const { runContracts: run } = await import('./contracts.mjs');
  return run(input, ports);
}

export async function loadInterfaceDraft() {
  const { contractCoverage, coverageView, missingInterfaces } = await import('./interface-draft.mjs');
  return { contractCoverage, coverageView, missingInterfaces };
}

export async function runInterfaceDraft(input, ports) {
  const { runInterfaceDraft: run } = await import('./interface-draft.mjs');
  return run(input, ports);
}

export async function runAutomaticApproval(input, ports) {
  const { runAutomaticApproval: run } = await import('./interface-draft.mjs');
  return run(input, ports);
}

export async function runMcp(input, ports) {
  const { runMcp: run } = await import('./try-mcp.mjs');
  return run(input, ports);
}

export async function runShim(descriptorPath, argv, ports) {
  const { runShim: run } = await import('./try-doors.mjs');
  return run(descriptorPath, argv, ports);
}

export async function loadRuntimeClient() {
  const { DEFAULT_RUNTIME_URL, checkRuntimeHealth, runtimeOrigin } = await import('./runtime-client.mjs');
  return { DEFAULT_RUNTIME_URL, checkRuntimeHealth, runtimeOrigin };
}

export async function checkRuntimeHealth(input, ports) {
  const { checkRuntimeHealth: check } = await import('./runtime-client.mjs');
  return check(input, ports);
}

export function createSavedStoryEvidenceReader(ports = {}) {
  let readerPromise = null;
  return async input => {
    readerPromise ??= import('./runtime-client.mjs').then(m => m.createSavedStoryEvidenceReader(ports));
    return (await readerPromise)(input);
  };
}

export async function runCheck(input, ports) {
  const { runCheck: run } = await import('./runtime-client.mjs');
  return run(input, ports);
}

export async function runTry(input, ports) {
  const { runTry: run } = await import('./runtime-client.mjs');
  return run(input, ports);
}

export async function readTryOwner(input, ports) {
  const { readTryOwner: read } = await import('./runtime-client.mjs');
  return read(input, ports);
}

export async function createAgentBridge(context, test, tryId, options, link, seamPorts) {
  const { createAgentBridge: create } = await import('./agent-chat.mjs');
  return create(context, test, tryId, options, link, seamPorts);
}

export async function migrateRuntimeWorkspace(input, ports) {
  const { migrateRuntimeWorkspace: migrate } = await import('./runtime-workspace-migration.mjs');
  return migrate(input, ports);
}
