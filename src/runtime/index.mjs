// Generated from prompts/cli/runtime-entry.prompt.md (sha256: f97733acc0d28351be733812025ed125e3f86f1ee62bef37034592f26bd79fe6).
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

const req = createRequire(import.meta.url);

let checkPlanModule = null;
function loadCheckPlan() {
  return (checkPlanModule ??= req('./runtime-check-plan.mjs'));
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
  return (productCompositionModule ??= req('./product-composition.mjs'));
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
  return (agentGuideModule ??= req('./agent-guide.mjs'));
}

export function createTryGuide(options) {
  return loadAgentGuide().createTryGuide(options);
}

let agentProjectModule = null;
function loadAgentProject() {
  return (agentProjectModule ??= req('./agent-project.mjs'));
}

export function buildProjectCard(input) {
  return loadAgentProject().buildProjectCard(input);
}

export function readAgentScenarios(input) {
  return loadAgentProject().readAgentScenarios(input);
}

export async function runJobs(input, ports) {
  const { runJobs: run } = await import('./runtime-slots.mjs');
  return run(input, ports);
}

let contractsModule = null;
function loadContracts() {
  return (contractsModule ??= req('./contracts.mjs'));
}

export function runContracts(input, ports) {
  return loadContracts().runContracts(input, ports);
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

let tryMcpModule = null;
function loadTryMcp() {
  return (tryMcpModule ??= req('./try-mcp.mjs'));
}

export function createTryTools(input, ports) {
  return loadTryMcp().createTryTools(input, ports);
}

export async function runMcp(input, ports) {
  const { runMcp: run } = await import('./try-mcp.mjs');
  return run(input, ports);
}

export async function openCli(context, test, sessionId, options) {
  const { openCli: open } = await import('./try-doors.mjs');
  return open(context, test, sessionId, options);
}

export async function runShim(descriptorPath, argv, ports) {
  const { runShim: run } = await import('./try-doors.mjs');
  return run(descriptorPath, argv, ports);
}

export async function saveLast(input) {
  const { saveLast: save } = await import('./try-doors.mjs');
  return save(input);
}

let runtimeClientModule = null;
function loadRuntimeClientSync() {
  return (runtimeClientModule ??= req('./runtime-client.mjs'));
}

export function readContractHistory(input, ports) {
  return loadRuntimeClientSync().readContractHistory(input, ports);
}

export function runtimeWorkspaceMigrationStore(input, given) {
  return loadRuntimeClientSync().runtimeWorkspaceMigrationStore(input, given);
}

export function saveDoorCaseResult(root, saved, options) {
  return loadRuntimeClientSync().saveDoorCaseResult(root, saved, options);
}

export function saveDoorCase(root, saved, options) {
  return loadRuntimeClientSync().saveDoorCase(root, saved, options);
}

export async function loadRuntimeClient() {
  const { DEFAULT_RUNTIME_URL, checkRuntimeHealth, runtimeOrigin } = await import('./runtime-client.mjs');
  return { DEFAULT_RUNTIME_URL, checkRuntimeHealth, runtimeOrigin };
}

export async function checkRuntimeHealth(input, ports) {
  const { checkRuntimeHealth: check } = await import('./runtime-client.mjs');
  return check(input, ports);
}

export async function savedStoryEvidence(input, ports) {
  const { savedStoryEvidence: read } = await import('./runtime-client.mjs');
  return read(input, ports);
}

export function createSavedStoryEvidenceReader(ports = {}) {
  let readerPromise = null;
  return async input => {
    readerPromise ??= import('./runtime-client.mjs').then(m => m.createSavedStoryEvidenceReader(ports));
    return (await readerPromise)(input);
  };
}

export async function acquireRuntimeBatchLock(folder, options) {
  const { acquireRuntimeBatchLock: acquire } = await import('./runtime-client.mjs');
  return acquire(folder, options);
}

export async function acquireCaseWriteOwnership(input, ports) {
  const { acquireCaseWriteOwnership: acquire } = await import('./runtime-client.mjs');
  return acquire(input, ports);
}

export async function applyPendingCase(input, ports) {
  const { applyPendingCase: apply } = await import('./runtime-client.mjs');
  return apply(input, ports);
}

export async function applyPendingCaseWithHandoff(input, ports) {
  const { applyPendingCaseWithHandoff: apply } = await import('./runtime-client.mjs');
  return apply(input, ports);
}

export async function runCheck(input, ports) {
  const { runCheck: run } = await import('./runtime-client.mjs');
  return run(input, ports);
}

export async function runTry(input, ports) {
  const { runTry: run } = await import('./runtime-client.mjs');
  return run(input, ports);
}

export async function runDoorCall(descriptor, input, ports) {
  const { runDoorCall: run } = await import('./runtime-client.mjs');
  return run(descriptor, input, ports);
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
