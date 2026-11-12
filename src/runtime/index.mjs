// Generated from prompts/cli/runtime-entry.prompt.md (sha256: 443d22f5cde45b9bf07ecc3d502a24d3205d4d807712bc65bba7a224549df7e0).
import { createRequire } from 'node:module';

const req = createRequire(import.meta.url);

export const LIMITS = Object.freeze({ bytes: 10_485_760, files: 10_000 });
export const PROMPT_TESTS_LABEL = 'Prompt tests';
export const PROMPT_TESTS_WORDS = '(?:Prompt tests|Runtime check)';

let scenarioJsonModule = null;
export function runtimeScenarioJsonSlice() {
  return (scenarioJsonModule ??= req('./scenario-json.mjs'));
}

let workspaceModule = null;
export function runtimeWorkspaceSlice() {
  return (workspaceModule ??= req('./runtime-workspace.mjs'));
}

let outcomeModule = null;
export function runtimeOutcomeSlice() {
  return (outcomeModule ??= req('./runtime-outcome.mjs'));
}

let outputModule = null;
export function runtimeOutputSlice() {
  return (outputModule ??= req('./runtime-output.mjs'));
}

let preflightModule = null;
export function runtimePreflightSlice() {
  return (preflightModule ??= req('./runtime-preflight.mjs'));
}

let agentPacketModule = null;
export function runtimeAgentPacketSlice() {
  return (agentPacketModule ??= req('./agent-packet.mjs'));
}

let checkPlanModule = null;
export function runtimeCheckPlanSlice() {
  return (checkPlanModule ??= req('./runtime-check-plan.mjs'));
}

let runtimeClientModule = null;
export function runtimeClientSlice() {
  return (runtimeClientModule ??= req('./runtime-client.mjs'));
}

export function exactIntegerLeaves(...args) {
  return runtimeScenarioJsonSlice().exactIntegerLeaves(...args);
}

export function jsonSafe(...args) {
  return runtimeScenarioJsonSlice().jsonSafe(...args);
}

export function parseScenarioJson(...args) {
  return runtimeScenarioJsonSlice().parseScenarioJson(...args);
}

export function stringifyScenarioJson(...args) {
  return runtimeScenarioJsonSlice().stringifyScenarioJson(...args);
}

export function withExactIntegers(...args) {
  return runtimeScenarioJsonSlice().withExactIntegers(...args);
}

export function allowsRuntimePath(...args) {
  return runtimeWorkspaceSlice().allowsRuntimePath(...args);
}

export function loadRuntimeWorkspace(...args) {
  return runtimeWorkspaceSlice().loadRuntimeWorkspace(...args);
}

export function requireRuntimePath(...args) {
  return runtimeWorkspaceSlice().requireRuntimePath(...args);
}

export function outcomeText(...args) {
  return runtimeOutcomeSlice().outcomeText(...args);
}

export function resultOutcome(...args) {
  return runtimeOutcomeSlice().resultOutcome(...args);
}

export function causeText(...args) {
  return runtimeOutputSlice().causeText(...args);
}

export function cleanText(...args) {
  return runtimeOutputSlice().cleanText(...args);
}

export function storyLines(...args) {
  return runtimeOutputSlice().storyLines(...args);
}

export function captureSource(...args) {
  return runtimePreflightSlice().captureSource(...args);
}

export function checkInput(...args) {
  return runtimePreflightSlice().checkInput(...args);
}

export function findTests(...args) {
  return runtimePreflightSlice().findTests(...args);
}

export function gitFiles(...args) {
  return runtimePreflightSlice().gitFiles(...args);
}

export function interfaceBlocks(...args) {
  return runtimePreflightSlice().interfaceBlocks(...args);
}

export function interfaceSchemaProblems(...args) {
  return runtimePreflightSlice().interfaceSchemaProblems(...args);
}

export function isSecretPath(...args) {
  return runtimePreflightSlice().isSecretPath(...args);
}

export function isStoryPath(...args) {
  return runtimePreflightSlice().isStoryPath(...args);
}

export function preflight(...args) {
  return runtimePreflightSlice().preflight(...args);
}

export function promptRefusal(...args) {
  return runtimePreflightSlice().promptRefusal(...args);
}

export function promptSchemaRefusals(...args) {
  return runtimePreflightSlice().promptSchemaRefusals(...args);
}

export function proseSha256(...args) {
  return runtimePreflightSlice().proseSha256(...args);
}

export function readPrompt(...args) {
  return runtimePreflightSlice().readPrompt(...args);
}

export function sha256(...args) {
  return runtimePreflightSlice().sha256(...args);
}

export function sourceFilePort(...args) {
  return runtimePreflightSlice().sourceFilePort(...args);
}

export function buildAgentInput(...args) {
  return runtimeAgentPacketSlice().buildAgentInput(...args);
}

export function buildCheckPlan(input, ports) {
  return runtimeCheckPlanSlice().buildCheckPlan(input, ports);
}

export function checkPlanResults(plan, rows) {
  return runtimeCheckPlanSlice().checkPlanResults(plan, rows);
}

export function checkPlanResultLines(result) {
  return runtimeCheckPlanSlice().checkPlanResultLines(result);
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

export function runtimeOrigin(env) {
  return runtimeClientSlice().runtimeOrigin(env);
}

export function readContractHistory(input, ports) {
  return runtimeClientSlice().readContractHistory(input, ports);
}

export function runtimeWorkspaceMigrationStore(input, given) {
  return runtimeClientSlice().runtimeWorkspaceMigrationStore(input, given);
}

export function saveDoorCaseResult(root, saved, options) {
  return runtimeClientSlice().saveDoorCaseResult(root, saved, options);
}

export function saveDoorCase(root, saved, options) {
  return runtimeClientSlice().saveDoorCase(root, saved, options);
}

export function createSavedStoryEvidenceReader(ports = {}) {
  return runtimeClientSlice().createSavedStoryEvidenceReader(ports);
}

export async function loadRuntimeClient() {
  const { DEFAULT_RUNTIME_URL, checkRuntimeHealth, runtimeOrigin: origin } = await import('./runtime-client.mjs');
  return { DEFAULT_RUNTIME_URL, checkRuntimeHealth, runtimeOrigin: origin };
}

export async function checkRuntimeHealth(input, ports) {
  const { checkRuntimeHealth: check } = await import('./runtime-client.mjs');
  return check(input, ports);
}

export async function savedStoryEvidence(input, ports) {
  const { savedStoryEvidence: read } = await import('./runtime-client.mjs');
  return read(input, ports);
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
