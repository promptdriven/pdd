// Generated from prompts/cli/runtime-entry.prompt.md (sha256: 4ee8da83ca6ebf98cd3446e7482db398ebb2d933b12ac1768e4a51803d2dca6d).
import { createRequire } from 'node:module';
import { isDeepStrictEqual } from 'node:util';

const req = createRequire(import.meta.url);

export const LIMITS = Object.freeze({ bytes: 10_485_760, files: 10_000 });
export const TEST_SCHEMA = 'prompt-runtime.program-scenario.v1';
const APP_MAP_SCHEMA = 'prompt-runtime.app-map.v1';
const ENGINE_SHA = 'eae2202a68d00ab762fcbbf1eba0d8607a132a15';
export const DRAFT_SERVER_TEXT = 'The server does not run draft prompts yet. Approve the prompt first, or wait for the server update.';
export const STALE_HINT = 'the text changed after approval: set status to draft, run pdd test --fill-hash, ask the person';
export const staleHint = `pdd: ${STALE_HINT}.`;
export const PROVIDER_TEXT = 'the AI provider failed during the run. It is not a failed check. Do not send it again yet.';
export const CHECK_STATES = Object.freeze(['waiting', 'sent', 'passed', 'failed', 'refused', 'partial', 'not run']);
export const OPEN_STATES = new Set(['queued', 'running', 'sent']);

export class PreflightError extends Error {
  constructor(exitCode, message) {
    const Real = runtimePreflightSlice().PreflightError;
    return new Real(exitCode, message);
  }
  static [Symbol.hasInstance](value) {
    return value instanceof runtimePreflightSlice().PreflightError;
  }
}

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

export function exactValue(...args) {
  return runtimeScenarioJsonSlice().exactValue(...args);
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

export function hasProgress(...args) {
  return runtimeOutcomeSlice().hasProgress(...args);
}

export function outcomeDone(...args) {
  return runtimeOutcomeSlice().outcomeDone(...args);
}

export function outcomeFor(...args) {
  return runtimeOutcomeSlice().outcomeFor(...args);
}

export function outcomeOverall(...args) {
  return runtimeOutcomeSlice().outcomeOverall(...args);
}

export function outcomeText(...args) {
  return runtimeOutcomeSlice().outcomeText(...args);
}

export function progressText(...args) {
  return runtimeOutcomeSlice().progressText(...args);
}

export function resultOutcome(...args) {
  return runtimeOutcomeSlice().resultOutcome(...args);
}

export function resultOverall(...args) {
  return runtimeOutcomeSlice().resultOverall(...args);
}

export function causeText(...args) {
  return runtimeOutputSlice().causeText(...args);
}

export function cleanText(...args) {
  return runtimeOutputSlice().cleanText(...args);
}

export function coverageText(...args) {
  return runtimeOutputSlice().coverageText(...args);
}

export function jsonRow(...args) {
  return runtimeOutputSlice().jsonRow(...args);
}

export function progressTicker(...args) {
  return runtimeOutputSlice().progressTicker(...args);
}

export function projectAnswer(...args) {
  return runtimeOutputSlice().projectAnswer(...args);
}

export function refusalView(...args) {
  return runtimeOutputSlice().refusalView(...args);
}

export function renderJson(...args) {
  return runtimeOutputSlice().renderJson(...args);
}

export function renderText(...args) {
  return runtimeOutputSlice().renderText(...args);
}

export function sinceText(...args) {
  return runtimeOutputSlice().sinceText(...args);
}

export function stepTimeLimit(...args) {
  return runtimeOutputSlice().stepTimeLimit(...args);
}

export function storyLines(...args) {
  return runtimeOutputSlice().storyLines(...args);
}

export function summaryLine(...args) {
  return runtimeOutputSlice().summaryLine(...args);
}

export function tryUsage(...args) {
  return runtimeOutputSlice().tryUsage(...args);
}

export function tryUsageHeaders(...args) {
  return runtimeOutputSlice().tryUsageHeaders(...args);
}

export function tryUsageLine(...args) {
  return runtimeOutputSlice().tryUsageLine(...args);
}

export function validLink(...args) {
  return runtimeOutputSlice().validLink(...args);
}

export function captureSource(...args) {
  return runtimePreflightSlice().captureSource(...args);
}

export function checkInput(...args) {
  return runtimePreflightSlice().checkInput(...args);
}

export function createStrictSourceAccess(...args) {
  return runtimePreflightSlice().createStrictSourceAccess(...args);
}

export function defaultMaxCalls(...args) {
  return runtimePreflightSlice().defaultMaxCalls(...args);
}

export function discoveryRefusal(...args) {
  return runtimePreflightSlice().discoveryRefusal(...args);
}

export function discoveryVisibleFiles(...args) {
  return runtimePreflightSlice().discoveryVisibleFiles(...args);
}

export function executableInterfaceText(...args) {
  return runtimePreflightSlice().executableInterfaceText(...args);
}

export function fillHashes(...args) {
  return runtimePreflightSlice().fillHashes(...args);
}

export function findTests(...args) {
  return runtimePreflightSlice().findTests(...args);
}

export function formatSize(...args) {
  return runtimePreflightSlice().formatSize(...args);
}

export function formatWarningLines(...args) {
  return runtimePreflightSlice().formatWarningLines(...args);
}

export function gitFiles(...args) {
  return runtimePreflightSlice().gitFiles(...args);
}

export function hasPromptInterface(...args) {
  return runtimePreflightSlice().hasPromptInterface(...args);
}

export function interfaceBlocks(...args) {
  return runtimePreflightSlice().interfaceBlocks(...args);
}

export function interfaceFormatWarnings(...args) {
  return runtimePreflightSlice().interfaceFormatWarnings(...args);
}

export function interfaceKindProblems(...args) {
  return runtimePreflightSlice().interfaceKindProblems(...args);
}

export function interfaceSchemaProblems(...args) {
  return runtimePreflightSlice().interfaceSchemaProblems(...args);
}

export function isSecretPath(...args) {
  return runtimePreflightSlice().isSecretPath(...args);
}

export function numberWarnings(...args) {
  return runtimePreflightSlice().numberWarnings(...args);
}

export function otherFiles(...args) {
  return runtimePreflightSlice().otherFiles(...args);
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

export function scenarioShapeRefusal(...args) {
  return runtimePreflightSlice().scenarioShapeRefusal(...args);
}

export function schemaKeywordWarningLines(...args) {
  return runtimePreflightSlice().schemaKeywordWarningLines(...args);
}

export function sha256(...args) {
  return runtimePreflightSlice().sha256(...args);
}

export function sharedSourceFiles(...args) {
  return runtimePreflightSlice().sharedSourceFiles(...args);
}

export function sourceFilePort(...args) {
  return runtimePreflightSlice().sourceFilePort(...args);
}

export function storyCriteria(...args) {
  return runtimePreflightSlice().storyCriteria(...args);
}

export function tarFiles(...args) {
  return runtimePreflightSlice().tarFiles(...args);
}

export function buildAgentInput(...args) {
  return runtimeAgentPacketSlice().buildAgentInput(...args);
}

export function baselineReport(input) {
  return runtimeCheckPlanSlice().baselineReport(input);
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

export function selectCheckTests(plan, options) {
  return runtimeCheckPlanSlice().selectCheckTests(plan, options);
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

export function selectJourneys(tests, selector, ports) {
  return loadProductComposition().selectJourneys(tests, selector, ports);
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

export function readAgentScenarios(input, ports) {
  return loadAgentProject().readAgentScenarios(input, ports);
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

export async function openServe(context, test, sessionId, options) {
  const { openServe: open } = await import('./try-http.mjs');
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

export function defaultLineReader(stdin) {
  return runtimeClientSlice().defaultLineReader(stdin);
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
  const { DEFAULT_RUNTIME_URL: defaultUrl, checkRuntimeHealth: checkHealth, runtimeOrigin: origin } = await import('./runtime-client.mjs');
  return { DEFAULT_RUNTIME_URL: defaultUrl, checkRuntimeHealth: checkHealth, runtimeOrigin: origin };
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

export async function askAgent(input, ports) {
  const { askAgent: ask } = await import('./agent-ask.mjs');
  return ask(input, ports);
}

export async function createAgentBridge(context, test, tryId, options, link, seamPorts) {
  const { createAgentBridge: create } = await import('./agent-chat.mjs');
  return create(context, test, tryId, options, link, seamPorts);
}

export async function migrateRuntimeWorkspace(input, ports) {
  const { migrateRuntimeWorkspace: migrate } = await import('./runtime-workspace-migration.mjs');
  return migrate(input, ports);
}

const isPlainObject = value =>
  value !== null &&
  typeof value === 'object' &&
  !Array.isArray(value) &&
  (Object.getPrototypeOf(value) === Object.prototype || Object.getPrototypeOf(value) === null);

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

export async function check(input = {}, ports) {
  const extraOptions =
    input?.affected === true && input?.options?.['--affected'] === undefined ? { '--affected': true } : {};
  return runCheck(buildCheckInput(input, { defaultCache: true, extraOptions }), ports);
}

export async function lint(input = {}, ports) {
  const extraOptions = {
    '--lint': true,
    ...(input?.local === true && input?.options?.['--local'] === undefined ? { '--local': true } : {}),
  };
  return runCheck(buildCheckInput(input, { defaultCache: true, extraOptions }), ports);
}

export async function read(input = {}, ports) {
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

export async function retry(input = {}, ports) {
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

export async function local(input = {}, ports) {
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

export async function simulate(input = {}, ports) {
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

export async function jobs(input = {}, ports) {
  const env = input?.env ?? ports?.env;
  return runJobs({ ...(input ?? {}), ...(env !== undefined ? { env } : {}) }, ports);
}

export async function health(input = {}, ports) {
  const env = input?.env ?? ports?.env;
  return checkRuntimeHealth({ ...(input ?? {}), ...(env !== undefined ? { env } : {}) }, ports);
}

export async function mcp(input = {}, ports) {
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

export async function draftInterfaces(input = {}, ports) {
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

export function contracts(input = {}, ports) {
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

function parseInterfaceBlockMatch(match) {
  let parsed = null;
  try {
    const candidate = JSON.parse(match[1]);
    if (isPlainObject(candidate)) parsed = candidate;
  } catch {
    parsed = null;
  }
  return {
    raw: match[0],
    json: parsed,
    status: typeof parsed?.status === 'string' ? parsed.status : null,
    prose_sha256: typeof parsed?.prose_sha256 === 'string' ? parsed.prose_sha256 : null,
    start: match.indices[0][0],
    end: match.indices[0][1],
  };
}

function topLevelStringSpans(body) {
  const skipString = start => {
    let i = start + 1;
    while (i < body.length) {
      if (body[i] === '\\') {
        i += 2;
        continue;
      }
      if (body[i] === '"') return i + 1;
      i += 1;
    }
    return -1;
  };
  const spans = new Map();
  const counts = new Map();
  let depth = 0;
  for (let i = 0; i < body.length; ) {
    const ch = body[i];
    if (ch === '"') {
      const end = skipString(i);
      if (end < 0) return null;
      const after = /^\s*:\s*/.exec(body.slice(end));
      if (depth === 1 && after) {
        const key = JSON.parse(body.slice(i, end));
        counts.set(key, (counts.get(key) ?? 0) + 1);
        const valStart = end + after[0].length;
        if (body[valStart] === '"') {
          const valEnd = skipString(valStart);
          if (valEnd < 0) return null;
          spans.set(key, [valStart, valEnd]);
          i = valEnd;
          continue;
        }
        spans.delete(key);
      }
      i = end;
      continue;
    }
    if (ch === '{' || ch === '[') depth += 1;
    else if (ch === '}' || ch === ']') depth -= 1;
    i += 1;
  }
  return { spans, counts };
}

function setInterfaceStatusImpl(text, { status, prose_sha256: nextDigest } = {}) {
  if (typeof text !== 'string' || typeof status !== 'string') return null;
  if (nextDigest !== undefined && typeof nextDigest !== 'string') return null;
  const preflightSlice = runtimePreflightSlice();
  const blocks = preflightSlice.interfaceBlocks(text);
  if (blocks.length !== 1) return null;
  const [start, end] = blocks[0].indices[1];
  const body = blocks[0][1];
  const expectedDigest = preflightSlice.proseSha256(text);
  let value;
  try {
    value = JSON.parse(body);
  } catch {
    return null;
  }
  if (!isPlainObject(value)) return null;
  const parsedSpans = topLevelStringSpans(body);
  if (!parsedSpans) return null;
  const { spans, counts } = parsedSpans;
  if (counts.get('status') !== 1 || counts.get('prose_sha256') !== 1) return null;
  const statusSpan = spans.get('status');
  const digestSpan = spans.get('prose_sha256');
  if (!statusSpan || !digestSpan) return null;
  const edits = [[...statusSpan, JSON.stringify(status)]];
  if (nextDigest !== undefined) edits.push([...digestSpan, JSON.stringify(nextDigest)]);
  edits.sort((a, b) => b[0] - a[0]);
  const changed = edits.reduce(
    (acc, [from, to, replacement]) => acc.slice(0, from) + replacement + acc.slice(to),
    body,
  );
  const next = text.slice(0, start) + changed + text.slice(end);
  try {
    const expectedValue = {
      ...value,
      status,
      ...(nextDigest !== undefined ? { prose_sha256: nextDigest } : {}),
    };
    const nextBlocks = preflightSlice.interfaceBlocks(next);
    if (nextBlocks.length !== 1 || preflightSlice.proseSha256(next) !== expectedDigest) return null;
    return isDeepStrictEqual(JSON.parse(changed), expectedValue) &&
      isDeepStrictEqual(JSON.parse(nextBlocks[0][1]), expectedValue)
      ? next
      : null;
  } catch {
    return null;
  }
}

export const format = Object.freeze({
  parseScenario(text) {
    return runtimeScenarioJsonSlice().parseScenarioJson(text);
  },
  stringifyScenario(doc, space) {
    return runtimeScenarioJsonSlice().stringifyScenarioJson(doc, space);
  },
  exactValue(value) {
    return runtimeScenarioJsonSlice().exactValue(value);
  },
  isScenario(text) {
    if (typeof text !== 'string') return false;
    try {
      const doc = runtimeScenarioJsonSlice().parseScenarioJson(text);
      return isPlainObject(doc) && doc.schema_version === TEST_SCHEMA;
    } catch {
      return false;
    }
  },
  interfaceBlocks(text) {
    return runtimePreflightSlice().interfaceBlocks(String(text ?? '')).map(parseInterfaceBlockMatch);
  },
  proseSha256(text) {
    return runtimePreflightSlice().proseSha256(text);
  },
  interfaceProblems(json) {
    return runtimePreflightSlice().interfaceSchemaProblems(json);
  },
  setInterfaceStatus(text, fields) {
    return setInterfaceStatusImpl(text, fields);
  },
  storyCriteria(text) {
    return runtimePreflightSlice().storyCriteria(text);
  },
});

export const source = Object.freeze({
  identity({ root, tests, ...options } = {}, ports) {
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
  results(input = {}, ports) {
    return savedStoryEvidence(input, ports);
  },
});

export const workspace = Object.freeze({
  policy(input) {
    return runtimeWorkspaceSlice().loadRuntimeWorkspace(input);
  },
  allows(policy, path) {
    return runtimeWorkspaceSlice().allowsRuntimePath(policy, path);
  },
});

export function render(result, { as = 'table' } = {}, ports) {
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

export function version() {
  return {
    package: '@promptdriven/runtime-client',
    api_version: 1,
    formats: { scenario: TEST_SCHEMA, app_map: APP_MAP_SCHEMA },
    limits: { ...LIMITS },
    engine_sha: ENGINE_SHA,
  };
}
