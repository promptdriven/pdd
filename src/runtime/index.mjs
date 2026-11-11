// Generated from prompts/cli/runtime-entry.prompt.md (sha256: a7c7a697a7aedc4f5c565442fce5524808cb5a70f98dedfa2740df1c1998ee44).
import { createRequire } from 'node:module';
import { isDeepStrictEqual } from 'node:util';
import { exactValue, parseScenarioJson, stringifyScenarioJson } from './scenario-json.mjs';
import { allowsRuntimePath, loadRuntimeWorkspace } from './runtime-workspace.mjs';
import { LIMITS, TEST_SCHEMA, captureSource, interfaceBlocks, interfaceSchemaProblems, proseSha256, storyCriteria } from './runtime-preflight.mjs';
import { renderJson, renderText, storyLines, summaryLine } from './runtime-output.mjs';

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

let contractsModule = null;
function loadContracts() {
  return (contractsModule ??= createRequire(import.meta.url)('./contracts.mjs'));
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

// Adapt package request names; all execution and output remain with the owners.
function commandInput(input = {}) {
  const { root, tests, ...rest } = input;
  return {
    ...rest,
    ...(rest.cwd === undefined && root !== undefined ? { cwd: root } : {}),
    ...(rest.words === undefined && tests !== undefined ? { words: tests.map(test => typeof test === 'string' ? test : test.path) } : {}),
  };
}

function checkMode(input, flag, value = true) {
  return { ...commandInput(input), options: { ...input?.options, [flag]: value } };
}

export function check(input, ports) {
  return runCheck(commandInput(input), ports);
}

export function lint(input, ports) {
  return runCheck(checkMode(input, '--lint'), ports);
}

export function read(input = {}, ports) {
  const request = checkMode(input, '--read');
  const id = input.call_id ?? input.batch;
  if (id !== undefined) request.words = [id];
  return runCheck(request, ports);
}

export function retry(input = {}, ports) {
  return runCheck(input.batch === undefined ? commandInput(input) : checkMode(input, '--retry', input.batch), ports);
}

export function simulate(input = {}, ports) {
  const request = commandInput(input);
  if (input.test !== undefined) request.words = [input.test];
  if (input.mode !== undefined && input.mode !== 'open') {
    if (!['cli', 'serve', 'save-last', 'stop'].includes(input.mode)) throw new TypeError(`Unknown simulation mode: ${input.mode}`);
    request.options = { ...request.options, [`--${input.mode}`]: true };
  }
  return runTry(request, ports);
}

export const jobs = runJobs;
export const health = checkRuntimeHealth;

export function mcp(input = {}, ports) {
  const request = commandInput(input);
  if (input.story !== undefined) request.words = [input.story];
  return runMcp(request, ports);
}

export function local(input = {}, ports) {
  if (input.what === undefined) {
    const options = input.options ?? {};
    if (!['--files', '--fill-hash', '--explain-bindings'].some(flag => options[flag] === true)
      && !(options['--lint'] === true && options['--local'] === true)) throw new TypeError('A local operation is required');
    return runCheck(commandInput(input), ports);
  }
  if (!['files', 'fill-hash', 'explain-bindings'].includes(input.what)) throw new TypeError(`Unknown local operation: ${input.what}`);
  return runCheck(checkMode(input, `--${input.what}`), ports);
}

export function draftInterfaces(input = {}, ports) {
  const request = commandInput(input);
  if (request.words === undefined && input.paths !== undefined) request.words = input.paths;
  return runInterfaceDraft(request, ports);
}

export function contracts(input = {}, ports) {
  const request = commandInput(input);
  if (input.sync !== undefined) request.words = input.sync ? ['sync'] : [];
  if (input.write === true) request.options = { ...request.options, '--write': true };
  return runContracts(request, ports);
}

function setInterfaceStatus(text, { status, prose_sha256 } = {}) {
  if (!['draft', 'approved'].includes(status) || typeof prose_sha256 !== 'string') return null;
  const blocks = interfaceBlocks(text);
  if (blocks.length !== 1) return null;
  const block = blocks[0], body = block[1];
  let value;
  try { value = parseScenarioJson(body); } catch { return null; }
  if (!value || typeof value !== 'object' || Array.isArray(value)) return null;
  const tokens = [...body.matchAll(/"(?:[^"\\]|\\[\s\S])*"|[{}\[\],:]/g)];
  const edits = [], counts = { status: 0, prose_sha256: 0 };
  let depth = 0, keyExpected = false;
  for (let index = 0; index < tokens.length; index++) {
    const token = tokens[index], spelling = token[0];
    if (spelling === '{' || spelling === '[') { depth++; if (depth === 1) keyExpected = true; }
    else if (spelling === '}' || spelling === ']') depth--;
    else if (depth === 1 && spelling === ',') keyExpected = true;
    else if (depth === 1 && keyExpected && spelling.startsWith('"')) {
      const key = JSON.parse(spelling);
      if (Object.hasOwn(counts, key)) {
        counts[key]++;
        const target = tokens[index + 2];
        if (tokens[index + 1]?.[0] !== ':' || !target?.[0].startsWith('"')) return null;
        edits.push([target.index, target.index + target[0].length, JSON.stringify(key === 'status' ? status : prose_sha256)]);
      }
      keyExpected = false;
    }
  }
  if (counts.status !== 1 || counts.prose_sha256 !== 1) return null;
  const changed = edits.sort((a, b) => b[0] - a[0]).reduce((text, [start, end, put]) => text.slice(0, start) + put + text.slice(end), body);
  if (!isDeepStrictEqual(parseScenarioJson(changed), { ...value, status, prose_sha256 })) return null;
  return text.slice(0, block.indices[1][0]) + changed + text.slice(block.indices[1][1]);
}

export const format = {
  parseScenario: parseScenarioJson,
  stringifyScenario: stringifyScenarioJson,
  exactValue,
  isScenario: text => parseScenarioJson(text)?.schema_version === TEST_SCHEMA,
  interfaceBlocks,
  proseSha256,
  interfaceProblems: interfaceSchemaProblems,
  setInterfaceStatus,
  storyCriteria,
};

export const source = {
  identity({ root, ...selection }) { return captureSource(root, selection); },
};

export const saved = {
  async results(input, ports) {
    const { savedStoryEvidence } = await import('./runtime-client.mjs');
    return savedStoryEvidence(input, ports);
  },
};

export const workspace = { policy: loadRuntimeWorkspace, allows: allowsRuntimePath };

export function render(result, { as = 'table' } = {}) {
  switch (as) {
    case 'table': return renderText(result);
    case 'json': return renderJson(result);
    case 'story-lines': return storyLines(result.rows);
    case 'summary': return summaryLine(result.rows);
    default: throw new TypeError(`Unknown render format: ${as}`);
  }
}

export function version() {
  return { package: null, api_version: null, formats: { scenario: TEST_SCHEMA }, limits: LIMITS, engine_sha: null };
}
