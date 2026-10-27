// Generated from prompts/cli/runtime-preflight.prompt.md (sha256: 1781d11a7ba37fc08a6207caccdfe1734ed5bbaa1f45bbb878aeb3c5335d2304).
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { lstatSync, readFileSync, writeFileSync } from 'node:fs';
import { basename, join } from 'node:path';
import { isDeepStrictEqual } from 'node:util';

export const TEST_SCHEMA = 'prompt-runtime.program-scenario.v1';
export const LIMITS = Object.freeze({ bytes: 10_485_760, files: 10_000, test: 1_048_576 });
const TOP_KEYS = new Set(['schema_version', 'story_path', 'criteria', 'initial_world', 'steps', 'entry_paths', 'simulation',
  'check_exemptions', 'context', 'context_byte_budget', 'criteria_scope', 'prompt_mappings']);
const REQUIRED_KEYS = ['schema_version', 'criteria', 'initial_world', 'steps'];
const STEP_KEYS = new Set(['step_id', 'entry_path', 'operation', 'input', 'checks', 'expected_error', 'simulation_overrides', 'model']);
const RULE_OPS = new Set(['at_most', 'at_least', 'not_contains', 'all_in', 'equals_ignore_case']);
const EXACT_OPS = new Set(['equals', 'not_equals', 'one_of', 'count', ...RULE_OPS]);
const SCHEMA_RULES = new Set(['type', 'properties', 'required', 'additionalProperties', 'items', 'enum', 'const',
  'minimum', 'maximum', 'minLength', 'maxLength', 'minItems', 'maxItems']);
const SCHEMA_NOTES = new Set(['title', 'description', 'default', 'examples', 'format', '$comment', '$schema', '$id']);

// The engine's _INTERFACE regex (prompt_program_discovery.py, 7b03d3ea).
const INTERFACE = /<details\b[^>]*>\s*<summary\b[^>]*>\s*(?:<strong\b[^>]*>\s*)?Runtime\s+interface(?:\s*:\s*[^<]+?)?\s*(?:<\/strong\s*>\s*)?(?:\s*:\s*[^<]+?)?\s*<\/summary\s*>\s*```json\b\s*([\s\S]*?)\s*```\s*<\/details\s*>/gid;

export class PreflightError extends Error {
  constructor(exitCode, message) { super(message); this.name = 'PreflightError'; this.exitCode = exitCode; }
}

export const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
export const interfaceBlocks = text => [...text.matchAll(INTERFACE)];
export const proseSha256 = text => sha256(Buffer.from(text.replace(INTERFACE, ''), 'utf8'));

// Python str.isspace, str.splitlines and str.split, so story criteria equal the engine's.
const PY_SPACE = '[\\t\\n\\v\\f\\r\\x1c-\\x1f \\x85\\xa0\\u1680\\u2000-\\u200a\\u2028\\u2029\\u202f\\u205f\\u3000]';
const pyStrip = text => text.replace(new RegExp(`^${PY_SPACE}+|${PY_SPACE}+$`, 'g'), '');
const pyWords = text => text.split(new RegExp(`${PY_SPACE}+`)).filter(Boolean).join(' ');
function pySplitLines(text) {
  const lines = text.split(/\r\n|[\n\r\v\f\x1c\x1d\x1e\x85\u2028\u2029]/);
  if (lines.at(-1) === '') lines.pop();
  return lines;
}
const AC_HEADING = /(?<![^\n])##[ \t]+Acceptance(?:[ \t]+Criteria)?[ \t]*(?![^\n])/i;
const NEXT_HEADING = /(?<![^\n])##[ \t]+/;
const NUMBERED_ITEM = /^([1-9][0-9]*)[.)][ \t]+(.+)$/;
const BULLET_ITEM = /(?<![^\n])[ \t]*[-*][ \t]+([\s\S]+?)(?=\n[ \t]*[-*][ \t]+|(?![\s\S]))/g;

// A port of the engine's explicit_story_criteria (program_scenario.py, 7b03d3ea).
export function storyCriteria(source) {
  const heading = AC_HEADING.exec(source);
  const body = heading ? source.slice(heading.index + heading[0].length) : source;
  const result = [];
  let current = null, expected = 1;
  for (const line of pySplitLines(body)) {
    const match = NUMBERED_ITEM.exec(line);
    if (match) {
      if (Number(match[1]) !== expected) {
        if (result.length || current !== null) break;
        continue;
      }
      if (current !== null) result.push(current.join(' '));
      current = [pyStrip(match[2])];
      expected += 1;
    } else if (current !== null) {
      if (!pyStrip(line) || line.startsWith('#')) { result.push(current.join(' ')); current = null; }
      else current.push(pyStrip(line));
    }
  }
  if (current !== null) result.push(current.join(' '));
  if (!result.length && heading) {
    const next = NEXT_HEADING.exec(body);
    const section = next ? body.slice(0, next.index) : body;
    return [...section.matchAll(BULLET_ITEM)].map(match => pyWords(match[1]));
  }
  return result;
}

export function gitFiles(root) {
  const listed = spawnSync('git', ['ls-files', '-z', '-co', '--exclude-standard'], { cwd: root, maxBuffer: 512 * 1024 * 1024 });
  if (listed.status !== 0) throw new PreflightError(5, 'pdd could not list the Git files of this repository.');
  return [...new Set(listed.stdout.toString('utf8').split('\0').filter(Boolean))].sort();
}

const statOf = path => { try { return lstatSync(path, { bigint: true }); } catch (error) { if (error.code === 'ENOENT') return null; throw error; } };
const readText = (root, path) => readFileSync(join(root, path), 'utf8');
const storyName = path => basename(path).replace(/\.md$/, '');
const titleOf = text => text.split('\n').find(line => line.startsWith('# '))?.slice(2).trim() || null;

// Tests, stories and Git-visible regular files of one repo.
export function findTests({ root, files = gitFiles(root) }) {
  const visible = new Set(), tests = [], stories = [];
  for (const path of files) {
    const stat = statOf(join(root, path));
    if (!stat?.isFile()) continue;
    visible.add(path);
    if (path.endsWith('.json') && stat.size <= LIMITS.test) {
      const text = readText(root, path);
      if (!text.includes('prompt-runtime.program-scenario')) continue;
      let doc;
      try { doc = JSON.parse(text); } catch (error) { tests.push({ path, error: error.message }); continue; }
      if (typeof doc?.schema_version === 'string' && doc.schema_version.startsWith('prompt-runtime.program-scenario')) tests.push({ path, doc });
    } else if (path.endsWith('.md') && path.split('/').slice(0, -1).includes('user_stories')) {
      stories.push({ path, name: storyName(path), title: titleOf(readText(root, path)) });
    }
  }
  for (const test of tests) {
    const storyPath = typeof test.doc?.story_path === 'string' ? test.doc.story_path : null;
    const story = stories.find(item => item.path === storyPath);
    test.storyPath = storyPath;
    test.story = storyPath ? storyName(storyPath) : storyName(test.path.replace(/\.json$/, ''));
    test.title = story?.title ?? (storyPath && visible.has(storyPath) ? titleOf(readText(root, storyPath)) : null) ?? test.story;
  }
  const named = new Set(tests.map(test => test.storyPath));
  const warnings = stories.filter(story => !named.has(story.path)).map(story => `Warning: ${story.path} has no test.`);
  return { visible, tests, stories, warnings };
}

// STORY words: a test path, a story path, a story name or a test file name. Returns {selected, unknown}.
export function selectTests(found, words = []) {
  if (!words.length) return { selected: [...found.tests], unknown: [] };
  const selected = new Set(), unknown = [];
  for (const raw of words) {
    const word = raw.replace(/^\.\//, '');
    const hits = found.tests.filter(test => test.path === word || test.storyPath === word || test.story === word || basename(test.path, '.json') === word);
    if (!hits.length) unknown.push(raw);
    for (const hit of hits) selected.add(hit);
  }
  return { selected: found.tests.filter(test => selected.has(test)), unknown };
}

const refusal = (code, section, message, extra = {}) => ({ code, section, message, ...extra });
const isObject = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const show = value => { const text = JSON.stringify(value) ?? String(value); return text.length > 60 ? `${text.slice(0, 57)}...` : text; };
const plural = (count, word) => `${count} ${word}${count === 1 ? '' : 's'}`;
function range(min, max, unit = '') {
  const tail = unit ? ` ${unit}${(max ?? min) === 1 ? '' : 's'}` : '';
  if (min !== undefined && max !== undefined) return `${min} to ${max}${tail}`;
  return min !== undefined ? `at least ${min}${tail}` : `at most ${max}${tail}`;
}
const typeName = value => value === null ? 'null' : Array.isArray(value) ? 'array'
  : typeof value === 'number' ? (Number.isInteger(value) ? 'integer' : 'number') : typeof value;
const typeMatches = (value, type) => type === 'number' ? typeof value === 'number' : type === 'integer' ? Number.isInteger(value) : typeName(value) === type;
const article = type => /^[aeiou]/.test(type) ? `an ${type}` : `a ${type}`;

function unknownKeyword(schema) {
  if (!isObject(schema)) return null;
  for (const [key, value] of Object.entries(schema)) {
    if (!SCHEMA_RULES.has(key) && !SCHEMA_NOTES.has(key)) return key;
    if (key === 'properties' && isObject(value)) for (const child of Object.values(value)) { const found = unknownKeyword(child); if (found) return found; }
    if (key === 'items' || key === 'additionalProperties') { const found = unknownKeyword(value); if (found) return found; }
  }
  return null;
}

// The small JSON Schema check of rule P9. Returns null or {pointer, tokens, rule}.
function schemaProblem(value, schema, tokens = []) {
  const at = rule => ({ tokens, rule });
  if (!isObject(schema)) return null;
  if (schema.type !== undefined) {
    const types = Array.isArray(schema.type) ? schema.type : [schema.type];
    if (!types.some(type => typeMatches(value, type))) return at(`is ${show(value)}. The prompt wants ${types.map(article).join(' or ')}.`);
  }
  if (Object.hasOwn(schema, 'const') && !isDeepStrictEqual(value, schema.const)) return at(`is ${show(value)}. The prompt wants ${show(schema.const)}.`);
  if (Array.isArray(schema.enum) && !schema.enum.some(choice => isDeepStrictEqual(choice, value))) {
    const choices = schema.enum.map(show);
    return at(`is ${show(value)}. The prompt allows ${choices.length > 1 ? `${choices.slice(0, -1).join(', ')} or ${choices.at(-1)}` : choices[0]}.`);
  }
  if (typeof value === 'number' && ((schema.minimum !== undefined && value < schema.minimum) || (schema.maximum !== undefined && value > schema.maximum))) {
    return at(`is ${show(value)}. The prompt allows ${range(schema.minimum, schema.maximum)}.`);
  }
  if (typeof value === 'string') {
    const length = [...value].length;
    if ((schema.minLength !== undefined && length < schema.minLength) || (schema.maxLength !== undefined && length > schema.maxLength)) {
      return at(`has ${plural(length, 'character')}. The prompt allows ${range(schema.minLength, schema.maxLength, 'character')}.`);
    }
  }
  if (Array.isArray(value)) {
    if ((schema.minItems !== undefined && value.length < schema.minItems) || (schema.maxItems !== undefined && value.length > schema.maxItems)) {
      return at(`has ${plural(value.length, 'item')}. The prompt allows ${range(schema.minItems, schema.maxItems, 'item')}.`);
    }
    if (isObject(schema.items)) for (const [index, item] of value.entries()) {
      const problem = schemaProblem(item, schema.items, [...tokens, String(index)]);
      if (problem) return problem;
    }
  }
  if (isObject(value)) {
    for (const key of Array.isArray(schema.required) ? schema.required : []) if (!Object.hasOwn(value, key)) return at(`has no ${show(key)}. The prompt requires it.`);
    const properties = isObject(schema.properties) ? schema.properties : {};
    for (const [key, child] of Object.entries(value)) {
      if (Object.hasOwn(properties, key)) { const problem = schemaProblem(child, properties[key], [...tokens, key]); if (problem) return problem; }
      else if (schema.additionalProperties === false) return at(`has ${show(key)}. The prompt does not allow it.`);
      else if (isObject(schema.additionalProperties)) { const problem = schemaProblem(child, schema.additionalProperties, [...tokens, key]); if (problem) return problem; }
    }
  }
  return null;
}

const hasReference = value => Array.isArray(value) ? value.some(hasReference)
  : isObject(value) && (Object.hasOwn(value, '$step_result') || Object.values(value).some(hasReference));
const pointerOf = tokens => tokens.map(token => `/${token.replace(/~/g, '~0').replace(/\//g, '~1')}`).join('');
const sectionOf = (base, tokens) => tokens.reduce((text, token) => /^\d+$/.test(token) ? `${text}[${token}]` : `${text}.${token}`, base);

// P9 on one step input. Returns {skip: keyword} | {code, section, message} | null.
export function checkInput(input, schema, index) {
  if (hasReference(input)) return null;
  const keyword = unknownKeyword(schema);
  if (keyword) return { skip: keyword };
  const problem = schemaProblem(input, schema);
  if (!problem) return null;
  const pointer = pointerOf(problem.tokens);
  return refusal('invalid-input', sectionOf(`steps[${index}].input`, problem.tokens),
    `steps[${index}] input${pointer ? ` ${pointer}` : ''} ${problem.rule}`, { step: index + 1 });
}

// The prompt file of an entry: {path, text, blocks, interface, error}.
export function readPrompt(root, visible, path) {
  if (typeof path !== 'string' || !path.endsWith('.prompt.md') || !visible.has(path)) return { path, error: 'entry-missing' };
  const text = readText(root, path), blocks = interfaceBlocks(text);
  if (!blocks.length) return { path, text, blocks, error: 'interface-missing' };
  if (blocks.length > 1) return { path, text, blocks, error: 'pdd-two-interfaces' };
  let value;
  try { value = JSON.parse(blocks[0][1]); } catch (error) { return { path, text, blocks, error: 'invalid-json', detail: error.message }; }
  if (!isObject(value)) return { path, text, blocks, error: 'invalid-json', detail: 'The interface is not a JSON object.' };
  return { path, text, blocks, interface: value, prose: proseSha256(text) };
}

// Drafts may run (Serhan, Oct 27); until the server takes them, its refusal gets this plain text.
export const DRAFT_SERVER_TEXT = 'The server does not run draft prompts yet. Approve the prompt first, or wait for the server update.';
const draftStaleHint = path => `pdd: ${path} is a draft whose text changed after its hash was filled. Run pdd check --fill-hash.`;
export const STALE_HINT = 'the text changed after approval: set status to draft, run pdd check --fill-hash, ask the person';
export const staleHint = `pdd: ${STALE_HINT}.`;
const PROMPT_MESSAGES = {
  'entry-missing': path => `${path} is not a Git-visible *.prompt.md file.`,
  'interface-missing': path => `${path} has no Runtime interface block.`,
  'pdd-two-interfaces': path => `${path} has more than one Runtime interface block. Keep one.`,
  'invalid-json': path => `The Runtime interface of ${path} is not valid JSON.`,
};

// Rule P7 for one prompt. Returns null or a refusal (without the step).
export function promptRefusal(prompt, section) {
  if (prompt.error) return refusal(prompt.error, section, PROMPT_MESSAGES[prompt.error](prompt.path));
  const status = prompt.interface.status;
  if (status !== 'approved' && status !== 'draft') {
    return refusal('interface-unapproved', section, `${prompt.path} has status ${show(status)}. Use "draft" or "approved".`);
  }
  if (prompt.interface.prose_sha256 !== prompt.prose) {
    return status === 'draft' ? refusal('interface-stale', section, `${prompt.path} has a prose_sha256 that is not current.`, { hint: draftStaleHint(prompt.path) })
      : refusal('interface-stale', section, `${prompt.path} changed after its interface was approved.`, { hint: staleHint });
  }
  return null;
}

function numbersIn(text) {
  const numbers = [];
  for (const match of text.matchAll(/\d+(?:,\d{3})*(?:\.\d+)?/g)) {
    const before = text.slice(0, match.index);
    const negative = before.endsWith('-') && !/[\w.]-$/.test(before);
    numbers.push({ text: `${negative ? '-' : ''}${match[0]}`, value: Number(match[0].replace(/,/g, '')) * (negative ? -1 : 1) });
  }
  return numbers;
}

// Issue 19: a number in a check that is not in its criterion's text.
export function numberWarnings(doc) {
  const texts = new Map((Array.isArray(doc?.criteria) ? doc.criteria : []).filter(isObject).map(item => [item.id, item.text]));
  const warnings = new Set();
  for (const step of Array.isArray(doc?.steps) ? doc.steps : []) for (const check of Array.isArray(step?.checks) ? step.checks : []) {
    if (!isObject(check) || typeof texts.get(check.criterion_id) !== 'string') continue;
    const values = check.op === 'one_of' && Array.isArray(check.value) ? check.value : ['equals', 'count'].includes(check.op) ? [check.value] : [];
    const found = numbersIn(texts.get(check.criterion_id));
    for (const value of values) {
      if (typeof value !== 'number' || !found.length || found.some(item => item.value === value)) continue;
      const closest = found.reduce((best, item) => Math.abs(item.value - value) < Math.abs(best.value - value) ? item : best);
      warnings.add(`Warning: the ${check.criterion_id} check expects ${value}, but the ${check.criterion_id} text says ${closest.text}.`);
    }
  }
  return [...warnings];
}

const stepCount = doc => Array.isArray(doc?.steps) ? doc.steps.length : 0;
// Steps with saved data or prompt calls cost 2 to 3 AI calls each (real-projects report): 4 per step, 6 to 100.
export const defaultMaxCalls = doc => Math.min(100, Math.max(6, stepCount(doc) * 4));

function firstDifference(testTexts, storyTexts) {
  const left = [...storyTexts];
  for (const text of testTexts) {
    const index = left.indexOf(text);
    if (index < 0) return `The test has this criterion, but the story does not: "${text}"`;
    left.splice(index, 1);
  }
  return `The story has this criterion, but the test does not: "${left[0]}"`;
}

function checkTest(root, found, test, prompts) {
  const doc = test.doc;
  if (test.error) return refusal('invalid-document', 'scenario', `${test.path} is not valid JSON: ${test.error}`);
  if (!isObject(doc)) return refusal('invalid-document', 'scenario', `${test.path} is not a JSON object.`);
  const missing = REQUIRED_KEYS.filter(key => !Object.hasOwn(doc, key)), extra = Object.keys(doc).filter(key => !TOP_KEYS.has(key));
  if (missing.length) return refusal('invalid-document', 'scenario', `The test has no ${missing.map(key => `"${key}"`).join(', ')}.`);
  if (extra.length) return refusal('invalid-document', 'scenario', `The test has keys the runtime does not know: ${extra.map(key => `"${key}"`).join(', ')}.`);
  if (doc.schema_version !== TEST_SCHEMA) return refusal('invalid-document', 'schema_version', `schema_version must be "${TEST_SCHEMA}".`);
  if (typeof doc.story_path !== 'string' || !doc.story_path) return refusal('pdd-no-story', 'story_path', 'The test has no story_path. Name its story, for example "user_stories/<story>.md".');
  if (!found.visible.has(doc.story_path)) return refusal('story-missing', 'story_path', `${doc.story_path} is not a Git-visible file.`);
  if (Object.hasOwn(doc, 'criteria_scope') || (Object.hasOwn(doc, 'check_exemptions') && !(Array.isArray(doc.check_exemptions) && !doc.check_exemptions.length))) {
    return refusal('pdd-partial-test', Object.hasOwn(doc, 'criteria_scope') ? 'criteria_scope' : 'check_exemptions', 'In the beta a test checks the whole story. Remove criteria_scope and check_exemptions.');
  }
  if (!Array.isArray(doc.criteria) || !doc.criteria.length) return refusal('invalid-criterion', 'criteria', 'The test has no criteria.');
  const ids = new Set();
  for (const [index, item] of doc.criteria.entries()) {
    if (!isObject(item) || !isDeepStrictEqual(Object.keys(item).sort(), ['id', 'text']) || typeof item.id !== 'string' || !item.id || typeof item.text !== 'string' || !item.text) {
      return refusal('invalid-criterion', `criteria[${index}]`, 'Each criterion has only a nonempty "id" and "text".');
    }
    if (ids.has(item.id)) return refusal('duplicate-criterion', `criteria[${index}]`, `The criterion ID ${item.id} is used twice.`);
    ids.add(item.id);
  }
  const story = storyCriteria(readText(root, doc.story_path));
  if (!story.length) return refusal('story-criteria-missing', 'story_path', `${doc.story_path} has no numbered "## Acceptance criteria" list.`);
  const testTexts = doc.criteria.map(item => item.text).sort(), storyTexts = [...story].sort();
  if (!isDeepStrictEqual(testTexts, storyTexts)) return refusal('story-criterion-mismatch', 'criteria', firstDifference(testTexts, storyTexts));
  if (!Array.isArray(doc.steps) || !doc.steps.length) return refusal('missing-steps', 'steps', 'The test has no steps.');
  const checked = new Set(), exact = new Set();
  for (const [index, step] of doc.steps.entries()) {
    const section = `steps[${index}]`, at = { step: index + 1 };
    if (!isObject(step) || Object.keys(step).some(key => !STEP_KEYS.has(key)) || ['step_id', 'entry_path', 'operation', 'input', 'checks'].some(key => !Object.hasOwn(step, key))
      || ['step_id', 'entry_path', 'operation'].some(key => typeof step[key] !== 'string' || !step[key])) {
      return refusal('invalid-step', section, 'A step has step_id, entry_path, operation, input and checks.', at);
    }
    if (Object.hasOwn(step, 'model') && (typeof step.model !== 'string' || !step.model.trim())) {
      return refusal('invalid-step-model', `${section}.model`, 'A step model must be a model name (a string).', at);
    }
    if (!prompts.has(step.entry_path)) prompts.set(step.entry_path, readPrompt(root, found.visible, step.entry_path));
    const prompt = prompts.get(step.entry_path), broken = promptRefusal(prompt, section);
    if (broken) return { ...broken, ...at };
    const entry = (Array.isArray(prompt.interface.entries) ? prompt.interface.entries : []).find(item => item?.operation === step.operation);
    if (!entry) return refusal('entry-operation-missing', section, `${step.entry_path} has no operation "${step.operation}".`, at);
    const errorStep = Object.hasOwn(step, 'expected_error');
    if (errorStep && !(Array.isArray(entry.errors) && entry.errors.includes(step.expected_error))) {
      return refusal('pdd-unknown-error', `${section}.expected_error`, `"${step.expected_error}" is not in the errors of ${step.operation} in ${step.entry_path}.`, at);
    }
    if (!Array.isArray(step.checks)) return refusal('invalid-check', `${section}.checks`, 'checks must be a list.', at);
    let errorChecks = 0;
    for (const [checkIndex, check] of step.checks.entries()) {
      if (!isObject(check) || ['criterion_id', 'target', 'path', 'op'].some(key => !Object.hasOwn(check, key))) {
        return refusal('invalid-check', `${section}.checks[${checkIndex}]`, 'A check has criterion_id, target, path and op.', at);
      }
      if (!ids.has(check.criterion_id)) return refusal('unknown-criterion', `${section}.checks[${checkIndex}]`, `The check names ${show(check.criterion_id)}, which is not a criterion ID.`, at);
      checked.add(check.criterion_id);
      if (EXACT_OPS.has(check.op) || (Object.hasOwn(check, 'html') && check.op === 'exists')) exact.add(check.criterion_id);
      if (check.target === 'error' && check.path === '/code' && check.op === 'equals' && check.value === step.expected_error) errorChecks += 1;
    }
    if (errorStep && errorChecks === 0) {
      return refusal('missing-error-check', `${section}.checks`, `An error step needs one check: target "error", path "/code", op "equals", value "${step.expected_error}".`, at);
    }
    const input = checkInput(step.input, entry.input_schema, index);
    if (input?.code) return input;
  }
  const unchecked = [...ids].filter(id => !checked.has(id));
  if (unchecked.length) return refusal('unchecked-criteria', 'criteria', `These criteria have no check: ${unchecked.join(', ')}.`);
  const loose = [...ids].filter(id => !exact.has(id));
  if (loose.length) return refusal('criterion-needs-exact-check', 'criteria', `These criteria need an exact check (equals, not_equals, one_of or count): ${loose.join(', ')}.`);
  return null;
}

// Rules P1-P10 for the selected tests. Returns rows and warnings; never throws for a test problem.
export function preflight({ root, found, selected }) {
  const prompts = new Map(), warnings = [];
  const rows = selected.map(test => {
    const refused = checkTest(root, found, test, prompts);
    const row = { test: test.path, story: test.story, title: test.title, refusals: refused ? [refused] : [], warnings: numberWarnings(test.doc),
      max_calls: defaultMaxCalls(test.doc), steps: Array.isArray(test.doc?.steps) ? test.doc.steps : [],
      criteria_total: Array.isArray(test.doc?.criteria) ? test.doc.criteria.length : 0, draft: false };
    row.draft = row.steps.some(step => prompts.get(step?.entry_path)?.interface?.status === 'draft');
    if (!refused) for (const [index, step] of row.steps.entries()) {
      const prompt = prompts.get(step.entry_path), entry = prompt?.interface?.entries?.find?.(item => item?.operation === step.operation);
      const input = entry ? checkInput(step.input, entry.input_schema, index) : null;
      if (input?.skip) warnings.push(`Warning: ${test.path} steps[${index}] input was not checked here: the prompt schema uses "${input.skip}". The runtime still checks it.`);
    }
    return row;
  });
  return { rows, warnings };
}

// --fill-hash: fill draft hashes; report approved interfaces whose text changed.
export function fillHashes({ root, files = gitFiles(root) }) {
  const result = { filled: [], current: [], refused: [], stale: [] };
  for (const path of files) {
    if (!path.endsWith('.prompt.md') || !statOf(join(root, path))?.isFile()) continue;
    const text = readText(root, path), blocks = interfaceBlocks(text);
    if (!blocks.length) continue;
    if (blocks.length > 1) { result.refused.push({ path, message: `${path} has more than one Runtime interface block. Keep one.` }); continue; }
    const [start, end] = blocks[0].indices[1], body = blocks[0][1];
    let value;
    try { value = JSON.parse(body); } catch { result.refused.push({ path, message: `The Runtime interface of ${path} is not valid JSON.` }); continue; }
    if (!isObject(value)) { result.refused.push({ path, message: `The Runtime interface of ${path} is not a JSON object.` }); continue; }
    const hash = proseSha256(text);
    if (value.status === 'approved') { (value.prose_sha256 === hash ? result.current : result.stale).push({ path }); continue; }
    if (value.status !== 'draft') { result.refused.push({ path, message: `${path} has status ${show(value.status)}. Use "draft" until the person approves it.` }); continue; }
    if (!Object.hasOwn(value, 'prose_sha256')) { result.refused.push({ path, message: `${path} has no "prose_sha256" key. Add "prose_sha256": "" to its Runtime interface.` }); continue; }
    if (value.prose_sha256 === hash) { result.current.push({ path }); continue; }
    const key = /("prose_sha256"\s*:\s*)"(?:[^"\\]|\\.)*"/g;
    const changed = [...body.matchAll(key)].length === 1 ? body.replace(key, `$1"${hash}"`) : null;
    let same = false;
    try { same = changed !== null && isDeepStrictEqual(JSON.parse(changed), { ...value, prose_sha256: hash }); } catch { same = false; }
    if (!same) { result.refused.push({ path, message: `pdd could not fill "prose_sha256" in ${path}. Make it one string value, for example "prose_sha256": "".` }); continue; }
    const next = text.slice(0, start) + changed + text.slice(end);
    if (proseSha256(next) !== hash) { result.refused.push({ path, message: `pdd could not fill "prose_sha256" in ${path} without a change to its text.` }); continue; }
    writeFileSync(join(root, path), next);
    result.filled.push({ path });
  }
  return result;
}

const SECRET_NAME = /^(?:\.env.*|auth\.json|credentials\.json|id_rsa|id_ed25519|id_ecdsa|id_dsa|\.npmrc|\.netrc|\.git-credentials|\.pypirc|.+\.(?:pem|key|p12|pfx|keystore|tfstate|tfvars))$/;
const SECRET_PART = new Set(['secrets', '.ssh', '.codex', '.terraform', '.aws']);
export const isSecretPath = path => SECRET_NAME.test(basename(path)) || path.split('/').some(part => SECRET_PART.has(part))
  || /(?:^|\/)\.docker\/config\.json$/.test(path);

function octal(header, offset, length, value) { header.write(`${value.toString(8).padStart(length - 1, '0')}\0`, offset, length, 'latin1'); }
function tarHeader(name, size, type) {
  const header = Buffer.alloc(512);
  header.write(name, 0, 100, 'utf8');
  octal(header, 100, 8, 0o600); octal(header, 108, 8, 0); octal(header, 116, 8, 0);
  octal(header, 124, 12, size); octal(header, 136, 12, 0);
  header.fill(0x20, 148, 156);
  header.write(type, 156, 1, 'latin1');
  header.write('ustar\0', 257, 6, 'latin1'); header.write('00', 263, 2, 'latin1');
  octal(header, 329, 8, 0); octal(header, 337, 8, 0);
  let sum = 0;
  for (const byte of header) sum += byte;
  header.write(`${sum.toString(8).padStart(6, '0')}\0 `, 148, 8, 'latin1');
  return header;
}
const pad = size => Buffer.alloc((512 - (size % 512)) % 512);
function paxRecord(key, value) {
  const body = ` ${key}=${value}\n`;
  let length = Buffer.byteLength(body) + 1;
  while (Buffer.byteLength(`${length}${body}`) !== length) length += 1;
  return Buffer.from(`${length}${body}`, 'utf8');
}

// A deterministic ustar archive: Git names, mode 0600, mtime 0, PAX path for long or non-ASCII names.
export function tarFiles(entries) {
  const parts = [];
  for (const { path, bytes } of entries) {
    let name = path;
    if (Buffer.byteLength(path) > 100 || /[^\x20-\x7e]/.test(path)) {
      const record = paxRecord('path', path);
      parts.push(tarHeader('PaxHeader', record.length, 'x'), record, pad(record.length));
      name = path.replace(/[^\x20-\x7e]/g, '_').slice(-100);
    }
    parts.push(tarHeader(name, bytes.length, '0'), bytes, pad(bytes.length));
  }
  parts.push(Buffer.alloc(1024));
  return Buffer.concat(parts);
}

export const formatSize = bytes => bytes < 1024 ? `${bytes} bytes` : bytes < 1024 * 1024 ? `${Math.round(bytes / 1024)} KB` : `${(bytes / 1048576).toFixed(1)} MB`;

function captureOnce(root) {
  const names = gitFiles(root), files = [], problems = [];
  for (const path of names) {
    const stat = statOf(join(root, path));
    if (!stat) continue;
    if (isSecretPath(path)) problems.push(`${path}: the name looks like a secret. pdd never sends it. Remove it from Git or add it to .gitignore.`);
    else if (stat.isSymbolicLink()) problems.push(`${path}: a symbolic link. pdd sends only regular files.`);
    else if (stat.isDirectory()) problems.push(`${path}: a submodule or folder. pdd sends only regular files.`);
    else if (!stat.isFile()) problems.push(`${path}: not a regular file. pdd sends only regular files.`);
    else files.push({ path, stat, size: Number(stat.size) });
  }
  if (problems.length) throw new PreflightError(4, ['pdd refused to send these files:', ...problems.slice(0, 20).map(text => `  ${text}`),
    ...(problems.length > 20 ? [`  and ${problems.length - 20} more.`] : [])].join('\n'));
  const total = files.reduce((sum, file) => sum + file.size, 0);
  if (files.length > LIMITS.files || total > LIMITS.bytes) {
    const largest = [...files].sort((a, b) => b.size - a.size).slice(0, 5).map(file => `  ${file.path}  ${formatSize(file.size)}`);
    throw new PreflightError(4, [`The repository is too big to send: ${files.length} files, ${formatSize(total)}. The limit is ${LIMITS.files} files and 10 MB.`,
      'The largest files:', ...largest].join('\n'));
  }
  let entries;
  try { entries = files.map(file => ({ path: file.path, bytes: readFileSync(join(root, file.path)) })); }
  catch (error) { if (error.code === 'ENOENT') return null; throw error; }
  const tar = tarFiles(entries);
  if (tar.length > LIMITS.bytes) throw new PreflightError(4, `The source archive is ${formatSize(tar.length)}. The limit is 10 MB.`);
  const same = isDeepStrictEqual(gitFiles(root), names) && files.every((file, index) => {
    const after = statOf(join(root, file.path));
    return after && after.ino === file.stat.ino && after.size === file.stat.size && after.mtimeNs === file.stat.mtimeNs
      && entries[index].bytes.length === file.size;
  });
  return same ? { tar, sha256: sha256(tar), files: files.map(({ path, size }) => ({ path, size })), bytes: total } : null;
}

// One source capture for a batch. Throws PreflightError (exit 4 refused, exit 5 not stable).
export function captureSource(root, { attempts = 3 } = {}) {
  for (let attempt = 0; attempt < attempts; attempt += 1) {
    const captured = captureOnce(root);
    if (captured) return captured;
  }
  throw new PreflightError(5, `The files changed while pdd read them (${attempts} times). Stop other edits, then run pdd check again.`);
}

// Files sent that are not prompt, story or test files.
export function otherFiles(files, found) {
  const known = new Set([...found.tests.map(test => test.path), ...found.stories.map(story => story.path)]);
  return files.filter(file => !file.path.endsWith('.prompt.md') && !known.has(file.path));
}
