// Generated from prompts/cli/runtime-preflight.prompt.md (sha256: dceba715dc55d8b91d04db2f3d12e4013c8b0a508800876bcd7fa0dea6f8dc49).
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { closeSync, constants, fstatSync, lstatSync, openSync, readFileSync, writeFileSync } from 'node:fs';
import { basename, join, posix } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { expandSource } from './contract-refs.mjs';

export const TEST_SCHEMA = 'prompt-runtime.program-scenario.v1';
export const LIMITS = Object.freeze({ bytes: 10_485_760, files: 10_000, test: 1_048_576 });
const TOP_KEYS = new Set(['schema_version', 'story_path', 'criteria', 'initial_world', 'steps', 'entry_paths', 'simulation',
  'check_exemptions', 'context', 'context_byte_budget', 'criteria_scope', 'prompt_mappings']);
const REQUIRED_KEYS = ['schema_version', 'criteria', 'initial_world', 'steps'];
const STEP_KEYS = new Set(['step_id', 'entry_path', 'operation', 'input', 'checks', 'expected_error', 'simulation_overrides', 'model']);
const RULE_OPS = new Set(['at_most', 'at_least', 'not_contains', 'all_in', 'equals_ignore_case']);
const EXACT_OPS = new Set(['equals', 'not_equals', 'one_of', 'count', ...RULE_OPS]);
const SCHEMA_RULES = new Set(['type', 'properties', 'required', 'additionalProperties', 'items', 'enum', 'const', 'oneOf',
  'minimum', 'maximum', 'exclusiveMinimum', 'exclusiveMaximum', 'multipleOf', 'minLength', 'maxLength', 'pattern',
  'minItems', 'maxItems', 'uniqueItems', 'minProperties', 'maxProperties']);
const SCHEMA_NOTES = new Set(['title', 'description', 'default', 'examples', 'format', '$comment', '$schema', '$id']);

// The engine's _INTERFACE regex (prompt_program_discovery.py, eae2202a).
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

// A port of the engine's explicit_story_criteria (program_scenario.py, eae2202a).
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
  const listed = spawnSync('git', ['ls-files', '-z', '-co', '--exclude-standard'], { cwd: root, maxBuffer: 512 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] });
  if (listed.status !== 0) throw new PreflightError(5, 'pdd could not list the Git files of this repository.');
  return [...new Set(listed.stdout.toString('utf8').split('\0').filter(Boolean))].sort();
}

const statOf = path => { try { return lstatSync(path, { bigint: true }); } catch (error) { if (['ENOENT', 'ENAMETOOLONG'].includes(error.code)) return null; throw error; } };
const readText = (root, path) => {
  const stat=statOf(join(root,path));
  sourceLimit([{path,size:Number(stat?.size ?? 0)}]);
  return readFileSync(join(root,path),'utf8');
};
const storyName = path => basename(path).replace(/\.md$/, '');
const titleOf = text => text.split('\n').find(line => line.startsWith('# '))?.slice(2).trim() || null;

// Tests, stories and Git-visible regular files of one repo.
export function findTests({ root, files = gitFiles(root) }) {
  const visible = new Set(), tests = [], stories = [], discoveryWarnings = [];
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
    } else if (path.endsWith('.md') && path.split('/').slice(0, -1).includes('user_stories') && !/^(?:plan|readme)\.md$/i.test(basename(path))) {
      // An index (PLAN.md, README.md) or a file with no acceptance criteria section is not a Story (2048 session, 0.1.6).
      if (stat.size > LIMITS.bytes) { discoveryWarnings.push(`Warning: ${path}: discovery unavailable (too big; limit 10 MB).`); continue; }
      const text = readText(root, path);
      if (AC_HEADING.test(text)) stories.push({ path, name: storyName(path), title: titleOf(text) });
    }
  }
  for (const test of tests) {
    const storyPath = typeof test.doc?.story_path === 'string' ? test.doc.story_path : null;
    const story = stories.find(item => item.path === storyPath);
    test.storyPath = storyPath;
    test.story = storyPath ? storyName(storyPath) : storyName(test.path.replace(/\.json$/, ''));
    test.title = story?.title ?? (storyPath && visible.has(storyPath) && Number(statOf(join(root,storyPath))?.size ?? 0) <= LIMITS.bytes ? titleOf(readText(root, storyPath)) : null) ?? test.story;
  }
  const named = new Set(tests.map(test => test.storyPath));
  const warnings = [...discoveryWarnings, ...stories.filter(story => !named.has(story.path)).map(story => `Warning: ${story.path} has no test.`)];
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
    if (key === 'oneOf' && Array.isArray(value)) for (const child of value) { const found = unknownKeyword(child); if (found) return found; }
  }
  return null;
}

const either = items => items.length > 1 ? `${items.slice(0, -1).join(', ')} or ${items.at(-1)}` : items[0];
const variantNames = variants => [...new Set(variants.map(variant => typeof variant?.type === 'string' ? (variant.type === 'null' ? 'null' : article(variant.type)) : 'another shape'))];

// The JSON Schema check of rule P9: every problem, not only the first. Pattern misses are warnings (JS and Python regexes differ).
// Only a common regex subset is evidence of cross-runtime membership. Other
// syntax may still be checked by the runtime, but cannot establish overlap.
function portablePattern(source, value) {
  // Character classes and end anchors differ outside this concrete domain.
  // Empty JS classes are also invalid in Python, even with ASCII input.
  if (/[^\x20-\x7e]/u.test(source) || /[^\x20-\x7e]/u.test(value) || /\[\^?\]/u.test(source)) return null;
  if (/\\(?:[1-9bBAZzGkpPuU]|x|c)|\(\?|[\s\S]*[\u0080-\uffff]/u.test(source)) return null;
  try { return new RegExp(source, 'u'); } catch { return null; }
}
function schemaRun(value, schema, tokens) {
  const problems = [], warnings = [], evidence = { miss: false, unknown: false };
  schemaProblems(value, schema, tokens, problems, warnings, evidence);
  return { problems, warnings, state: problems.length || evidence.miss ? 'miss' : evidence.unknown ? 'unknown' : 'match' };
}
function schemaProblems(value, schema, tokens, out, warnings, evidence = { miss: false, unknown: false }) {
  const at = rule => out.push({ tokens, rule });
  if (!isObject(schema)) return;
  if (Array.isArray(schema.oneOf)) {
    const runs = schema.oneOf.map(variant => schemaRun(value, variant, tokens));
    const fits = runs.filter(run => run.state === 'match').length;
    if (fits > 1) return at(`fits more than one of the allowed shapes (oneOf). Make the shapes exclusive.`);
    if (fits === 1) {
      if (runs.some(run => run.state === 'unknown')) evidence.unknown = true;
      return;
    }
    if (runs.some(run => run.state === 'unknown')) { evidence.unknown = true; return; }
    evidence.miss = true;
    const advisory = runs.find(run => !run.problems.length);
    if (advisory) { warnings.push(...advisory.warnings); return; }
    const same = schema.oneOf.findIndex(variant => typeof variant?.type === 'string' && typeMatches(value, variant.type));
    if (same >= 0) { out.push(...runs[same].problems); return; }
    return at(`is ${show(value)}. The prompt allows ${either(variantNames(schema.oneOf))}.`);
  }
  if (schema.type !== undefined) {
    const types = Array.isArray(schema.type) ? schema.type : [schema.type];
    if (!types.some(type => typeMatches(value, type))) return at(`is ${show(value)}. The prompt wants ${types.map(article).join(' or ')}.`);
  }
  if (Object.hasOwn(schema, 'const') && !isDeepStrictEqual(value, schema.const)) at(`is ${show(value)}. The prompt wants ${show(schema.const)}.`);
  if (Array.isArray(schema.enum) && !schema.enum.some(choice => isDeepStrictEqual(choice, value))) at(`is ${show(value)}. The prompt allows ${either(schema.enum.map(show))}.`);
  if (typeof value === 'number') {
    if ((schema.minimum !== undefined && value < schema.minimum) || (schema.maximum !== undefined && value > schema.maximum)) at(`is ${show(value)}. The prompt allows ${range(schema.minimum, schema.maximum)}.`);
    if (typeof schema.exclusiveMinimum === 'number' && value <= schema.exclusiveMinimum) at(`is ${show(value)}. The prompt wants more than ${schema.exclusiveMinimum}.`);
    if (typeof schema.exclusiveMaximum === 'number' && value >= schema.exclusiveMaximum) at(`is ${show(value)}. The prompt wants less than ${schema.exclusiveMaximum}.`);
    if (typeof schema.multipleOf === 'number' && schema.multipleOf > 0) {
      const ratio = value / schema.multipleOf;
      if (Math.abs(ratio - Math.round(ratio)) > 1e-9) at(`is ${show(value)}. The prompt wants a multiple of ${schema.multipleOf}.`);
    }
  }
  if (typeof value === 'string') {
    const length = [...value].length;
    if ((schema.minLength !== undefined && length < schema.minLength) || (schema.maxLength !== undefined && length > schema.maxLength)) {
      at(`has ${plural(length, 'character')}. The prompt allows ${range(schema.minLength, schema.maxLength, 'character')}.`);
    }
    if (typeof schema.pattern === 'string') {
      const pattern = portablePattern(schema.pattern, value);
      if (!pattern) evidence.unknown = true;
      const pointer = pointerOf(tokens);
      if (pattern && !pattern.test(value)) {
        evidence.miss = true;
        warnings.push(`input${pointer ? ` ${pointer}` : ''} is ${show(value)}. It does not match the pattern ${schema.pattern}, so the runtime will likely refuse it.`);
      }
    }
  }
  if (Array.isArray(value)) {
    if ((schema.minItems !== undefined && value.length < schema.minItems) || (schema.maxItems !== undefined && value.length > schema.maxItems)) {
      at(`has ${plural(value.length, 'item')}. The prompt allows ${range(schema.minItems, schema.maxItems, 'item')}.`);
    }
    if (schema.uniqueItems === true && value.some((item, index) => value.findIndex(other => isDeepStrictEqual(other, item)) !== index)) at('has the same item twice. The prompt wants unique items.');
    if (isObject(schema.items)) for (const [index, item] of value.entries()) schemaProblems(item, schema.items, [...tokens, String(index)], out, warnings, evidence);
  }
  if (isObject(value)) {
    const count = Object.keys(value).length;
    if ((schema.minProperties !== undefined && count < schema.minProperties) || (schema.maxProperties !== undefined && count > schema.maxProperties)) {
      at(`has ${plural(count, 'field')}. The prompt allows ${range(schema.minProperties, schema.maxProperties, 'field')}.`);
    }
    for (const key of Array.isArray(schema.required) ? schema.required : []) if (!Object.hasOwn(value, key)) at(`has no ${show(key)}. The prompt requires it.`);
    const properties = isObject(schema.properties) ? schema.properties : {};
    for (const [key, child] of Object.entries(value)) {
      if (Object.hasOwn(properties, key)) schemaProblems(child, properties[key], [...tokens, key], out, warnings, evidence);
      else if (schema.additionalProperties === false) at(`has ${show(key)}. The prompt does not allow it.`);
      else if (isObject(schema.additionalProperties)) schemaProblems(child, schema.additionalProperties, [...tokens, key], out, warnings, evidence);
    }
  }
}

const hasReference = value => Array.isArray(value) ? value.some(hasReference)
  : isObject(value) && (Object.hasOwn(value, '$step_result') || Object.values(value).some(hasReference));
const pointerOf = tokens => tokens.map(token => `/${String(token).replace(/~/g, '~0').replace(/\//g, '~1')}`).join('');
const sectionOf = (base, tokens) => tokens.reduce((text, token) => /^\d+$/.test(token) ? `${text}[${token}]` : `${text}.${token}`, base);

// P9 on one step input: {refusals, warnings}. An unknown schema keyword skips that input with a warning.
export function checkInput(input, schema, index) {
  if (hasReference(input)) return { refusals: [], warnings: [] };
  const keyword = unknownKeyword(schema);
  if (keyword) return { refusals: [], warnings: [`steps[${index}] input was not checked here: the prompt schema uses "${keyword}". The runtime still checks it.`] };
  const problems = [], warnings = [];
  schemaProblems(input, schema, [], problems, warnings);
  const seen = new Set();
  return {
    refusals: problems.filter(problem => { const key = `${pointerOf(problem.tokens)} ${problem.rule}`; if (seen.has(key)) return false; seen.add(key); return true; })
      .map(problem => refusal('invalid-input', sectionOf(`steps[${index}].input`, problem.tokens),
        `steps[${index}] input${problem.tokens.length ? ` ${pointerOf(problem.tokens)}` : ''} ${problem.rule}`, { step: index + 1 })),
    warnings: warnings.map(text => `steps[${index}] ${text}`),
  };
}

// The engine's executable schema subset (graph_runtime_protocol.py, _validate_schema_node, eae2202a).
const SCHEMA_ANNOTATIONS = new Set(['default', 'description', 'title', 'examples', 'format']);
const SCHEMA_FORBIDDEN = new Set(['$ref', '$dynamicRef', 'anyOf', 'allOf', 'not', 'if', 'then', 'else', 'contains',
  'unevaluatedProperties', 'patternProperties', 'propertyNames', 'contentEncoding']);
const NUMBER_FIELDS = ['type', 'enum', 'const', 'minimum', 'maximum', 'exclusiveMinimum', 'exclusiveMaximum', 'multipleOf'];
const SCHEMA_FIELDS = { null: ['type', 'enum', 'const'], boolean: ['type', 'enum', 'const'], string: ['type', 'enum', 'const', 'minLength', 'maxLength', 'pattern'],
  integer: NUMBER_FIELDS, number: NUMBER_FIELDS, array: ['type', 'items', 'enum', 'const', 'minItems', 'maxItems', 'uniqueItems'],
  object: ['type', 'properties', 'required', 'additionalProperties', 'enum', 'const', 'minProperties', 'maxProperties'] };
const COUNT_FIELDS = ['minLength', 'maxLength', 'minItems', 'maxItems', 'minProperties', 'maxProperties'];
const BOUND_FIELDS = ['minimum', 'maximum', 'exclusiveMinimum', 'exclusiveMaximum'];

function schemaRules(schema, pointer, out) {
  const add = (code, rule) => out.push({ code, pointer, rule });
  if (!isObject(schema) || !Object.keys(schema).length) return add('graph-schema-type-invalid', 'is not a schema. Use an object such as {"type": "string"}.');
  if (Array.isArray(schema.type)) {
    return add('graph-schema-type-list', `has a list of types (${schema.type.map(String).join(', ')}). Use "oneOf" with one schema for each type, for example {"oneOf": [{"type": "string"}, {"type": "null"}]}.`);
  }
  for (const key of Object.keys(schema)) if (SCHEMA_FORBIDDEN.has(key)) add('graph-schema-unsupported-keyword', `uses "${key}", which the runtime does not support.`);
  if (Object.hasOwn(schema, 'oneOf')) {
    for (const key of Object.keys(schema)) if (key !== 'oneOf' && !SCHEMA_ANNOTATIONS.has(key) && !SCHEMA_FORBIDDEN.has(key)) add('graph-schema-unsupported-keyword', `has "${key}" next to "oneOf". Put it inside each oneOf schema.`);
    if (!Array.isArray(schema.oneOf) || !schema.oneOf.length) add('graph-schema-invalid', '"oneOf" must be a list of at least one schema.');
    else {
      schema.oneOf.forEach((variant, index) => schemaRules(variant, `${pointer}/oneOf/${index}`, out));
      if (schema.oneOf.some((variant, index) => schema.oneOf.findIndex(other => isDeepStrictEqual(other, variant)) !== index)) add('graph-schema-invalid', '"oneOf" has the same schema twice.');
    }
    return annotationRules(schema, add);
  }
  const type = schema.type;
  if (typeof type !== 'string' || !Object.hasOwn(SCHEMA_FIELDS, type)) {
    return add('graph-schema-type-invalid', `${type === undefined ? 'has no "type"' : `has the type ${show(type)}`}. Use null, boolean, string, integer, number, array or object, or "oneOf".`);
  }
  const allowed = new Set(SCHEMA_FIELDS[type]);
  for (const key of Object.keys(schema)) {
    if (!allowed.has(key) && !SCHEMA_ANNOTATIONS.has(key) && !SCHEMA_FORBIDDEN.has(key)) add('graph-schema-unsupported-keyword', `uses "${key}", which a ${type} schema cannot have. It can have ${[...allowed].join(', ')}.`);
  }
  if (type === 'array') {
    if (!Object.hasOwn(schema, 'items')) add('graph-schema-invalid', 'is an array with no "items". Add "items" with the schema of one item.');
    else schemaRules(schema.items, `${pointer}/items`, out);
  }
  if (type === 'object') {
    if (schema.additionalProperties !== false) add('graph-schema-open-object', 'needs "additionalProperties": false.');
    const properties = isObject(schema.properties) ? schema.properties : null, required = schema.required;
    if (!properties) add('graph-schema-invalid', 'needs "properties": an object with one schema for each field (it may be empty).');
    if (!Array.isArray(required)) add('graph-schema-invalid', 'needs "required": a list of the property names that must be present. It may be empty; a property that is not in the list is optional.');
    else {
      const wrong = required.find(name => typeof name !== 'string' || !properties || !Object.hasOwn(properties, name));
      if (wrong !== undefined) add('graph-schema-invalid', `has ${show(wrong)} in "required", but not in "properties".`);
      else if (new Set(required).size !== required.length) add('graph-schema-invalid', 'names a property twice in "required".');
    }
    for (const [name, child] of Object.entries(properties ?? {})) schemaRules(child, `${pointer}/properties/${pointerOf([name]).slice(1)}`, out);
  }
  for (const key of COUNT_FIELDS) if (Object.hasOwn(schema, key) && !(Number.isInteger(schema[key]) && schema[key] >= 0)) add('graph-schema-invalid', `"${key}" must be a whole number of 0 or more.`);
  for (const key of BOUND_FIELDS) if (Object.hasOwn(schema, key) && typeof schema[key] !== 'number') add('graph-schema-invalid', `"${key}" must be a number.`);
  if (Object.hasOwn(schema, 'multipleOf') && !(typeof schema.multipleOf === 'number' && schema.multipleOf > 0)) add('graph-schema-invalid', '"multipleOf" must be a number above 0.');
  if (Object.hasOwn(schema, 'pattern') && typeof schema.pattern !== 'string') add('graph-schema-invalid', '"pattern" must be a string.');
  if (Object.hasOwn(schema, 'uniqueItems') && typeof schema.uniqueItems !== 'boolean') add('graph-schema-invalid', '"uniqueItems" must be true or false.');
  if (Object.hasOwn(schema, 'enum')) {
    if (!Array.isArray(schema.enum) || !schema.enum.length) add('graph-schema-invalid', '"enum" must be a list of at least one value.');
    else if (schema.enum.some((item, index) => schema.enum.findIndex(other => isDeepStrictEqual(other, item)) !== index)) add('graph-schema-invalid', '"enum" has the same value twice.');
    else if (schema.enum.some(item => !typeMatches(item, type))) add('graph-schema-invalid', `"enum" has a value that is not ${article(type)}.`);
  }
  if (Object.hasOwn(schema, 'const') && !typeMatches(schema.const, type)) add('graph-schema-invalid', `"const" is not ${article(type)}.`);
  if (Object.hasOwn(schema, 'default') && !typeMatches(schema.default, type)) add('graph-schema-invalid', `"default" is not ${article(type)}.`);
  annotationRules(schema, add);
}

function annotationRules(schema, add) {
  for (const key of ['description', 'title', 'format']) if (Object.hasOwn(schema, key) && typeof schema[key] !== 'string') add('graph-schema-invalid', `"${key}" must be a string.`);
  if (Object.hasOwn(schema, 'examples') && !Array.isArray(schema.examples)) add('graph-schema-invalid', '"examples" must be a list.');
}

// Preserve numeric JSON spelling only for parsed prompt interfaces; ordinary callers supply JSON values.
const numberSources = new WeakMap();
function limitProblems(iface) {
  const out = [], keys = ['max_steps', 'max_model_calls'];
  const add = (code, pointer, rule, hint) => out.push({code,pointer,rule,hint});
  const shapeHint = 'Fix limits: use exactly "max_steps" and "max_model_calls", each an integer of at least 1.';
  if (!isObject(iface) || !Object.hasOwn(iface, 'limits')) {
    add('invalid-interface', '/limits', 'has no limits object.', 'Add "limits": {"max_steps": 1, "max_model_calls": 1}.');
    return out;
  }
  const limits = iface.limits;
  if (!isObject(limits)) {
    add('invalid-limits', '/limits', 'must be an object with exactly max_steps and max_model_calls.', shapeHint);
    return out;
  }
  for (const key of Object.keys(limits)) if (!keys.includes(key)) {
    add('invalid-limits', `/limits/${pointerOf([key]).slice(1)}`, 'is not an allowed limit field.', `Remove the extra limits key ${JSON.stringify(key)}; use exactly "max_steps" and "max_model_calls", each an integer of at least 1.`);
  }
  for (const key of keys) {
    const token = numberSources.get(limits)?.get(key);
    const integer = typeof limits[key] === 'number' && (token === undefined ? Number.isInteger(limits[key]) && limits[key] >= 1
      : /^-?(?:0|[1-9]\d*)$/.test(token) && BigInt(token) >= 1n);
    if (!Object.hasOwn(limits, key) || !integer) {
      add('invalid-limits', `/limits/${key}`, Object.hasOwn(limits, key) ? 'must be an integer JSON literal of at least 1.' : 'is missing; must be an integer JSON literal of at least 1.', `Fix limits.${key}: set an integer of at least 1 (for example 1), without a decimal point or exponent.`);
    }
  }
  return out;
}

// Every schema problem of one interface: entry input and result schemas (any root) and resource operation schemas (object root).
export function interfaceSchemaProblems(iface) {
  const out = limitProblems(iface);
  for (const [index, entry] of (Array.isArray(iface?.entries) ? iface.entries : []).entries()) {
    for (const key of ['input_schema', 'result_schema']) if (isObject(entry) && Object.hasOwn(entry, key)) schemaRules(entry[key], `/entries/${index}/${key}`, out);
  }
  for (const [index, resource] of (Array.isArray(iface?.resources) ? iface.resources : []).entries()) {
    for (const [opIndex, operation] of (Array.isArray(resource?.operations) ? resource.operations : []).entries()) {
      for (const key of ['arguments_schema', 'result_schema']) {
        if (!isObject(operation) || !Object.hasOwn(operation, key)) continue;
        const pointer = `/resources/${index}/operations/${opIndex}/${key}`;
        schemaRules(operation[key], pointer, out);
        if (isObject(operation[key]) && !Array.isArray(operation[key].type) && operation[key].type !== 'object' && !Object.hasOwn(operation[key], 'oneOf')) {
          out.push({ code: 'graph-schema-invalid', pointer, rule: 'must be an object schema ("type": "object").' });
        }
      }
    }
  }
  return out;
}

// The prompt file of an entry: {path, text, blocks, interface, error}.
export function readPrompt(root, visible, path) {
  if (typeof path !== 'string' || !path.endsWith('.prompt.md') || !visible.has(path)) return { path, error: 'entry-missing' };
  const raw = sourceFilePort(root,visible).read({path}).content, prepared = preparedText(root,visible,path,raw,'prompt'), text = prepared.text, blocks = interfaceBlocks(text);
  if (!blocks.length) return { path, text, blocks, error: 'interface-missing' };
  if (blocks.length > 1) return { path, text, blocks, error: 'pdd-two-interfaces' };
  let value;
  try {
    value = JSON.parse(blocks[0][1], function(key, value, context) {
      if (typeof value === 'number' && context?.source !== undefined) {
        if (!numberSources.has(this)) numberSources.set(this, new Map());
        numberSources.get(this).set(key, context.source);
      }
      return value;
    });
  } catch (error) { return { path, text, blocks, error: 'invalid-json', detail: error.message }; }
  if (!isObject(value)) return { path, text, blocks, error: 'invalid-json', detail: 'The interface is not a JSON object.' };
  return { path, text, blocks, interface: value, prose: proseSha256(text), references:prepared.references };
}

// Drafts may run; until the server takes them, its refusal gets this plain text.
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
    numbers.push({ index: match.index, end: match.index + match[0].length, text: `${negative ? '-' : ''}${match[0]}`, value: Number(match[0].replace(/,/g, '')) * (negative ? -1 : 1) });
  }
  return numbers;
}

const REVIEW_FILE = 'pdd-numeric-reviews.json';
const REVIEW_KEYS = ['test_path','test_sha256','step_id','criterion_id','target','path','value','reason'];
function validNumericReview(row) {
  return isObject(row) && Object.keys(row).length === REVIEW_KEYS.length && REVIEW_KEYS.every(key => Object.hasOwn(row,key))
    && ['test_path','step_id','criterion_id','target','path','test_sha256','reason'].every(key => typeof row[key] === 'string')
    && row.test_path.endsWith('.json') && !row.test_path.startsWith('/') && posix.normalize(row.test_path) === row.test_path
    && !row.test_path.split('/').includes('..') && /^[a-f0-9]{64}$/i.test(row.test_sha256)
    && !!row.step_id.trim() && !!row.criterion_id.trim() && ['result','error'].includes(row.target)
    && (row.path === '' || row.path.startsWith('/')) && Number.isFinite(row.value)
    && !!row.reason.trim() && row.reason.length <= 1000 && !/[\r\n]/.test(row.reason);
}
function numericReviews(root, found, warnings) {
  const path = join(root, REVIEW_FILE), stat = statOf(path);
  if (!stat) return [];
  const ignore = () => { warnings.push(`Warning: ${REVIEW_FILE} is invalid, unreadable or not a Git-visible regular file; its numeric reviews are ignored.`); return []; };
  if (!found.visible.has(REVIEW_FILE) || !stat.isFile() || stat.isSymbolicLink() || stat.size > 16n * 1024n) return ignore();
  let fd;
  try {
    fd = openSync(path, constants.O_RDONLY | constants.O_NOFOLLOW);
    const actual = fstatSync(fd);
    if (!actual.isFile() || actual.size > 16 * 1024) return ignore();
    const source = readFileSync(fd,'utf8');
    if (Buffer.byteLength(source) > 16 * 1024) return ignore();
    const data = JSON.parse(source);
    if (!isObject(data) || Object.keys(data).length !== 2 || data.schema_version !== 'pdd.numeric-reviews.v1'
      || !Array.isArray(data.reviews) || data.reviews.length > 100 || !data.reviews.every(validNumericReview)) return ignore();
    return data.reviews;
  } catch { return ignore(); } finally { if (fd !== undefined) closeSync(fd); }
}
const quantityWords = text => String(text ?? '').replace(/([a-z])([A-Z])/g,'$1 $2').toLowerCase().split(/[^a-z]+/).filter(Boolean);
const aggregateWords = new Set(['total','combined','cumulative','aggregate','sum','cap','limit','budget']);

const namedQuantity = text => {
  const words = quantityWords(text);
  const names = new Set(words.map(word => /^(scores?|points?)$/.test(word) ? 'score'
    : /^(moves?|turns?)$/.test(word) ? 'moves' : /^seeds?$/.test(word) ? 'seed' : null).filter(Boolean));
  return names.size === 1 ? [...names][0] : null;
};
function numberQuantity(text, number) {
  // Prefer an immediately following unit ("30 moves"), then a preceding
  // subject ("score is 30"). Do not cross clauses or another number.
  const after = /^\s*([a-z]+)/i.exec(text.slice(number.end));
  const following = after && namedQuantity(after[1]);
  if (following) return following;
  const before = /([a-z]+)(?:\s+(?:is|of|equals|at|the|fixed))*\s*$/i.exec(text.slice(0, number.index));
  return before ? namedQuantity(before[1]) : null;
}

// A number can be a component of the criterion's quantity, rather than a typo.
export function numberWarnings(doc, { testPath, testSha, reviews = [] } = {}) {
  const texts = new Map((Array.isArray(doc?.criteria) ? doc.criteria : []).filter(isObject).map(item => [item.id, item.text]));
  const steps = Array.isArray(doc?.steps) ? doc.steps : [], allChecks = steps.flatMap(step => Array.isArray(step?.checks) ? step.checks : []);
  const warnings = new Set();
  for (const [stepIndex,step] of steps.entries()) for (const [checkIndex,check] of (Array.isArray(step?.checks) ? step.checks : []).entries()) {
    const text = texts.get(check?.criterion_id);
    if (!isObject(check) || typeof text !== 'string' || !['result','error'].includes(check.target)) continue;
    const values = check.op === 'one_of' && Array.isArray(check.value) ? check.value : check.op === 'equals' ? [check.value] : [];
    const allNumbers = numbersIn(text), quantity = namedQuantity(check.path);
    const associated = allNumbers.map(item => ({ ...item, quantity: numberQuantity(text, item) }));
    const matching = associated.filter(item => quantity && item.quantity === quantity);
    const found = quantity && matching.length ? matching
      : quantity && associated.length && associated.every(item => item.quantity) ? [] : associated;
    const leaf = quantityWords(String(check.path ?? '').split('/').at(-1));
    const sameQuantity = leaf.some(word => aggregateWords.has(word)) && quantityWords(text).some(word => aggregateWords.has(word));
    const members = /\bacross\b([\s\S]*)/i.exec(text)?.[1] ?? '';
    const namedComponent = !sameQuantity && /\b(?:combined|cumulative|total|aggregate|sum|across)\b/i.test(text)
      && quantityWords(check.path).some(word => word.length > 2 && quantityWords(members).includes(word));
    for (const value of values) {
      if (typeof value !== 'number' || !found.length || found.some(item => item.value === value)) continue;
      const closest = found.reduce((best,item) => Math.abs(item.value-value) < Math.abs(best.value-value) ? item : best);
      if (Math.abs(closest.value-value) > 0.1 * Math.max(Math.abs(closest.value),Math.abs(value))) continue;
      const companion = allChecks.some(peer => isObject(peer) && peer !== check && peer.criterion_id === check.criterion_id
        && peer.target === check.target && peer.path !== check.path && peer.op === 'equals' && peer.value === closest.value);
      if (namedComponent || (!sameQuantity && !matching.length && companion)) continue;
      if (reviews.some(row => validNumericReview(row) && row.test_path === testPath && row.test_sha256.toLowerCase() === testSha
        && row.step_id === step.step_id && row.criterion_id === check.criterion_id && row.target === check.target && row.path === check.path && row.value === value)) continue;
      const location = `${testPath ?? 'test'} steps[${stepIndex}].checks[${checkIndex}] (${check.target} ${check.path})`;
      warnings.add(`Warning: possible numeric mismatch at ${location}: expected ${value}; ${doc.story_path ?? 'criterion text'} ${check.criterion_id} contains ${closest.text}. These may be different quantities. Confirm against the Story and prompt; retain a correct expected value. Record a scoped rationale in ${REVIEW_FILE} if needed (RUNBOOK §4).`);
    }
  }
  return [...warnings];
}

const stepCount = doc => Array.isArray(doc?.steps) ? doc.steps.length : 0;
// Leave room for the whole call graph; the budget is a ceiling, not a charge.
export const defaultMaxCalls = doc => Math.min(1000, Math.max(18, stepCount(doc) * 12));

function firstDifference(testTexts, storyTexts) {
  const left = [...storyTexts];
  for (const text of testTexts) {
    const index = left.indexOf(text);
    if (index < 0) return `The test has this criterion, but the story does not: "${text}"`;
    left.splice(index, 1);
  }
  return `The story has this criterion, but the test does not: "${left[0]}"`;
}

// The schema rules of a prompt and of the prompts it calls, all at once (cached per prompt).
function promptSchemaRefusals(root, found, prompt, prompts, seen = new Set()) {
  if (!prompt?.interface || seen.has(prompt.path)) return [];
  seen.add(prompt.path);
  prompt.schemaIssues ??= interfaceSchemaProblems(prompt.interface).map(problem =>
    refusal(problem.code, problem.pointer, `${prompt.path} ${problem.pointer} ${problem.rule}`, problem.hint ? {hint:problem.hint,path:prompt.path} : {}));
  const called = (Array.isArray(prompt.interface.calls) ? prompt.interface.calls : []).map(call => call?.target).filter(target => typeof target === 'string');
  return [...prompt.schemaIssues, ...called.flatMap(target => {
    if (!prompts.has(target)) prompts.set(target, readPrompt(root, found.visible, target));
    return promptSchemaRefusals(root, found, prompts.get(target), prompts, seen);
  })];
}

function checkTest(root, found, test, prompts) {
  let doc = test.doc;
  if (!test.error && isObject(doc)) {
    const prepared = preparedText(root,found.visible,test.path,readText(root,test.path),'scenario');
    try { doc = JSON.parse(prepared.text); } catch { /* Preserve ordinary malformed scenario handling. */ }
  }
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
  const checked = new Set(), exact = new Set(), inputIssues = [];
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
    const schemaIssues = promptSchemaRefusals(root, found, prompt, prompts);
    if (schemaIssues.length) return schemaIssues;
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
    inputIssues.push(...checkInput(step.input, entry.input_schema, index).refusals);
  }
  if (inputIssues.length) return inputIssues;
  const unchecked = [...ids].filter(id => !checked.has(id));
  if (unchecked.length) return refusal('unchecked-criteria', 'criteria', `These criteria have no check: ${unchecked.join(', ')}.`);
  const loose = [...ids].filter(id => !exact.has(id));
  if (loose.length) return refusal('criterion-needs-exact-check', 'criteria', `These criteria need an exact check (equals, not_equals, one_of or count): ${loose.join(', ')}.`);
  return null;
}

// Rules P1-P10 for the selected tests. Returns rows and warnings; never throws for a test problem.
export function preflight({ root, found, selected }) {
  const prompts = new Map(), warnings = [];
  const reviews = numericReviews(root, found, warnings);
  const rows = selected.map(test => {
    const refused = checkTest(root, found, test, prompts);
    const row = { test: test.path, story: test.story, title: test.title, refusals: refused ? [refused].flat() : [], warnings: numberWarnings(test.doc, { testPath: test.path, testSha: reviews.length ? sha256(readFileSync(join(root,test.path))) : null, reviews }),
      max_calls: defaultMaxCalls(test.doc), steps: Array.isArray(test.doc?.steps) ? test.doc.steps : [],
      criteria_total: Array.isArray(test.doc?.criteria) ? test.doc.criteria.length : 0, draft: false };
    row.draft = row.steps.some(step => prompts.get(step?.entry_path)?.interface?.status === 'draft');
    for (const [index, step] of row.steps.entries()) {
      const prompt = prompts.get(step?.entry_path), entry = prompt?.interface?.entries?.find?.(item => item?.operation === step?.operation);
      for (const text of entry ? checkInput(step.input, entry.input_schema, index).warnings : []) warnings.push(`Warning: ${test.path} ${text}`);
    }
    return row;
  });
  return { rows, warnings };
}

// --fill-hash: fill draft hashes; report approved interfaces whose text changed.
export function fillHashes({ root, files = gitFiles(root) }) {
  const result = { filled: [], current: [], refused: [], stale: [], warnings: [] };
  for (const path of files) {
    if (!path.endsWith('.prompt.md') || !statOf(join(root, path))?.isFile()) continue;
    const text = readText(root, path), blocks = interfaceBlocks(text);
    try { preparedText(root,new Set(files),path,text,'prompt'); }
    catch (error) { result.refused.push({path,message:error.message}); continue; }
    if (!blocks.length) continue;
    if (blocks.length > 1) { result.refused.push({ path, message: `${path} has more than one Runtime interface block. Keep one.` }); continue; }
    const [start, end] = blocks[0].indices[1], body = blocks[0][1];
    let value;
    try { value = JSON.parse(body); } catch { result.refused.push({ path, message: `The Runtime interface of ${path} is not valid JSON.` }); continue; }
    if (!isObject(value)) { result.refused.push({ path, message: `The Runtime interface of ${path} is not a JSON object.` }); continue; }
    if (!Object.hasOwn(value, 'status')) {
      if (Object.hasOwn(value, 'prose_sha256')) result.refused.push({ path, message: `The Runtime interface of ${path} has no status. Add "status": "draft" and run pdd check --fill-hash again.` });
      else result.warnings.push({ path, message: `The Runtime interface of ${path} has no status and no prose_sha256, so pdd skipped it. If this is a prompt you check, add "status": "draft" and run pdd check --fill-hash again.` });
      continue;
    }
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
  || /(?:^|\/)\.docker\/config\.json$/.test(path)
  || /(?:^|\/)(?:\.pdd\/agents\.json|\.config\/pdd\/agents\.json)$/i.test(path);

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

// Selection is metadata, not a rewritten project: every archive name remains authored in the repo.
const SOURCE_CONFIG = 'pdd-source.json';
const sameStat = (a, b) => a && b && a.ino === b.ino && a.dev === b.dev && a.size === b.size && a.mtimeNs === b.mtimeNs && a.ctimeNs === b.ctimeNs;
const unstableSource = Symbol('unstable source');
const sourceProblem = (from, path, reason) => new PreflightError(4, `${from}: ${path}${reason.startsWith(':') ? '' : ' '}${reason}`);

function sourcePath(raw, from) {
  if (typeof raw !== 'string' || !raw || raw.includes('\\') || /[\0-\x1f]/.test(raw) || raw.startsWith('/') || /^[A-Za-z]:/.test(raw)
    || raw.split('/').includes('..')) throw sourceProblem(from, String(raw), 'must be a repository-relative file path with no traversal.');
  const path = posix.normalize(raw);
  if (path === '.' || path === '.git' || path.startsWith('.git/')) throw sourceProblem(from, raw, 'must be a repository-relative file path.');
  return path;
}

// Markdown links are relative to their owner; repo-root spellings also work when Git names them.
function contextPath(raw, from, visible) {
  if (!raw || raw.startsWith('#') || /^(?:[a-z][a-z0-9+.-]*:|\/\/)/i.test(raw)) return null;
  let target;
  try { target = decodeURIComponent(raw.split('#')[0]); }
  catch { throw sourceProblem(from, raw, 'is not a valid local context path.'); }
  if (!target) return null;
  if (target.startsWith('/') || target.includes('\\')) throw sourceProblem(from, raw, 'must stay inside this repository.');
  const relative = posix.normalize(posix.join(posix.dirname(from), target));
  const path = visible.has(relative) ? relative : visible.has(target.replace(/^\.\//, '')) ? target.replace(/^\.\//, '') : relative;
  return sourcePath(path, from);
}

// Return local destinations without treating link labels or reference definitions as file paths.
function markdownLinks(text, definitions, imagesOnly = false) {
  const paths = [];
  for (const match of text.matchAll(/(!?)\[[^\]\n]*\]\([ \t]*/g)) {
    if (imagesOnly && !match[1]) continue;
    let index = match.index + match[0].length, path = '', depth = 0;
    if (text[index] === '<') {
      const end = text.indexOf('>', index + 1);
      if (end >= 0) paths.push(text.slice(index + 1, end));
      continue;
    }
    for (; index < text.length; index++) {
      const char = text[index];
      if (char === '\\' && index + 1 < text.length) { path += text[++index]; continue; }
      if (/\s/.test(char) || (char === ')' && depth === 0)) break;
      if (char === '(') depth++;
      if (char === ')') depth--;
      path += char;
    }
    if (path) paths.push(path);
  }
  for (const match of text.matchAll(/(!?)\[([^\]\n]+)\](?:\[([^\]\n]*)\])?/g)) {
    if (imagesOnly && !match[1]) continue;
    const following = text[match.index + match[0].length];
    if (following === '(' || following === ':') continue;
    const target = definitions.get((match[3] || match[2]).trim().replace(/\s+/g, ' ').toLowerCase());
    if (target) paths.push(target);
  }
  return paths;
}

// Only section detection uses this mask; capture and dependency/image parsing keep original bytes.
function markdownSectionText(text) {
  const tokens = /^ {0,3}(`{3,}|~{3,})[^\r\n]*|`+|<!--/gm, parts = [];
  let copied = 0;
  for (let match; (match = tokens.exec(text));) {
    let end;
    if (match[1]) {
      const fence = match[1];
      // A backtick fence's info string cannot itself contain a backtick.
      if (fence[0] === '`' && match[0].trimStart().slice(fence.length).includes('`')) continue;
      const closing = new RegExp('^ {0,3}' + fence[0] + '{' + fence.length + ',}[ \\t]*\\r?$', 'gm');
      closing.lastIndex = tokens.lastIndex;
      const close = closing.exec(text);
      end = close ? close.index + close[0].length : text.length;
    } else if (match[0] === '<!--') {
      const close = text.indexOf('-->', tokens.lastIndex);
      end = close < 0 ? text.length : close + 3;
    } else {
      const closing = new RegExp('(?<!`)`{' + match[0].length + '}(?!`)', 'g');
      closing.lastIndex = tokens.lastIndex;
      const close = closing.exec(text);
      if (!close) continue;
      end = close.index + close[0].length;
    }
    parts.push(text.slice(copied, match.index), text.slice(match.index, end).replace(/[^\r\n]/g, ' '));
    copied = end;
    tokens.lastIndex = end;
  }
  return parts.join('') + text.slice(copied);
}

// Read only a section name, never rewritten HTML. Ambiguous markup retains context.
function markdownSectionTitle(text) {
  const tokens = /<\/(strong|em|b|i)\s*>|<(strong|em|b|i)(?:\s+[A-Za-z_:][A-Za-z0-9_.:-]*(?:\s*=\s*(?:"[^"]*"|'[^']*'|[^\s"'=<>`]+))?)*\s*>|[^<>]+/giy;
  const parts = [], tags = [];
  let consumed = 0;
  for (let match; (match = tokens.exec(text));) {
    if (match[1]) {
      if (tags.pop() !== match[1].toLowerCase()) return null;
    } else if (match[2]) tags.push(match[2].toLowerCase());
    else parts.push(match[0]);
    consumed = tokens.lastIndex;
  }
  if (consumed !== text.length || tags.length) return null;
  return parts.join('').replace(/\s+/g, ' ').trim();
}

function markdownContext(text) {
  const prose = text.replace(INTERFACE, ''), definitions = new Map();
  for (const match of prose.matchAll(/^ {0,3}\[([^\]\n]+)\]:[ \t]*(?:<([^>\n]+)>|(\S+))/gm)) {
    const id = match[1].trim().replace(/\s+/g, ' ').toLowerCase();
    if (!definitions.has(id)) definitions.set(id, match[2] ?? match[3]);
  }
  const heading = /^##[ \t]+Dependencies[ \t]*\r?$/im.exec(prose);
  const rest = heading ? prose.slice(heading.index + heading[0].length) : '';
  const end = /^#{1,2}[ \t]+/m.exec(rest);
  let dependencies = end ? rest.slice(0, end.index) : rest;
  // Legacy prompts use collapsible rule/reference sections instead of Markdown headings.
  // Keep collapsible dependency context; only an explicitly named new section ends it.
  for (const match of markdownSectionText(dependencies).matchAll(/^ {0,3}<details\b[^>]*>\s*<summary\b[^>]*>([\s\S]*?)<\/summary\s*>/gim)) {
    const title = markdownSectionTitle(match[1]);
    if (title !== null && /^(?:(?:required )?(?:module )?rules|(?:required )?interface reference|decision path)(?:\s*:|$)/i.test(title)) {
      dependencies = dependencies.slice(0, match.index);
      break;
    }
  }
  const paths = [...markdownLinks(dependencies, definitions), ...markdownLinks(prose, definitions, true)];
  // A bare filename is shorthand for a dependency item, not every code span in its description.
  for (const match of dependencies.matchAll(/^ {0,3}(?:[-+*]|[0-9]+[.)])[ \t]+`([^`\n]+)`(?=[ \t:]|$)/gm)) {
    const path = match[1];
    const externalOrCode = /^[~/%$]/.test(path) || /[\s\\:$%~<>*?|[\]{}()]/.test(path);
    const fileName = /\.[A-Za-z][A-Za-z0-9_-]*$/.test(posix.basename(path));
    const commonFile = /\.(?:md|prompt|txt|json|svg|css|csv|ya?ml|toml|xml|html?|[cm]?js|[cm]?ts|jsx|tsx|py|sh|sql|ini|conf)$/i.test(path);
    if (!externalOrCode && ((path.includes('/') && fileName) || commonFile || isSecretPath(path))) paths.push(path);
  }
  return paths;
}

function sourceLimit(files) {
  const total = files.reduce((sum, file) => sum + file.size, 0);
  if (files.length > LIMITS.files || total > LIMITS.bytes) {
    const largest = [...files].sort((a, b) => b.size - a.size).slice(0, 5).map(file => `  ${file.path}  ${formatSize(file.size)}`);
    throw new PreflightError(4, [`The repository is too big to send: ${files.length} files, ${formatSize(total)}. The limit is ${LIMITS.files} files and 10 MB.`,
      'The largest files:', ...largest].join('\n'));
  }
  return total;
}

function snapshotReader(root, diskVisible, beforeRead = () => {}) {
  const snapshots = new Map();
  let unstable = false;
  function inspectRaw(path, from, allowMissing = false) {
    path = sourcePath(path, from);
    if (snapshots.has(path)) return snapshots.get(path);
    if (isSecretPath(path)) throw sourceProblem(from, path, ': the name looks like a secret. pdd never sends it.');
    const parts = path.split('/');
    for (let i = 1; i < parts.length; i++) {
      const parent = parts.slice(0, i).join('/'), stat = statOf(join(root, parent));
      if (stat?.isSymbolicLink()) throw sourceProblem(from, path, `has a symbolic link ancestor (${parent}). pdd sends only regular files.`);
      if (stat && !stat.isDirectory()) throw sourceProblem(from, path, `has a non-directory ancestor (${parent}).`);
    }
    const stat = statOf(join(root, path));
    if (stat?.isSymbolicLink()) throw sourceProblem(from, path, ': a symbolic link. pdd sends only regular files.');
    if (stat && !stat.isFile()) throw sourceProblem(from, path, ': a submodule, folder or other non-regular file. pdd sends only regular files.');
    if (stat && !diskVisible.has(path)) throw sourceProblem(from, path, 'is not a Git-visible file. Add it to Git or correct the declared dependency.');
    if (!stat && !allowMissing) throw sourceProblem(from, path, 'is not a Git-visible file on disk. Restore it or correct the declared dependency.');
    const file = { path, stat, size: Number(stat?.size ?? 0) };
    snapshots.set(path, file);
    return file;
  }
  function bytes(file) {
    if (file.bytes) return file.bytes;
    sourceLimit([file]);
    beforeRead(file);
    let fd;
    try {
      fd = openSync(join(root, file.path), constants.O_RDONLY | constants.O_NOFOLLOW);
      if (!sameStat(file.stat, fstatSync(fd, { bigint: true }))) { unstable = true; throw unstableSource; }
      file.bytes = readFileSync(fd);
      if (!sameStat(file.stat, fstatSync(fd, { bigint: true })) || file.bytes.length !== file.size) { unstable = true; throw unstableSource; }
      return file.bytes;
    } catch (error) {
      if (['ENOENT', 'ELOOP', 'ENOTDIR'].includes(error.code)) { unstable = true; throw unstableSource; }
      throw error;
    } finally { if (fd !== undefined) closeSync(fd); }
  }
  return { inspectRaw, bytes, snapshots, get unstable() { return unstable; } };
}

export function sourceFilePort(root, visible = new Set(gitFiles(root))) {
  const reader = snapshotReader(root, visible);
  return {
    stat({path}) {
      const file = reader.inspectRaw(path, 'Source', true);
      return { exists: !!file.stat, is_symlink: false, size: file.size };
    },
    read({path}) {
      const file = reader.inspectRaw(path, 'Source');
      if (!file.stat) throw sourceProblem('Source',path,'is missing.');
      try { return { content: reader.bytes(file).toString('utf8') }; }
      catch (error) { if (error === unstableSource) throw new PreflightError(5, `${path}: the file changed while pdd read it.`); throw error; }
    },
  };
}

function preparedText(root, visible, path, text, format) {
  try { return expandSource({path,text,format},sourceFilePort(root,visible)); }
  catch (error) {
    if (error.code) throw new PreflightError(4, `${error.code}: ${error.message}`);
    throw error;
  }
}

function captureOnce(root, { tests, sourceFiles, appMap = null, prepareSource }) {
  const names = gitFiles(root), visible = new Set(names), overlay = new Map(), payload = new Map(), queue = [], visited = new Set();
  const effective = new Map(), provenance = new Map(), edges = new Map(), shared = new Set(), footprintPayload = new Map();
  let selecting = true;
  const unavailable = new Map();
  const markUnavailable = (path,error) => unavailable.set(path,{path,cause:String(error.message ?? error).replace(/[\r\n\x00-\x1f\x7f]/g,' ').slice(0,4000)});
  const reader = snapshotReader(root,new Set(names),file => { if (payload.has(file.path)) sourceLimit([...payload.values()]); });
  const { inspectRaw, bytes, snapshots } = reader;
  function inspect(path, from) {
    if (overlay.has(path)) return overlay.get(path);
    const file = inspectRaw(path, from);
    if (!file.stat) throw sourceProblem(from, path, 'is missing. Restore it or correct the declared dependency.');
    return file;
  }
  function add(raw, from, role = 'context') {
    const path = sourcePath(raw, from), file = inspect(path, from);
    for (const selected of payload.keys()) if (selected.startsWith(`${path}/`) || path.startsWith(`${selected}/`)) {
      throw sourceProblem(from, path, `conflicts with selected file ${selected}.`);
    }
    if (!footprintPayload.has(path)) footprintPayload.set(path,file);
    if (selecting && !payload.has(path)) payload.set(path, file);
    if (visible.has(from)) {
      if (!edges.has(from)) edges.set(from,new Set());
      edges.get(from).add(path);
    }
    queue.push({ path, role, upload:selecting });
  }
  const referenceFiles = {
    stat({path}) {
      const file = overlay.get(path) ?? inspectRaw(path,'Reference',true);
      return {exists:overlay.has(path) || !!file.stat,is_symlink:false,size:file.size};
    },
    read({path}) { return {content:bytes(inspect(path,'Reference')).toString('utf8')}; },
  };
  function prepare(file, format) {
    if (effective.has(file.path)) return effective.get(file.path);
    let expanded;
    try { expanded = expandSource({path:file.path,text:bytes(file).toString('utf8'),format},referenceFiles); }
    catch (error) {
      if (reader.unstable || error === unstableSource) throw unstableSource;
      if (error.code) throw new PreflightError(4, `${error.code}: ${error.message}`);
      throw error;
    }
    const content = expanded.references.length ? Buffer.from(expanded.text,'utf8') : bytes(file);
    const result = {...file,bytes:content,size:content.length};
    effective.set(file.path,result); provenance.set(file.path,expanded.references);
    footprintPayload.set(file.path,result);
    if (selecting) payload.set(file.path,result);
    return result;
  }
  const addStrings = (values, from, role) => { if (Array.isArray(values)) for (const path of values) if (typeof path === 'string') add(path, from, role); };
  try {
    if (prepareSource !== undefined) {
      if (typeof prepareSource !== 'function') throw new PreflightError(4, 'prepareSource must be a synchronous function.');
      let active = true, prepared;
      const raw = path => {
        if (!active) throw new PreflightError(4, 'Preparation ports are valid only during prepareSource.');
        return inspectRaw(sourcePath(path, 'prepareSource'), 'prepareSource', true);
      };
      try {
        prepared = prepareSource({
          readFile(path) {
            const file = raw(path);
            if (!file.stat) throw sourceProblem('prepareSource', path, 'is missing.');
            return Buffer.from(bytes(file));
          },
          statFile(path) {
            const file = raw(path);
            return { exists: !!file.stat, is_symlink: false, size: file.size };
          },
        });
      } finally { active = false; }
      if (reader.unstable) throw unstableSource;
      if (!Array.isArray(prepared)) throw new PreflightError(4, 'prepareSource must return an array of files synchronously.');
      for (const output of prepared) {
        if (!isObject(output) || !(typeof output.bytes === 'string' || output.bytes instanceof Uint8Array)) throw new PreflightError(4, 'prepareSource files need a path and Buffer, Uint8Array or UTF-8 string bytes.');
        const path = sourcePath(output.path, 'prepareSource');
        if (overlay.has(path)) throw sourceProblem('prepareSource', path, `duplicates prepared file ${path}.`);
        for (const other of overlay.keys()) if (other.startsWith(`${path}/`) || path.startsWith(`${other}/`)) throw sourceProblem('prepareSource', path, `conflicts with prepared file ${other}.`);
        inspectRaw(path, 'prepareSource', true);
        const content = Buffer.from(output.bytes), file = { path, bytes: content, size: content.length };
        overlay.set(path, file);
        visible.add(path);
      }
      for (const path of overlay.keys()) add(path, 'prepareSource');
    }
    if (visible.has(SOURCE_CONFIG)) {
      const config = inspect(SOURCE_CONFIG, SOURCE_CONFIG);
      if (config.size > LIMITS.test) throw sourceProblem(SOURCE_CONFIG, '', 'must be at most 1 MiB.');
      let doc;
      try { doc = JSON.parse(bytes(config).toString('utf8')); } catch (error) {
        if (error === unstableSource) throw error;
        throw sourceProblem(SOURCE_CONFIG, '', 'must be valid JSON with only an include array.');
      }
      if (!isObject(doc) || Object.keys(doc).length !== 1 || !Array.isArray(doc.include)) throw sourceProblem(SOURCE_CONFIG, '', 'must contain only an include array of file paths.');
      for (const path of doc.include) { add(path, SOURCE_CONFIG); shared.add(sourcePath(path,SOURCE_CONFIG)); }
    }
    const selected = tests ?? [...new Set([
      ...findTests({root,files:names}).tests.map(test=>test.path).filter(path=>!overlay.has(path)),
      ...[...overlay.keys()].sort().filter(path => {
      if (!path.endsWith('.json')) return false;
      const file = overlay.get(path);
      if (file.size > LIMITS.test) return false;
      const text = bytes(file).toString('utf8');
      if (!text.includes('prompt-runtime.program-scenario')) return false;
      try { const version=JSON.parse(text)?.schema_version; return typeof version==='string' && version.startsWith('prompt-runtime.program-scenario'); } catch { return true; }
    })])];
    for (const path of selected) add(path, 'Selected test', 'test');
    if (sourceFiles !== undefined) {
      if (!Array.isArray(sourceFiles)) throw new PreflightError(4, 'sourceFiles must be an array of repository-relative file paths.');
      for (const path of sourceFiles) add(path, 'Selected source');
    }
    if (appMap) { add(appMap, 'App map', 'app-map'); shared.add(sourcePath(appMap,'App map')); }
    const storyTests = new Map();
    let siblingsAdded = false;
    for (let index = 0; index < queue.length || !siblingsAdded; index++) {
      if (index === queue.length && !siblingsAdded) {
        siblingsAdded = true; selecting = false;
        const selectedStories = new Set(storyTests.keys());
        const discovered=findTests({root,files:names}).tests.filter(test=>!overlay.has(test.path));
        for (const [path,file] of overlay) {
          if (!path.endsWith('.json') || file.size>LIMITS.test) continue;
          try { const doc=JSON.parse(bytes(file).toString('utf8')); if (typeof doc?.schema_version==='string' && doc.schema_version.startsWith('prompt-runtime.program-scenario')) discovered.push({path,doc}); } catch {}
        }
        for (const test of discovered) {
          if (!selectedStories.has(test.doc?.story_path)) continue;
          if (!storyTests.get(test.doc.story_path).includes(test.path)) storyTests.get(test.doc.story_path).push(test.path);
          try { add(test.path,'Story footprint','test'); } catch (error) { if (reader.unstable || error === unstableSource) throw error; markUnavailable(test.path,error); }
        }
        if (index === queue.length) break;
      }
      const { path, role, upload } = queue[index], key = `${path}\0${role}\0${upload}`;
      selecting = upload;
      if (visited.has(key)) continue;
      visited.add(key);
      try {
        let file = effective.get(path) ?? footprintPayload.get(path);
        if (selecting) payload.set(path,file);
        if (path.endsWith('.prompt.md')) file = prepare(file,'prompt');
        else if (role === 'test') file = prepare(file,'scenario');
        if (role === 'test' || role === 'app-map' || path.endsWith('.prompt.md') || path.endsWith('.md')) {
          const text = bytes(file).toString('utf8');
          if (role === 'test') {
            let doc;
            try { doc = JSON.parse(text); } catch { continue; } // Format refusals belong to preflight or server lint.
            if (!isObject(doc)) continue;
            if (typeof doc.story_path === 'string') {
              if (selecting) { if (!storyTests.has(doc.story_path)) storyTests.set(doc.story_path,[]); if (!storyTests.get(doc.story_path).includes(path)) storyTests.get(doc.story_path).push(path); }
              add(doc.story_path, path, 'story');
            }
            addStrings(doc.entry_paths, path);
            for (const step of Array.isArray(doc.steps) ? doc.steps : []) if (typeof step?.entry_path === 'string') add(step.entry_path, path);
            for (const item of Array.isArray(doc.context) ? doc.context : []) {
              if (typeof item?.prompt_path === 'string') add(item.prompt_path, path);
              addStrings(item?.paths, path);
            }
          } else if (role === 'app-map') {
            let map;
            try { map = JSON.parse(text); } catch { throw sourceProblem(path, '', 'must be valid app-map JSON.'); }
            const walk = value => {
              if (Array.isArray(value)) { for (const item of value) walk(item); return; }
              if (!isObject(value)) return;
              if (typeof value.prompt_path === 'string') add(value.prompt_path, path);
              addStrings(value.stylesheets, path);
              for (const key of ['screens', 'router', 'routes', 'handlers', 'handler', 'after']) walk(value[key]);
            };
            walk(map);
          } else {
            for (const raw of markdownContext(text)) { const context = contextPath(raw, path, visible); if (context) add(context, path); }
            if (path.endsWith('.prompt.md')) {
              for (const block of interfaceBlocks(text)) {
                let doc;
                try { doc = JSON.parse(block[1]); } catch { continue; }
                for (const call of Array.isArray(doc?.calls) ? doc.calls : []) if (typeof call?.target === 'string') add(call.target, path);
              }
            }
          }
        }
        // Footprint-only binary/plain inputs still need bounded bytes for hashes.
        if (!selecting) bytes(file);
      } catch (error) {
        if (selecting || reader.unstable || error === unstableSource) throw error;
        markUnavailable(path,error);
      }
    }
    const files = [...payload.values()].sort((a, b) => a.path < b.path ? -1 : a.path > b.path ? 1 : 0), total = sourceLimit(files);
    const entries = files.map(file => ({ path: file.path, bytes: bytes(file) }));
    const rawPromptHashes = Object.fromEntries(files.filter(file=>file.path.endsWith('.prompt.md')).flatMap(file=>{
      const original=inspectRaw(file.path,'Prompt snapshot',true);
      return original.stat ? [[file.path,sha256(bytes(original))]] : [];
    }));
    const tar = tarFiles(entries);
    if (tar.length > LIMITS.bytes) throw new PreflightError(4, `The source archive is ${formatSize(tar.length)}. The limit is 10 MB.`);
    const same = !reader.unstable && isDeepStrictEqual(gitFiles(root), names) && [...snapshots.values()].every(file => {
      const after = inspectParentsAndStat(root, file.path);
      return file.stat === null ? after === null : sameStat(file.stat, after);
    });
    if (!same) return null;
    const stories = new Map();
    for (const path of selected) {
      let doc; try { doc = JSON.parse(bytes(payload.get(sourcePath(path,'Selected test'))).toString('utf8')); } catch { continue; }
      if (typeof doc?.story_path !== 'string') continue;
      if (!stories.has(doc.story_path)) stories.set(doc.story_path,{story_path:doc.story_path,tests:[],selected:new Set(shared)});
      const story = stories.get(doc.story_path);
      story.tests = storyTests.get(doc.story_path) ?? [path];
      for (const sibling of story.tests) story.selected.add(sibling);
    }
    const footprints = [...stories.values()].map(story => {
      const reached = new Set(), pending = [...story.selected];
      for (let i=0;i<pending.length;i++) {
        const path=pending[i]; if (reached.has(path)) continue;
        reached.add(path); pending.push(...(edges.get(path) ?? []));
      }
      const failures = [...reached].sort().filter(path=>unavailable.has(path)).map(path=>unavailable.get(path));
      if (failures.length) return {story_path:story.story_path,tests:story.tests.sort(),unavailable:failures};
      return {story_path:story.story_path,tests:story.tests.sort(),files:[...reached].sort().filter(path=>footprintPayload.has(path)).map(path=>({path,sha256:sha256(bytes(footprintPayload.get(path)))})),references:[...reached].sort().flatMap(path=>provenance.get(path) ?? [])};
    });
    return { tar, sha256: sha256(tar), files: files.map(({ path, size }) => ({ path, size })), bytes: total,
      references:[...provenance.keys()].filter(path=>payload.has(path)).sort().flatMap(path=>provenance.get(path)), stories:footprints,
      warnings:footprints.flatMap(story=>(story.unavailable ?? []).map(item=>`Warning: ${story.story_path}: footprint unavailable: ${item.cause}`)),
      raw_prompt_hashes:rawPromptHashes,
      sources:entries.map(file=>({path:file.path,bytes:Buffer.from(file.bytes)})) };
  } catch (error) { if (reader.unstable || error === unstableSource) return null; throw error; }
}

function inspectParentsAndStat(root, path) {
  const parts = path.split('/');
  for (let i = 1; i < parts.length; i++) {
    const parent = statOf(join(root, ...parts.slice(0, i)));
    if (parent && !parent.isDirectory()) return unstableSource;
  }
  return statOf(join(root, path));
}

// Rebuild the selection on each attempt, including metadata and newly declared dependencies.
export function captureSource(root, { attempts = 3, ...selection } = {}) {
  for (let attempt = 0; attempt < attempts; attempt += 1) {
    const captured = captureOnce(root, selection);
    if (captured) return captured;
  }
  throw new PreflightError(5, `The files changed while pdd read them (${attempts} times). Stop other edits, then run pdd check again.`);
}

// Why a repo has no tests: foreign JSON under tests/, *.prompt names, prompts with no interface.
export function whyNoTests(root, visible) {
  const files = [...visible].sort(), why = [];
  for (const path of files.filter(file => file.endsWith('.json') && file.split('/').slice(0, -1).includes('tests'))) {
    let doc = null;
    try { doc = JSON.parse(readText(root, path)); } catch { doc = null; }
    if (doc?.schema_version !== TEST_SCHEMA) why.push(`${path} is not a PDD test file (it has no "schema_version": "${TEST_SCHEMA}"). See RUNBOOK.md §2.`);
  }
  for (const path of files.filter(file => file.endsWith('.prompt'))) why.push(`PDD prompts must end in .prompt.md: rename ${path} to ${path}.md.`);
  for (const path of files.filter(file => file.endsWith('.prompt.md'))) {
    if (!interfaceBlocks(readText(root, path)).length) why.push(`${path} has no Runtime interface block. See RUNBOOK.md §2.`);
  }
  return why.length > 5 ? [...why.slice(0, 5), `…and ${why.length - 5} more`] : why;
}

// Source files named (in backticks) by more than one prompt: one warning line each (real-user cli issue 10).
export function sharedSourceFiles(root, visible) {
  const owners = new Map();
  for (const prompt of [...visible].filter(path => path.endsWith('.prompt.md')).sort()) {
    if (Number(statOf(join(root,prompt))?.size ?? 0) > LIMITS.bytes) continue;
    const text = readText(root, prompt);
    for (const match of text.matchAll(/`([^`\s]+)`/g)) {
      const path = match[1].replace(/^\.\//, '');
      if (path === prompt || path.endsWith('.md') || !visible.has(path)) continue;
      owners.set(path, new Set([...(owners.get(path) ?? []), prompt]));
    }
  }
  return [...owners].filter(([, prompts]) => prompts.size > 1).sort(([a], [b]) => a.localeCompare(b))
    .map(([path, prompts]) => `Warning: ${path} is named by ${prompts.size} prompts (${[...prompts].join(', ')}). One prompt should own each source file.`);
}

// Files sent that are not prompt, story or test files.
export function otherFiles(files, found) {
  const known = new Set([...found.tests.map(test => test.path), ...found.stories.map(story => story.path)]);
  return files.filter(file => !file.path.endsWith('.prompt.md') && !known.has(file.path));
}
