// Generated from prompts/cli/scenario-compile.prompt.md (sha256: 25f1b2026b804e0b2013414d1b7b861159292cc8993d42ed69be7682120af458).
import { basename } from 'node:path';

export const V1_SCENARIO_SCHEMA = 'prompt-runtime.program-scenario.v1';
export const SHORT_SCENARIO_SCHEMA = 'pdd.scenario.short.v1';

const EXACT_INTEGER = /^-?(?:0|[1-9][0-9]*)$/;
const PY_SPACE = '[\t\n\v\f\r\x1c-\x1f \x85\xa0\u1680\u2000-\u200a\u2028\u2029\u202f\u205f\u3000]';
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

const V1_TOP_KEYS = new Set([
  'schema_version', 'story_path', 'criteria', 'initial_world', 'steps', 'entry_paths',
  'simulation', '$simulation', 'check_exemptions', 'context', 'context_byte_budget',
  'criteria_scope', 'prompt_mappings', 'app_maps',
]);
const ALLOWED_TOP_KEYS = new Set([...V1_TOP_KEYS, 'seeds', 'entry_path']);

const V1_STEP_KEYS = new Set([
  'step_id', 'entry_path', 'operation', 'input', 'checks',
  'expected_error', 'simulation_overrides', 'model',
]);
const ALLOWED_STEP_KEYS = new Set([
  ...V1_STEP_KEYS, 'id', 'op', 'error', 'from', 'patch', 'set',
]);

const TARGETS = new Set(['result', 'world', 'calls', 'error']);
const CANONICAL_OPS = new Set([
  'equals', 'not_equals', 'contains', 'not_contains', 'count', 'exists',
  'one_of', 'all_in', 'equals_ignore_case', 'at_least', 'at_most',
  'lt', 'lte', 'gt', 'gte', 'integer_relation',
]);
const OP_ALIASES = new Map([
  ['=', { op: 'equals' }],
  ['==', { op: 'equals' }],
  ['!=', { op: 'not_equals' }],
  ['>=', { op: 'at_least', measure: 'value' }],
  ['<=', { op: 'at_most', measure: 'value' }],
  ['len>=', { op: 'at_least', measure: 'length' }],
  ['length_at_least', { op: 'at_least', measure: 'length' }],
  ['len<=', { op: 'at_most', measure: 'length' }],
  ['length_at_most', { op: 'at_most', measure: 'length' }],
  ['>', { op: 'gt' }],
  ['<', { op: 'lt' }],
]);

const isPlainObject = value =>
  value !== null &&
  typeof value === 'object' &&
  !Array.isArray(value) &&
  (Object.getPrototypeOf(value) === Object.prototype || Object.getPrototypeOf(value) === null);

const cloneExact = value => {
  if (Array.isArray(value)) return value.map(cloneExact);
  if (isPlainObject(value)) {
    const out = {};
    for (const key of Object.keys(value)) out[key] = cloneExact(value[key]);
    return out;
  }
  return value;
};

export function parseExactScenarioJson(text) {
  return JSON.parse(text, (_key, value, context) =>
    typeof value === 'number' &&
    !Number.isSafeInteger(value) &&
    typeof context?.source === 'string' &&
    EXACT_INTEGER.test(context.source)
      ? BigInt(context.source)
      : value,
  );
}

export function stringifyExactScenarioJson(value, space) {
  return JSON.stringify(
    value,
    (_key, item) => (typeof item === 'bigint' ? JSON.rawJSON(item.toString()) : item),
    space,
  );
}

export function jsonSafeScenario(value) {
  if (typeof value === 'bigint') return Number(value);
  if (Array.isArray(value)) return value.map(jsonSafeScenario);
  if (isPlainObject(value)) {
    return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, jsonSafeScenario(v)]));
  }
  return value;
}

function numberedStoryCriteria(source, { requireHeading = false } = {}) {
  if (typeof source !== 'string' || !source) return [];
  const heading = AC_HEADING.exec(source);
  if (requireHeading && !heading) return [];
  const body = heading ? source.slice(heading.index + heading[0].length) : source;
  const result = [];
  let current = null;
  let expected = 1;
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
      if (!pyStrip(line) || line.startsWith('#')) {
        result.push(current.join(' '));
        current = null;
      } else {
        current.push(pyStrip(line));
      }
    }
  }
  if (current !== null) result.push(current.join(' '));
  return result;
}

export function extractStoryCriteria(source) {
  if (typeof source !== 'string' || !source) return [];
  const result = numberedStoryCriteria(source);
  if (result.length) return result;
  const heading = AC_HEADING.exec(source);
  if (!heading) return result;
  const body = source.slice(heading.index + heading[0].length);
  const next = NEXT_HEADING.exec(body);
  const section = next ? body.slice(0, next.index) : body;
  return [...section.matchAll(BULLET_ITEM)].map(match => pyWords(match[1]));
}

const refusal = (code, section, message, extra = {}) => ({
  code,
  section,
  message,
  hint: extra.hint ?? 'Fix the Short JSON scenario syntax, then run pdd lint --local or pdd lint --emit-v1.',
  ...(extra.step !== undefined ? { step: extra.step } : {}),
});

const normalizeQuotesAndSpace = text =>
  String(text)
    .replace(/[\u2018\u2019]/g, "'")
    .replace(/[\u201c\u201d]/g, '"')
    .replace(/\s+/g, ' ')
    .trim()
    .toLowerCase();

function hasValueMacro(value, seedNames) {
  if (Array.isArray(value)) return value.some(item => hasValueMacro(item, seedNames));
  if (!isPlainObject(value)) return false;
  if (
    Object.hasOwn(value, '$use') ||
    Object.hasOwn(value, '$from') ||
    Object.hasOwn(value, '$json') ||
    Object.hasOwn(value, '$step') ||
    (Object.hasOwn(value, '$seed') && typeof value.$seed === 'string' && seedNames.has(value.$seed))
  ) {
    return true;
  }
  return Object.values(value).some(item => hasValueMacro(item, seedNames));
}

const isNumericOrLabeledId = raw =>
  typeof raw === 'number' ||
  (typeof raw === 'string' && (/^[1-9][0-9]*$/.test(raw.trim()) || /^(?:ac-?)?[1-9][0-9]*\s*:/i.test(raw.trim())));

export function isShortScenarioDoc(doc) {
  if (!isPlainObject(doc)) return false;
  if (doc.schema_version === SHORT_SCENARIO_SCHEMA) return true;
  if (Object.hasOwn(doc, 'seeds') || Object.hasOwn(doc, 'entry_path')) return true;
  const seedNames = isPlainObject(doc.seeds) ? new Set(Object.keys(doc.seeds)) : new Set();
  if (Array.isArray(doc.steps)) {
    if (!Object.hasOwn(doc, 'schema_version') || !Object.hasOwn(doc, 'initial_world')) {
      return true;
    }
    for (const step of doc.steps) {
      if (!isPlainObject(step)) continue;
      if (
        Object.hasOwn(step, 'id') ||
        Object.hasOwn(step, 'op') ||
        Object.hasOwn(step, 'error') ||
        Object.hasOwn(step, 'from') ||
        Object.hasOwn(step, 'patch') ||
        Object.hasOwn(step, 'set') ||
        !Object.hasOwn(step, 'step_id') ||
        !Object.hasOwn(step, 'entry_path') ||
        !Object.hasOwn(step, 'operation') ||
        !Object.hasOwn(step, 'input') ||
        isPlainObject(step.checks)
      ) {
        return true;
      }
      if (Array.isArray(step.checks)) {
        for (const check of step.checks) {
          if (Array.isArray(check)) return true;
          if (isPlainObject(check)) {
            if (!Object.hasOwn(check, 'criterion_id') || isNumericOrLabeledId(check.criterion_id)) return true;
            if (OP_ALIASES.has(check.op) || ((check.op === 'at_least' || check.op === 'at_most') && !Object.hasOwn(check, 'measure'))) {
              return true;
            }
          }
        }
      }
    }
  }
  if (Array.isArray(doc.criteria)) {
    for (const item of doc.criteria) {
      if (isNumericOrLabeledId(item)) return true;
      if (isPlainObject(item) && isNumericOrLabeledId(item.id)) return true;
    }
  }
  return (
    hasValueMacro(doc.initial_world, seedNames) ||
    hasValueMacro(doc.steps, seedNames) ||
    hasValueMacro(doc.simulation, seedNames)
  );
}

class CompileAbort extends Error {
  constructor(issue) {
    super(issue.message);
    this.issue = issue;
  }
}

function fail(code, section, message, extra) {
  throw new CompileAbort(refusal(code, section, message, extra));
}

function parseCriterionSpec(raw, storyItems, section, extra) {
  if (typeof raw === 'number') {
    if (!Number.isSafeInteger(raw) || raw < 1) {
      fail('invalid-criterion', section, `Criterion number ${String(raw)} must be a positive whole number.`, extra);
    }
    const index = raw;
    if (storyItems.length && index > storyItems.length) {
      fail('unknown-criterion', section, `Criterion ${index} exceeds the ${storyItems.length} criteria in the Story.`, extra);
    }
    return { id: `AC${index}`, index };
  }
  if (typeof raw !== 'string' || !raw.trim()) {
    fail('invalid-criterion', section, 'Criterion reference must be a nonblank string or positive integer.', extra);
  }
  const trimmed = raw.trim();
  const labeled = /^(?:ac-?)?([1-9][0-9]*)\s*:\s*(.+)$/i.exec(trimmed);
  if (labeled) {
    const index = Number(labeled[1]);
    const label = labeled[2].trim();
    if (storyItems.length) {
      if (index > storyItems.length) {
        fail('unknown-criterion', section, `Criterion AC${index} exceeds the ${storyItems.length} criteria in the Story.`, extra);
      }
      const actual = normalizeQuotesAndSpace(storyItems[index - 1]);
      const wanted = normalizeQuotesAndSpace(label);
      if (wanted && !actual.includes(wanted)) {
        fail(
          'story-criterion-mismatch',
          section,
          `Criterion "${trimmed}" does not match Story item ${index} ("${storyItems[index - 1]}").`,
          extra,
        );
      }
    }
    return { id: `AC${index}`, index };
  }
  if (/^[1-9][0-9]*$/.test(trimmed)) {
    const index = Number(trimmed);
    if (storyItems.length && index > storyItems.length) {
      fail('unknown-criterion', section, `Criterion AC${index} exceeds the ${storyItems.length} criteria in the Story.`, extra);
    }
    return { id: `AC${index}`, index };
  }
  const acMatch = /^ac-?([1-9][0-9]*)$/i.exec(trimmed);
  if (acMatch) {
    const index = Number(acMatch[1]);
    if (storyItems.length && index > storyItems.length) {
      fail('unknown-criterion', section, `Criterion AC${index} exceeds the ${storyItems.length} criteria in the Story.`, extra);
    }
    return { id: `AC${index}`, index };
  }
  return { id: trimmed, index: 0 };
}

function mergePatch(target, patch) {
  if (!isPlainObject(patch)) return cloneExact(patch);
  const result = isPlainObject(target) ? cloneExact(target) : {};
  for (const key of Object.keys(patch)) {
    const val = patch[key];
    if (val === null) {
      delete result[key];
    } else {
      result[key] = mergePatch(result[key], val);
    }
  }
  return result;
}

function decodePointerTokens(pointer, section, extra) {
  if (typeof pointer !== 'string' || (pointer !== '' && !pointer.startsWith('/'))) {
    fail('invalid-seed', section, `Invalid JSON Pointer "${String(pointer)}"; pointers must be "" or start with "/".`, extra);
  }
  if (pointer === '') return [];
  return pointer
    .slice(1)
    .split('/')
    .map(part => {
      if (/~(?![01])/.test(part)) {
        fail('invalid-seed', section, `Invalid JSON Pointer escape in "${pointer}".`, extra);
      }
      return part.replaceAll('~1', '/').replaceAll('~0', '~');
    });
}

function applyPointerSet(base, setMap, section, extra) {
  if (!isPlainObject(setMap)) {
    fail('invalid-seed', section, '"set" overrides must be a JSON object mapping JSON Pointers to values.', extra);
  }
  let current = cloneExact(base);
  for (const rawPointer of Object.keys(setMap)) {
    const tokens = decodePointerTokens(rawPointer, section, extra);
    const replacement = cloneExact(setMap[rawPointer]);
    if (!tokens.length) {
      current = replacement;
      continue;
    }
    let holder = current;
    for (const token of tokens.slice(0, -1)) {
      if (Array.isArray(holder)) {
        const idx = /^[0-9]+$/.test(token) ? Number(token) : -1;
        if (idx < 0 || idx >= holder.length) {
          fail('invalid-seed', section, `JSON Pointer "${rawPointer}" index "${token}" is out of bounds.`, extra);
        }
        holder = holder[idx];
      } else if (isPlainObject(holder)) {
        if (!Object.hasOwn(holder, token) || (!isPlainObject(holder[token]) && !Array.isArray(holder[token]))) {
          holder[token] = {};
        }
        holder = holder[token];
      } else {
        fail('invalid-seed', section, `JSON Pointer "${rawPointer}" cannot traverse scalar at "${token}".`, extra);
      }
    }
    const last = tokens.at(-1);
    if (Array.isArray(holder)) {
      if (last === '-') {
        holder.push(replacement);
      } else {
        const idx = /^[0-9]+$/.test(last) ? Number(last) : -1;
        if (idx < 0 || idx > holder.length) {
          fail('invalid-seed', section, `JSON Pointer "${rawPointer}" array index "${last}" is out of bounds.`, extra);
        }
        holder[idx] = replacement;
      }
    } else if (isPlainObject(holder)) {
      holder[last] = replacement;
    } else {
      fail('invalid-seed', section, `JSON Pointer "${rawPointer}" target parent is not an object or array.`, extra);
    }
  }
  return current;
}

function parseHtmlSelector(spec, section, extra) {
  if (isPlainObject(spec)) {
    if (typeof spec.tag !== 'string' || !/^[a-z][a-z0-9-]*$/.test(spec.tag)) {
      fail('invalid-check', section, 'HTML selector object requires a lowercase "tag" name.', extra);
    }
    return cloneExact(spec);
  }
  if (typeof spec !== 'string' || !spec.trim()) {
    fail('invalid-check', section, 'HTML selector must be a tag string (such as "button" or "button#start") or selector object.', extra);
  }
  let rest = spec.trim();
  const tagMatch = /^([a-zA-Z][a-zA-Z0-9-]*)/.exec(rest);
  if (!tagMatch) {
    fail('invalid-check', section, `HTML selector "${spec}" needs a tag name, such as "button${spec.startsWith('#') ? spec : '#id'}".`, extra);
  }
  const tag = tagMatch[1].toLowerCase();
  rest = rest.slice(tagMatch[0].length);
  const attributes = {};
  while (rest.length) {
    if (rest.startsWith('#')) {
      const idMatch = /^#([A-Za-z0-9_:-]+)/.exec(rest);
      if (!idMatch) fail('invalid-check', section, `Invalid #id in HTML selector "${spec}".`, extra);
      attributes.id = idMatch[1];
      rest = rest.slice(idMatch[0].length);
      continue;
    }
    if (rest.startsWith('.')) {
      const clsMatch = /^\.([A-Za-z0-9_:-]+)/.exec(rest);
      if (!clsMatch) fail('invalid-check', section, `Invalid .class in HTML selector "${spec}".`, extra);
      attributes.class = attributes.class ? `${attributes.class} ${clsMatch[1]}` : clsMatch[1];
      rest = rest.slice(clsMatch[0].length);
      continue;
    }
    if (rest.startsWith('[')) {
      const attrMatch = /^\[([a-zA-Z_:][a-zA-Z0-9_.:-]*)=("([^"]*)"|'([^']*)'|([^\]]*))\]/.exec(rest);
      if (!attrMatch) fail('invalid-check', section, `Invalid [attr=value] in HTML selector "${spec}".`, extra);
      attributes[attrMatch[1]] = attrMatch[3] ?? attrMatch[4] ?? attrMatch[5] ?? '';
      rest = rest.slice(attrMatch[0].length);
      continue;
    }
    fail('invalid-check', section, `Unsupported HTML selector syntax "${rest}" in "${spec}". Use tag, tag#id, or tag[attr=val].`, extra);
  }
  return Object.keys(attributes).length ? { tag, attributes } : { tag };
}

function normalizeOp(rawOp, section, extra) {
  if (typeof rawOp !== 'string' || !rawOp) {
    fail('invalid-check', section, `Check operator must be a nonblank string, got ${JSON.stringify(rawOp)}.`, extra);
  }
  if (OP_ALIASES.has(rawOp)) return OP_ALIASES.get(rawOp);
  if (CANONICAL_OPS.has(rawOp)) {
    if (rawOp === 'at_least' || rawOp === 'at_most') return { op: rawOp, measure: 'value' };
    return { op: rawOp };
  }
  fail(
    'invalid-check',
    section,
    `Unknown check operator "${rawOp}". Allowed operators: =, !=, >=, <=, len>=, len<=, equals, not_equals, contains, not_contains, contains_all, count, exists, one_of, all_in, equals_ignore_case, at_least, at_most.`,
    extra,
  );
}

function normalizeCallsPath(rawPath, entryPath, section, extra) {
  if (typeof rawPath !== 'string' || !rawPath.trim()) {
    fail('invalid-check', section, 'A calls check needs a nonblank path such as "/resources/node-store-save" or "store.save".', extra);
  }
  const path = rawPath.trim();
  if (path.startsWith('/')) return path;
  if (path.startsWith('internal:')) {
    const node = path.slice('internal:'.length).trim();
    if (!node) fail('invalid-check', section, `Invalid internal call target "${rawPath}".`, extra);
    return `/internal/${node}`;
  }
  const parts = path.split('.');
  if (parts.length === 3 && parts.every(Boolean)) {
    return `/resources/${parts[0]}-${parts[1]}-${parts[2]}`;
  }
  if (parts.length === 2 && parts.every(Boolean)) {
    const node = typeof entryPath === 'string' && entryPath.endsWith('.prompt.md')
      ? basename(entryPath, '.prompt.md')
      : null;
    if (!node) {
      fail('invalid-check', section, `Cannot infer prompt node for calls shorthand "${rawPath}" without a .prompt.md entry_path.`, extra);
    }
    return `/resources/${node}-${parts[0]}-${parts[1]}`;
  }
  fail(
    'invalid-check',
    section,
    `Invalid calls path "${rawPath}". Use "/resources/<node>-<resource>-<op>", "/internal/<node>", "<resource>.<op>", or "internal:<node>".`,
    extra,
  );
}

function expandTupleChecks(tuple, criterionId, entryPath, section, extra, expandVal) {
  if (!Array.isArray(tuple) || tuple.length < 2) {
    fail('invalid-check', section, 'A Short JSON check tuple needs at least 2 items.', extra);
  }
  const head = tuple[0];
  if (head === 'error' && tuple.length === 3) {
    const { op } = normalizeOp(tuple[1], section, extra);
    return [{
      criterion_id: criterionId,
      target: 'error',
      path: '/code',
      op,
      value: expandVal(tuple[2], `${section}[2]`),
    }];
  }
  if (head === 'html_exists') {
    if (tuple.length < 2 || tuple.length > 4) {
      fail('invalid-check', section, 'html_exists tuple takes ["html_exists", selector, boolValue?, htmlPath?].', extra);
    }
    const selector = parseHtmlSelector(tuple[1], section, extra);
    const boolVal = tuple.length >= 3 ? Boolean(tuple[2]) : true;
    const htmlPath = tuple.length === 4 ? tuple[3] : '/html';
    if (typeof htmlPath !== 'string' || !htmlPath.startsWith('/')) {
      fail('invalid-check', section, 'htmlPath in html_exists must be a JSON Pointer such as "/html".', extra);
    }
    return [{
      criterion_id: criterionId,
      target: 'result',
      path: htmlPath,
      op: 'exists',
      value: boolVal,
      html: { selector, kind: 'element' },
    }];
  }
  if (head === 'html_text') {
    if (tuple.length < 3 || tuple.length > 5) {
      fail('invalid-check', section, 'html_text tuple takes ["html_text", selector, op, value?, htmlPath?].', extra);
    }
    const selector = parseHtmlSelector(tuple[1], section, extra);
    const { op } = normalizeOp(tuple[2], section, extra);
    const value = tuple.length >= 4 ? expandVal(tuple[3], `${section}[3]`) : true;
    const htmlPath = tuple.length === 5 ? tuple[4] : '/html';
    return [{
      criterion_id: criterionId,
      target: 'result',
      path: htmlPath,
      op,
      value,
      html: { selector, kind: 'text' },
    }];
  }
  if (head === 'html_attr') {
    if (tuple.length < 4 || tuple.length > 6) {
      fail('invalid-check', section, 'html_attr tuple takes ["html_attr", selector, attribute, op, value?, htmlPath?].', extra);
    }
    const selector = parseHtmlSelector(tuple[1], section, extra);
    const attribute = tuple[2];
    if (typeof attribute !== 'string' || !attribute.trim()) {
      fail('invalid-check', section, 'html_attr requires a nonblank attribute name.', extra);
    }
    const { op } = normalizeOp(tuple[3], section, extra);
    const value = tuple.length >= 5 ? expandVal(tuple[4], `${section}[4]`) : true;
    const htmlPath = tuple.length === 6 ? tuple[5] : '/html';
    return [{
      criterion_id: criterionId,
      target: 'result',
      path: htmlPath,
      op,
      value,
      html: { selector, kind: 'attribute', attribute },
    }];
  }
  if (head === 'html') {
    if (tuple.length < 4 || tuple.length > 5 || tuple[2] !== 'labels_include') {
      fail('invalid-check', section, 'html helper tuple takes ["html", selector, "labels_include", ["Label1", ...], htmlPath?].', extra);
    }
    const selector = parseHtmlSelector(tuple[1], section, extra);
    const labels = expandVal(tuple[3], `${section}[3]`);
    const htmlPath = tuple.length === 5 ? tuple[4] : '/html';
    if (!Array.isArray(labels) || !labels.length || labels.some(item => typeof item !== 'string' || !item.length)) {
      fail('invalid-check', section, 'labels_include requires a nonempty array of nonempty strings.', extra);
    }
    return [
      {
        criterion_id: criterionId,
        target: 'result',
        path: htmlPath,
        op: 'exists',
        value: true,
        html: { selector, kind: 'element' },
      },
      ...labels.map(label => ({
        criterion_id: criterionId,
        target: 'result',
        path: htmlPath,
        op: 'contains',
        value: label,
      })),
    ];
  }

  if (!TARGETS.has(head)) {
    fail(
      'invalid-check',
      section,
      `Unknown check target "${String(head)}". Allowed targets: result, world, calls, error, html, html_exists, html_text, html_attr.`,
      extra,
    );
  }
  if (tuple.length < 3 || tuple.length > 4) {
    fail('invalid-check', section, `Check tuple for "${head}" takes [${JSON.stringify(head)}, path, op, value].`, extra);
  }
  const rawPath = tuple[1];
  const rawOp = tuple[2];
  const path = head === 'calls' ? normalizeCallsPath(rawPath, entryPath, section, extra) : rawPath;
  if (typeof path !== 'string' || (path !== '' && !path.startsWith('/'))) {
    fail('invalid-check', section, `Check path "${String(path)}" must be "" or a JSON Pointer starting with "/".`, extra);
  }

  if (rawOp === 'contains_all' || rawOp === 'includes_all') {
    if (head !== 'result' && head !== 'world') {
      fail('invalid-check', section, `${rawOp} is supported only on "result" or "world" string paths.`, extra);
    }
    if (tuple.length !== 4) {
      fail('invalid-check', section, `${rawOp} requires an array of substrings as its 4th element.`, extra);
    }
    const items = expandVal(tuple[3], `${section}[3]`);
    if (!Array.isArray(items) || !items.length || items.some(item => typeof item !== 'string' || !item.length)) {
      fail('invalid-check', section, `${rawOp} requires a nonempty array of nonempty strings.`, extra);
    }
    return items.map(sub => ({
      criterion_id: criterionId,
      target: head,
      path,
      op: 'contains',
      value: sub,
    }));
  }

  const { op, measure } = normalizeOp(rawOp, section, extra);
  if (op === 'exists' && tuple.length === 3) {
    return [{ criterion_id: criterionId, target: head, path, op: 'exists', value: true }];
  }
  if (tuple.length !== 4) {
    fail('invalid-check', section, `Operator "${op}" requires a 4th expected value in check tuple.`, extra);
  }
  const value = expandVal(tuple[3], `${section}[3]`);
  return [{
    criterion_id: criterionId,
    target: head,
    path,
    op,
    ...(measure ? { measure } : {}),
    value,
  }];
}

export function compileScenario(doc, { path = 'tests/story.json', storyPath = null, storySource = null } = {}) {
  if (!isPlainObject(doc) || !isShortScenarioDoc(doc)) {
    return { doc, changed: false, refusal: null };
  }
  try {
    const unknownTop = Object.keys(doc).filter(key => !ALLOWED_TOP_KEYS.has(key));
    if (unknownTop.length) {
      fail('invalid-document', 'scenario', `${path} has unknown top-level keys: ${unknownTop.map(k => `"${k}"`).join(', ')}.`);
    }
    if (
      Object.hasOwn(doc, 'schema_version') &&
      doc.schema_version !== V1_SCENARIO_SCHEMA &&
      doc.schema_version !== SHORT_SCENARIO_SCHEMA
    ) {
      fail('invalid-document', 'schema_version', `schema_version must be "${V1_SCENARIO_SCHEMA}" or "${SHORT_SCENARIO_SCHEMA}".`);
    }
    const effectiveStoryPath = Object.hasOwn(doc, 'story_path') ? doc.story_path : storyPath;
    if (Object.hasOwn(doc, 'entry_path') && (typeof doc.entry_path !== 'string' || !doc.entry_path.trim())) {
      fail('invalid-document', 'entry_path', 'Top-level "entry_path" must be a nonblank prompt path string.');
    }
    const defaultEntryPath = typeof doc.entry_path === 'string'
      ? doc.entry_path
      : Array.isArray(doc.entry_paths) && doc.entry_paths.length === 1 && typeof doc.entry_paths[0] === 'string'
        ? doc.entry_paths[0]
        : null;

    if (Object.hasOwn(doc, 'seeds') && !isPlainObject(doc.seeds)) {
      fail('invalid-seed', 'seeds', 'Top-level "seeds" must be a JSON object mapping seed names to values.');
    }
    const rawSeeds = isPlainObject(doc.seeds) ? doc.seeds : {};
    const resolvedSeeds = new Map();
    const stepInputs = new Map();

    function resolveSeed(name, chain, section, extra) {
      const cleanName = name.startsWith('$seed.') ? name.slice('$seed.'.length) : name;
      if (!Object.hasOwn(rawSeeds, cleanName)) {
        fail('invalid-seed', section, `Unknown seed "${name}". Declared seeds: ${Object.keys(rawSeeds).join(', ') || '(none)'}.`, extra);
      }
      if (resolvedSeeds.has(cleanName)) return cloneExact(resolvedSeeds.get(cleanName));
      if (chain.includes(cleanName)) {
        fail('seed-cycle', section, `Seed reference cycle: ${[...chain, cleanName].join(' -> ')}.`, extra);
      }
      const expanded = expandValue(rawSeeds[cleanName], `seeds.${cleanName}`, [...chain, cleanName], extra);
      resolvedSeeds.set(cleanName, expanded);
      return cloneExact(expanded);
    }

    function resolveBaseRef(ref, chain, section, extra) {
      if (typeof ref !== 'string' || !ref.trim()) {
        fail('invalid-seed', section, 'Reference target must be a nonblank seed or step name.', extra);
      }
      if (ref.startsWith('step:')) {
        const stepId = ref.slice('step:'.length);
        if (!stepInputs.has(stepId)) {
          fail('invalid-seed', section, `Unknown earlier step "${stepId}" in "${ref}".`, extra);
        }
        return cloneExact(stepInputs.get(stepId));
      }
      if (ref.startsWith('$seed.')) {
        return resolveSeed(ref, chain, section, extra);
      }
      if (Object.hasOwn(rawSeeds, ref)) {
        return resolveSeed(ref, chain, section, extra);
      }
      if (stepInputs.has(ref)) {
        return cloneExact(stepInputs.get(ref));
      }
      fail('invalid-seed', section, `Unknown seed or earlier step "${ref}".`, extra);
    }

    function expandValue(value, section, chain = [], extra = {}) {
      if (Array.isArray(value)) {
        return value.map((item, idx) => expandValue(item, `${section}[${idx}]`, chain, extra));
      }
      if (!isPlainObject(value)) return value;

      if (Object.hasOwn(value, '$json')) {
        if (Object.keys(value).length !== 1) {
          fail('invalid-seed', section, '"$json" macro cannot have sibling keys.', extra);
        }
        const inner = expandValue(value.$json, `${section}.$json`, chain, extra);
        return stringifyExactScenarioJson(inner);
      }

      if (Object.hasOwn(value, '$step')) {
        if (Object.keys(value).length !== 1) {
          fail('invalid-step-ref', section, '"$step" macro cannot have sibling keys.', extra);
        }
        const spec = value.$step;
        if (typeof spec === 'string' && spec.trim()) {
          const hash = spec.indexOf('#');
          const stepId = hash < 0 ? spec : spec.slice(0, hash);
          const ptr = hash < 0 ? '' : spec.slice(hash + 1);
          if (!stepId || (ptr !== '' && !ptr.startsWith('/'))) {
            fail('invalid-step-ref', section, `Invalid "$step" reference "${spec}". Use "<step_id>" or "<step_id>#/pointer".`, extra);
          }
          return { $step_result: { step_id: stepId, path: ptr } };
        }
        if (Array.isArray(spec) && spec.length === 2 && typeof spec[0] === 'string' && spec[0] && typeof spec[1] === 'string') {
          if (spec[1] !== '' && !spec[1].startsWith('/')) {
            fail('invalid-step-ref', section, `Invalid "$step" pointer "${spec[1]}".`, extra);
          }
          return { $step_result: { step_id: spec[0], path: spec[1] } };
        }
        fail('invalid-step-ref', section, '"$step" must be "<step_id>", "<step_id>#/pointer", or ["<step_id>", "/pointer"].', extra);
      }

      const macroKey = Object.hasOwn(value, '$use')
        ? '$use'
        : Object.hasOwn(value, '$from')
          ? '$from'
          : Object.hasOwn(value, '$seed') && typeof value.$seed === 'string' && Object.hasOwn(rawSeeds, value.$seed)
            ? '$seed'
            : null;

      if (macroKey) {
        const extraKeys = Object.keys(value).filter(k => k !== macroKey && k !== 'patch' && k !== 'set');
        if (extraKeys.length) {
          fail('invalid-seed', section, `"${macroKey}" allows only optional "patch" and "set" sibling keys (found ${extraKeys.map(k => `"${k}"`).join(', ')}).`, extra);
        }
        let current = resolveBaseRef(value[macroKey], chain, section, extra);
        if (Object.hasOwn(value, 'patch')) {
          const expandedPatch = expandValue(value.patch, `${section}.patch`, chain, extra);
          current = mergePatch(current, expandedPatch);
        }
        if (Object.hasOwn(value, 'set')) {
          const expandedSet = expandValue(value.set, `${section}.set`, chain, extra);
          current = applyPointerSet(current, expandedSet, `${section}.set`, extra);
        }
        return current;
      }

      const out = {};
      for (const key of Object.keys(value)) {
        out[key] = expandValue(value[key], `${section}.${key}`, chain, extra);
      }
      return out;
    }

    const storyItems = extractStoryCriteria(storySource);
    let compiledCriteria;
    let hasExplicitCriteria = Object.hasOwn(doc, 'criteria');

    if (!hasExplicitCriteria) {
      if (storyItems.length) {
        compiledCriteria = storyItems.map((text, idx) => ({ id: `AC${idx + 1}`, text }));
        hasExplicitCriteria = true;
      }
    } else {
      if (!Array.isArray(doc.criteria) || !doc.criteria.length) {
        fail('invalid-criterion', 'criteria', 'The test has no criteria.');
      }
      const seenIds = new Set();
      compiledCriteria = doc.criteria.map((item, idx) => {
        const section = `criteria[${idx}]`;
        if (isPlainObject(item) && typeof item.text === 'string' && item.text && Object.keys(item).length === 2 && Object.hasOwn(item, 'id')) {
          const { id } = parseCriterionSpec(item.id, storyItems, section);
          if (seenIds.has(id)) fail('duplicate-criterion', section, `The criterion ID ${id} is used twice.`);
          seenIds.add(id);
          return { id, text: item.text };
        }
        const rawRef = isPlainObject(item) && Object.keys(item).length === 1 && Object.hasOwn(item, 'id') ? item.id : item;
        const { id, index } = parseCriterionSpec(rawRef, storyItems, section);
        if (seenIds.has(id)) fail('duplicate-criterion', section, `The criterion ID ${id} is used twice.`);
        seenIds.add(id);
        if (!storyItems.length) {
          return id;
        }
        if (!index || index > storyItems.length) {
          fail('invalid-criterion', section, `Criterion "${String(rawRef)}" does not match numbered item 1..${storyItems.length} in ${effectiveStoryPath ?? 'the Story'}.`);
        }
        return { id, text: storyItems[index - 1] };
      });
    }

    if (!Array.isArray(doc.steps) || !doc.steps.length) {
      fail('missing-steps', 'steps', 'The test has no steps.');
    }

    const compiledSteps = doc.steps.map((step, index) => {
      const section = `steps[${index}]`;
      const at = { step: index + 1 };
      if (!isPlainObject(step)) {
        fail('invalid-step', section, 'A step must be a JSON object.', at);
      }
      const unknownStepKeys = Object.keys(step).filter(k => !ALLOWED_STEP_KEYS.has(k));
      if (unknownStepKeys.length) {
        fail('invalid-step', section, `Step has unknown keys: ${unknownStepKeys.map(k => `"${k}"`).join(', ')}.`, at);
      }
      if (Object.hasOwn(step, 'step_id') && Object.hasOwn(step, 'id') && step.step_id !== step.id) {
        fail('invalid-step', section, 'Step specifies conflicting "step_id" and "id".', at);
      }
      if (Object.hasOwn(step, 'operation') && Object.hasOwn(step, 'op') && step.operation !== step.op) {
        fail('invalid-step', section, 'Step specifies conflicting "operation" and "op".', at);
      }
      const normalizeErrSpec = val =>
        isPlainObject(val) && Object.keys(val).length === 1 && typeof val.code === 'string' && val.code.trim()
          ? val.code
          : val;
      const normExpectedErr = normalizeErrSpec(step.expected_error);
      const normErr = normalizeErrSpec(step.error);
      if (Object.hasOwn(step, 'expected_error') && Object.hasOwn(step, 'error') && normExpectedErr !== normErr) {
        fail('invalid-step', section, 'Step specifies conflicting "expected_error" and "error".', at);
      }
      if (Object.hasOwn(step, 'from') && Object.hasOwn(step, 'input')) {
        fail('invalid-step', section, 'Step cannot specify both "from" and "input"; put "patch" alongside "from".', at);
      }

      const stepId = step.step_id ?? step.id ?? `step-${index + 1}`;
      const entryPath = step.entry_path ?? defaultEntryPath;
      const operation = step.operation ?? step.op;
      if (typeof stepId !== 'string' || !stepId.trim()) {
        fail('invalid-step', `${section}.step_id`, 'Step "step_id" must be a nonblank string.', at);
      }
      if (typeof entryPath !== 'string' || !entryPath.trim()) {
        fail('invalid-step', `${section}.entry_path`, 'Step has no "entry_path" (set step "entry_path" or top-level "entry_path").', at);
      }
      if (typeof operation !== 'string' || !operation.trim()) {
        fail('invalid-step', `${section}.operation`, 'Step has no "operation" (or "op").', at);
      }

      let stepInput;
      if (Object.hasOwn(step, 'from')) {
        stepInput = resolveBaseRef(step.from, [], `${section}.from`, at);
      } else if (Object.hasOwn(step, 'input')) {
        stepInput = expandValue(step.input, `${section}.input`, [], at);
      } else {
        stepInput = {};
      }
      if (Object.hasOwn(step, 'patch')) {
        const expandedPatch = expandValue(step.patch, `${section}.patch`, [], at);
        stepInput = mergePatch(stepInput, expandedPatch);
      }
      if (Object.hasOwn(step, 'set')) {
        const expandedSet = expandValue(step.set, `${section}.set`, [], at);
        stepInput = applyPointerSet(stepInput, expandedSet, `${section}.set`, at);
      }
      stepInputs.set(stepId, cloneExact(stepInput));

      const expandCheckItem = (item, criterionId, checkSection) => {
        if (Array.isArray(item)) {
          return expandTupleChecks(item, criterionId, entryPath, checkSection, at, (val, subSec) => expandValue(val, subSec, [], at));
        }
        if (!isPlainObject(item)) {
          fail('invalid-check', checkSection, 'Each check must be an object or tuple array.', at);
        }
        const rawCid = item.criterion_id ?? criterionId;
        if (rawCid === undefined) {
          fail('invalid-check', checkSection, 'Check is missing "criterion_id".', at);
        }
        const normCid = parseCriterionSpec(rawCid, storyItems, checkSection, at).id;
        const norm = Object.hasOwn(item, 'op') ? normalizeOp(item.op, checkSection, at) : { op: item.op };
        const outCheck = { ...expandValue(item, checkSection, [], at), criterion_id: normCid, op: norm.op };
        if ((outCheck.op === 'at_least' || outCheck.op === 'at_most') && !Object.hasOwn(outCheck, 'measure')) {
          outCheck.measure = norm.measure ?? 'value';
        }
        return [outCheck];
      };

      const compiledChecks = [];
      if (isPlainObject(step.checks)) {
        for (const [rawCritKey, rawGroup] of Object.entries(step.checks)) {
          const groupSec = `${section}.checks[${JSON.stringify(rawCritKey)}]`;
          const { id: critId } = parseCriterionSpec(rawCritKey, storyItems, groupSec, at);
          if (!Array.isArray(rawGroup)) {
            fail('invalid-check', groupSec, `Checks for "${rawCritKey}" must be a list of check tuples or check objects.`, at);
          }
          const items = rawGroup.length > 0 && typeof rawGroup[0] === 'string' ? [rawGroup] : rawGroup;
          items.forEach((item, cIdx) => {
            compiledChecks.push(...expandCheckItem(item, critId, `${groupSec}[${cIdx}]`));
          });
        }
      } else if (Array.isArray(step.checks)) {
        step.checks.forEach((item, cIdx) => {
          const checkSec = `${section}.checks[${cIdx}]`;
          if (Array.isArray(item)) {
            if (item.length < 3) {
              fail('invalid-check', checkSec, 'A tuple inside array "checks" must start with criterion ID: [criterion, target, ...].', at);
            }
            const { id: critId } = parseCriterionSpec(item[0], storyItems, `${checkSec}[0]`, at);
            compiledChecks.push(...expandTupleChecks(item.slice(1), critId, entryPath, checkSec, at, (val, subSec) => expandValue(val, subSec, [], at)));
          } else {
            compiledChecks.push(...expandCheckItem(item, undefined, checkSec));
          }
        });
      } else {
        fail('invalid-check', `${section}.checks`, 'Step "checks" must be an array or a criterion-keyed object.', at);
      }

      let hasExpectedError = Object.hasOwn(step, 'expected_error') || Object.hasOwn(step, 'error');
      let resolvedExpectedError = normExpectedErr ?? normErr;
      if (!hasExpectedError) {
        const inferredErrorCodes = [
          ...new Set(
            compiledChecks
              .filter(
                chk =>
                  isPlainObject(chk) &&
                  chk.target === 'error' &&
                  chk.path === '/code' &&
                  chk.op === 'equals' &&
                  typeof chk.value === 'string' &&
                  chk.value.trim().length > 0,
              )
              .map(chk => chk.value),
          ),
        ];
        if (inferredErrorCodes.length === 1) {
          hasExpectedError = true;
          resolvedExpectedError = inferredErrorCodes[0];
        }
      }

      const outStep = {
        step_id: stepId,
        entry_path: entryPath,
        operation,
        input: stepInput,
        ...(hasExpectedError ? { expected_error: resolvedExpectedError } : {}),
        ...(Object.hasOwn(step, 'simulation_overrides')
          ? { simulation_overrides: expandValue(step.simulation_overrides, `${section}.simulation_overrides`, [], at) }
          : {}),
        ...(Object.hasOwn(step, 'model') ? { model: step.model } : {}),
        checks: compiledChecks,
      };
      return outStep;
    });

    const outDoc = {
      schema_version: V1_SCENARIO_SCHEMA,
      ...(typeof effectiveStoryPath === 'string' && effectiveStoryPath ? { story_path: effectiveStoryPath } : {}),
      ...(hasExplicitCriteria && compiledCriteria !== undefined ? { criteria: compiledCriteria } : {}),
      initial_world: Object.hasOwn(doc, 'initial_world')
        ? expandValue(doc.initial_world, 'initial_world')
        : {},
    };

    for (const key of Object.keys(doc)) {
      if (['schema_version', 'story_path', 'criteria', 'initial_world', 'steps', 'seeds', 'entry_path'].includes(key)) {
        continue;
      }
      if (key === 'simulation') {
        outDoc.simulation = expandValue(doc.simulation, 'simulation');
      } else {
        outDoc[key] = cloneExact(doc[key]);
      }
    }
    outDoc.steps = compiledSteps;

    return { doc: outDoc, changed: true, refusal: null };
  } catch (error) {
    if (error instanceof CompileAbort) {
      return { doc, changed: false, refusal: error.issue };
    }
    throw error;
  }
}

export function compileScenarioText(text, { path = 'tests/story.json', storyPath = null, storySource = null, space = 2 } = {}) {
  const exactParsed = parseExactScenarioJson(text);
  const compiled = compileScenario(exactParsed, { path, storyPath, storySource });
  if (compiled.refusal || !compiled.changed) {
    return {
      text,
      doc: jsonSafeScenario(exactParsed),
      exactDoc: exactParsed,
      changed: false,
      refusal: compiled.refusal,
    };
  }
  const outText = `${stringifyExactScenarioJson(compiled.doc, space)}\n`;
  return {
    text: outText,
    doc: jsonSafeScenario(compiled.doc),
    exactDoc: compiled.doc,
    changed: true,
    refusal: null,
  };
}
