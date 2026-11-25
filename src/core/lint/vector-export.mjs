// Prompt: prompts/cli/vector-export.prompt.md

// Offline Formal-to-Vector Short JSON exporter for pdd.formal-vectors.v1 specs and Quint ITF traces.
import { execFileSync } from 'node:child_process';
import { lstatSync, mkdirSync, readFileSync, realpathSync, writeFileSync } from 'node:fs';
import { dirname, isAbsolute, join, relative, resolve, sep } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import {
  compileScenario,
  parseExactScenarioJson,
  stringifyExactScenarioJson,
} from '../../scenario-compile.mjs';
import { canonicalRepoPath, readSafeUtf8 } from './diagnostics.mjs';
import { DEFAULT_SCENARIO_MAX_STEPS, evaluateScenarioHygiene } from './scenario-hygiene.mjs';

export const FORMAL_VECTORS_SCHEMA = 'pdd.formal-vectors.v1';
export const FORMAL_EXPORT_RESULT_SCHEMA = 'pdd.formal-vectors-export.v1';
export const DEFAULT_EXPORT_MAX_STEPS = DEFAULT_SCENARIO_MAX_STEPS;

const ALLOWED_SPEC_KEYS = new Set([
  'schema_version', 'story_path', 'entry_path', 'default_op', 'default_criterion',
  'initial_world', 'simulation', 'seeds', 'cases',
]);
const ALLOWED_CASE_KEYS = new Set([
  'id', 'op', 'entry_path', 'criterion', 'input', 'from', 'patch', 'set',
  'error', 'expect', 'expect_world', 'checks',
]);
const ITF_META_STATE_KEYS = new Set(['#meta', 'action', 'op', 'input', 'result', 'error']);
const EXACT_INTEGER_RE = /^-?(?:0|[1-9][0-9]*)$/;

const isPlainObject = value => {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return false;
  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
};

function setOwn(obj, key, value) {
  if (key === '__proto__') {
    Object.defineProperty(obj, key, { value, enumerable: true, writable: true, configurable: true });
  } else {
    obj[key] = value;
  }
  return obj;
}

const cloneExact = value => {
  if (Array.isArray(value)) return value.map(cloneExact);
  if (isPlainObject(value)) {
    const out = {};
    for (const key of Object.keys(value)) setOwn(out, key, cloneExact(value[key]));
    return out;
  }
  return value;
};

function makeRefusal(code, section, message, hint = 'Fix the formal vector input and rerun `pdd vector export`.') {
  return { ok: false, refusal: { code, section, message, hint } };
}

function isValidPointer(ptr) {
  return typeof ptr === 'string' && ptr.startsWith('/') && !/~(?![01])/.test(ptr);
}

function encodePointerToken(key) {
  return String(key).replaceAll('~', '~0').replaceAll('/', '~1');
}

function parseExactBigIntText(raw) {
  const s = String(raw).trim();
  if (!EXACT_INTEGER_RE.test(s)) return null;
  const num = Number(s);
  if (Number.isSafeInteger(num) && String(num) === s) return num;
  return BigInt(s);
}

export function normalizeItfValue(value) {
  if (Array.isArray(value)) return value.map(normalizeItfValue);
  if (!isPlainObject(value)) return value;
  const keys = Object.keys(value);
  if (keys.length === 1 && keys[0] === '#bigint' && typeof value['#bigint'] === 'string') {
    const parsed = parseExactBigIntText(value['#bigint']);
    return parsed !== null ? parsed : value['#bigint'];
  }
  if (keys.length === 1 && keys[0] === '#tup' && Array.isArray(value['#tup'])) {
    return value['#tup'].map(normalizeItfValue);
  }
  if (keys.length === 1 && keys[0] === '#set' && Array.isArray(value['#set'])) {
    return value['#set'].map(normalizeItfValue);
  }
  if (keys.length === 1 && keys[0] === '#map' && Array.isArray(value['#map'])) {
    const pairs = value['#map'];
    if (pairs.every(pair => Array.isArray(pair) && pair.length === 2 && typeof pair[0] === 'string')) {
      const mapped = {};
      for (const [k, v] of pairs) setOwn(mapped, k, normalizeItfValue(v));
      return mapped;
    }
    return pairs.map(normalizeItfValue);
  }
  const out = {};
  for (const key of keys) {
    if (key === '#meta') continue;
    setOwn(out, key, normalizeItfValue(value[key]));
  }
  return out;
}

function isItfTraceDoc(doc) {
  if (!isPlainObject(doc) || !Array.isArray(doc.states)) return false;
  if (Object.hasOwn(doc, '#meta')) return true;
  return doc.states.some(s => isPlainObject(s) && Object.hasOwn(s, '#meta'));
}

export function convertItfTrace(
  itfDoc,
  { storyPath = null, entryPath = null, defaultOp = null, defaultCriterion = '1', initialWorld = null, simulation = null } = {},
) {
  if (!isItfTraceDoc(itfDoc)) {
    return makeRefusal('invalid-itf', 'states', 'Input is not a Quint/Apalache ITF trace object with "#meta" and "states".');
  }
  if (itfDoc.states.length < 2) {
    return makeRefusal('invalid-itf', 'states', 'ITF trace requires at least 2 states (initial state 0 plus >= 1 transition state).');
  }
  const states = itfDoc.states.map(s => (isPlainObject(s) ? normalizeItfValue(s) : null));
  if (states.some(s => !isPlainObject(s))) {
    return makeRefusal('invalid-itf', 'states', 'Every ITF trace state must be a JSON object.');
  }

  const state0 = states[0];
  const derivedWorld = {};
  for (const key of Object.keys(state0)) {
    if (!ITF_META_STATE_KEYS.has(key)) setOwn(derivedWorld, key, cloneExact(state0[key]));
  }
  const world = isPlainObject(initialWorld) ? cloneExact(initialWorld) : derivedWorld;

  const cases = [];
  for (let i = 1; i < states.length; i++) {
    const prev = states[i - 1];
    const cur = states[i];
    if (cur.action !== undefined && (typeof cur.action !== 'string' || !cur.action.trim())) {
      return makeRefusal('invalid-itf', `states[${i}].action`, `ITF transition state ${i} "action" must be a nonblank string when provided.`);
    }
    if (cur.op !== undefined && (typeof cur.op !== 'string' || !cur.op.trim())) {
      return makeRefusal('invalid-itf', `states[${i}].op`, `ITF transition state ${i} "op" must be a nonblank string when provided.`);
    }
    if (cur.input !== undefined && !isPlainObject(cur.input)) {
      return makeRefusal('invalid-itf', `states[${i}].input`, `ITF transition state ${i} "input" must be a JSON object when provided.`);
    }
    const op = typeof cur.action === 'string'
      ? cur.action.trim()
      : (typeof cur.op === 'string'
        ? cur.op.trim()
        : (typeof defaultOp === 'string' && defaultOp.trim() ? defaultOp.trim() : null));
    if (!op) {
      return makeRefusal(
        'missing-operation',
        `states[${i}]`,
        `ITF transition state ${i} has no "action" or "op" field and no --op fallback was provided.`,
        'Pass --op <operation> or include an "action" field on each transition state.',
      );
    }
    const input = cur.input !== undefined ? cloneExact(cur.input) : {};
    const stepCase = {
      id: `case-${i}`,
      op,
      criterion: String(defaultCriterion ?? '1'),
      input,
    };
    if (typeof cur.error === 'string' && cur.error.trim()) {
      stepCase.error = cur.error.trim();
    } else if (isPlainObject(cur.result) && Object.keys(cur.result).length > 0) {
      const expect = {};
      for (const k of Object.keys(cur.result)) {
        setOwn(expect, `/${encodePointerToken(k)}`, cloneExact(cur.result[k]));
      }
      stepCase.expect = expect;
    } else {
      const expect = {};
      for (const k of Object.keys(cur)) {
        if (ITF_META_STATE_KEYS.has(k)) continue;
        if (!Object.hasOwn(prev, k) || !isDeepStrictEqual(prev[k], cur[k])) {
          setOwn(expect, `/${encodePointerToken(k)}`, cloneExact(cur[k]));
        }
      }
      if (!Object.keys(expect).length) {
        for (const k of Object.keys(cur)) {
          if (!ITF_META_STATE_KEYS.has(k)) setOwn(expect, `/${encodePointerToken(k)}`, cloneExact(cur[k]));
        }
      }
      if (Object.keys(expect).length) stepCase.expect = expect;
    }
    cases.push(stepCase);
  }

  return {
    ok: true,
    spec: {
      schema_version: FORMAL_VECTORS_SCHEMA,
      ...(typeof storyPath === 'string' && storyPath.trim() ? { story_path: storyPath.trim() } : {}),
      ...(typeof entryPath === 'string' && entryPath.trim() ? { entry_path: entryPath.trim() } : {}),
      ...(typeof defaultOp === 'string' && defaultOp.trim() ? { default_op: defaultOp.trim() } : {}),
      default_criterion: String(defaultCriterion ?? '1'),
      ...(Object.keys(world).length ? { initial_world: world } : {}),
      ...(isPlainObject(simulation) && Object.keys(simulation).length ? { simulation: cloneExact(simulation) } : {}),
      cases,
    },
  };
}

export function formatCompanionOutputPaths(basePath, chunkCount) {
  const clean = String(basePath || 'tests/formal-export.json').replace(/^\.\//, '');
  const count = Number.isSafeInteger(chunkCount) && chunkCount > 0 ? chunkCount : 1;
  if (count <= 1) return [clean];
  const width = Math.max(2, String(count).length);
  const hasJson = /\.json$/i.test(clean);
  const prefix = hasJson ? clean.slice(0, -5) : clean;
  const suffix = hasJson ? clean.slice(-5) : '.json';
  const out = [];
  for (let i = 1; i <= count; i++) {
    out.push(`${prefix}-${String(i).padStart(width, '0')}${suffix}`);
  }
  return out;
}

function normalizeCriterionKey(raw, fallback) {
  const chosen = raw !== undefined && raw !== null ? raw : fallback;
  if (typeof chosen === 'number' && Number.isSafeInteger(chosen) && chosen >= 1) return String(chosen);
  if (typeof chosen === 'string' && chosen.trim()) return chosen.trim();
  return null;
}

function buildStepFromCase(rawCase, index, { defaultOp, defaultEntryPath, defaultCriterion, seenIds }) {
  const section = `cases[${index}]`;
  if (!isPlainObject(rawCase)) {
    return makeRefusal('invalid-case', section, `${section} must be a JSON object.`);
  }
  for (const key of Object.keys(rawCase)) {
    if (!ALLOWED_CASE_KEYS.has(key)) {
      return makeRefusal('invalid-case', `${section}.${key}`, `Unknown key "${key}" on ${section}.`);
    }
  }
  const id = rawCase.id !== undefined ? rawCase.id : `case-${index + 1}`;
  if (typeof id !== 'string' || !id.trim()) {
    return makeRefusal('invalid-case', `${section}.id`, `${section}.id must be a nonblank string.`);
  }
  const trimmedId = id.trim();
  if (seenIds.has(trimmedId)) {
    return makeRefusal('duplicate-step-id', `${section}.id`, `Duplicate case id "${trimmedId}".`);
  }
  seenIds.add(trimmedId);

  if (rawCase.op !== undefined && (typeof rawCase.op !== 'string' || !rawCase.op.trim())) {
    return makeRefusal('invalid-case', `${section}.op`, `${section}.op must be a nonblank string when provided.`);
  }
  if (rawCase.entry_path !== undefined && (typeof rawCase.entry_path !== 'string' || !rawCase.entry_path.trim())) {
    return makeRefusal('invalid-case', `${section}.entry_path`, `${section}.entry_path must be a nonblank string when provided.`);
  }
  const op = typeof rawCase.op === 'string'
    ? rawCase.op.trim()
    : (typeof defaultOp === 'string' && defaultOp.trim() ? defaultOp.trim() : null);
  if (!op) {
    return makeRefusal('missing-operation', `${section}.op`, `${section} requires "op" (or top-level "default_op" / --op).`);
  }
  if (rawCase.from !== undefined && rawCase.input !== undefined) {
    return makeRefusal('invalid-case', section, `${section} cannot specify both "from" and "input".`);
  }

  const criterion = normalizeCriterionKey(rawCase.criterion, defaultCriterion);
  if (!criterion) {
    return makeRefusal('invalid-criterion', `${section}.criterion`, `${section}.criterion must be a nonblank criterion ID or positive integer.`);
  }

  const checkList = [];
  let expectedError = null;
  if (rawCase.error !== undefined && rawCase.error !== null) {
    if (typeof rawCase.error !== 'string' || !rawCase.error.trim()) {
      return makeRefusal('invalid-case', `${section}.error`, `${section}.error must be a nonblank error code string.`);
    }
    expectedError = rawCase.error.trim();
    checkList.push(['error', '=', expectedError]);
  }
  if (rawCase.expect !== undefined) {
    if (!isPlainObject(rawCase.expect)) {
      return makeRefusal('invalid-case', `${section}.expect`, `${section}.expect must be a plain object mapping JSON Pointers to expected values.`);
    }
    for (const [ptr, val] of Object.entries(rawCase.expect)) {
      if (!isValidPointer(ptr)) {
        return makeRefusal('invalid-pointer', `${section}.expect`, `Invalid JSON Pointer "${ptr}" in ${section}.expect; pointers must start with "/".`);
      }
      checkList.push(['result', ptr, '=', cloneExact(val)]);
    }
  }
  if (rawCase.expect_world !== undefined) {
    if (!isPlainObject(rawCase.expect_world)) {
      return makeRefusal('invalid-case', `${section}.expect_world`, `${section}.expect_world must be a plain object mapping JSON Pointers to expected values.`);
    }
    for (const [ptr, val] of Object.entries(rawCase.expect_world)) {
      if (!isValidPointer(ptr)) {
        return makeRefusal('invalid-pointer', `${section}.expect_world`, `Invalid JSON Pointer "${ptr}" in ${section}.expect_world; pointers must start with "/".`);
      }
      checkList.push(['world', ptr, '=', cloneExact(val)]);
    }
  }
  if (rawCase.checks !== undefined) {
    if (!Array.isArray(rawCase.checks)) {
      return makeRefusal('invalid-check', `${section}.checks`, `${section}.checks must be an array of Short JSON check tuples.`);
    }
    for (let ci = 0; ci < rawCase.checks.length; ci++) {
      const tuple = rawCase.checks[ci];
      if (!Array.isArray(tuple) || tuple.length < 2 || typeof tuple[0] !== 'string') {
        return makeRefusal('invalid-check', `${section}.checks[${ci}]`, `${section}.checks[${ci}] must be a non-empty Short JSON check tuple array.`);
      }
      checkList.push(cloneExact(tuple));
    }
  }

  if (!checkList.length) {
    return makeRefusal(
      'missing-checks',
      section,
      `${section} ("${trimmedId}") has zero checks; supply "expect", "expect_world", "error", or "checks".`,
    );
  }

  const step = { id: trimmedId, op };
  if (typeof rawCase.entry_path === 'string' && rawCase.entry_path.trim() !== defaultEntryPath) {
    step.entry_path = rawCase.entry_path.trim();
  }
  if (rawCase.from !== undefined) {
    step.from = cloneExact(rawCase.from);
  } else {
    step.input = rawCase.input !== undefined ? cloneExact(rawCase.input) : {};
  }
  if (rawCase.patch !== undefined) step.patch = cloneExact(rawCase.patch);
  if (rawCase.set !== undefined) step.set = cloneExact(rawCase.set);
  if (expectedError) step.error = expectedError;
  step.checks = { [criterion]: checkList };
  return { ok: true, step, checkCount: checkList.length };
}

export function exportFormalVectors(
  inputDoc,
  {
    storyPath = null,
    entryPath = null,
    defaultOp = null,
    defaultCriterion = null,
    maxSteps = DEFAULT_EXPORT_MAX_STEPS,
    split = false,
    outputBasePath = 'tests/formal-export.json',
    storySource = null,
  } = {},
) {
  if (!isPlainObject(inputDoc)) {
    return makeRefusal('invalid-document', 'root', 'Formal vector input must be a JSON object.');
  }

  let spec = inputDoc;
  if (isItfTraceDoc(inputDoc)) {
    const itfCriterion = (defaultCriterion !== undefined && defaultCriterion !== null)
      ? normalizeCriterionKey(defaultCriterion, null)
      : '1';
    if (!itfCriterion) {
      return makeRefusal('invalid-criterion', 'default_criterion', 'defaultCriterion (--criterion) must be a nonblank criterion ID or positive integer.');
    }
    const converted = convertItfTrace(inputDoc, { storyPath, entryPath, defaultOp, defaultCriterion: itfCriterion });
    if (!converted.ok) return converted;
    spec = converted.spec;
  }

  for (const key of Object.keys(spec)) {
    if (!ALLOWED_SPEC_KEYS.has(key)) {
      return makeRefusal('invalid-document', key, `Unknown top-level key "${key}" in formal vector spec.`);
    }
  }
  if (spec.schema_version !== undefined && spec.schema_version !== FORMAL_VECTORS_SCHEMA) {
    return makeRefusal(
      'invalid-schema',
      'schema_version',
      `Unsupported schema_version "${String(spec.schema_version)}"; expected "${FORMAL_VECTORS_SCHEMA}".`,
    );
  }

  if (entryPath !== undefined && entryPath !== null && (typeof entryPath !== 'string' || !entryPath.trim())) {
    return makeRefusal('invalid-document', 'entry_path', 'entryPath (--entry) must be a nonblank string when provided.');
  }
  if (storyPath !== undefined && storyPath !== null && (typeof storyPath !== 'string' || !storyPath.trim())) {
    return makeRefusal('invalid-document', 'story_path', 'storyPath (--story) must be a nonblank string when provided.');
  }
  if (defaultOp !== undefined && defaultOp !== null && (typeof defaultOp !== 'string' || !defaultOp.trim())) {
    return makeRefusal('invalid-document', 'default_op', 'defaultOp (--op) must be a nonblank string when provided.');
  }
  if (spec.entry_path !== undefined && (typeof spec.entry_path !== 'string' || !spec.entry_path.trim())) {
    return makeRefusal('invalid-document', 'entry_path', '"entry_path" must be a nonblank string when provided.');
  }
  if (spec.story_path !== undefined && (typeof spec.story_path !== 'string' || !spec.story_path.trim())) {
    return makeRefusal('invalid-document', 'story_path', '"story_path" must be a nonblank string when provided.');
  }
  if (spec.default_op !== undefined && (typeof spec.default_op !== 'string' || !spec.default_op.trim())) {
    return makeRefusal('invalid-document', 'default_op', '"default_op" must be a nonblank string when provided.');
  }

  const effEntryPath = typeof entryPath === 'string'
    ? entryPath.trim()
    : (typeof spec.entry_path === 'string' ? spec.entry_path.trim() : null);
  if (!effEntryPath) {
    return makeRefusal('missing-entry-path', 'entry_path', 'Formal vector export requires "entry_path" (or --entry PATH).');
  }
  const effStoryPath = typeof storyPath === 'string'
    ? storyPath.trim()
    : (typeof spec.story_path === 'string' ? spec.story_path.trim() : null);
  const effDefaultOp = typeof defaultOp === 'string'
    ? defaultOp.trim()
    : (typeof spec.default_op === 'string' ? spec.default_op.trim() : null);

  const overrideCriterion = (defaultCriterion !== undefined && defaultCriterion !== null)
    ? normalizeCriterionKey(defaultCriterion, null)
    : null;
  if (defaultCriterion !== undefined && defaultCriterion !== null && !overrideCriterion) {
    return makeRefusal('invalid-criterion', 'default_criterion', 'defaultCriterion (--criterion) must be a nonblank criterion ID or positive integer.');
  }
  const specCriterion = (spec.default_criterion !== undefined && spec.default_criterion !== null)
    ? normalizeCriterionKey(spec.default_criterion, null)
    : null;
  if (spec.default_criterion !== undefined && spec.default_criterion !== null && !specCriterion) {
    return makeRefusal('invalid-criterion', 'default_criterion', 'spec.default_criterion must be a nonblank criterion ID or positive integer.');
  }
  const effDefaultCriterion = overrideCriterion ?? specCriterion ?? '1';

  if (!Number.isSafeInteger(maxSteps) || maxSteps < 1 || maxSteps > 1000) {
    return makeRefusal('invalid-max-steps', 'maxSteps', `maxSteps (${String(maxSteps)}) must be an integer between 1 and 1000.`);
  }
  if (!Array.isArray(spec.cases) || spec.cases.length === 0) {
    return makeRefusal('missing-cases', 'cases', 'Formal vector spec requires a non-empty "cases" array.');
  }
  if (spec.initial_world !== undefined && !isPlainObject(spec.initial_world)) {
    return makeRefusal('invalid-document', 'initial_world', '"initial_world" must be a JSON object when provided.');
  }
  if (spec.simulation !== undefined && !isPlainObject(spec.simulation)) {
    return makeRefusal('invalid-document', 'simulation', '"simulation" must be a JSON object when provided.');
  }
  if (spec.seeds !== undefined && !isPlainObject(spec.seeds)) {
    return makeRefusal('invalid-document', 'seeds', '"seeds" must be a JSON object when provided.');
  }

  if (spec.cases.length > maxSteps && !split) {
    return makeRefusal(
      'max-steps-exceeded',
      'cases',
      `Input contains ${spec.cases.length} cases, exceeding --max-steps ${maxSteps}.`,
      `Pass --split to emit focused companion scenarios of <= ${maxSteps} steps each, or increase --max-steps.`,
    );
  }

  const seenIds = new Set();
  const builtSteps = [];
  for (let i = 0; i < spec.cases.length; i++) {
    const built = buildStepFromCase(spec.cases[i], i, {
      defaultOp: effDefaultOp,
      defaultEntryPath: effEntryPath,
      defaultCriterion: effDefaultCriterion,
      seenIds,
    });
    if (!built.ok) return built;
    builtSteps.push(built);
  }

  const chunks = [];
  for (let offset = 0; offset < builtSteps.length; offset += maxSteps) {
    chunks.push(builtSteps.slice(offset, offset + maxSteps));
  }
  const outputPaths = formatCompanionOutputPaths(outputBasePath, chunks.length);
  const files = [];
  const allWarnings = [];

  for (let ci = 0; ci < chunks.length; ci++) {
    const chunk = chunks[ci];
    const chunkPath = outputPaths[ci];
    const doc = {};
    if (effStoryPath) doc.story_path = effStoryPath;
    doc.entry_path = effEntryPath;
    if (spec.seeds && Object.keys(spec.seeds).length > 0) doc.seeds = cloneExact(spec.seeds);
    if (spec.initial_world && Object.keys(spec.initial_world).length > 0) doc.initial_world = cloneExact(spec.initial_world);
    if (spec.simulation && Object.keys(spec.simulation).length > 0) doc.simulation = cloneExact(spec.simulation);
    doc.steps = chunk.map(item => item.step);

    const compiled = compileScenario(doc, {
      path: chunkPath,
      storyPath: effStoryPath,
      storySource,
    });
    if (compiled.refusal) {
      return { ok: false, refusal: compiled.refusal };
    }
    const patchNullWarn = (compiled.warnings ?? []).find(w => w?.code === 'patch-null-deletes-key');
    if (patchNullWarn) {
      return makeRefusal(
        'patch-null-deletes-key',
        patchNullWarn.section ?? 'patch',
        patchNullWarn.message,
        'Use "set": { "<pointer>": null } instead of setting null in "patch".',
      );
    }

    const hygiene = evaluateScenarioHygiene(doc, { path: chunkPath, maxSteps });
    if (hygiene.finding) allWarnings.push(hygiene.finding.detail);

    const text = `${stringifyExactScenarioJson(doc, 2)}\n`;
    files.push({
      path: chunkPath,
      doc,
      text,
      step_count: chunk.length,
      check_count: chunk.reduce((sum, item) => sum + item.checkCount, 0),
    });
  }

  return {
    ok: true,
    schema_version: FORMAL_EXPORT_RESULT_SCHEMA,
    files,
    warnings: allWarnings,
  };
}

function resolveRepoRoot(cwd) {
  try {
    const out = execFileSync('git', ['rev-parse', '--show-toplevel'], {
      cwd,
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'ignore'],
      timeout: 5000,
    }).trim();
    return out ? realpathSync(out) : realpathSync(cwd);
  } catch {
    return realpathSync(cwd);
  }
}

function validateSafeOutputPath(realRoot, rawOutPath) {
  if (typeof rawOutPath !== 'string' || !rawOutPath.trim()) {
    return { ok: false, error: '--out PATH must be a nonblank repository-relative path.' };
  }
  const trimmed = rawOutPath.trim();
  if (trimmed.includes('\0') || trimmed.includes('\\')) {
    return { ok: false, error: `Unsafe --out path "${rawOutPath}".` };
  }
  const abs = isAbsolute(trimmed) ? resolve(trimmed) : resolve(realRoot, trimmed);
  const rel = relative(realRoot, abs).split(sep).join('/');
  if (!canonicalRepoPath(rel)) {
    return { ok: false, error: `--out path "${rawOutPath}" must stay inside the repository root (${realRoot}).` };
  }
  // Refuse symlinks on any existing ancestor or target path, and verify ancestor/target file kinds.
  const parts = rel.split('/');
  let cur = realRoot;
  for (let i = 0; i < parts.length; i++) {
    cur = join(cur, parts[i]);
    const isLast = i === parts.length - 1;
    try {
      const st = lstatSync(cur);
      if (st.isSymbolicLink()) {
        return { ok: false, error: `Refusing to write through symlink path "${rel}".` };
      }
      if (!isLast && !st.isDirectory()) {
        return { ok: false, error: `Cannot create output path "${rel}": ancestor "${parts.slice(0, i + 1).join('/')}" is not a directory.` };
      }
      if (isLast && !st.isFile()) {
        return { ok: false, error: `Refusing to overwrite non-regular file "${rel}".` };
      }
    } catch (err) {
      if (err?.code === 'ENOENT') break;
      return { ok: false, error: `Cannot inspect output path "${rel}": ${err?.message || String(err)}.` };
    }
  }
  return { ok: true, rel, abs: join(realRoot, ...parts) };
}

function readStreamSync(stream) {
  if (typeof stream === 'string') return stream;
  if (stream && typeof stream.readText === 'function') return stream.readText();
  try {
    return readFileSync(0, 'utf8');
  } catch {
    return '';
  }
}

export function runVectorExport(
  {
    cwd = process.cwd(),
    inputPath = null,
    outPath = null,
    storyPath = null,
    entryPath = null,
    op = null,
    criterion = null,
    maxSteps = DEFAULT_EXPORT_MAX_STEPS,
    split = false,
    write = false,
    json = false,
  } = {},
  ports = {},
) {
  const stdout = ports.stdout ?? process.stdout;
  const stderr = ports.stderr ?? process.stderr;
  const writeErr = msg => stderr.write(`${msg}\n`);

  if (write && (!outPath || !String(outPath).trim())) {
    writeErr('pdd vector export --write requires --out PATH (for example --out tests/<story>.formal.json).');
    return 2;
  }

  let realRoot;
  try {
    realRoot = resolveRepoRoot(cwd);
  } catch (err) {
    writeErr(`pdd vector export could not resolve working directory: ${err?.message || String(err)}`);
    return 2;
  }

  let rawText = '';
  const stdinPort = ports.stdin ?? process.stdin;
  const useStdin = inputPath === '-'
    || (!inputPath && ports.stdinText !== undefined)
    || (!inputPath && (typeof ports.stdin === 'string' || typeof ports.stdin?.readText === 'function'))
    || (!inputPath && !stdinPort?.isTTY);
  if (useStdin && (!inputPath || inputPath === '-')) {
    rawText = ports.stdinText !== undefined ? String(ports.stdinText) : readStreamSync(ports.stdin);
  } else if (typeof inputPath === 'string' && inputPath.trim()) {
    const resolvedInput = isAbsolute(inputPath.trim()) ? resolve(inputPath.trim()) : resolve(cwd, inputPath.trim());
    try {
      const st = lstatSync(resolvedInput);
      if (!st.isFile() && !st.isSymbolicLink()) {
        writeErr(`Input path "${inputPath}" is not a regular file.`);
        return 2;
      }
      rawText = readFileSync(resolvedInput, 'utf8');
    } catch (err) {
      writeErr(`Could not read input "${inputPath}": ${err?.message || String(err)}`);
      return 2;
    }
  } else {
    writeErr('Provide an input JSON path or pipe JSON on stdin (for example `pdd vector export cases.json --out tests/story.formal.json` or `pdd vector export --out tests/story.formal.json < cases.json`).');
    return 2;
  }

  let parsed;
  try {
    parsed = parseExactScenarioJson(rawText);
  } catch (err) {
    const refusal = {
      code: 'invalid-json',
      section: 'root',
      message: `Invalid input JSON: ${err?.message || String(err)}`,
      hint: 'Provide valid JSON (pdd.formal-vectors.v1 or Quint ITF trace) and rerun `pdd vector export`.',
    };
    if (json) {
      stdout.write(`${stringifyExactScenarioJson({ schema_version: FORMAL_EXPORT_RESULT_SCHEMA, ok: false, written: false, refusal }, 2)}\n`);
    } else {
      writeErr(refusal.message);
    }
    return 1;
  }

  let outputBasePath = 'tests/formal-export.json';
  if (outPath) {
    const cleanOut = String(outPath).trim().replace(/^\.\//, '');
    if (write) {
      const checked = validateSafeOutputPath(realRoot, cleanOut);
      if (!checked.ok) {
        writeErr(checked.error);
        return 2;
      }
      outputBasePath = checked.rel;
    } else {
      outputBasePath = cleanOut;
    }
  }

  // Load Story text safely (checking every ancestor for symlinks, regular-file kind, and byte cap).
  let storySource = null;
  const candidateStory = (typeof storyPath === 'string' && storyPath.trim())
    ? storyPath.trim().replace(/^\.\//, '')
    : (typeof parsed?.story_path === 'string' && parsed.story_path.trim() ? parsed.story_path.trim().replace(/^\.\//, '') : null);
  if (candidateStory && canonicalRepoPath(candidateStory)) {
    storySource = readSafeUtf8(realRoot, candidateStory);
  }

  const exported = exportFormalVectors(parsed, {
    storyPath: storyPath ?? null,
    entryPath: entryPath ?? null,
    defaultOp: op ?? null,
    defaultCriterion: criterion ?? null,
    maxSteps: Number(maxSteps),
    split: Boolean(split),
    outputBasePath,
    storySource,
  });

  if (!exported.ok) {
    const r = exported.refusal;
    if (json) {
      stdout.write(`${stringifyExactScenarioJson({ schema_version: FORMAL_EXPORT_RESULT_SCHEMA, ok: false, written: false, refusal: r }, 2)}\n`);
    } else {
      writeErr(`Error [${r.code}] (${r.section}): ${r.message}`);
      if (r.hint) writeErr(`  Fix: ${r.hint}`);
    }
    return 1;
  }

  if (write) {
    const validatedTargets = [];
    for (const file of exported.files) {
      const checked = validateSafeOutputPath(realRoot, file.path);
      if (!checked.ok) {
        writeErr(checked.error);
        return 2;
      }
      validatedTargets.push({ file, abs: checked.abs, rel: checked.rel });
    }
    try {
      for (const { file, abs } of validatedTargets) {
        mkdirSync(dirname(abs), { recursive: true });
        writeFileSync(abs, file.text, 'utf8');
      }
    } catch (err) {
      writeErr(`Could not write output file: ${err?.message || String(err)}`);
      return 2;
    }
  }

  if (json) {
    stdout.write(`${stringifyExactScenarioJson({
      schema_version: FORMAL_EXPORT_RESULT_SCHEMA,
      ok: true,
      written: Boolean(write),
      files: exported.files.map(f => ({
        path: f.path,
        step_count: f.step_count,
        check_count: f.check_count,
        doc: f.doc,
      })),
      warnings: exported.warnings,
    }, 2)}\n`);
    return 0;
  }

  for (const w of exported.warnings) stderr.write(`Warning: ${w}\n`);
  if (write) {
    for (const f of exported.files) {
      stdout.write(`Wrote ${f.path} (${f.step_count} steps, ${f.check_count} checks).\n`);
    }
  } else if (exported.files.length === 1) {
    stdout.write(exported.files[0].text);
  } else {
    for (const f of exported.files) {
      stdout.write(`--- ${f.path} (${f.step_count} steps, ${f.check_count} checks) ---\n${f.text}`);
    }
  }
  return 0;
}
