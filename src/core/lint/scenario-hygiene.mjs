// Prompt: prompts/cli/scenario-hygiene.prompt.md

// Offline scenario size & call-budget hygiene evaluator (Layer-1 Core: 0 AI, 0 network, 0 writes).
import { posix } from 'node:path';
import { parseExactScenarioJson, stringifyExactScenarioJson } from '../../scenario-compile.mjs';
import { TEST_SCENARIO_JSON_RE } from '../../shared/test-paths.mjs';
import { readSafeUtf8 } from './diagnostics.mjs';

export const DEFAULT_SCENARIO_MAX_STEPS = 15;
export const DEFAULT_SCENARIO_MAX_WORLD_BYTES = 16384;

const NON_SCENARIO_TEST_SUBDIR_RE = /(?:^|\/)(?:fixtures|__fixtures__|mocks|__mocks__|snapshots|__snapshots__|data|testdata|golden|cassettes)\//i;
const TOOLING_CONFIG_JSON = new Set([
  'jsconfig.json', 'package.json', 'package-lock.json', 'npm-shrinkwrap.json', 'composer.json',
  'biome.json', 'deno.json', 'jsr.json', 'eslint.json', 'prettier.json', 'vitest.json', 'jest.json', 'babel.json',
]);
const POSITIVE_CALLS_OPS = new Set(['equals', '=', '==', 'count', 'at_least', '>=', 'gte']);
const STRICT_GT_CALLS_OPS = new Set(['gt', '>']);

const isPlainObject = value => value !== null && typeof value === 'object' && !Array.isArray(value);

function isCandidateScenarioPath(relPath) {
  if (typeof relPath !== 'string' || !TEST_SCENARIO_JSON_RE.test(relPath) || NON_SCENARIO_TEST_SUBDIR_RE.test(relPath)) {
    return false;
  }
  const base = posix.basename(relPath).toLowerCase();
  if (TOOLING_CONFIG_JSON.has(base) || /^tsconfig.*\.json$/.test(base)) return false;
  if (base === 'cases.json' || base.endsWith('-cases.json')) return false;
  return true;
}

function isPositiveNumberLike(value, allowZero = false) {
  if (typeof value === 'bigint') return allowZero ? value >= 0n : value > 0n;
  if (typeof value === 'number' && Number.isFinite(value)) return allowZero ? value >= 0 : value > 0;
  return false;
}

function isPositiveCallsCheck(check) {
  if (Array.isArray(check)) {
    // Short JSON tuple:
    // - criterion-keyed map entry: ["calls", path, op, value]
    // - array-form step.checks entry: [criterion, "calls", path, op, value]
    if (check.length >= 4 && check[0] === 'calls') {
      const op = check[2];
      const val = check[3];
      if (POSITIVE_CALLS_OPS.has(op)) return isPositiveNumberLike(val, false);
      if (STRICT_GT_CALLS_OPS.has(op)) return isPositiveNumberLike(val, true);
    } else if (check.length >= 5 && check[1] === 'calls') {
      const op = check[3];
      const val = check[4];
      if (POSITIVE_CALLS_OPS.has(op)) return isPositiveNumberLike(val, false);
      if (STRICT_GT_CALLS_OPS.has(op)) return isPositiveNumberLike(val, true);
    }
    return false;
  }
  if (isPlainObject(check) && check.target === 'calls') {
    if (POSITIVE_CALLS_OPS.has(check.op)) return isPositiveNumberLike(check.value, false);
    if (STRICT_GT_CALLS_OPS.has(check.op)) return isPositiveNumberLike(check.value, true);
  }
  return false;
}

function countStepPositiveCallsChecks(step) {
  if (!isPlainObject(step)) return 0;
  let total = 0;
  const checks = step.checks;
  if (Array.isArray(checks)) {
    for (const item of checks) {
      if (isPositiveCallsCheck(item)) total += 1;
    }
  } else if (isPlainObject(checks)) {
    for (const entry of Object.values(checks)) {
      if (Array.isArray(entry) && typeof entry[0] === 'string') {
        if (isPositiveCallsCheck(entry)) total += 1;
      } else if (Array.isArray(entry)) {
        for (const item of entry) {
          if (isPositiveCallsCheck(item)) total += 1;
        }
      } else if (isPositiveCallsCheck(entry)) {
        total += 1;
      }
    }
  }
  return total;
}

function countStepOverrides(step) {
  if (!isPlainObject(step)) return 0;
  const ov = step.simulation_overrides;
  if (Array.isArray(ov)) return ov.length;
  if (isPlainObject(ov)) return Object.keys(ov).length;
  return 0;
}

function serializedBytes(value) {
  try {
    const raw = stringifyExactScenarioJson(value);
    return typeof raw === 'string' ? Buffer.byteLength(raw, 'utf8') : 0;
  } catch {
    return 0;
  }
}

function companionPathHint(scenarioPath) {
  const normalized = String(scenarioPath || 'tests/story.json').replace(/^\.\//, '');
  const dir = posix.dirname(normalized);
  const base = posix.basename(normalized).replace(/\.json$/i, '') || 'story';
  const dot = base.indexOf('.');
  const storyStem = dot > 0 ? base.slice(0, dot) : base;
  const prefix = dir && dir !== '.' ? dir : 'tests';
  return `${prefix}/${storyStem}.<focus>.json`;
}

export function computeDefaultScenarioCallCap(doc) {
  const steps = Array.isArray(doc?.steps) ? doc.steps.length : 0;
  if (steps === 0) return 0;
  const fallback = Math.min(1000, Math.max(18, steps * 12));
  if (steps <= 2) return fallback;
  const hasWorldOrPorts =
    (isPlainObject(doc.initial_world) && Object.keys(doc.initial_world).length > 0) ||
    (isPlainObject(doc.simulation) && Object.keys(doc.simulation).length > 0) ||
    doc.steps.some(step => countStepOverrides(step) > 0);
  const perStep = 4 + (hasWorldOrPorts ? 1 : 0);
  return Math.min(fallback, Math.max(24, steps * perStep + 6));
}

export function evaluateScenarioHygiene(
  doc,
  {
    path = 'tests/story.json',
    maxSteps = DEFAULT_SCENARIO_MAX_STEPS,
    maxWorldBytes = DEFAULT_SCENARIO_MAX_WORLD_BYTES,
  } = {},
) {
  const emptyMetrics = { steps: 0, state_bytes: 0, min_estimated_calls: 0, default_call_cap: 0 };
  if (
    !isPlainObject(doc) ||
    !Array.isArray(doc.steps) ||
    Array.isArray(doc.cases) ||
    String(doc.schema_version ?? '').startsWith('pdd.native-cases.')
  ) {
    return { oversized: false, metrics: emptyMetrics, reasons: [], finding: null };
  }

  const effMaxSteps = Number.isSafeInteger(maxSteps) && maxSteps >= 1 ? maxSteps : DEFAULT_SCENARIO_MAX_STEPS;
  const effMaxWorldBytes = Number.isSafeInteger(maxWorldBytes) && maxWorldBytes >= 1 ? maxWorldBytes : DEFAULT_SCENARIO_MAX_WORLD_BYTES;

  const steps = doc.steps.length;
  let stateBytes = 0;
  if (Object.hasOwn(doc, 'initial_world') && doc.initial_world !== undefined) {
    stateBytes += serializedBytes(doc.initial_world);
  }
  if (Object.hasOwn(doc, 'seeds') && doc.seeds !== undefined) {
    stateBytes += serializedBytes(doc.seeds);
  }

  let minEstimatedCalls = 0;
  for (const step of doc.steps) {
    minEstimatedCalls += 1 + countStepPositiveCallsChecks(step) + countStepOverrides(step);
  }
  const defaultCallCap = computeDefaultScenarioCallCap(doc);
  const metrics = {
    steps,
    state_bytes: stateBytes,
    min_estimated_calls: minEstimatedCalls,
    default_call_cap: defaultCallCap,
  };

  const reasons = [];
  if (steps > effMaxSteps) {
    reasons.push(`${steps} scenario steps (limit: ${effMaxSteps})`);
  }
  if (stateBytes > effMaxWorldBytes) {
    reasons.push(`${stateBytes} serialized state bytes (limit: ${effMaxWorldBytes})`);
  }
  if (defaultCallCap > 0 && minEstimatedCalls > defaultCallCap) {
    reasons.push(`minimum ${minEstimatedCalls} estimated calls exceeding default per-request cap ${defaultCallCap}`);
  }

  if (!reasons.length) {
    return { oversized: false, metrics, reasons: [], finding: null };
  }

  const companionHint = companionPathHint(path);
  const detail = `Scenario "${path}" has ${reasons.join(' and ')} (default per-request cap: ${defaultCallCap} calls).`;
  const fix = `Split into focused companion scenarios (${companionHint}) or adjust "lint.scenario" in pdd.json`;
  return {
    oversized: true,
    metrics,
    reasons,
    finding: {
      filePath: path,
      line: 1,
      order: 12,
      code: 'scenario-oversized',
      category: 'scenario hygiene',
      defaultSeverity: 'warn',
      detail,
      fix,
      rerun: 'pdd lint',
    },
  };
}

export function collectScenarioHygieneFindings({
  realRoot,
  scenarioPaths = [],
  readFile,
  scenarioConfig = {},
} = {}) {
  if (!Array.isArray(scenarioPaths) || !scenarioPaths.length) return [];
  const read = typeof readFile === 'function' ? readFile : (p => readSafeUtf8(realRoot, p));
  const maxSteps = scenarioConfig?.maxSteps ?? DEFAULT_SCENARIO_MAX_STEPS;
  const maxWorldBytes = scenarioConfig?.maxWorldBytes ?? DEFAULT_SCENARIO_MAX_WORLD_BYTES;
  const findings = [];

  for (const relPath of [...new Set(scenarioPaths)].sort()) {
    if (!isCandidateScenarioPath(relPath)) continue;
    const raw = read(relPath);
    if (typeof raw !== 'string' || !raw.trim()) continue;
    let doc;
    try {
      doc = parseExactScenarioJson(raw);
    } catch {
      continue;
    }
    const evaluated = evaluateScenarioHygiene(doc, { path: relPath, maxSteps, maxWorldBytes });
    if (evaluated.finding) findings.push(evaluated.finding);
  }
  return findings;
}
