// Prompt: prompts/cli/scenario-hygiene.prompt.md

// Offline scenario structural size hygiene evaluator (Layer-1 Core: 0 AI, 0 network, 0 writes).
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

export function evaluateScenarioHygiene(
  doc,
  {
    path = 'tests/story.json',
    maxSteps = DEFAULT_SCENARIO_MAX_STEPS,
    maxWorldBytes = DEFAULT_SCENARIO_MAX_WORLD_BYTES,
  } = {},
) {
  const emptyMetrics = { steps: 0, state_bytes: 0, simulated_ports: 0 };
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
  const simulatedPorts = isPlainObject(doc.simulation) ? Object.keys(doc.simulation).length : 0;

  const metrics = {
    steps,
    state_bytes: stateBytes,
    simulated_ports: simulatedPorts,
  };

  const reasons = [];
  if (steps > effMaxSteps) {
    reasons.push(`${steps} scenario steps (limit: ${effMaxSteps})`);
  }
  if (stateBytes > effMaxWorldBytes) {
    reasons.push(`${stateBytes} serialized state bytes (limit: ${effMaxWorldBytes})`);
  }

  if (!reasons.length) {
    return { oversized: false, metrics, reasons: [], finding: null };
  }

  const companionHint = companionPathHint(path);
  const portNote = simulatedPorts > 0
    ? ` (${simulatedPorts} simulated ${simulatedPorts === 1 ? 'port' : 'ports'})`
    : '';
  const detail = `Scenario "${path}" has ${reasons.join(' and ')}${portNote}.`;
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
