import '../../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {
  DEFAULT_SCENARIO_MAX_STEPS,
  DEFAULT_SCENARIO_MAX_WORLD_BYTES,
  computeDefaultScenarioCallCap,
  evaluateScenarioHygiene,
} from '../../../src/core/lint/scenario-hygiene.mjs';

function mulberry32(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6D2B79F5) >>> 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function makeSteps(count, positiveCallChecksPerStep = 0) {
  const checks = [['result', '/ok', '=', true]];
  for (let i = 0; i < positiveCallChecksPerStep; i++) {
    checks.push(['calls', `port.op${i}`, '=', 1]);
  }
  return Array.from({ length: count }, (_, idx) => ({
    id: `step-${idx + 1}`,
    op: 'run',
    input: { idx },
    checks: { '1': checks },
  }));
}

test('formal grid: exact threshold classification across steps (0..25) and state byte boundaries', () => {
  for (let steps = 0; steps <= 25; steps++) {
    const doc = {
      entry_path: 'prompts/mod.prompt.md',
      initial_world: { k: 'v' },
      steps: makeSteps(steps),
    };
    const res = evaluateScenarioHygiene(doc, {
      path: 'tests/grid.json',
      maxSteps: DEFAULT_SCENARIO_MAX_STEPS,
      maxWorldBytes: DEFAULT_SCENARIO_MAX_WORLD_BYTES,
    });
    assert.equal(res.metrics.steps, steps);
    assert.equal(res.oversized, steps > DEFAULT_SCENARIO_MAX_STEPS);
    if (steps > DEFAULT_SCENARIO_MAX_STEPS) {
      assert.equal(res.finding.code, 'scenario-oversized');
      assert.equal(res.finding.defaultSeverity, 'warn');
    } else {
      assert.equal(res.finding, null);
    }
    const cap = computeDefaultScenarioCallCap(doc);
    assert.equal(res.metrics.default_call_cap, cap);
    if (steps === 0) assert.equal(cap, 0);
    else assert.ok(cap >= 18 && cap <= 1000, `cap out of bounds: ${cap}`);
  }

  // Exact byte-limit boundary check: bytes == limit stays clean, bytes == limit + 1 warns.
  const payloadBase = '{"p":""}';
  const limit = 128;
  const exactLen = limit - Buffer.byteLength(payloadBase, 'utf8');
  const atLimit = evaluateScenarioHygiene(
    { entry_path: 'prompts/a.prompt.md', initial_world: { p: 'x'.repeat(exactLen) }, steps: makeSteps(1) },
    { path: 'tests/bytes.json', maxWorldBytes: limit },
  );
  assert.equal(atLimit.metrics.state_bytes, limit);
  assert.equal(atLimit.oversized, false);

  const overLimit = evaluateScenarioHygiene(
    { entry_path: 'prompts/a.prompt.md', initial_world: { p: 'x'.repeat(exactLen + 1) }, steps: makeSteps(1) },
    { path: 'tests/bytes.json', maxWorldBytes: limit },
  );
  assert.equal(overLimit.metrics.state_bytes, limit + 1);
  assert.equal(overLimit.oversized, true);
  assert.equal(overLimit.finding.defaultSeverity, 'warn');
});

test('formal PRNG (300 seeded worlds): monotonicity, non-mutation, and exact predicate equivalence', () => {
  const rng = mulberry32(0x3704BEEF);
  for (let trial = 0; trial < 300; trial++) {
    const steps = 1 + Math.floor(rng() * 24);
    const maxSteps = 5 + Math.floor(rng() * 18);
    const maxWorldBytes = 64 + Math.floor(rng() * 2048);
    const payloadSize = Math.floor(rng() * 2400);
    const posCallsPerStep = Math.floor(rng() * 8);

    const doc = {
      entry_path: 'prompts/mod.prompt.md',
      initial_world: payloadSize > 0 ? { blob: 'z'.repeat(payloadSize) } : {},
      steps: makeSteps(steps, posCallsPerStep),
    };
    const snapshot = JSON.stringify(doc);

    const res = evaluateScenarioHygiene(doc, {
      path: `tests/story-${trial}.focus.json`,
      maxSteps,
      maxWorldBytes,
    });
    // Zero input mutation
    assert.equal(JSON.stringify(doc), snapshot);

    // Exact predicate equivalence
    const expectedOver =
      res.metrics.steps > maxSteps ||
      res.metrics.state_bytes > maxWorldBytes ||
      (res.metrics.default_call_cap > 0 && res.metrics.min_estimated_calls > res.metrics.default_call_cap);
    assert.equal(res.oversized, expectedOver, `trial ${trial}: oversized predicate mismatch`);

    if (res.oversized) {
      assert.equal(res.finding.code, 'scenario-oversized');
      assert.equal(res.finding.defaultSeverity, 'warn');
      assert.ok(res.reasons.length >= 1);
      // Monotonicity: increasing steps or state bytes never clears an oversized flag
      const grown = {
        ...doc,
        initial_world: { blob: 'z'.repeat(payloadSize + 64) },
        steps: [...doc.steps, ...makeSteps(1, posCallsPerStep)],
      };
      const grownRes = evaluateScenarioHygiene(grown, {
        path: `tests/story-${trial}.focus.json`,
        maxSteps,
        maxWorldBytes,
      });
      assert.equal(grownRes.oversized, true, `trial ${trial}: monotonicity violated`);
    } else {
      assert.equal(res.finding, null);
      assert.deepEqual(res.reasons, []);
    }
  }
});
