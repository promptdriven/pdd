import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { describeCallPreflight } from '../src/lint-call-preflight.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/lint-call-preflight.json', import.meta.url)));
for (const step of scenario.steps) test(`issue820 replay ${step.step_id}`, () => {
  assert.equal(step.operation, 'describeCallPreflight');
  const input = structuredClone(step.input), before = structuredClone(input);
  const result = describeCallPreflight(input);
  for (const check of step.checks) {
    assert.equal(check.target, 'result'); assert.equal(check.path, '/text'); assert.equal(check.op, 'equals');
    assert.deepEqual(result.text, check.value, `${check.criterion_id}: ${step.step_id}`);
  }
  assert.deepEqual(input, before, 'display never changes supplied facts');
});

// Native association edges from AC4. Expected headings come from the Story,
// not from a run; the prompt-space vectors above stay unchanged.
test('issue820: missing and inconsistent identity cannot support an estimate', () => {
  const base = scenario.steps[0].input;
  const mutations = [
    input => { input.context = null; },
    input => { input.preflight = null; },
    input => { input.context.engine_build = 'unknown'; },
    input => { input.context.selected_cap = 24; },
    input => { input.preflight.selected_cap = 24; },
    input => { input.context.source_sha256 = 'd'.repeat(64); },
  ];
  for (const change of mutations) {
    const input = structuredClone(base); change(input);
    const result = describeCallPreflight(input);
    assert.ok(result.text.startsWith('Call preflight (tests/example.json): unavailable; no estimate or cap-fit claim.'));
    assert.doesNotMatch(result.text, /structural catalog estimate|Warning:|Step first/);
    assert.match(result.text, /no guarantee of actual calls or completion/);
  }
});
