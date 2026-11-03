import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { renderJson } from '../src/runtime-output.mjs';

// Replay the approved prompt-tests-line Story vectors on the real renderJson export (RUNBOOK §17).
const scenario = JSON.parse(readFileSync(new URL('./runtime/prompt-tests-line.json', import.meta.url), 'utf8'));
const pointer = (value, path) => path === '' ? value : path.slice(1).split('/').reduce(
  (current, key) => current?.[key.replace(/~1/g, '/').replace(/~0/g, '~')], value);
const compare = {
  equals: (actual, value) => assert.deepEqual(actual, value),
  not_equals: (actual, value) => assert.notDeepEqual(actual, value),
  contains: (actual, value) => { assert.equal(typeof actual, 'string'); assert.ok(actual.includes(value), JSON.stringify(actual)); },
  not_contains: (actual, value) => { assert.equal(typeof actual, 'string'); assert.ok(!actual.includes(value), JSON.stringify(actual)); },
  count: (actual, value) => { assert.ok(Array.isArray(actual), JSON.stringify(actual)); assert.equal(actual.length, value); },
};

test('replay approved prompt-tests-line Story vectors through renderJson', async t => {
  assert.ok(scenario.steps.length > 0);
  const seen = new Set();
  for (const step of scenario.steps) {
    await t.test(step.step_id, async st => {
      assert.equal(step.operation, 'renderJson', `Not replayed: unmapped operation ${step.operation}`);
      const result = renderJson(structuredClone(step.input));
      for (const check of step.checks) {
        assert.equal(check.target, 'result', `Not replayed: unmapped target ${check.target}`);
        assert.ok(compare[check.op], `Not replayed: unmapped comparison ${check.op}`);
        seen.add(check.criterion_id);
        await st.test(`${check.criterion_id} ${check.path} ${check.op} ${JSON.stringify(check.value)}`,
          () => compare[check.op](pointer(result, check.path), check.value));
      }
    });
  }
  assert.deepEqual([...seen].sort(), scenario.criteria.map(criterion => criterion.id).sort());
});
