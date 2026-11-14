import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { evaluateCheckBudget } from '../../src/runtime/runtime-check-plan.mjs';

const scenario = JSON.parse(readFileSync(new URL('../runtime/invocation-call-budget.json', import.meta.url), 'utf8'));
const at = (value, path) => path === '' ? value : path.slice(1).split('/').reduce((item, key) => item[key.replace(/~1/g, '/').replace(/~0/g, '~')], value);

test('793 approved pure Runtime replay: invocation-call-budget', () => {
  assert.equal(scenario.steps.length, 6);
  for (const step of scenario.steps) {
    assert.equal(step.operation, 'evaluateCheckBudget', `unmapped operation ${step.operation}`);
    const result = evaluateCheckBudget(step.input);
    for (const [index, check] of step.checks.entries()) {
      assert.equal(check.target, 'result', `unmapped target ${check.target}`);
      assert.equal(check.op, 'equals', `unmapped operator ${check.op}`);
      assert.deepEqual(at(result, check.path), check.value, `invocation-call-budget/${step.step_id}/${index}/${check.criterion_id}`);
    }
  }
});
