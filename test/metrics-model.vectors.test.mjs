import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { calculateMetrics } from '../src/metrics-model.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/metrics-shared-report.json', import.meta.url), 'utf8'));
const pointer = (value, path) => path === '' ? value : path.slice(1).split('/').reduce((v, segment) => v?.[segment.replaceAll('~1','/').replaceAll('~0','~')], value);
for (const step of scenario.steps) {
  test(`scenario ${step.step_id}`, () => {
    assert.equal(step.operation, 'calculateMetrics');
    const result = calculateMetrics(step.input);
    for (const check of step.checks) {
      assert.equal(check.target, 'result', `${step.step_id}: unsupported target`);
      const actual = pointer(result, check.path);
      if (check.op === 'count') assert.equal(actual?.length, check.value, check.criterion_id);
      else if (check.op === 'equals') assert.deepEqual(actual, check.value, check.criterion_id);
      else assert.fail(`Unsupported check ${check.op}`);
    }
  });
}
