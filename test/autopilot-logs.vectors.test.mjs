import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { describeWorkerProcess } from '../src/autopilot-logs.mjs';

const { steps } = JSON.parse(readFileSync(new URL('./runtime/autopilot-worker-logs.json', import.meta.url)));
for (const step of steps) test(`Autopilot worker logs: ${step.step_id}`, () => {
  assert.equal(step.operation, 'describeWorkerProcess');
  const display = describeWorkerProcess(step.input);
  for (const check of step.checks) {
    assert.deepEqual([check.target, check.path, check.op], ['result', '', 'equals']);
    assert.equal(display, check.value, check.criterion_id);
  }
});
