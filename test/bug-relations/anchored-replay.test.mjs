// Reuse the native replays for the two linked scenarios; both read the approved
// scenario files at execution time and invoke their public exports.
import '../import-authorized-workspace-evidence.vectors.test.mjs';
import '../pr-current-head-evidence.vectors.test.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { runStatus } from '../../src/workflow-runner.mjs';
import { viewRun } from '../../src/workflow-view.mjs';
import { setup } from '../helpers/workflow-step-results-2922-fixture.mjs';

const scenario = JSON.parse(readFileSync(new URL('../runtime/workflow-step-results-2922.json', import.meta.url)));

test('anchored 2922 scenario: replay each operation and check', async t => {
  const fixture = await setup(t);
  for (const step of scenario.steps) {
    const input = { ...step.input, cwd: fixture.source };
    const operation = { runStatus, viewRun }[step.operation];
    assert.ok(operation, `unmapped operation ${step.operation}`);
    const result = await operation(input, fixture.ports);
    for (const check of step.checks) {
      assert.equal(check.target, 'result', `unmapped target ${check.target}`);
      const actual = check.path.slice(1).split('/').reduce((value, key) => value?.[key.replace(/~1/g, '/').replace(/~0/g, '~')], result);
      const label = `${step.step_id} ${check.criterion_id} ${check.path}`;
      if (check.op === 'equals') assert.deepEqual(actual, check.value, label);
      else if (check.op === 'contains') assert.ok(actual?.includes(check.value), label);
      else assert.fail(`unmapped check operator ${check.op}`);
    }
  }
});
