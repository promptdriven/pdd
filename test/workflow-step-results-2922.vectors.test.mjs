import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { setup, scenario } from './helpers/workflow-step-results-2922-fixture.mjs';
import { runStatus } from '../src/workflow-runner.mjs';
import { viewRun } from '../src/workflow-view.mjs';

test('2922 PARTIAL lexical Runtime replay through real public operations (native setup)', async t => {
  const f = await setup(t);
  // The resolver's logical /project becomes the generated native project. IDs,
  // Git base and lifecycle metadata are native; step data/times stay exact, as
  // asserted by setup. Runtime files.* replies have no native injection API.
  const boundaries = { runStatus, viewRun };
  for (const vector of scenario.steps) {
    assert.equal(typeof boundaries[vector.operation], 'function', vector.operation);
    const result = await boundaries[vector.operation]({ ...vector.input, cwd: f.source }, f.ports);
    for (const check of vector.checks) {
      assert.equal(check.target, 'result', 'Unmapped targets must fail, never disappear');
      const got = check.path.slice(1).split('/').reduce((at, key) => at?.[key.replace(/~1/g, '/').replace(/~0/g, '~')], result);
      const label = `${vector.step_id}/${check.criterion_id}${check.path}`;
      if (check.op === 'equals') assert.deepEqual(got, check.value, label);
      else if (check.op === 'contains') assert.ok(typeof got === 'string' && got.includes(check.value), label);
      else assert.fail(`Unmapped check operation: ${check.op}`);
    }
  }
});
