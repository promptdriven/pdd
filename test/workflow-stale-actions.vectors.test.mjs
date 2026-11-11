import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {changeRun} from '../src/workflow-runner.mjs';
import {writeRun} from '../src/workflow-runs.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/stale-workflow-actions.json', import.meta.url), 'utf8'));
test('replay stale workflow scenario', async t => {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record(); run.state = 'waiting'; run.gate = {id:'gate-current', kind:'approve', area:run.areas[run.area].name, at:1000}; writeRun(run, f.ports);
  for (const step of scenario.steps) {
    assert.equal(step.operation, 'changeRun');
    const result = await changeRun({...step.input, cwd:f.source, packageRoot}, f.ports);
    for (const check of step.checks) {
      assert.equal(check.target, 'result');
      const actual = check.path.split('/').slice(1).reduce((value, key) => value[key], result);
      if (check.op === 'equals') assert.equal(actual, check.value, `${step.step_id}: ${check.criterion_id}`);
      else if (check.op === 'contains') assert.ok(actual.includes(check.value), `${step.step_id}: ${check.criterion_id}`);
      else assert.fail(`Unsupported operation ${check.op}`);
    }
  }
});
