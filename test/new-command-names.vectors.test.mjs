import './helpers/test-home.mjs';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import test from 'node:test';
import { runPdd } from '../src/pdd-cli.mjs';

const pointer = (value, path) => path === '' ? value : path.slice(1).split('/').reduce(
  (current, key) => current?.[key.replace(/~1/g, '/').replace(/~0/g, '~')], value);
const capture = () => ({ text: '', write(value) { this.text += value; } });
const compare = {
  equals: (actual, value) => assert.deepEqual(actual, value),
  not_equals: (actual, value) => assert.notDeepEqual(actual, value),
  contains: (actual, value) => { assert.equal(typeof actual, 'string'); assert.ok(actual.includes(value), JSON.stringify(actual)); },
  not_contains: (actual, value) => { assert.equal(typeof actual, 'string'); assert.ok(!actual.includes(value), JSON.stringify(actual)); },
};
const RETIRED_WORKFLOW_STEPS = new Set([
  'workflow-run-help',
  'workflow-start-help-is-run-help',
  'workflow-run-without-name-keeps-guidance',
  'workflow-start-without-name-names-run',
]);

test('replay approved new-command-names Story vectors through runPdd (excluding retired workflow steps)', async t => {
  const scenario = JSON.parse(readFileSync(new URL('./runtime/new-command-names.json', import.meta.url), 'utf8'));
  const steps = scenario.steps.filter(step => !RETIRED_WORKFLOW_STEPS.has(step.step_id));
  assert.ok(steps.length > 0);
  const noDispatch = new Proxy({}, { get() { assert.fail('A help or usage-error step must not dispatch'); } });
  for (const step of steps) {
    await t.test(step.step_id, async st => {
      assert.equal(step.operation, 'runPdd', `Not replayed: unmapped operation ${step.operation}`);
      const stdout = capture(), stderr = capture();
      const exit_code = await runPdd(step.input.argv, { stdout, stderr, workflowRunner: noDispatch, autopilotLauncher: noDispatch });
      const result = { exit_code, stdout: stdout.text, stderr: stderr.text };
      const checks = step.checks.filter(check => !(step.step_id === 'root-help-shows-new-names' && check.op === 'contains' && check.value === 'pdd workflow run'));
      for (const check of checks) {
        assert.equal(check.target, 'result', `Not replayed: unmapped target ${check.target}`);
        assert.ok(compare[check.op], `Not replayed: unmapped comparison ${check.op}`);
        await st.test(`${check.criterion_id} ${check.path} ${check.op} ${JSON.stringify(check.value)}`, () => {
          compare[check.op](pointer(result, check.path), check.value);
        });
      }
    });
  }
});
