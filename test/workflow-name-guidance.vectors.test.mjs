import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { runPdd } from '../src/pdd-cli.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/workflow-name-guidance.json', import.meta.url), 'utf8'));
const capture = () => ({ text: '', write(value) { this.text += value; } });
const pointer = (value, path) => path === '' ? value : path.slice(1).split('/').reduce(
  (current, key) => current[key.replace(/~1/g, '/').replace(/~0/g, '~')], value);

test('replay approved workflow-name-guidance Story vectors through runPdd', async t => {
  for (const step of scenario.steps) {
    await t.test(step.step_id, async () => {
      assert.equal(step.operation, 'runPdd');
      const stdout = capture(), stderr = capture();
      const exit_code = await runPdd(step.input.argv, {
        stdout, stderr,
        workflowRunner: new Proxy({}, { get() { assert.fail('Usage error must not dispatch'); } }),
      });
      const result = { exit_code, stdout: stdout.text, stderr: stderr.text };
      for (const check of step.checks) {
        assert.equal(check.target, 'result', `Not replayed: unsupported target ${check.target}`);
        assert.equal(check.op, 'equals', `Not replayed: unsupported comparison ${check.op}`);
        assert.deepEqual(pointer(result, check.path), check.value, `${check.criterion_id} ${check.path}`);
      }
    });
  }
});
