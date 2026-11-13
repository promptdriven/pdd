import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import * as trySession from '../src/try-session.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/existing-session-try.json', import.meta.url), 'utf8'));

function pointer(value, path) {
  if (path === '') return value;
  let current = value;
  for (const part of path.slice(1).split('/').map(segment => segment.replace(/~1/g, '/').replace(/~0/g, '~'))) {
    assert.ok(current !== null && typeof current === 'object' && Object.hasOwn(current, part), `missing pointer ${path}`);
    current = current[part];
  }
  return current;
}

test('existing-session-try runtime scenario vectors replay identically on src/try-session.mjs', async t => {
  assert.ok(scenario.steps.length >= 11);
  for (const step of scenario.steps) {
    await t.test(step.step_id, () => {
      const fn = trySession[step.operation];
      assert.equal(typeof fn, 'function', `missing operation ${step.operation}`);
      if (step.expected_error) {
        let caught = null;
        try {
          fn(step.input);
        } catch (error) {
          caught = error;
        }
        assert.ok(caught, `expected ${step.step_id} to throw ${step.expected_error}`);
        assert.equal(caught.code, step.expected_error);
        for (const check of step.checks) {
          assert.equal(check.target, 'error');
          assert.deepEqual(pointer({ code: caught.code }, check.path), check.value);
        }
        return;
      }
      const result = fn(step.input);
      for (const check of step.checks) {
        assert.equal(check.target, 'result');
        assert.deepEqual(pointer(result, check.path), check.value);
      }
    });
  }
});
