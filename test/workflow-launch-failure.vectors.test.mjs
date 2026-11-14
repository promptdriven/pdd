import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {observeLifecycle} from '../src/workflow-chat.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/workflow-launch-failure.json', import.meta.url), 'utf8'));
for (const step of scenario.steps) test(`launch lifecycle vector: ${step.step_id}`, () => {
  const {chat, live, at, agent, ran} = step.input;
  const result = observeLifecycle(chat, live, at, agent, ran);
  for (const check of step.checks) {
    assert.equal(check.target, 'result');
    assert.equal(check.op, 'equals');
    const value = check.path.slice(1).split('/').reduce((part, key) => part?.[key], result);
    assert.deepEqual(value, check.value, `${step.step_id}: ${check.path}`);
  }
});
