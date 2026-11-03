import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { storyCount } from '../src/workflow-runner.mjs';
import { preparePrEvidence } from '../src/workflow-pr-evidence.mjs';
import { renderJson } from '../src/runtime-output.mjs';

test('current head evidence: replay all frozen scenario checks', async () => {
  const scenario = JSON.parse(readFileSync(new URL('./runtime/pr-current-head-evidence.json', import.meta.url)));
  const lookup = (name, input) => {
    const rule = scenario.simulation[name];
    const rows = scenario.initial_world[rule.world_pointer.slice(1)];
    const key = rule.key_argument_pointer.slice(1), itemKey = rule.item_key_pointer.slice(1).split('/');
    const row = rows.find(row => JSON.stringify(itemKey.reduce((v,k) => v[k], row)) === JSON.stringify(input[key]));
    assert.ok(row, `${name}: ${JSON.stringify(input)}`);
    assert.deepEqual(row.request, input);
    return structuredClone(row.reply);
  };
  for (const step of scenario.steps) {
    const input = structuredClone(step.input);
    let result;
    if (step.operation === 'storyCount') result = storyCount(input, {
      fingerprint: root => lookup('source.fingerprint', { root }).value,
      capture: (root, options) => lookup('source.capture', { root, ...options })
    });
    else if (step.operation === 'preparePrEvidence') result = await preparePrEvidence(input, Object.fromEntries(['currentHead','readStepNotes','readOldCodeProof'].map(name => [name, args => lookup(`publication.${name}`, args)])));
    else if (step.operation === 'renderJson') result = renderJson(input);
    else assert.fail(`Unknown operation ${step.operation}`);
    for (const check of step.checks) {
      assert.equal(check.target, 'result'); assert.equal(check.op, 'equals');
      const actual = check.path.slice(1).split('/').reduce((v,k) => v?.[k.replace(/~1/g,'/').replace(/~0/g,'~')], result);
      assert.deepEqual(actual, check.value, `${step.step_id} ${check.path}`);
    }
  }
});
