import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { evaluateScreenLook, lintScreenDesign } from '../src/screen-design-check.mjs';

const parseExactJson = raw => JSON.parse(raw, (_key, value, context) => (
  typeof value === 'number' && /^-?\d+$/.test(context.source) && !Number.isSafeInteger(value)
    ? BigInt(context.source)
    : value
));
const pointer = (value, path) => path.split('/').slice(1).reduce((row, key) => row?.[key.replaceAll('~1', '/').replaceAll('~0', '~')], value);

const operations = { lintScreenDesign, evaluateScreenLook };
const scenario = parseExactJson(readFileSync(new URL('./runtime/screen-design-check.json', import.meta.url), 'utf8'));

for (const step of scenario.steps) test(`screen-design-check replay: ${step.step_id}`, () => {
  const fn = operations[step.operation];
  assert.equal(typeof fn, 'function', `mapped operation ${step.operation}`);
  const input = structuredClone(step.input);
  const before = structuredClone(input);
  const result = fn(input);
  for (const check of step.checks) {
    const label = `${step.step_id} ${check.criterion_id} ${check.path} ${check.op}`;
    assert.equal(check.target, 'result', `${label}: unsupported replay target`);
    const actual = pointer(result, check.path);
    if (check.op === 'equals') assert.deepEqual(actual, check.value, label);
    else if (check.op === 'count') assert.equal(actual.length, check.value, label);
    else assert.fail(`${label}: unsupported replay operation`);
  }
  assert.deepEqual(input, before, `${step.step_id}: pure check must not mutate input`);
});
