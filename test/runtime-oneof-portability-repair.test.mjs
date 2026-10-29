import test from 'node:test';
import assert from 'node:assert/strict';
import { checkInput } from '../src/runtime-preflight.mjs';

for (const [value, pattern] of [['x', '[^]'], ['x', '[]|x'], ['a\r', '^a$'], ['a\n', '^a$']]) {
  test(`ONEOF2500 unsupported cross-engine evidence ${JSON.stringify([value, pattern])}`, () => {
    const schema = { oneOf: [{ type: 'string', pattern }, { type: 'string' }] };
    assert.deepEqual(checkInput(value, schema, 0).refusals, []);
  });
}

test('ONEOF2500 printable ASCII class overlap remains definite', () => {
  for (const [value, pattern] of [[' ', '^\\s$'], ['a', '^\\D$'], ['!', '^\\W$']]) {
    assert.equal(checkInput(value, { oneOf: [{ type: 'string', pattern }, { type: 'string' }] }, 0).refusals.length, 1);
  }
});
