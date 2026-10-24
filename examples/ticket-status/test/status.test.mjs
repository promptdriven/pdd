import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import test from 'node:test';
import { statusLabel } from '../src/status.mjs';

// Literal expectations are authored from the contract, never from statusLabel.
const vectors = JSON.parse(
  readFileSync(new URL('../vectors/status-labels.json', import.meta.url), 'utf8'),
);

for (const vector of vectors.cases) {
  test(vector.id, () => {
    if (Object.hasOwn(vector, 'expectedError')) {
      assert.throws(() => statusLabel(vector.input), TypeError);
      return;
    }
    assert.equal(statusLabel(vector.input), vector.expected);
  });
}

// These values extend AC3 beyond the example's JSON input representation.
for (const [name, input] of [
  ['undefined', undefined], ['false', false], ['true', true],
  ['array', []], ['object', {}], ['NaN', NaN], ['infinity', Infinity],
  ['bigint', 7n], ['symbol', Symbol('open')], ['function', () => 'open'],
]) {
  test(`AC3: ${name} throws actual TypeError`, () => {
    assert.throws(() => statusLabel(input), TypeError);
  });
}

test('AC3: omitted argument throws actual TypeError', () => {
  assert.throws(() => statusLabel(), TypeError);
});

test('AC4: invalid input is rejected without calling conversion hooks', () => {
  let conversions = 0;
  const input = {
    [Symbol.toPrimitive]() { conversions++; return 'open'; },
    toString() { conversions++; return 'open'; },
    valueOf() { conversions++; return 'open'; },
  };
  assert.throws(() => statusLabel(input), TypeError);
  assert.equal(conversions, 0);
});
