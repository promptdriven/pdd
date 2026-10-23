import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import test from 'node:test';
import { statusLabel } from '../src/status.mjs';

const vectors = JSON.parse(
  readFileSync(new URL('../vectors/status-labels.json', import.meta.url), 'utf8'),
);

for (const vector of vectors.cases) {
  test(vector.id, () => {
    if (Object.hasOwn(vector, 'expectedError')) {
      assert.throws(() => statusLabel(vector.input), {
        name: vector.expectedError,
      });
      return;
    }

    assert.equal(statusLabel(vector.input), vector.expected);
  });
}
