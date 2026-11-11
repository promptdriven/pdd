import test from 'node:test';
import assert from 'node:assert/strict';
import { clamp, slugify, sum } from '../src/helpers.mjs';

test('clamp bounds ordinary ranges and retains interior values', () => {
  assert.equal(clamp(-1), 0);
  assert.equal(clamp(101), 100);
  assert.equal(clamp(7, 2, 9), 7);
});

test('slugify normalizes spaces and punctuation', () => {
  assert.equal(slugify(' Hello, World! '), 'hello-world');
  assert.equal(slugify(''), '');
});

test('sum adds finite values and accepts an empty array', () => {
  assert.equal(sum([2, -1, 4]), 5);
  assert.equal(sum([]), 0);
});
