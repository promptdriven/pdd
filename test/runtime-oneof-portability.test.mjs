import test from 'node:test';
import assert from 'node:assert/strict';
import { checkInput } from '../src/runtime-preflight.mjs';

// ASCII pattern spelling does not make JS/Python character classes equivalent.
// Python rejects these first branches, so the CLI cannot prove an overlap.
for (const [label, value, pattern] of [
  ['BOM whitespace', '\ufeff', '^\\s$'],
  ['Unicode decimal digit', '\u0661', '^\\D$'],
  ['Unicode word character', '\u00e9', '^\\W$'],
]) test(`ONEOF2500 portability: ${label} cannot establish overlap`, () => {
  const choices = { oneOf: [{ type: 'string', pattern }, { type: 'string', pattern: '^[\\s\\S]$' }] };
  for (const [input, schema] of [
    [value, choices],
    [{ items: [value] }, { oneOf: [
      { type: 'object', properties: { items: { type: 'array', items: choices } }, required: ['items'], additionalProperties: false },
      { type: 'object', properties: { items: { type: 'array', items: { type: 'string' } } }, required: ['items'], additionalProperties: false },
    ] }],
  ]) assert.deepEqual(checkInput(input, schema, 0).refusals, []);
});
