import test from 'node:test';
import assert from 'node:assert/strict';
import { isRecentLintReceipt } from '../src/runtime-lint-receipt.mjs';

const ENGINE = 'eae2202a68d00ab762fcbbf1eba0d8607a132a15';
const scope = { root: '/repo', origin: 'https://runtime.example', login: 'dana', user_id: '42', source_sha256: 'a'.repeat(64),
  authored_sha256: 'b'.repeat(64), tests: ['tests/a.json'], version: '0.1.28', selected_cap: null };
const receipt = { schema_version: 'pdd.lint-receipt.v1', scope, received_at: 1000, engine_sha: ENGINE, answer: {} };

// Wrong: an unknown current engine, or authored bytes that the upload hash cannot see, allow reuse.
test('reuse needs a known current engine equal to the receipt engine', () => {
  assert.equal(isRecentLintReceipt({ receipt, scope, now: 2000, engineSha: ENGINE }), true);
  for (const engineSha of [undefined, null, '', 'unknown', 'UNKNOWN', 'f'.repeat(40)])
    assert.equal(isRecentLintReceipt({ receipt, scope, now: 2000, ...(engineSha === undefined ? {} : { engineSha }) }), false, String(engineSha));
});

test('the authored file hash is part of the receipt identity', () => {
  assert.equal(isRecentLintReceipt({ receipt, scope: { ...scope, authored_sha256: 'c'.repeat(64) }, now: 2000, engineSha: ENGINE }), false);
  const { authored_sha256, ...older } = scope;
  assert.equal(isRecentLintReceipt({ receipt: { ...receipt, scope: older }, scope, now: 2000, engineSha: ENGINE }), false, 'a receipt without it is not reused');
  assert.equal(isRecentLintReceipt({ receipt, scope: { ...scope, authored_sha256: null }, now: 2000, engineSha: ENGINE }), false);
});
