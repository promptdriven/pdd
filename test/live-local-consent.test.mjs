import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

// Python's standard-library PTY supplies actual stdin/stdout terminals to Node.
// The controls are automated test inputs, never a person's write authorization.
for (const scenario of ['same', 'separate', 'decline', 'blank', 'interrupt', 'close', 'eof', 'read-error', 'typeahead', 'partial-typeahead', 'pretyped', 'pretyped-partial', 'decline-typeahead', 'interrupt-typeahead', 'execute', 'bridge']) {
  test(`native consent: ${scenario} requires one fresh terminal answer per call`, { skip: process.platform === 'win32' }, () => {
    const result = spawnSync('python3', [fileURLToPath(new URL('./helpers/live-local-consent-pty.py', import.meta.url)), scenario], {
      encoding: 'utf8', timeout: 20000, env: { ...process.env, PDD_TEST_NODE: process.execPath },
    });
    assert.ifError(result.error);
    assert.equal(result.status, 0, `${scenario}: ${result.stdout}\n${result.stderr}`);
    assert.equal(JSON.parse(result.stdout).passed, true);
  });
}
