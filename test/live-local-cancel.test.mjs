import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

for (const scenario of ['host-before', 'host-drain', 'host-queued', 'host-active', 'host-both', 'host-race', 'abort-service', 'abort-remote', 'abort-close']) {
  test(`native cancellation: ${scenario} releases only its consent without an answer`, { skip: process.platform === 'win32' }, () => {
    const result = spawnSync('python3', [fileURLToPath(new URL('./helpers/live-local-cancel-pty.py', import.meta.url)), scenario], {
      encoding: 'utf8', timeout: 15000, env: { ...process.env, PDD_TEST_NODE: process.execPath },
    });
    assert.ifError(result.error);
    assert.equal(result.status, 0, `${scenario}: ${result.stdout}\n${result.stderr}`);
    assert.equal(JSON.parse(result.stdout).passed, true);
  });
}
