import test from 'node:test';
import assert from 'node:assert/strict';
import {spawnSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';

test('public desktop affinity regression needs no native CPU or process observations', () => {
  const env = {...process.env};
  delete env.NODE_TEST_CONTEXT;
  const result = spawnSync(process.execPath, [
    '--import', fileURLToPath(new URL('./helpers/deny-native-machine.mjs', import.meta.url)),
    '--test', '--test-concurrency=8', '--test-name-pattern=Linux desktop child',
    fileURLToPath(new URL('./autopilot-machine-checks.test.mjs', import.meta.url)),
  ], {env, encoding:'utf8', timeout:15000});
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.match(result.stdout, /# pass 1\b/);
  assert.match(result.stdout, /# skipped 0\b/);
});
