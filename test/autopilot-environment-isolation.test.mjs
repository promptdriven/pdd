import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

for (const code of ['ESRCH', 'EPERM']) test(`synthetic queue health is independent of host PID probes: ${code}`, () => {
  const env = { ...process.env, PDD_TEST_OWNER_PROBE: code };
  delete env.NODE_TEST_CONTEXT;
  const result = spawnSync(process.execPath, [
    '--import', fileURLToPath(new URL('./helpers/synthetic-queue-processes.mjs', import.meta.url)),
    '--test', '--test-concurrency=8', '--test-name-pattern=shared suite queue permits capacity',
    fileURLToPath(new URL('./autopilot-environment-health.test.mjs', import.meta.url)),
  ], { env, encoding: 'utf8', timeout: 15000 });
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.match(result.stdout, /# pass 1\b/);
  assert.match(result.stdout, /# skipped 0\b/);
});
