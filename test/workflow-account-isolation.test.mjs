import test from 'node:test';
import assert from 'node:assert/strict';
import {spawnSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';

const guard = fileURLToPath(new URL('./helpers/host-account-read-guard.mjs', import.meta.url));
const childEnv = {...process.env};
delete childEnv.NODE_TEST_CONTEXT;
test('Theme D OS-home replacement test never opens host account configuration', () => {
  const result = spawnSync(process.execPath, ['--import', guard, '--test',
    '--test-name-pattern=full replacement expands tilde with OS home',
    fileURLToPath(new URL('./workflow-account-resume.test.mjs', import.meta.url))],
  {env:childEnv, encoding:'utf8', timeout:60_000});
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.match(result.stdout, /# pass 1\b/);
  assert.doesNotMatch(result.stdout + result.stderr, /HOST_ACCOUNT_READ_BLOCKED/);
});

test('Theme D host-account guard blocks reads before opening the file', () => {
  const result = spawnSync(process.execPath, ['--import', guard, '--input-type=module', '-e',
    "import fs from 'node:fs'; import {homedir} from 'node:os'; import {join} from 'node:path'; try { fs.readFileSync(join(homedir(), 'config.toml')); } catch {}"],
  {encoding:'utf8', timeout:10_000});
  assert.equal(result.status, 91);
  assert.match(result.stderr, /HOST_ACCOUNT_READ_BLOCKED/);
});
