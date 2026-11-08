import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync, writeFileSync, rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';

const launcher = fileURLToPath(new URL('../src/autopilot-launcher.mjs', import.meta.url));
const preload = fileURLToPath(new URL('./helpers/autopilot-timer-preload.mjs', import.meta.url));
const env = {...process.env, NODE_OPTIONS:`--import=${JSON.stringify(preload)}`};
delete env.NODE_TEST_CONTEXT;

test('ordinary timer entry dispatches the state operand and reports a rejected tick', t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-timer-entry-'));
  t.after(() => rmSync(root, {recursive:true,force:true}));
  const state = join(root, 'state.json');
  writeFileSync(state, JSON.stringify({enabled:false}));
  const stopped = spawnSync(process.execPath, [launcher,state], {env,encoding:'utf8',timeout:5000});
  assert.equal(stopped.status, 0, stopped.stderr);
  assert.equal(stopped.stdout, ''); assert.equal(stopped.stderr, '');
  writeFileSync(state, '{\ninvalid');
  const rejected = spawnSync(process.execPath, [launcher,state], {env,encoding:'utf8',timeout:5000});
  assert.equal(rejected.status, 1, rejected.stderr);
  assert.equal(rejected.stdout, '');
  assert.equal(rejected.stderr.trim().split('\n').length, 1);
  assert.match(rejected.stderr, /^Autopilot:/);
});

test('timer preload rejects the old imported-tick process boundary', () => {
  const bypass = spawnSync(process.execPath, ['--input-type=module','-e',`import {tickAutopilot} from ${JSON.stringify(new URL('../src/autopilot-launcher.mjs', import.meta.url).href)}; await tickAutopilot('/unused-state');`], {env,encoding:'utf8',timeout:5000});
  assert.equal(bypass.status, 1);
  assert.match(bypass.stderr, /ERR_ASSERTION/);
});
