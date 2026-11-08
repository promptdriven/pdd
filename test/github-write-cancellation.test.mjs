import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { join } from 'node:path';
import { spawn } from 'node:child_process';
import { setTimeout as delay } from 'node:timers/promises';
import { githubWriteEnvironment, githubWriteUsages } from '../src/github-write-proxy.mjs';

import { tmpdir } from 'node:os';
const report = tmpdir();

for (const signal of ['SIGTERM', 'SIGINT', 'SIGHUP']) for (const wrapped of [false, true]) test(`${signal} ${wrapped ? 'private wrapper' : 'direct gh control'} cancels an in-flight child before its write effect`, async t => {
  const root = fs.mkdtempSync(join(report, 'next-writes-final-cancel.'));
  const bin = join(root, 'bin'), started = join(root, 'started'), effect = join(root, 'effect');
  fs.mkdirSync(bin);
  fs.writeFileSync(join(bin, 'gh'), `#!${process.execPath}
import('node:fs').then(async fs => {
  if (process.argv[2] === 'auth') {
    process.stdout.write(JSON.stringify({hosts:{'github.com':[{login:'acme',active:true}]}}));
    return;
  }
  fs.writeFileSync(process.env.TEST_STARTED, String(process.pid));
  await new Promise(resolve => setTimeout(resolve, 700));
  fs.writeFileSync(process.env.TEST_EFFECT, 'dispatched');
  process.stdout.write('{}');
});
`, { mode: 0o700 });
  let child;
  t.after(() => {
    if (child && child.exitCode === null && child.signalCode === null) child.kill('SIGKILL');
    if (fs.existsSync(started)) try { process.kill(Number(fs.readFileSync(started, 'utf8')), 'SIGKILL'); } catch {}
    fs.rmSync(root, { recursive: true, force: true });
  });
  const base = { HOME: root, PATH: bin + ':/usr/bin:/bin', TEST_STARTED: started, TEST_EFFECT: effect };
  const env = wrapped ? { ...base, ...githubWriteEnvironment({ root, env: base }) } : base;
  const executable = join(env.PATH.split(':')[0], 'gh');
  child = spawn(executable, ['api', '--method', 'PATCH', 'repos/acme/widgets/issues/1'], { env, stdio: 'ignore' });
  const exited = new Promise((resolve, reject) => { child.on('error', reject); child.on('close', (code, signal) => resolve({code, signal})); });
  for (let attempt = 0; !fs.existsSync(started) && attempt < 200; attempt++) await delay(10);
  assert.ok(fs.existsSync(started), 'the original gh reached the pending effect');
  assert.equal(child.kill(signal), true);
  assert.deepEqual(await exited, { code: null, signal });
  await delay(900);
  const effectAfterCancellation = fs.existsSync(effect);
  t.diagnostic(JSON.stringify({ wrapped, effectAfterCancellation }));
  assert.equal(effectAfterCancellation, false, 'terminating gh must stop its pending write');
  if (wrapped) {
    assert.throws(() => process.kill(Number(fs.readFileSync(started, 'utf8')), 0), { code: 'ESRCH' });
    assert.equal(githubWriteUsages({ root, env: base }).reduce((n, usage) => n + usage.hour, 0), 1);
  }
});
