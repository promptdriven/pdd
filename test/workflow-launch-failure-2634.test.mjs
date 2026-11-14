import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, writeFileSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { fixture } from './helpers/workflow-runner-fixture.mjs';
import { runStatus } from '../src/workflow-runner.mjs';

test('an actual failed pane command leaves an attributed receipt and status reports the exit', async t => {
  const f = await fixture(t, {agent: 'codex', name: 'feature'});
  const bin = join(f.base, 'bin'); mkdirSync(bin);
  writeFileSync(join(bin, 'codex'), '#!/bin/sh\necho secret-startup-error >&2\nexit 1\n', {mode: 0o755});
  const result = await f.run();
  assert.equal(result.exitCode, 0, result.message);
  assert.doesNotMatch(result.message, /Codex works/);
  const chat = f.record().chats.at(-1);
  const line = f.herdr.calls.find(a => a[0] === 'pane' && a[1] === 'run')[3];
  const child = spawnSync('sh', ['-c', line], {env: {...process.env, PATH: `${bin}:${process.env.PATH}`}, encoding: 'utf8'});
  assert.equal(child.status, 1);
  assert.match(child.stderr, /secret-startup-error/);
  assert.deepEqual(JSON.parse(readFileSync(chat.launchAttempt.exitFile, 'utf8')), {attemptId: chat.launchAttempt.id, exitCode: 1});
  f.herdr.paneOf(chat).agent = null;
  const status = await runStatus({ref:'17',cwd:f.source}, f.ports);
  assert.match(status.message, /failed.*code 1/);
  assert.match(status.message, /pdd workflow open 17 --new/);
  assert.doesNotMatch(JSON.stringify(f.record()), /secret-startup-error/);
  assert.equal(f.record().chats.at(-1).code, 'agent_launch_exited');
});

for (const receipt of ['bad', JSON.stringify({attemptId:'other',exitCode:1}), JSON.stringify({exitCode:0})]) test(`unattributed receipt ${receipt} does not prove failure`, async t => {
  const f = await fixture(t, {agent:'codex'}); await f.run();
  const chat = f.record().chats.at(-1); f.herdr.paneOf(chat).agent = null;
  writeFileSync(chat.launchAttempt.exitFile, receipt);
  const status = await runStatus({ref:'17',cwd:f.source}, f.ports);
  assert.match(status.message, /starting/);
  assert.equal(f.record().chats.at(-1).state, 'starting');
});

test('a matching zero receipt and a live agent do not establish startup failure', async t => {
  const f = await fixture(t, {agent:'codex'}); await f.run();
  const chat = f.record().chats.at(-1);
  writeFileSync(chat.launchAttempt.exitFile, JSON.stringify({attemptId:chat.launchAttempt.id,exitCode:0}));
  f.herdr.paneOf(chat).agent = null;
  assert.match((await runStatus({ref:'17',cwd:f.source},f.ports)).message, /starting/);
  writeFileSync(chat.launchAttempt.exitFile, JSON.stringify({attemptId:chat.launchAttempt.id,exitCode:1}));
  f.herdr.paneOf(chat).agent = { kind:'codex', status:'working' };
  const status = await runStatus({ref:'17',cwd:f.source},f.ports);
  assert.doesNotMatch(status.message, /chat failed/);
});
