// Approved fresh-session preservation variants; native commands are recorded by fake Herdr only.
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { openRun, stepDone, approveRun } from '../src/workflow-runner.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const open = (f, input = {}) => openRun({ ref: '17', cwd: f.source, packageRoot, ...input }, f.ports);
const launches = f => f.herdr.calls.filter(args => args[0] === 'pane' && args[1] === 'run');

test('2627 terminal replacement permits normal advancement and opening the next current area', async t => {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  const original = f.record().chats.at(-1);
  assert.equal((await open(f, { newSession: true })).exitCode, 0);
  const replaced = f.record();
  assert.notEqual(replaced.chats.at(-1).paneId, original.paneId, 'Explicit replacement must install a fresh identity');
  assert.equal(replaced.chatReplacement.phase, 'launched');
  assert.equal((await stepDone({ step: 'scope', summary: 'Scope is complete; continue the saved run.', cwd: replaced.root }, f.agentPorts())).exitCode, 0);
  assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  const advanced = f.record(), current = advanced.chats.at(-1);
  assert.equal(advanced.areas[advanced.area].name, 'build');
  assert.equal(advanced.chatReplacement.area, 'plan');
  const dispatches = launches(f).length;
  const result = await open(f);
  assert.equal(result.exitCode, 0, result.message);
  assert.equal(f.herdr.focus, current.tabId);
  assert.equal(launches(f).length, dispatches, 'Opening the later current area focuses its saved chat');
  assert.equal(f.record().area, advanced.area);
});

test('2627 Codex replacement keeps the saved configuration and launches once without resume', async t => {
  const f = await fixture(t, { agent: 'codex' });
  const configDir = join(f.base, 'saved codex config');
  mkdirSync(configDir);
  f.ports.env.CODEX_HOME = configDir;
  assert.equal((await f.run()).exitCode, 0);
  const before = f.record(), original = before.chats.at(-1);
  f.herdr.calls.length = 0;
  const result = await open(f, { newSession: true });
  assert.equal(result.exitCode, 0, result.message);
  const after = f.record(), replacement = after.chats.at(-1);
  assert.notEqual(replacement.paneId, original.paneId, 'Explicit replacement must install a fresh Codex identity');
  assert.equal(replacement.agent, 'codex');
  assert.equal(replacement.configDir, configDir);
  assert.equal(after.root, before.root);
  assert.equal(after.runId, before.runId);
  assert.equal(after.branch, before.branch);
  assert.equal(launches(f).length, 1);
  const command = launches(f)[0][3];
  assert.ok(command.includes(`CODEX_HOME='${configDir}'`));
  assert.match(command, /codex --no-daemon --dangerously-bypass-approvals-and-sandbox/);
  assert.doesNotMatch(command, /\bresume\b|--session-id|--resume/);
  assert.equal(after.abandonedChats.length, 1);
});
