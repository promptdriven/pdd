import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, writeFileSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { fixture } from './helpers/workflow-delivery-fixture.mjs';
import { stepDone, approveRun, changeRun, runStatus } from '../src/workflow-runner.mjs';

async function held(t) {
  const f = await fixture(t, { name: 'feature', agent: 'codex' });
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({strict_approvals:true}));
  const skill = join(f.source, '.agents/skills/pdd-feature'); mkdirSync(skill, { recursive: true });
  writeFileSync(join(skill, 'workflow.json'), JSON.stringify({ version: 2, areas: [
    { name: 'story', steps: ['understand', 'prompt-story'], optional: [], gate: 'approve' },
    { name: 'prompt-pr', steps: ['check', 'try'], optional: ['try'], gate: 'pr', before: 'approve', then: 'ask-code' },
    { name: 'code', steps: ['build', 'verify'], optional: [], gate: 'pr' }
  ] }));
  assert.equal((await f.run()).exitCode, 0);
  const root = f.record().root;
  const finish = async step => { f.tick(); const r = await stepDone({ step, summary: 'Synthetic result', cwd: root }, f.agentPorts()); assert.equal(r.exitCode, 0, r.message); };
  await finish('understand'); writeFileSync(join(root, 'feature.prompt.md'), 'Return two.\n');
  f.git(root, 'add', '.'); f.git(root, 'commit', '-qm', 'fixture prompt');
  await finish('prompt-story'); f.tick(); assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  await finish('check'); await finish('try');
  const old = f.record().chats.at(-1), pane = f.herdr.paneOf(old); pane.agent.agent_status = 'blocked';
  const answers = [true, false]; f.ports.confirm = async () => answers.shift(); f.tick();
  const stopped = await approveRun({ ref: '17', cwd: f.source }, f.ports); assert.equal(stopped.exitCode, 0, stopped.message);
  const notice = f.journal().find(row => row.kind === 'notice'); assert.ok(notice, 'the unsent PR notice is retained'); assert.equal(notice.state, 'pending'); assert.ok(notice.reason);
  assert.match(stopped.message, /warning:/); assert.equal(f.record().changes.length, 0);
  return { f, pane, notice };
}

test('held PR notice remains visible after approval advances to code', async t => {
  const { f, pane, notice } = await held(t);
  pane.agent.agent_status = 'idle'; f.ports.confirm = async () => true; f.tick();
  const advanced = await approveRun({ ref: '17', cwd: f.source }, f.ports); assert.equal(advanced.exitCode, 0, advanced.message);
  assert.ok(advanced.message.includes(notice.text)); assert.ok(advanced.message.includes(notice.reason)); assert.match(advanced.message, /will not send/);
  const before = readFileSync(join(f.record().runDir, 'delivery-journal.json'), 'utf8');
  const status = await runStatus({ ref: '17', cwd: f.source }, f.ports);
  assert.ok(status.message.includes(notice.text)); assert.ok(status.message.includes(notice.reason)); assert.match(status.message, /will not send/);
  const json = JSON.parse((await runStatus({ ref: '17', cwd: f.source, json: true }, f.ports)).message).runs[0];
  assert.deepEqual(json.pendingRequests.find(row => row.id === notice.id), { id: notice.id, text: notice.text, area: notice.area, paneId: notice.paneId, kind: 'notice', reason: notice.reason });
  assert.equal(readFileSync(join(f.record().runDir, 'delivery-journal.json'), 'utf8'), before);
  const current = f.record().chats.at(-1); f.herdr.paneOf(current).agent.agent_status = 'idle';
  const changed = await changeRun({ ref: '17', text: 'Add a test', cwd: f.source }, f.ports); assert.equal(changed.exitCode, 0, changed.message);
  const sends = f.herdr.calls.filter(args => args[0] === 'agent' && args[1] === 'prompt');
  assert.equal(sends.length, 1); assert.equal(sends[0][2], current.paneId); assert.ok(sends[0][3].includes('Add a test'));
  assert.deepEqual(f.journal().find(row => row.id === notice.id), notice); assert.equal(f.record().changes.length, 1);
});


test('held notice is sent once before the next change in its original chat', async t => {
  const { f, pane, notice } = await held(t);
  pane.agent.agent_status = 'idle';
  const result = await changeRun({ ref: '17', text: 'Use a retry', cwd: f.source }, f.ports);
  assert.equal(result.exitCode, 0, result.message);
  const sends = f.herdr.calls.filter(args => args[0] === 'agent' && args[1] === 'prompt');
  assert.equal(sends.length, 2); assert.equal(sends[0][3], notice.text); assert.ok(sends[1][3].includes('Use a retry'));
  assert.equal(f.journal().find(row => row.id === notice.id).state, 'delivered');
  assert.equal(f.record().changes.length, 1);
  await changeRun({ ref: '17', text: 'Another change', cwd: f.source }, f.ports);
  assert.equal(f.herdr.calls.filter(args => args[1] === 'prompt' && args[3] === notice.text).length, 1);
});
