import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, writeFileSync, readFileSync, symlinkSync, existsSync, realpathSync } from 'node:fs';
import { join, resolve, delimiter } from 'node:path';
import { spawnSync } from 'node:child_process';
import { fixture } from './helpers/workflow-delivery-fixture.mjs';
import { stepDone, approveRun, cancelRun, runStatus } from '../src/workflow-runner.mjs';

// Build the held notice through the public workflow, not a saved-state edit.
async function heldNotice(t) {
  const f = await fixture(t, { name: 'feature', agent: 'codex' });
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({strict_approvals:true}));
  f.ports.stateDir = join(f.ports.env.HOME, '.local', 'state', 'pdd');
  const skill = join(f.source, '.agents/skills/pdd-feature');
  mkdirSync(skill, { recursive: true });
  writeFileSync(join(skill, 'workflow.json'), JSON.stringify({ version: 2, areas: [
    { name: 'story', steps: ['understand', 'prompt-story'], optional: [], gate: 'approve' },
    { name: 'prompt-pr', steps: ['check', 'try'], optional: ['try'], gate: 'pr', before: 'approve', then: 'ask-code' },
    { name: 'code', steps: ['build', 'verify'], optional: [], gate: 'pr' }
  ] }));
  assert.equal((await f.run()).exitCode, 0);
  const root = f.record().root;
  const finish = async step => {
    f.tick();
    const result = await stepDone({ step, summary: 'Synthetic integration fixture.', cwd: root }, f.agentPorts());
    assert.equal(result.exitCode, 0, result.message);
  };
  await finish('understand');
  writeFileSync(join(root, 'feature.prompt.md'), 'Return two.\n');
  f.git(root, 'add', '.'); f.git(root, 'commit', '-qm', 'synthetic integration prompt');
  await finish('prompt-story'); f.tick();
  assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  await finish('check'); await finish('try');
  const pane = f.herdr.paneOf(f.record().chats.at(-1));
  pane.agent.agent_status = 'blocked';
  const answers = [true, false];
  f.ports.confirm = async () => answers.shift(); f.tick();
  const stopped = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(stopped.exitCode, 0, stopped.message);
  const notice = f.journal().find(row => row.kind === 'notice');
  assert.ok(notice, 'PR 1 creates retained notice custody');
  assert.equal(notice.state, 'pending');
  assert.ok(notice.text.includes('\n'), 'the public producer supplies a multiline notice');
  assert.ok(notice.reason);
  return { f, pane, notice };
}

function finalNotice(message, notice, ended = false) {
  assert.match(message, /pdd notice was not sent and later changes will not send it/);
  assert.ok(message.includes(notice.text), 'the exact saved multiline notice remains readable');
  assert.ok(message.includes(notice.reason), 'the last saved delivery reason remains readable');
  if (ended) assert.match(message, /run ended/i);
}

test('2949 ended current-area notice stays complete in API and real CLI status without delivery', async t => {
  const { f, notice } = await heldNotice(t);
  assert.equal((await cancelRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  const run = f.record();
  assert.equal(run.areas[run.area].name, notice.area, 'ending did not advance the original area');
  const path = join(run.runDir, 'delivery-journal.json'), before = readFileSync(path);
  const sends = f.herdr.calls.filter(args => args[0] === 'agent' && args[1] === 'prompt').length;
  for (const input of [{ ref: '17' }, {}, { all: true }]) {
    const status = await runStatus({ ...input, cwd: f.source, cancelled: true }, f.ports);
    assert.equal(status.exitCode, 0, status.message);
    finalNotice(status.message, notice, true);
  }
  const json = JSON.parse((await runStatus({ ref: '17', cwd: f.source, json: true }, f.ports)).message).runs[0];
  assert.deepEqual(json.nativeResults, [], 'main native-results projection survives alongside notice status');
  assert.deepEqual(json.pendingRequests.find(row => row.id === notice.id), {
    id: notice.id, text: notice.text, area: notice.area, paneId: notice.paneId, kind: 'notice', reason: notice.reason
  });

  // Isolate the real CLI from installed Herdr/gh and credentials. Git reads the
  // disposable fixture; external tools are unavailable, never live services.
  const bin = join(f.base, 'status-bin'); mkdirSync(bin);
  const git = process.env.PATH.split(delimiter).map(dir => join(dir, 'git')).find(path => existsSync(path));
  assert.ok(git, 'the fixture already requires native Git');
  symlinkSync(realpathSync(git), join(bin, 'git'));
  for (const tool of ['gh', 'herdr']) writeFileSync(join(bin, tool), '#!/bin/sh\nexit 1\n', { mode: 0o700 });
  const cli = spawnSync(process.execPath, [resolve(import.meta.dirname, '../bin/pdd.mjs'), 'workflow', 'status', '17', '--cancelled'], {
    cwd: f.source, encoding: 'utf8', timeout: 10000,
    env: { ...f.ports.env, PATH: bin, PDD_STATE_DIR: f.state }
  });
  assert.equal(cli.error, undefined, cli.error?.message);
  assert.equal(cli.status, 0, cli.stderr + cli.stdout);
  finalNotice(cli.stdout, notice, true);
  assert.deepEqual(readFileSync(path), before, 'all status readers preserve journal bytes');
  assert.equal(f.herdr.calls.filter(args => args[0] === 'agent' && args[1] === 'prompt').length, sends);
});

test('2949 merged PR 1 completion retains the current-area full notice fallback', async t => {
  const { f, notice } = await heldNotice(t);
  const before = readFileSync(join(f.record().runDir, 'delivery-journal.json'));
  f.mergedNumbers.push(f.prs[0].number);
  const status = await runStatus({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(status.exitCode, 0, status.message);
  assert.equal(f.record().state, 'completed');
  assert.equal(f.record().areas[f.record().area].name, notice.area);
  finalNotice(status.message, notice, true);
  assert.deepEqual(readFileSync(join(f.record().runDir, 'delivery-journal.json')), before);
});

test('2949 ended status never classifies uncertain or in-flight notice custody as definitely unsent', async t => {
  const { f, notice } = await heldNotice(t);
  assert.equal((await cancelRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  for (const state of ['uncertain', 'in-flight']) {
    const entry = { ...notice, state: state === 'uncertain' ? 'uncertain' : 'pending', ...(state === 'in-flight' ? { inFlight: true } : {}) };
    const bytes = JSON.stringify({ requests: [entry] });
    const ports = { ...f.ports, deliveryFiles: {
      readFileSync: () => bytes,
      writeFileSync: () => assert.fail('status cannot mutate protected delivery custody')
    } };
    for (const input of [{ ref: '17' }, {}, { all: true }]) {
      const result = await runStatus({ ...input, cwd: f.source, cancelled: true }, ports);
      assert.equal(result.exitCode, 0, result.message);
      assert.ok(!result.message.includes('was not sent'), `${state} cannot claim never sent`);
      assert.ok(!result.message.includes('later changes will not send it'), `${state} retains its uncertainty/protection advice`);
      assert.ok(result.message.includes(notice.id));
    }
    const json = JSON.parse((await runStatus({ ref: '17', cwd: f.source, json: true }, ports)).message).runs[0];
    assert.equal(json.pendingRequests.length, 0);
    const rows = state === 'uncertain' ? json.uncertainRequests : json.inFlightRequests;
    assert.equal(rows[0].text, notice.text);
    assert.equal(rows[0].paneId, notice.paneId);
    assert.equal(bytes, JSON.stringify({ requests: [entry] }));
  }
});

test('2949 approval retains full notice and saved custody when the next chat launch is unconfirmed', async t => {
  const { f, pane, notice } = await heldNotice(t);
  pane.agent.agent_status = 'idle'; f.ports.confirm = async () => true; f.tick();
  const before = readFileSync(join(f.record().runDir, 'delivery-journal.json'));
  const herdr = f.ports.herdr;
  f.ports.herdr = args => {
    if (args[0] === 'pane' && args[1] === 'run') throw Object.assign(Error('synthetic lost launch reply'), { code: 'server_unavailable' });
    return herdr(args);
  };
  const result = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(result.exitCode, 1);
  assert.match(result.message, /Approved the prompt-pr area/);
  assert.match(result.message, /startup was not confirmed/);
  assert.match(result.message, /warning: Request/);
  finalNotice(result.message, notice);
  assert.ok(result.message.includes(`${notice.text}\nwarning: Last delivery reason: ${notice.reason}.`), 'approval retains the raw notice before its warning-prefixed delivery reason');
  assert.equal(f.record().areas[f.record().area].name, 'code');
  assert.deepEqual(readFileSync(join(f.record().runDir, 'delivery-journal.json')), before);
});
