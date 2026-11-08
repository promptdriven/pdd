import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { fixture } from './helpers/workflow-runner-fixture.mjs';
import { updateRun } from '../src/workflow-runs.mjs';
import { runAutopilotLauncher } from '../src/autopilot-launcher.mjs';
import { captureCosts, applyCostMeasurement } from '../src/cost-ledger.mjs';

const at = Date.parse('2026-10-27T17:00:00Z');
const ids = ['22222222-2222-4222-8222-222222222222', '33333333-3333-4333-8333-333333333333'];
const usage = (id, message) => JSON.stringify({ type: 'assistant', sessionId: id,
  message: { id: message, usage: { input_tokens: 20, output_tokens: 10 } } }) + '\n';
function sessions(t) {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-cost-repair-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const run = { agent: 'claude', configDir: join(root, 'wrong-default'), root: join(root, 'work'), runDir: root,
    startedAt: at, state: 'running', chats: [], abandonedChats: [] };
  const chats = ids.map((id, i) => ({ agent: 'claude', configDir: join(root, `account-${i}`), session: { id }, startedAt: at }));
  const files = chats.map((chat, i) => {
    const file = join(chat.configDir, 'projects', run.root.replace(/[^a-zA-Z0-9]/g, '-'), `${ids[i]}.jsonl`);
    fs.mkdirSync(join(file, '..'), { recursive: true }); fs.writeFileSync(file, usage(ids[i], 'first'));
    return file;
  });
  return { run, chats, files, ports: { now: () => at, env: { HOME: root }, fs } };
}

test('machine JSON retains archived attempts at reused paths in totals and merged percentiles', async t => {
  const f = await fixture(t); f.ports.skipMetricsDelivery = true; assert.equal((await f.run()).exitCode, 0);
  const old = updateRun(f.record().runDir, run => applyCostMeasurement(run, { id: 'old', suiteMinutes: 2, outcome: 'closed' }, f.clock), f.ports);
  const archive = `${old.runDir}-cancelled-aabbcc`; fs.renameSync(old.runDir, archive); fs.mkdirSync(old.runDir);
  const current = { ...old, runId: 'new-attempt', startedAt: f.clock + 1000, state: 'running', cost: undefined };
  applyCostMeasurement(current, { id: 'new', suiteMinutes: 5, outcome: 'merged' }, f.clock + 1000);
  fs.writeFileSync(join(current.runDir, 'status.json'), JSON.stringify(current)); f.tick(2000);
  const reply = await runAutopilotLauncher({ command: 'status', json: true, all: true, cwd: f.source, env: f.ports.env }, f.ports);
  assert.equal(reply.exitCode, 0); const report = JSON.parse(reply.message);
  assert.equal(report.runs.length, 2);
  assert.deepEqual(report.runs.map(row => row.suiteMinutes).sort((a,b) => a-b), [2,5]);
  for (const window of [report.day, report.week]) {
    assert.equal(window.totals.suiteMinutes, 7); assert.equal(window.mergedIssues, 1);
    assert.equal(window.p50.suiteMinutes, 7); assert.equal(window.p90.suiteMinutes, 7);
  }
  assert.equal(JSON.parse(fs.readFileSync(join(archive, 'status.json'))).cost.suiteMinutes, 2);
});

test('first capture includes abandoned sessions under each saved account and deduplicates custody', t => {
  const { run, chats, ports } = sessions(t);
  run.chats = [chats[1]]; run.abandonedChats = [{ ...chats[0], abandonedAt: at, reason: 'explicit-new-session' }];
  run.chatReplacement = { original: chats[1], replacement: chats[1] };
  run.cost = captureCosts(null, run, ports);
  assert.equal(run.cost.tokens.reduce((sum, row) => sum + row.total, 0), 60);
  assert.equal(run.cost.tokens.length, 2); assert.equal(Object.keys(run.cost.sessions).length, 2);
  const once = structuredClone(run.cost.tokens);
  run.cost = captureCosts(run, run, ports); assert.deepEqual(run.cost.tokens, once);
  for (const chat of chats) { assert.ok(!JSON.stringify(run.cost).includes(chat.session.id)); assert.ok(!JSON.stringify(run.cost).includes(chat.configDir)); }
});

test('bounded Claude backlog continues after chat custody moves to abandoned history', t => {
  const { run, chats, files, ports } = sessions(t);
  const padding = (JSON.stringify({ type: 'user', message: { content: 'synthetic padding'.repeat(50) } }) + '\n').repeat(500);
  fs.writeFileSync(files[0], usage(ids[0], 'first') + padding + usage(ids[0], 'last'));
  let bytes = 0;
  ports.sessionFs = { ...fs, readSync(fd, buffer, offset, length, position) { bytes += length; return fs.readSync(fd, buffer, offset, length, position); } };
  run.chats = [chats[0]]; run.cost = captureCosts(null, run, ports);
  assert.ok(bytes <= 256 * 1024); assert.ok(run.cost.coverage.includes('session-backlog'));
  assert.equal(run.cost.tokens[0].total, 30);
  const before = structuredClone(run); bytes = 0;
  run.chats = []; run.abandonedChats = [{ ...chats[0], abandonedAt: at }]; run.chatReplacement = { original: chats[0] };
  run.cost = captureCosts(before, run, ports); assert.ok(bytes <= 256 * 1024);
  // A new row arrives after the move and after the replacement envelope is overwritten.
  fs.appendFileSync(files[0], usage(ids[0], 'after-move')); run.chatReplacement = undefined; bytes = 0;
  run.cost = captureCosts(run, run, ports);
  assert.ok(bytes > 0 && bytes <= 256 * 1024); assert.equal(run.cost.tokens[0].total, 90);
  assert.equal(Object.keys(run.cost.sessions).length, 1); assert.ok(!run.cost.coverage.includes('session-backlog'));
  run.cost = captureCosts(run, run, ports); assert.equal(run.cost.tokens[0].total, 90);
});

test('a mutation retains prior abandoned and replacement custody while the new inventory is empty', t => {
  const { run, chats, ports } = sessions(t);
  const before = { ...run, abandonedChats: [chats[0]], chatReplacement: { original: chats[1] } };
  run.cost = captureCosts(before, run, ports);
  assert.equal(run.cost.tokens.reduce((sum, row) => sum + row.total, 0), 60);
  assert.equal(Object.keys(run.cost.sessions).length, 2);
});

test('workflow cost reads and explicit measurements preserve progress, index and completion journal', async t => {
  const f = await fixture(t); f.ports.skipMetricsDelivery = true; assert.equal((await f.run()).exitCode, 0);
  const { runCosts } = await import('../src/workflow-runner.mjs');
  const before = f.record(), file = join(before.runDir, 'status.json'), changedAt = f.clock - 2 * 60 * 60000;
  fs.utimesSync(file, new Date(changedAt), new Date(changedAt));
  const index = fs.readFileSync(join(f.state, 'runs.json'), 'utf8');
  f.tick(120000);
  for (const input of [undefined, { id: 'suite-repair', suiteMinutes: 2 }, undefined]) {
    assert.equal((await runCosts({ ref: '17', cwd: f.source, input }, f.ports)).exitCode, 0);
    const after = f.record();
    assert.equal(after.updatedAt, before.updatedAt); assert.equal(after.journalSeq, before.journalSeq);
    assert.deepEqual(after.metrics, before.metrics); assert.deepEqual(after.done, before.done);
    assert.deepEqual(after.gate, before.gate); assert.equal(after.progressAt, changedAt);
    assert.equal(fs.readFileSync(join(f.state, 'runs.json'), 'utf8'), index);
    f.tick(120000);
  }
  assert.equal(f.record().cost.suiteMinutes, 2);
});
