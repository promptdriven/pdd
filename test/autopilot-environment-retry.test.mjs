import test from 'node:test';
import assert from 'node:assert/strict';
import { parkAutomaticRun, changeRun, runStatus, stepDone, askPerson } from '../src/workflow-runner.mjs';
import { environmentRun } from './helpers/environment-retry-fixture.mjs';
const minute = 60_000;
const cause = 'Native full suite cancelled/incomplete in confirmed filesystem journal I/O stall';
const tag = r => `Environment validation wake for ${r.area}:${r.step} at ${new Date(r.at).toISOString()} attempt ${r.attempts + 1}.`;

for (const [reason, expected] of [
  [cause, 'environment'], ['Native validation timeout', 'environment'], ['Native test process killed', 'environment'],
  ['Full suite queue is full', 'environment'], ['missing tool: node', 'environment'],
  ['Real failing test with disk pressure', 'work'], ['Review must-fix after native timeout', 'work'],
  ['Unresolved proof assertion and filesystem journal I/O stall', 'work'],
  ['Interpreter saved-batch read has an unknown outcome; do not resend', 'interpreter'],
  ['A product decision is required', 'work'],
  ['unknown outcome; assertion failed', 'work'],
  ['Real failing test and saved-batch reconciliation', 'work'],
  ['Native test timeout; 2 tests failed', 'work'],
  ['A failing test and filesystem journal I/O stall', 'work'],
  ['Native test failure during disk pressure', 'work'],
  ['Public suite is red; native timeout', 'work'],
  ['3 failures in tests; native test timeout', 'work'],
  ['Killed test process during infrastructure stall', 'environment'],
]) test(`park classifies: ${expected}: ${reason}`, async t => {
  const { f, ports, root } = await environmentRun(t);
  const before = f.record();
  const result = await parkAutomaticRun({ reason, step: 'verify', cwd: root }, ports());
  assert.equal(result.exitCode, 0, result.message);
  assert.equal(f.record().stuckCause, expected, 'stop cause is recorded');
  for (const key of ['area', 'done', 'gate', 'branch', 'root', 'automaticOrigin', 'chats']) assert.deepEqual(f.record()[key], before[key], key);
});

test('environment park waits visibly, preserves duplicate time and rejects invalid step without mutation', async t => {
  const { f, ports, root } = await environmentRun(t);
  await parkAutomaticRun({ reason: cause, step: 'verify', cwd: root }, ports());
  const parked = f.record();
  assert.equal(parked.environmentRetry?.nextAt, f.clock + 15 * minute, 'first retry waits 15 minutes');
  f.tick(minute);
  await parkAutomaticRun({ reason: cause, step: 'verify', cwd: root }, ports());
  assert.deepEqual(f.record().environmentRetry, parked.environmentRetry);
  const listed = JSON.parse((await runStatus({ cwd: f.source, json: true }, ports())).message).runs[0];
  assert.equal(listed.group, 'working');
  assert.match(listed.words, /attempt 1 of 3/); assert.ok(listed.words.includes(new Date(parked.environmentRetry.nextAt).toISOString()));
  const before = f.record();
  assert.equal((await parkAutomaticRun({ reason: cause, step: 'build', cwd: root }, ports())).exitCode, 1);
  assert.deepEqual(f.record(), before);
});

test('three retries keep work, reject stale/early/unhealthy wakes, and cannot exceed the budget', async t => {
  const { f, ports, root } = await environmentRun(t);
  const checks = [];
  const healthy = ports({ environmentHealthy: async () => { checks.push(f.clock); return true; } });
  const doneBefore = f.record().done;
  let previousTag;
  for (const [attempt, delay] of [15, 60, 240].entries()) {
    const reason = attempt ? `Native full suite timeout attempt ${attempt}` : cause;
    assert.equal((await parkAutomaticRun({ reason, step: 'verify', cwd: root }, healthy)).exitCode, 0);
    const parked = f.record(), retry = parked.environmentRetry;
    assert.equal(retry?.attempts, attempt, 'same validation retains its retry budget');
    assert.equal(retry.nextAt, f.clock + delay * minute);
    const text = tag(retry) + ' Rerun only verify.';
    const chat = f.herdr.paneOf(parked.chats.at(-1)); chat.agent.agent_status = 'idle';
    const sent = chat.agent.prompts.length;
    await changeRun({ ref: '17', text, cwd: f.source }, healthy);
    assert.equal(chat.agent.prompts.length, sent, 'early wake sends nothing');
    f.tick(delay * minute);
    await changeRun({ ref: '17', text, cwd: f.source }, ports({ environmentHealthy: async () => false }));
    if (previousTag) await changeRun({ ref: '17', text: previousTag, cwd: f.source }, healthy);
    assert.equal(chat.agent.prompts.length, sent, 'unhealthy and stale wakes cannot bypass retry admission');
    const delivered = await changeRun({ ref: '17', text, cwd: f.source }, healthy);
    assert.equal(delivered.exitCode, 0, delivered.message);
    assert.equal(chat.agent.prompts.length, sent + 1);
    assert.equal(f.record().environmentRetry.attempts, attempt + 1);
    assert.equal(f.record().state, 'running');
    for (const key of ['area', 'done', 'gate', 'branch', 'automaticOrigin']) assert.deepEqual(f.record()[key], parked[key], key);
    await changeRun({ ref: '17', text, cwd: f.source }, healthy);
    assert.equal(chat.agent.prompts.length, sent + 1, 'delivered wake is not repeated');
    previousTag = text;
  }
  await parkAutomaticRun({ reason: cause, step: 'verify', cwd: root }, healthy);
  assert.equal(f.record().environmentRetry.attempts, 3);
  assert.equal(f.record().environmentRetry.nextAt, null);
  const exhausted = await runStatus({ ref: '17', cwd: f.source }, healthy);
  assert.match(exhausted.message, /Next:.*exhausted/);
  const before = f.record(); f.tick(24 * 60 * minute);
  await changeRun({ ref: '17', text: tag(before.environmentRetry), cwd: f.source }, healthy);
  assert.equal(f.record().state, 'stuck'); assert.deepEqual(f.record().done, doneBefore);
  assert.ok(checks.length >= 9, 'health is rechecked on delivery');
});

test('successful failed-step completion clears budget; unrelated progress keeps it', async t => {
  const { f, ports, root } = await environmentRun(t);
  const p = ports({ environmentHealthy: async () => true });
  await parkAutomaticRun({ reason: cause, step: 'verify', cwd: root }, p);
  const retry = f.record().environmentRetry;
  assert.ok(retry, 'environment failure is recorded');
  f.tick(15 * minute);
  await changeRun({ ref: '17', text: tag(retry) + ' Rerun only verify.', cwd: f.source }, p);
  await stepDone({ step: 'change', summary: 'existing change', cwd: root }, p);
  assert.equal(f.record().environmentRetry.attempts, 1);
  await stepDone({ step: 'verify', skipped: 'pending validation', cwd: root }, p);
  assert.equal(f.record().environmentRetry.attempts, 1, 'a skipped validation cannot reset retries');
  await stepDone({ step: 'verify', summary: 'validation complete', cwd: root }, p);
  assert.equal(f.record().environmentRetry, undefined);
});


test('environment parks require the failed target instead of guessing between unfinished validations', async t => {
  const { f, ports, root } = await environmentRun(t);
  const before = f.record();
  const result = await parkAutomaticRun({ reason: cause, cwd: root }, ports());
  assert.equal(result.exitCode, 1, 'do not guess which validation failed');
  assert.deepEqual(f.record(), before);
});


test('CLI forwards the failed validation target without invoking any service', async () => {
  const { runPdd } = await import('../src/pdd-cli.mjs');
  const calls = [], output = { write() {} };
  const result = await runPdd(['workflow', 'park', '--reason', cause, '--step', 'verify'], {
    cwd: '/synthetic/project', packageRoot: '/synthetic/pdd', stdout: output, stderr: output,
    workflowRunner: { parkAutomaticRun: async input => { calls.push(input); return { exitCode: 0, message: 'recorded' }; } },
  });
  assert.equal(result, 0, 'CLI accepts the failed validation step');
  assert.equal(calls.length, 1);
  assert.deepEqual(calls[0], { reason: cause, step: 'verify', runtime: false, cwd: '/synthetic/project', packageRoot: '/synthetic/pdd' });
});


test('ordinary requests still reach an environment-stuck run without spending or resuming its retry', async t => {
  const { f, ports, root } = await environmentRun(t);
  const p = ports({ environmentHealthy: async () => false });
  await parkAutomaticRun({ reason: cause, step: 'verify', cwd: root }, p);
  const before = f.record(); f.herdr.paneOf(before.chats.at(-1)).agent.agent_status = 'idle';
  const result = await changeRun({ ref: '17', text: 'Use the retained validation log', cwd: f.source }, p);
  assert.equal(result.exitCode, 0, result.message);
  assert.equal(f.record().state, 'stuck');
  assert.deepEqual(f.record().environmentRetry, before.environmentRetry);
  assert.equal(f.record().changes.length, before.changes.length + 1);
});


for (const uncertain of [false, true]) test(`an ${uncertain ? 'uncertain' : 'unsent'} wake does not consume the retry or change the gate`, async t => {
  const { f, ports, root } = await environmentRun(t);
  const { writeRun } = await import('../src/workflow-runs.mjs');
  const run = f.record(); run.gate = { kind: 'approve', area: 'build', id: 'retained-gate', at: f.clock, promptSnapshot: [] }; writeRun(run);
  const p = ports({ environmentHealthy: async () => true });
  await parkAutomaticRun({ reason: cause, step: 'verify', cwd: root }, p);
  const before = f.record(); assert.ok(before.environmentRetry, 'environment failure is recorded'); f.tick(15 * minute); f.herdr.paneOf(before.chats.at(-1)).agent.agent_status = 'idle';
  const transport = p.herdr;
  p.herdr = async args => {
    if (args[0] === 'agent' && args[1] === 'prompt') {
      if (uncertain) await transport(args);
      throw Object.assign(Error('transport stopped'), { code: uncertain ? 'connection_lost' : 'agent_blocked' });
    }
    return transport(args);
  };
  const text = tag(before.environmentRetry) + ' Rerun only verify.';
  await changeRun({ ref: '17', text, cwd: f.source }, p);
  assert.equal(f.record().state, 'stuck');
  assert.equal(f.record().environmentRetry.attempts, 0);
  assert.deepEqual(f.record().gate, before.gate);
  // A repeat uses the existing journal: uncertain delivery is never sent blind.
  const count = f.herdr.paneOf(before.chats.at(-1)).agent.prompts.length;
  if (uncertain) {
    p.herdr = transport;
    await changeRun({ ref: '17', text, cwd: f.source }, p);
    assert.equal(f.herdr.paneOf(before.chats.at(-1)).agent.prompts.length, count);
    assert.equal(f.record().environmentRetry.attempts, 0);
  } else {
    p.herdr = transport;
    await changeRun({ ref: '17', text, cwd: f.source }, p);
    assert.equal(f.record().environmentRetry.attempts, 1);
    assert.deepEqual(f.record().gate, before.gate, 'confirmed validation retry preserves the gate identity');
  }
});


test('environment wake preserves an open question and is never delivered as its answer', async t => {
  const { f, ports, root } = await environmentRun(t);
  const p = ports({ environmentHealthy: async () => true });
  await askPerson({ text: 'Which output format should this work use?', cwd: root }, p);
  await parkAutomaticRun({ reason: cause, step: 'verify', cwd: root }, p);
  const before = f.record(); assert.ok(before.environmentRetry, 'environment failure is recorded'); f.tick(15 * minute); f.herdr.paneOf(before.chats.at(-1)).agent.agent_status = 'idle';
  const result = await changeRun({ ref: '17', text: tag(before.environmentRetry) + ' Rerun only verify.', cwd: f.source }, p);
  assert.equal(result.exitCode, 0, result.message);
  assert.deepEqual(f.record().question, before.question, 'a validation wake cannot answer a person decision');
  assert.equal(f.record().state, 'waiting');
  assert.equal(f.record().environmentRetry.attempts, 1);
  assert.equal(f.record().changes.at(-1).answer, undefined);
});

for (const stale of [false, true]) test(`a pending ${stale ? 'obsolete' : 'unhealthy'} wake cannot block a later ordinary request`, async t => {
  const { f, ports, root } = await environmentRun(t);
  const p = ports({ environmentHealthy: async () => true });
  await parkAutomaticRun({ reason: cause, step: 'verify', cwd: root }, p);
  const parked = f.record(); assert.ok(parked.environmentRetry, 'environment failure is recorded'); f.tick(15 * minute);
  f.herdr.paneOf(parked.chats.at(-1)).agent.agent_status = 'blocked';
  await changeRun({ ref: '17', text: tag(parked.environmentRetry) + ' Rerun only verify.', cwd: f.source }, p);
  assert.equal(f.record().environmentRetry.attempts, 0);
  if (stale) { f.tick(); await parkAutomaticRun({ reason: 'Native validation timeout', step: 'verify', cwd: root }, p); }
  else p.environmentHealthy = async () => false;
  f.herdr.paneOf(parked.chats.at(-1)).agent.agent_status = 'idle';
  const text = 'Retain the original validation evidence';
  const result = await changeRun({ ref: '17', text, cwd: f.source }, p);
  assert.equal(result.exitCode, 0, result.message);
  assert.equal(f.record().changes.at(-1).text, text, 'later requests must reach the chat');
  assert.equal(f.record().environmentRetry.attempts, 0);
  assert.equal(f.record().state, 'stuck');
});
