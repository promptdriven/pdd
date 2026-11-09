import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { launcher } from './helpers/environment-launcher-fixture.mjs';
import { environmentRun } from './helpers/environment-retry-fixture.mjs';
import { parkAutomaticRun, changeRun, askPerson } from '../src/workflow-runner.mjs';
import { writeRun } from '../src/workflow-runs.mjs';
const cause = 'Native validation timeout';
const issue = (f, extra = {}) => ({ number: 17, state: 'open', title: 'Retry validation', body: 'Retain work', user: { login: 'owner' },
  created_at: new Date(f.time).toISOString(), updated_at: new Date(f.time).toISOString(), comments: 0,
  labels: ['pdd:stuck', 'pdd:working'], html_url: 'https://github.com/owner/repo/issues/17', ...extra });
const comment = (f, author, body, id = 11) => ({ id, user: { login: author }, body,
  created_at: new Date(f.time).toISOString(), updated_at: new Date(f.time).toISOString() });
const delivered = f => f.packet().issues.find(row => row.number === 17);

for (const [working, legacy] of [[true, false], [false, false], [true, true]]) test(`removing stuck wakes held work on the next tick (working=${working}, legacy=${legacy}) and resumes only the failed step`, async t => {
  const f = await launcher(t); await f.start(); f.prompts.length = 0;
  f.issues = [issue(f)]; await f.tick(); assert.equal(f.prompts.length, 0);
  if (legacy) {
    const state = JSON.parse(readFileSync(f.stateFile(), 'utf8')); delete state.seen['17'].stuck;
    writeFileSync(f.stateFile(), JSON.stringify(state));
  }
  f.time += 60_000; f.issues[0].labels = working ? ['pdd:working'] : []; f.issues[0].updated_at = new Date(f.time).toISOString();
  // Continuation must not depend on fresh-work graph eligibility or allocator readiness.
  f.ports.reconcileDependencyIntake = async () => ({ eligible: [], queued: [], skipped: [] });
  f.ports.allocationCheck = async () => ({ state: 'refused', message: 'no fresh work' });
  await f.tick();
  assert.equal(f.prompts.length, 1, 'label removal must wake the coordinator at the next tick');
  assert.equal(delivered(f).retry?.source, 'stuck-label-removed');
  await f.tick(); assert.equal(f.prompts.length, 1, 'unchanged signals are consumed once');
  const worker = await environmentRun(t); const p = worker.ports();
  await parkAutomaticRun({ reason: cause, step: 'verify', cwd: worker.root }, p);
  const before = worker.f.record(); worker.f.herdr.paneOf(before.chats.at(-1)).agent.agent_status = 'idle';
  const result = await changeRun({ ref: '17', text: delivered(f).retry.text, cwd: worker.f.source }, p);
  assert.equal(result.exitCode, 0, result.message);
  assert.equal(worker.f.record().state, 'running', 'confirmed person retry resumes the failed step');
  for (const key of ['done', 'area', 'branch', 'automaticOrigin', 'environmentRetry']) assert.deepEqual(worker.f.record()[key], before[key]);
  assert.match(worker.f.herdr.paneOf(before.chats.at(-1)).agent.prompts.at(-1), /verify/);
});

test('a trusted retry comment on an initial stuck baseline wakes once; outsiders and old comments do not', async t => {
  const f = await launcher(t); await f.start(); f.prompts.length = 0;
  f.time += 60_000; let rows = [comment(f, 'outsider', 'Please retry the failed validation.')];
  f.ports.comments = async () => rows; f.issues = [issue(f, { comments: 1 })];
  await f.tick(); assert.equal(f.prompts.length, 0);
  rows.push(comment(f, 'owner', 'The machine is fixed; please retry the failed validation.', 12));
  f.issues[0].comments = 2; f.time += 60_000; f.issues[0].updated_at = new Date(f.time).toISOString();
  await f.tick(); assert.equal(f.prompts.length, 1);
  assert.equal(delivered(f).retry?.source, 'comment', 'trusted retry must have an explicit continuation action');
  assert.equal(delivered(f).retry.text, rows[1].body);
  const worker = await environmentRun(t); const p = worker.ports();
  await parkAutomaticRun({ reason: cause, step: 'verify', cwd: worker.root }, p);
  const before = worker.f.record(); const chat = worker.f.herdr.paneOf(before.chats.at(-1)); chat.agent.agent_status = 'idle';
  const resumed = await changeRun({ ref: '17', text: delivered(f).retry.text, cwd: worker.f.source }, p);
  assert.equal(resumed.exitCode, 0, resumed.message);
  assert.equal(worker.f.record().state, 'running', 'trusted comment resumes the failed validation');
  assert.deepEqual(worker.f.record().done, before.done);
  assert.deepEqual(worker.f.record().environmentRetry, before.environmentRetry);
  assert.match(chat.agent.prompts.at(-1), /verify/);
  assert.equal(delivered(f).comments.some(row => row.author === 'outsider'), false);
  await f.tick(); assert.equal(f.prompts.length, 1);
  // A new launcher baseline must still deliver a current trusted retry on a held issue.
  const state = JSON.parse(readFileSync(f.stateFile(), 'utf8')); state.seen = {}; writeFileSync(f.stateFile(), JSON.stringify(state));
  await f.tick(); assert.equal(f.prompts.length, 2, 'current retry cannot disappear into an initial waiting baseline');
  const old = JSON.parse(readFileSync(f.stateFile(), 'utf8')); old.seen = {}; writeFileSync(f.stateFile(), JSON.stringify(old));
  rows = [{ ...rows[1], created_at: '2020-01-01T00:00:00Z', updated_at: '2020-01-01T00:00:00Z' }];
  f.issues[0].comments = 1; f.issues[0].updated_at = new Date(++f.time).toISOString();
  await f.tick(); assert.equal(f.prompts.length, 2, 'historical retry is no fresh person instruction');
});

test('busy coordinator keeps a label-removal signal pending until confirmed delivery', async t => {
  const f = await launcher(t); await f.start(); f.prompts.length = 0; f.issues = [issue(f)]; await f.tick();
  const original = f.ports.herdr; let busy = true;
  f.ports.herdr = async args => {
    const result = await original(args);
    if (busy && args[0] === 'agent' && args[1] === 'get') result.result.agent.agent_status = 'working';
    return result;
  };
  f.issues[0].labels = ['pdd:working']; f.issues[0].updated_at = new Date(++f.time).toISOString();
  await f.tick(); assert.equal(f.prompts.length, 0);
  busy = false; await f.tick(); assert.equal(f.prompts.length, 1, 'busy delivery must not consume the retry signal');
  assert.equal(delivered(f).retry?.source, 'stuck-label-removed');
  await f.tick(); assert.equal(f.prompts.length, 1);
});

test('person retry preserves gates, questions and spent budget', async t => {
  const { f, ports, root } = await environmentRun(t); const p = ports();
  await askPerson({ text: 'Which output format?', cwd: root }, p);
  const run = f.record(); run.gate = { kind: 'approve', area: 'build', id: 'retained', at: f.clock - 1, promptSnapshot: [] }; writeRun(run);
  await parkAutomaticRun({ reason: cause, step: 'verify', cwd: root }, p);
  const exhausted = f.record(); exhausted.environmentRetry.attempts = 3; exhausted.environmentRetry.nextAt = null; writeRun(exhausted);
  const before = f.record(); const chat = f.herdr.paneOf(before.chats.at(-1)); chat.agent.agent_status = 'idle';
  await changeRun({ ref: '17', text: 'The machine is fixed\nPlease retry verify after the machine repair.', cwd: f.source }, p);
  assert.equal(f.record().state, 'waiting', 'retry resumes into the retained gate/question');
  for (const key of ['gate', 'question', 'done', 'environmentRetry']) assert.deepEqual(f.record()[key], before[key], key);
  assert.equal(f.record().changes.at(-1).answer, undefined);
  assert.equal(f.record().parkReason, undefined);
});

test('person retry resumes only after confirmed delivery and retains uncertain custody', async t => {
  for (const uncertain of [false, true]) {
    const { f, ports, root } = await environmentRun(t); const p = ports();
    await parkAutomaticRun({ reason: cause, step: 'verify', cwd: root }, p);
    const before = f.record(); const chat = f.herdr.paneOf(before.chats.at(-1)); chat.agent.agent_status = 'idle'; const transport = p.herdr;
    p.herdr = async args => {
      if (args[0] === 'agent' && args[1] === 'prompt') { if (uncertain) await transport(args); throw Object.assign(Error('transport'), { code: uncertain ? 'connection_lost' : 'agent_blocked' }); }
      return transport(args);
    };
    await changeRun({ ref: '17', text: 'Retry verify now.', cwd: f.source }, p);
    assert.equal(f.record().state, 'stuck'); assert.deepEqual(f.record().environmentRetry, before.environmentRetry);
    const sent = chat.agent.prompts.length; p.herdr = transport;
    await changeRun({ ref: '17', text: 'Retry verify now.', cwd: f.source }, p);
    assert.equal(f.record().state, uncertain ? 'stuck' : 'running', 'only confirmed delivery resumes');
    assert.equal(chat.agent.prompts.length, sent + (uncertain ? 0 : 1));
  }
});

test('person retries preserve STOP, claim ownership and repair ceilings', async t => {
  const { f, ports, root } = await environmentRun(t); const p = ports();
  await parkAutomaticRun({ reason: cause, step: 'verify', cwd: root }, p);
  const before = f.record(); const chat = f.herdr.paneOf(before.chats.at(-1)); chat.agent.agent_status = 'idle';
  const stateFile = join(p.autopilotStateRoot, (await import('node:fs')).readdirSync(p.autopilotStateRoot)[0]);
  const state = JSON.parse(readFileSync(stateFile, 'utf8'));
  for (const block of ['stop', 'claim', 'limit', 'integration-limit']) {
    writeFileSync(stateFile, JSON.stringify({ ...state, enabled: block !== 'stop' }));
    const run = structuredClone(before); if (block === 'limit') run.repairLimit = { area: 'build', step: 'verify', at: f.clock }; writeRun(run);
    if (block === 'integration-limit') { run.integrationLimit = { area: 'build', step: 'verify', at: f.clock }; writeRun(run); }
    const calls = chat.agent.prompts.length;
    const blocked = block === 'claim' ? ports({ execFile: async (file, args, options) => {
      if (file === 'gh' && args[0] === 'api' && args[1] === '--include') throw Error('ownership unavailable');
      return p.execFile(file, args, options);
    } }) : p;
    const result = await changeRun({ ref: '17', text: 'Retry verify now.', cwd: f.source }, blocked);
    assert.notEqual(result.exitCode, 0, `${block} refuses retry`);
    assert.equal(f.record().state, 'stuck'); assert.equal(chat.agent.prompts.length, calls);
  }
});
