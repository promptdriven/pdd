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
