import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { launcher } from './helpers/environment-launcher-fixture.mjs';
import { environmentRun } from './helpers/environment-retry-fixture.mjs';
import { isRetryRequest, parkAutomaticRun, changeRun } from '../src/workflow-runner.mjs';
import { writeRun } from '../src/workflow-runs.mjs';

const diagnostics = [
  ['release inflected status', 'Retrying.'],
  ['release inflected noun', 'Retries.'],
  ['release retrying denial', 'Please retry verify. No retrying.'],
  ['release retrying forbidden', 'Please retry verify. Retrying is forbidden.'],
  ['release retries disabled', 'Please retry verify. Retries are disabled.'],
  ['review counterexample', 'The last attempt failed; retry is still blocked by disk pressure. Do not resume.'],
  ['status after punctuation', 'The host is unhealthy; retry is blocked by disk pressure.'],
  ['leading retry status', 'Retry is still blocked by disk pressure.'],
  ['leading resume status', 'Resume remains unsafe while disk pressure is high.'],
  ['try-again mention', 'Try again is only the diagnostic text, not a request.'],
  ['negative after command', 'Please retry verify. Do not resume.'],
  ['negative before command', 'Do not resume.\nPlease retry verify.'],
  ['never instruction', 'Retry verify now; never retry while disk pressure is high.'],
  ['reported command', 'The log says: retry verify now.'],
  ['reported multiline command', 'Diagnostic output:\nRetry verify now.'],
  ['policy after repair', 'The machine is fixed; retry budget is still exhausted.'],
  ['diagnostic heading', 'Retry: still blocked by disk pressure.'],
  ['contracted negative', "Please retry verify. Don't resume."],
  ['negative continuation', 'Please retry verify. Do not continue until the disk is repaired.'],
  ['quoted command', '```text\nRetry verify now.\n```'],
  ['continuation denied', 'Please retry verify. Resume is not allowed.'],
  ['negative resuming', 'Please retry verify. No resuming.'],
  ['wait before resuming', 'Retry verify now. Wait for my approval before resuming.'],
];
const requests = [
  'Retry.', 'Resume the failed step.', 'Try again!',
  'Please retry the failed validation.', 'Can you please retry verify now?',
  'Could you resume the run?', 'Would you please try again?',
  'The machine is fixed; please retry the failed validation.',
  'The host is repaired. Retry verify now.',
  'The machine is fixed\nPlease retry verify after the machine repair.',
  'Retry the failed step from retained evidence. Preserve completed work, gates, questions, branch and claim.',
];
const issue = f => ({ number: 17, state: 'open', title: 'Retry validation', body: 'Retain work', user: { login: 'owner' },
  created_at: new Date(f.time).toISOString(), updated_at: new Date(f.time).toISOString(), comments: 1,
  labels: ['pdd:stuck', 'pdd:working'], html_url: 'https://github.com/owner/repo/issues/17' });

for (const [name, text] of diagnostics) {
  test(`retry predicate rejects ${name} and retains direct requests`, () => {
    assert.equal(isRetryRequest(text), false, name);
    for (const request of requests) assert.equal(isRetryRequest(request), true, request);
  });

    test(`confirmed ${name} delivery cannot unpark exhausted validation`, async t => {
    const { f, ports, root } = await environmentRun(t);
    const p = ports({ environmentHealthy: async () => false });
    await parkAutomaticRun({ reason: 'Native validation timeout', step: 'verify', cwd: root }, p);
    const exhausted = f.record(); exhausted.environmentRetry.attempts = 3; exhausted.environmentRetry.nextAt = null; writeRun(exhausted);
    const before = f.record(); const chat = f.herdr.paneOf(before.chats.at(-1)); chat.agent.agent_status = 'idle';
    const result = await changeRun({ ref: '17', text, cwd: f.source }, p);
    assert.equal(result.exitCode, 0, result.message);
    assert.equal(f.record().state, 'stuck', 'ordinary delivery must not clear the park');
    for (const key of ['parkReason', 'environmentRetry', 'done', 'area', 'branch', 'automaticOrigin']) assert.deepEqual(f.record()[key], before[key], key);
    assert.equal(f.record().changes.length, before.changes.length + 1, 'ordinary delivery is confirmed');
    assert.equal(chat.agent.prompts.length, 1);
    assert.doesNotMatch(chat.agent.prompts.at(-1), /Resume only/);
    const journal = JSON.parse(readFileSync(join(before.runDir, 'delivery-journal.json'), 'utf8'));
    assert.equal(journal.requests.at(-1).personRetry, undefined);
    assert.equal(journal.requests.at(-1).state, 'delivered');
  });
}

test('saved retry flags cannot promote a diagnostic; blocked multiline repair requests still resume', async t => {
  const { f, ports, root } = await environmentRun(t); const p = ports();
  await parkAutomaticRun({ reason: 'Native validation timeout', step: 'verify', cwd: root }, p);
  const before = f.record(); const chat = f.herdr.paneOf(before.chats.at(-1)); chat.agent.agent_status = 'idle';
  const transport = p.herdr;
  p.herdr = async args => {
    if (args[0] === 'agent' && args[1] === 'prompt') throw Object.assign(Error('blocked'), { code: 'agent_blocked' });
    return transport(args);
  };
  await changeRun({ ref: '17', text: diagnostics[0][1], cwd: f.source }, p);
  const path = join(before.runDir, 'delivery-journal.json');
  const journal = JSON.parse(readFileSync(path, 'utf8'));
  journal.requests[0].personRetry = true; // Legacy intent saved by the faulty classifier.
  writeFileSync(path, JSON.stringify(journal));
  p.herdr = transport;
  await changeRun({ ref: '17', text: diagnostics[0][1], cwd: f.source }, p);
  assert.equal(f.record().state, 'stuck', 'a legacy flag is not a direct request');
  assert.doesNotMatch(chat.agent.prompts.at(-1), /Resume only/);
  const text = 'The machine is fixed\nPlease retry verify after the machine repair.';
  p.herdr = async args => {
    if (args[0] === 'agent' && args[1] === 'prompt') throw Object.assign(Error('blocked'), { code: 'agent_blocked' });
    return transport(args);
  };
  await changeRun({ ref: '17', text, cwd: f.source }, p);
  assert.equal(f.record().state, 'stuck', 'blocked delivery retains the park');
  p.herdr = transport;
  await changeRun({ ref: '17', text: 'Inspect the retained evidence.', cwd: f.source }, p);
  assert.equal(f.record().state, 'running', 'confirmed pending multiline delivery resumes');
  assert.deepEqual(f.record().environmentRetry, before.environmentRetry);
  assert.deepEqual(f.record().done, before.done);
});
