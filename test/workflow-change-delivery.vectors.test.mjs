import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, chmodSync } from 'node:fs';
import { join } from 'node:path';
import { fixture } from './helpers/workflow-delivery-fixture.mjs';
import { stepDone, approveRun, changeRun } from '../src/workflow-runner.mjs';
import { writeRun } from '../src/workflow-runs.mjs';

const vectors = JSON.parse(readFileSync(new URL('./workflow-change-delivery/cases.json', import.meta.url), 'utf8'));
const changePrefix = 'The person asks for changes: ', changeSuffix = ' Revise in this chat, run done again for the step you changed, then show the result and ask again.';
const answerPrefix = 'The person answers your question: ', answerSuffix = ' Go on with the step.';
for (const vector of vectors.cases) test(`2677 vector: ${vector.id}`, async t => {
  const f = await fixture(t, { agent: 'codex', name: 'bug' });
  assert.equal((await f.run()).exitCode, 0);
  for (const step of ['reproduce', 'prompt-story']) assert.equal((await stepDone({ step, summary: 'done', cwd: f.record().root }, f.agentPorts())).exitCode, 0);
  assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  const given = vector.given, initial = f.record(), chat = initial.chats.at(-1), pane = f.herdr.paneOf(chat);
  const originalPane = chat.paneId, started = f.clock;
  chat.startedAt = f.clock - (given.chatAgeMs ?? 0);
  if (given.gateOpen) { initial.gate = { area: chat.area, at: f.clock, kind: 'approve' }; initial.state = 'waiting'; }
  if (given.question) { initial.question = { text: given.question, at: f.clock, area: chat.area }; initial.state = 'waiting'; }
  writeRun(initial, f.ports);
  let ready = given.ready === true, waitCalls = 0, mutated = false, attempts = 0, replacementSubmissions = 0;
  const submittedTexts = [], submittedAnswerTexts = [], custody = [], outputs = [];
  const healthy = f.ports.herdr;
  const launches = f.herdr.calls.filter(a => a[0] === 'pane' && a[1] === 'run').length;
  f.ports.sleep = async ms => {
    assert.ok(ms > 0 && ms <= 250, 'bounded readiness delay'); waitCalls++; f.tick(ms);
    if (vector.duringWait && !mutated) {
      mutated = true; const latest = f.record(), update = vector.duringWait;
      if (update.doneStep) latest.done[update.doneStep] = { summary: 'new progress', at: f.clock, area: chat.area };
      if (update.question) latest.question = { text: update.question, at: f.clock + 1, area: chat.area };
      if (update.gateAt) latest.gate = { area: chat.area, at: update.gateAt, kind: 'approve' };
      if (update.replacePane) latest.chats.at(-1).paneId = 'replacement-pane';
      writeRun(latest, f.ports);
    }
  };
  f.ports.herdr = async args => {
    if (args[0] === 'agent' && args[1] === 'get') {
      if (given.inspectError) throw Object.assign(Error(given.inspectError), { code: given.inspectError });
      if (!ready && given.readyAfterMs !== null && given.readyAfterMs !== undefined && f.clock - started >= given.readyAfterMs) ready = true;
      if (!ready) throw Object.assign(Error('starting'), { code: 'agent_not_found' });
      pane.agent.agent_status = given.statusWhenReady ?? 'working';
    }
    if (args[0] === 'agent' && args[1] === 'prompt') {
      attempts++; if (args[2] !== originalPane) replacementSubmissions++;
      const answer = args[3].startsWith(answerPrefix), prefix = answer ? answerPrefix : changePrefix, suffix = answer ? answerSuffix : changeSuffix;
      const text = args[3].slice(prefix.length, -suffix.length);
      custody.push((f.record().deliveryRequests ?? []).some(r => r.text === text && r.state === 'pending' && r.paneId === originalPane && r.kind === (answer ? 'answer' : 'change')));
      if (!ready) throw Object.assign(Error('starting'), { code: 'agent_not_found' });
      if (given.submitError) throw Object.assign(Error(given.submitError), { code: given.submitError });
      submittedTexts.push(text); if (answer) submittedAnswerTexts.push(text);
    }
    return healthy(args);
  };
  let questionAfterFirst;
  for (const [index, text] of vector.requests.entries()) {
    if (index === 1 && vector.beforeSecond?.ready) ready = true;
    if (given.custodyWriteFails) chmodSync(initial.runDir, 0o500);
    try { outputs.push(await changeRun({ ref: '17', text, cwd: f.source }, f.ports)); }
    catch (error) { outputs.push({ exitCode: 1, message: String(error) }); }
    finally { if (given.custodyWriteFails) chmodSync(initial.runDir, 0o700); }
    if (!index) questionAfterFirst = f.record().question?.text ?? null;
  }
  const run = f.record(), expected = vector.expect, requests = run.deliveryRequests ?? [], message = outputs.map(r => r.message).join('\n');
  if ('exitCode' in expected) assert.equal(outputs.at(-1).exitCode, expected.exitCode, message);
  if (expected.exitCodeNonzero) assert.notEqual(outputs.at(-1).exitCode, 0, message);
  if (expected.submittedTexts) assert.deepEqual(submittedTexts, expected.submittedTexts);
  if (expected.pendingTexts) assert.deepEqual(requests.filter(r => r.state === 'pending').map(r => r.text), expected.pendingTexts);
  if (expected.uncertainTexts) assert.deepEqual(requests.filter(r => r.state === 'uncertain').map(r => r.text), expected.uncertainTexts);
  if (expected.custodyBeforeSubmit) assert.ok(custody.length && custody.every(Boolean), 'durable exact text and original target exist before submit');
  if ('deliveredRequestCount' in expected) assert.equal(requests.filter(r => r.state === 'delivered').length, expected.deliveredRequestCount);
  if ('elapsedMsAtMost' in expected) assert.ok(f.clock - started <= expected.elapsedMsAtMost);
  if (expected.messageFacts) for (const fact of expected.messageFacts) assert.ok(message.toLowerCase().includes(fact), `message includes ${fact}: ${message}`);
  if ('gateOpen' in expected) assert.equal(Boolean(run.gate), expected.gateOpen);
  if ('agentStarts' in expected) assert.equal(f.herdr.calls.filter(a => a[0] === 'pane' && a[1] === 'run').length - launches, expected.agentStarts);
  if ('submitAttempts' in expected) assert.equal(attempts, expected.submitAttempts);
  if ('replacementSubmissions' in expected) assert.equal(replacementSubmissions, expected.replacementSubmissions);
  if ('waitCalls' in expected) assert.equal(waitCalls, expected.waitCalls);
  if (expected.doneStep) assert.equal(run.done[expected.doneStep]?.summary, 'new progress');
  if (expected.question) assert.equal(run.question?.text, expected.question);
  if (expected.gateAt) assert.equal(run.gate?.at, expected.gateAt);
  if ('questionAfterFirst' in expected) assert.equal(questionAfterFirst, expected.questionAfterFirst);
  if ('questionAfterSecond' in expected) assert.equal(run.question ?? null, expected.questionAfterSecond);
  if (expected.submittedAnswerTexts) assert.deepEqual(submittedAnswerTexts, expected.submittedAnswerTexts);
  if ('answerRecordCount' in expected) assert.equal(run.changes.filter(r => r.answer).length, expected.answerRecordCount);
  if ('approvalCount' in expected) assert.equal(run.decisions.filter(r => r.decision === 'approve').length - initial.decisions.filter(r => r.decision === 'approve').length, expected.approvalCount);
  if (submittedTexts.length) assert.ok(custody.every(Boolean), 'successful submission has durable custody');
  if (expected.exactText) assert.equal(run.changes.at(-1)?.text, expected.exactText);
});
