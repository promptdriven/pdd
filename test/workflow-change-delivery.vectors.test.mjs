import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, chmodSync, mkdirSync, readdirSync, existsSync, unlinkSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { EventEmitter } from 'node:events';
import { execFileSync } from 'node:child_process';
import { join } from 'node:path';
import { fixture } from './helpers/workflow-delivery-fixture.mjs';
import { stepDone, approveRun, changeRun, runStatus } from '../src/workflow-runner.mjs';
import { sendToChat } from '../src/workflow-chat.mjs';
import { writeRun } from '../src/workflow-runs.mjs';

const vectors = JSON.parse(readFileSync(new URL('./workflow-change-delivery/cases.json', import.meta.url), 'utf8'));
const changePrefix = 'The person asks for changes: ', changeSuffix = ' Revise in this chat, run done again for the step you changed, then show the result and ask again.';
const answerPrefix = 'The person answers your question: ', answerSuffix = ' Go on with the step.';
const deferred = () => { let resolve; const promise = new Promise(r => { resolve = r; }); return { promise, resolve }; };
const facts = (message, values = []) => { for (const value of values) assert.ok(message.toLowerCase().includes(value.toLowerCase()), `message includes ${value}: ${message}`); };
const records = path => existsSync(path) ? readdirSync(path).filter(name => name.endsWith('.json')) : [];

for (const vector of vectors.cases) test(`2677 vector: ${vector.id}`, async t => {
  const given = vector.given, expected = vector.expect;
  if (given.custodyWriteFails && process.geteuid?.() === 0) return t.skip('chmod cannot deny writes to root; injected write-failure tests cover custody');
  if (given.privateChildPerSignal && !process.env.PDD_VECTOR_SIGNAL) {
    for (const signal of given.signals) {
      const childEnv = { ...process.env, PDD_VECTOR_SIGNAL: signal };
      delete childEnv.NODE_TEST_CONTEXT;
      let result;
      try { result = execFileSync(process.execPath, ['--test', '--test-name-pattern=2677 vector: dispatch-signals-release-own-claim$', import.meta.filename],
        { encoding: 'utf8', env: childEnv, timeout: 20_000 }); }
      catch (error) { assert.fail(`private ${signal} child failed: ${error.stdout ?? ''}\n${error.stderr ?? ''}`); }
      assert.match(result, /# fail 0\b/, `private ${signal} child completed assertions`);
    }
    return;
  }
  const f = await fixture(t, { agent: 'codex', name: 'bug' });
  assert.equal((await f.run()).exitCode, 0);
  for (const step of ['reproduce', 'prompt-story']) assert.equal((await stepDone({ step, summary: 'done', cwd: f.record().root }, f.agentPorts())).exitCode, 0);
  assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  const initial = f.record(), chat = initial.chats.at(-1), pane = f.herdr.paneOf(chat);
  const originalPane = chat.paneId, started = f.elapsed, initialApprovals = initial.decisions.filter(r => r.decision === 'approve').length;
  const journalPath = join(initial.runDir, 'delivery-journal.json');
  const journalLock = join(initial.runDir, '.delivery-journal.lock');
  const dispatchLock = join(initial.runDir, `.delivery-${createHash('sha256').update(`${chat.area}\0${originalPane}`).digest('hex')}.lock`);
  const saveJournal = requests => writeFileSync(journalPath, JSON.stringify({ requests }));
  const readJournal = () => {
    if (!existsSync(journalPath)) return [];
    const journal = JSON.parse(readFileSync(journalPath, 'utf8'));
    assert.ok(Array.isArray(journal.requests), 'authoritative journal has a requests array');
    return journal.requests;
  };
  const baseRequest = { id: 'seed-request', text: '', kind: 'change', state: 'pending', area: chat.area, paneId: originalPane, at: f.clock, question: null, gate: null };
  chat.startedAt = f.clock - (given.chatAgeMs ?? 0);
  if (given.gateOpen) { initial.gate = { area: chat.area, at: f.clock, kind: 'approve' }; initial.state = 'waiting'; }
  if (given.question) { initial.question = { text: given.question, at: f.clock, area: chat.area }; initial.state = 'waiting'; }
  if (given.concurrentWriter === 'status') initial.chatFailure = { area: chat.area, phase: 'start', code: 'server_unavailable', message: 'Saved startup failure', at: f.clock };
  if (given.noChatRecord) initial.chats = initial.chats.filter(c => c.area !== chat.area);
  if (given.legacyDeliveryRequests) initial.deliveryRequests = given.legacyDeliveryRequests.map(r => ({ ...baseRequest, ...r }));
  writeRun(initial, f.ports);
  if (given.journalRequest) saveJournal([{ ...baseRequest, ...given.journalRequest }]);
  if (given.deliveredRequestWithRetryReceipt) saveJournal([{ ...baseRequest, text: given.deliveredRequestWithRetryReceipt, state: 'delivered', retryOwed: true }]);
  const ownerPid = 567890;
  f.ports.ownerPid = ownerPid;
  f.ports.processIdentity = pid => pid === ownerPid ? { alive: true, birth: 'this-birth' } :
    ({ 'confirmed-dead': { alive: false }, 'live-pid-different-birth': { alive: true, birth: 'new-birth' },
      'confirmed-live-same-birth': { alive: true, birth: 'saved-birth' }, 'identity-unavailable': { alive: null } }[given.dispatchClaim?.owner ?? given.journalClaim?.owner] ?? { alive: false });
  let tokenNumber = 0;
  f.ports.deliveryToken = () => `vector-token-${++tokenNumber}`;
  const seedClaim = (path, claim) => { mkdirSync(path, { recursive: true }); writeFileSync(join(path, `${claim.token}.json`), JSON.stringify({ pid: 654321, birth: 'saved-birth', token: claim.token })); };
  if (given.dispatchClaim) seedClaim(dispatchLock, given.dispatchClaim);
  if (given.journalClaim) seedClaim(journalLock, given.journalClaim);
  const healthy = f.ports.herdr;
  const launches = f.herdr.calls.filter(a => a[0] === 'pane' && a[1] === 'run').length;
  let ready = given.ready === true, readyAfter = given.readyAfterMs, readyBaseline = started;
  let waitBegan = started, waitCalls = 0, mutated = false, attempts = 0, replacementSubmissions = 0, beforeReady = 0, beforeSubmitCalls = 0;
  let errorUsed = false, jumped = false, statusTask, questionAfterFirst, secondElapsed = 0, repeatedUncertainSubmitAttempts = 0;
  let signalSent = false, ownClaimsRemaining;
  const submittedTexts = [], submittedAnswerTexts = [], submittedChangeTexts = [], custody = [], outputs = [], boundPanes = new Set();
  const overlapEntered = deferred(), overlapRelease = deferred(), statusEntered = deferred(), statusRelease = deferred();
  let overlapping = false;
  f.ports.sleep = async ms => {
    assert.ok(ms > 0 && ms <= 250, 'bounded readiness delay');
    waitCalls++; f.tick(ms);
    if (given.wallClockJumpAtElapsedMs && !jumped && f.elapsed - started >= given.wallClockJumpAtElapsedMs) { f.clock += given.wallClockJumpMs; jumped = true; }
    if (given.captureRunBeforeSubmit && !statusTask) {
      statusTask = runStatus({ ref: '17', cwd: f.source }, { ...f.ports, herdr: async args => {
        if (args[0] === 'agent' && args[1] === 'get') { statusEntered.resolve(); await statusRelease.promise; }
        return f.ports.herdr(args);
      } });
      await statusEntered.promise;
    }
    if (vector.duringWait && !mutated) {
      mutated = true; const latest = f.record(), update = vector.duringWait;
      if (update.doneStep) latest.done[update.doneStep] = { summary: 'new progress', at: f.clock, area: chat.area };
      if (update.question) latest.question = { text: update.question, at: f.clock + 1, area: chat.area };
      if (update.gateAt) latest.gate = { area: chat.area, at: update.gateAt, kind: 'approve' };
      if (update.replacePane) latest.chats.at(-1).paneId = 'replacement-pane';
      writeRun(latest, f.ports);
    }
    if (given.noChatRecord && given.chatAppearsAfterMs != null && f.elapsed - started >= given.chatAppearsAfterMs && !f.record().chats.some(c => c.area === chat.area)) {
      const latest = f.record(); latest.chats.push(chat); writeRun(latest, f.ports);
    }
    if (given.overlapIdenticalWhileFirstWaits && !overlapping) { overlapping = true; overlapEntered.resolve(); await overlapRelease.promise; }
    if (given.privateChildPerSignal && !signalSent) {
      signalSent = true; f.ports.processSignals.emit(process.env.PDD_VECTOR_SIGNAL);
      ownClaimsRemaining = records(dispatchLock).length + records(journalLock).length;
      assert.equal(ownClaimsRemaining, 0, 'signal releases owned claims before termination');
      ready = true;
    }
    assert.ok(f.elapsed - waitBegan <= 30_000, 'the invocation monotonic startup budget bounds every wait');
  };
  if (given.privateChildPerSignal) {
    f.ports.processSignals = new EventEmitter();
    f.ports.terminateSignal = () => {
      ownClaimsRemaining = records(dispatchLock).length + records(journalLock).length;
      assert.equal(ownClaimsRemaining, 0, 'signal releases own tokens before termination');
      throw Object.assign(Error('private sender interrupted'), { code: 'vector_interrupted' });
    };
  }
  const isKnownReady = () => ready || readyAfter != null && f.elapsed - readyBaseline >= readyAfter || given.knownReadyAfterMs != null && f.elapsed - started >= given.knownReadyAfterMs;
  f.ports.herdr = async args => {
    if (args[0] === 'agent' && args[1] === 'get') {
      if (given.inspectError) throw Object.assign(Error(given.inspectError), { code: given.inspectError });
      if (!isKnownReady() && !given.initialAgentAlive) throw Object.assign(Error('starting'), { code: 'agent_not_found' });
      pane.agent.agent_status = isKnownReady() ? given.statusWhenReady ?? 'working' : given.initialAgentStatus;
    }
    if (args[0] === 'agent' && args[1] === 'prompt') {
      attempts++; if (args[2] !== originalPane) replacementSubmissions++;
      const answer = args[3].startsWith(answerPrefix), change = args[3].startsWith(changePrefix);
      const text = answer ? args[3].slice(answerPrefix.length, -answerSuffix.length) : change ? args[3].slice(changePrefix.length, -changeSuffix.length) : args[3];
      if (!isKnownReady()) beforeReady++;
      if (answer || change) {
        const requests = readJournal();
        const owned = requests.find(r => r.text === text && r.state === 'pending' && r.paneId === originalPane && r.kind === (answer ? 'answer' : 'change'));
        custody.push(Boolean(owned));
        if (owned) { boundPanes.add(owned.paneId); }
      }
      if (!isKnownReady() && !given.initialAgentAlive) throw Object.assign(Error('starting'), { code: 'agent_not_found' });
      if (given.submitError && (!given.submitErrorOnce || !errorUsed)) { errorUsed = true; throw Object.assign(Error(given.submitError), { code: given.submitError }); }
      if (given.replaceOwnClaimBeforeCleanup) {
        for (const name of records(dispatchLock)) unlinkSync(join(dispatchLock, name));
        seedClaim(dispatchLock, { token: 'replacement-token' });
      }
      submittedTexts.push(text); if (answer) submittedAnswerTexts.push(text); if (change) submittedChangeTexts.push(text);
    }
    return healthy(args);
  };
  const invoke = async text => {
    if (!given.overlapIdenticalWhileFirstWaits) waitBegan = f.elapsed;
    try { return await changeRun({ ref: '17', text, cwd: f.source }, f.ports); }
    catch (error) {
      if (error.code === 'vector_interrupted') return { exitCode: 1, message: 'Private sender interrupted; request kept.' };
      if (['EACCES', 'EPERM'].includes(error.code)) return { exitCode: 1, message: String(error) };
      throw error;
    }
  };
  if (vector.operation === 'sendToChat') {
    const result = await sendToChat(chat, vector.requests[0], { ...f.ports, beforeSubmit: () => { beforeSubmitCalls++; return given.beforeSubmitResult; } });
    assert.equal(result.ok, expected.ok); assert.equal(result.code, expected.code);
    assert.equal(beforeSubmitCalls, expected.beforeSubmitCalls); assert.deepEqual(submittedTexts, expected.submittedTexts); return;
  }
  if (given.overlapIdenticalWhileFirstWaits) {
    const first = invoke(vector.requests[0]);
    // The old implementation may return without waiting. Always release the rendezvous before asserting.
    const entered = await Promise.race([overlapEntered.promise.then(() => true), first.then(() => false)]);
    if (!entered) { overlapRelease.resolve(); await first; assert.fail('starting delivery must wait so an identical caller can join its accepted request'); }
    outputs.push(await invoke(vector.requests[1]));
    overlapRelease.resolve(); outputs.unshift(await first);
    outputs.push(await invoke(vector.requests[2]));
    questionAfterFirst = f.record().question?.text ?? null;
  } else for (const [index, text] of vector.requests.entries()) {
    if (index === 1 && vector.beforeSecond?.ready) ready = true;
    if (index === 1 && vector.beforeSecond?.resumeNow) {
      const latest = f.record(); latest.chats.at(-1).resumedAt = f.clock; writeRun(latest, f.ports);
      readyAfter = vector.beforeSecond.readyAfterMs; readyBaseline = f.elapsed;
    }
    const before = f.elapsed;
    if (given.custodyWriteFails) chmodSync(initial.runDir, 0o500);
    try { outputs.push(await invoke(text)); }
    finally { if (given.custodyWriteFails) chmodSync(initial.runDir, 0o700); }
    if (index === 1) { secondElapsed = f.elapsed - before; if (given.mayHaveDispatched) repeatedUncertainSubmitAttempts = attempts - 1; }
    if (!index) {
      questionAfterFirst = f.record().question?.text ?? null;
      if (vector.afterFirst?.finishStaleStatusWrite && statusTask) { statusRelease.resolve(); assert.equal((await statusTask).exitCode, 0); }
      if (vector.afterFirst?.restoreStaleLegacyPending) {
        const latest = f.record(); latest.deliveryRequests = initial.deliveryRequests.map(r => ({ ...r, state: 'pending' })); writeRun(latest, f.ports);
      }
    }
  }
  const run = f.record(), requests = readJournal(), message = outputs.map(r => r.message).join('\n');
  if ('exitCode' in expected) assert.equal(outputs.at(-1).exitCode, expected.exitCode, message);
  if (expected.exitCodeNonzero) assert.notEqual(outputs.at(-1).exitCode, 0, message);
  if (expected.firstExitCodeNonzero) assert.notEqual(outputs[0].exitCode, 0, outputs[0].message);
  facts(outputs[0].message, expected.firstMessageFacts); facts(outputs.at(-1).message, expected.lastMessageFacts); facts(message, expected.messageFacts);
  for (const value of expected.messageAbsentFacts ?? []) assert.ok(!message.toLowerCase().includes(value.toLowerCase()), `message excludes ${value}: ${message}`);
  for (const [key, actual] of [['submittedTexts', submittedTexts], ['submittedAnswerTexts', submittedAnswerTexts], ['submittedChangeTexts', submittedChangeTexts]]) if (key in expected) assert.deepEqual(actual, expected[key], message);
  for (const [key, state] of [['pendingTexts', 'pending'], ['uncertainTexts', 'uncertain']]) if (key in expected) assert.deepEqual(requests.filter(r => r.state === state).map(r => r.text), expected[key]);
  if (expected.custodyBeforeSubmit || submittedTexts.length) assert.ok(custody.length && custody.every(Boolean), 'normalized text and original target are durably pending before submit');
  if ('deliveredRequestCount' in expected) assert.equal(requests.filter(r => r.state === 'delivered').length, expected.deliveredRequestCount);
  if ('elapsedMsAtMost' in expected) assert.ok(f.elapsed - started <= expected.elapsedMsAtMost);
  if ('elapsedMsAtLeast' in expected) assert.ok(f.elapsed - started >= expected.elapsedMsAtLeast);
  if ('secondElapsedMsAtLeast' in expected) assert.ok(secondElapsed >= expected.secondElapsedMsAtLeast);
  if ('submittedBeforeReady' in expected) assert.equal(beforeReady, expected.submittedBeforeReady);
  if ('gateOpen' in expected) assert.equal(Boolean(run.gate), expected.gateOpen);
  if ('agentStarts' in expected) assert.equal(f.herdr.calls.filter(a => a[0] === 'pane' && a[1] === 'run').length - launches, expected.agentStarts);
  for (const [key, actual] of [['submitAttempts', attempts], ['replacementSubmissions', replacementSubmissions], ['waitCalls', waitCalls], ['repeatedUncertainSubmitAttempts', repeatedUncertainSubmitAttempts]]) if (key in expected) assert.equal(actual, expected[key]);
  if (expected.doneStep) assert.equal(run.done[expected.doneStep]?.summary, 'new progress');
  if (expected.question) assert.equal(run.question?.text, expected.question);
  if (expected.gateAt) assert.equal(run.gate?.at, expected.gateAt);
  if ('questionAfterFirst' in expected) assert.equal(questionAfterFirst, expected.questionAfterFirst);
  if ('questionAfterSecond' in expected) assert.equal(run.question ?? null, expected.questionAfterSecond);
  if ('answerRecordCount' in expected) assert.equal(run.changes.filter(r => r.answer).length, expected.answerRecordCount);
  if ('approvalCount' in expected) assert.equal(run.decisions.filter(r => r.decision === 'approve').length - initialApprovals, expected.approvalCount);
  if (expected.exactText) assert.equal(run.changes.at(-1)?.text, expected.exactText);
  if ('acceptedRequestIdsCount' in expected) assert.equal(new Set(requests.map(r => r.id)).size, expected.acceptedRequestIdsCount);
  if ('boundPaneCount' in expected) assert.equal(boundPanes.size, expected.boundPaneCount);
  if (expected.retryReceiptConsumed) assert.ok(requests.some(r => r.state === 'delivered') && requests.every(r => !r.retryOwed), 'joined caller receipt is consumed on original delivered request');
  if (expected.dispatchClaimRemoved) assert.equal(records(dispatchLock).length, 0);
  if (expected.journalClaimRemoved) assert.equal(records(journalLock).length, 0);
  if (expected.claimToken) assert.ok(records(given.journalClaim ? journalLock : dispatchLock).includes(`${expected.claimToken}.json`));
  if (expected.replacementClaimRetained) assert.ok(records(dispatchLock).includes('replacement-token.json'));
  if (expected.authoritativeJournalFile) { assert.ok(existsSync(journalPath)); assert.ok(Array.isArray(JSON.parse(readFileSync(journalPath, 'utf8')).requests)); }
  if (expected.legacyDeliveredId) assert.equal(requests.find(r => r.id === expected.legacyDeliveredId)?.state, 'delivered');
  if ('legacyReplayCount' in expected) assert.equal(submittedTexts.filter(text => text === 'Legacy already sent').length, expected.legacyReplayCount);
  if ('newDeliveredRequestCount' in expected) assert.equal(requests.filter(r => r.id !== 'seed-request' && r.state === 'delivered').length, expected.newDeliveredRequestCount);
  if ('ownClaimsRemaining' in expected) assert.equal(ownClaimsRemaining, expected.ownClaimsRemaining);
  if (expected.nextReadyRetrySubmittedTexts) { ready = true; await invoke(vector.requests[0]); assert.deepEqual(submittedTexts, expected.nextReadyRetrySubmittedTexts); }
  if (expected.retryArgumentQuoted) assert.match(message, /workflow changes 17 (?:'First'|"First")(?=\s|[.\n]|$)/);
  if (expected.adviceBeforeRetryCommand) assert.ok(message.toLowerCase().indexOf('wait') >= 0 && message.toLowerCase().indexOf('wait') < message.indexOf('workflow changes'));
  if ('retryLabelCount' in expected) assert.equal((message.match(/retry:/gi) ?? []).length, expected.retryLabelCount);
  if (expected.genericTransportPreservesGateMessage) {
    const control = expected.genericTransportPreservesGateMessage; const sent = [];
    const result = await sendToChat(chat, control.input, { ...f.ports, herdr: async args => { if (args[0] === 'agent' && args[1] === 'prompt') sent.push(args[3]); return healthy(args); } });
    assert.equal(result.ok, true); assert.deepEqual(sent, [control.submitted]);
  }
});
