// Real temporary Git; Herdr/gh are injected fakes, and native agent commands never run.
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, rmSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { openRun, stepDone, approveRun, askPerson } from '../src/workflow-runner.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const caseName = name => `2627 ${name}`;
const closedChannel = () => Object.assign(Error('synthetic lost Herdr reply'), { code: 'server_unavailable' });
const chatFor = (run, area) => run.chats.find(chat => chat.area === area);
const launchCalls = f => f.herdr.calls.filter(args => args[0] === 'pane' && args[1] === 'run');
const mutationCalls = f => f.herdr.calls.filter(args => args[0] === 'pane' && args[1] === 'run'
  || ['tab', 'workspace', 'worktree'].includes(args[0]) && ['create', 'close', 'open'].includes(args[1]));
const statusBytes = f => readFileSync(join(f.record().runDir, 'status.json'));
function archivedChat(run, original) {
  const objects = value => value && typeof value === 'object'
    ? [value, ...Object.values(value).flatMap(objects)] : [];
  const archived = objects(run.abandonedChats).find(item => item.paneId === original.paneId && item.area === original.area);
  assert.ok(archived, 'Retain the original chat record under abandonedChats');
  for (const key of ['area', 'tabId', 'paneId', 'session']) assert.deepEqual(archived[key], original[key]);
  return archived;
}
function business(run) {
  return Object.fromEntries(['runId', 'repo', 'number', 'workflow', 'skill', 'skillDir', 'root', 'runDir',
    'sourceRoot', 'commonDir', 'branch', 'baseBranch', 'baseSha', 'agent', 'configDir', 'areas',
    'area', 'state', 'gate', 'question', 'waitingFor', 'done', 'approvalRecord', 'decisions', 'pr'].map(key => [key, run[key]]));
}
function stable(f) {
  const run = f.record();
  return { business: business(run), head: f.git(run.root, 'rev-parse', 'HEAD'),
    claim: readFileSync(join(f.source, '.git/pdd/worktree-assignments/issues/17.json')) };
}
function unchanged(f, before) {
  assert.deepEqual(stable(f), before, 'Opening a chat preserves worktree, progress and approval/PR history');
}
async function open(f, input = {}, ports = f.ports) {
  return openRun({ ref: '17', cwd: f.source, packageRoot, ...input }, ports);
}
async function started(t) {
  const f = await fixture(t);
  const result = await f.run();
  assert.equal(result.exitCode, 0, `Fixture start: ${result.message}`);
  f.herdr.calls.length = 0;
  return f;
}
async function inBuild(t, { question = false, completed = false } = {}) {
  const f = await started(t), run = f.record();
  f.tick();
  const done = await stepDone({ step: 'scope', summary: 'Keep the existing run and its recorded history.', cwd: run.root }, f.agentPorts());
  assert.equal(done.exitCode, 0, `Fixture scope: ${done.message}`);
  f.tick();
  const approved = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(approved.exitCode, 0, `Fixture approval: ${approved.message}`);
  assert.equal(f.record().area, 1);
  if (completed) {
    writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n');
    f.git(run.root, 'commit', '-qam', 'Use value two');
    f.tick();
    const changed = await stepDone({ step: 'change', summary: 'Changed value.mjs to two; preserve this completed work.', cwd: run.root }, f.agentPorts());
    assert.equal(changed.exitCode, 0, `Fixture completed change: ${changed.message}`);
  }
  if (question) {
    f.tick();
    const asked = await askPerson({ text: 'Should the report include the exact verification command?', cwd: run.root }, f.agentPorts());
    assert.equal(asked.exitCode, 0, `Fixture question: ${asked.message}`);
  }
  // Synthetic already-recorded PR metadata, using existing run.pr fields only.
  // No PR is opened: openRun must preserve a nonempty publication history.
  const saved = f.record();
  saved.pr = [{ stage: 'build', number: 23, url: 'https://github.com/example/project/pull/23',
    branch: saved.branch, base: saved.baseBranch }];
  writeFileSync(join(saved.runDir, 'status.json'), JSON.stringify(saved));
  f.herdr.calls.length = 0;
  return f;
}
function noEffectRefusal(f, beforeBytes, beforeStable, result) {
  assert.notEqual(result.exitCode, 0, 'Invalid selection must be refused');
  assert.ok(statusBytes(f).equals(beforeBytes), 'Refusal must not persist the run');
  assert.equal(f.herdr.calls.length, 0, 'Refusal must precede all native calls');
  unchanged(f, beforeStable);
}

test(caseName('historical AREA focuses its saved chat and preserves current progress'), async t => {
  const f = await inBuild(t), run = f.record(), build = chatFor(run, 'build'), plan = chatFor(run, 'plan');
  // Existing behavior controls pass on the base; only the historical selection is a new red case.
  for (const input of [{}, { area: 'build' }]) {
    const before = stable(f), result = await open(f, input);
    assert.equal(result.exitCode, 0, result.message);
    assert.equal(f.herdr.focus, build.tabId);
    assert.equal(mutationCalls(f).length, 0);
    unchanged(f, before);
  }
  f.herdr.calls.length = 0;
  const before = stable(f), result = await open(f, { area: 'plan' });
  assert.equal(result.exitCode, 0, result.message);
  assert.equal(f.herdr.focus, plan.tabId, 'AREA selects the saved historical tab');
  assert.equal(mutationCalls(f).length, 0);
  assert.deepEqual(chatFor(f.record(), 'build'), build);
  unchanged(f, before);
});

test(caseName('historical AREA resumes its recorded native session in the same tab'), async t => {
  const f = await inBuild(t), before = stable(f), run = f.record(), plan = chatFor(run, 'plan'), build = chatFor(run, 'build');
  const pane = f.herdr.paneOf(plan), buildCommands = f.herdr.paneOf(build).commands.length;
  pane.agent = null;
  const result = await open(f, { area: 'plan' });
  assert.equal(result.exitCode, 0, result.message);
  assert.equal(pane.commands.length, 2, 'Only the selected ended historical agent is resumed');
  assert.match(pane.commands[1], /--resume/);
  assert.ok(pane.commands[1].includes(plan.session.id), 'Resume the saved native session');
  assert.ok(pane.commands[1].includes(plan.configDir), 'Keep the saved account configuration');
  assert.equal(f.herdr.focus, plan.tabId);
  assert.equal(f.herdr.paneOf(build).commands.length, buildCommands);
  assert.equal(f.record().chats.length, run.chats.length);
  assert.equal(chatFor(f.record(), 'plan').tabId, plan.tabId);
  assert.equal(launchCalls(f).length, 1);
  assert.equal(mutationCalls(f).length, 1);
  unchanged(f, before);
});

test(caseName('a historical inspection failure cannot change the current question or chat failure'), async t => {
  const f = await inBuild(t, { question: true }), run = f.record(), plan = chatFor(run, 'plan');
  const healthy = f.ports.herdr;
  // Establish a current-area failure through the existing public path, then preserve it.
  f.ports.herdr = async args => { if (args[0] === 'agent') throw closedChannel(); return healthy(args); };
  assert.equal((await open(f)).exitCode, 1);
  const before = stable(f), failure = f.record().chatFailure;
  f.ports.herdr = async args => {
    if (args[0] === 'agent' && args[1] === 'get' && args[2] === plan.paneId) throw closedChannel();
    return healthy(args);
  };
  f.herdr.calls.length = 0;
  const result = await open(f, { area: 'plan' });
  assert.notEqual(result.exitCode, 0, 'Report the historical inspection failure');
  assert.equal(mutationCalls(f).length, 0);
  assert.deepEqual(f.record().chatFailure, failure, 'Historical failure does not overwrite/clear current failure');
  unchanged(f, before);
});

test(caseName('unknown AREA is refused before persistence or native effects'), async t => {
  const f = await started(t), saved = f.record();
  // Existing ended/config guards are controls, not separately counted failing tests.
  for (const state of ['cancelled', 'completed']) {
    writeFileSync(join(saved.runDir, 'status.json'), JSON.stringify({ ...saved, state }));
    const before = statusBytes(f);
    assert.notEqual((await open(f, { area: 'missing-area' })).exitCode, 0);
    assert.ok(statusBytes(f).equals(before));
    assert.equal(f.herdr.calls.length, 0);
  }
  writeFileSync(join(saved.runDir, 'status.json'), JSON.stringify(saved));
  rmSync(saved.configDir, { recursive: true });
  const withoutConfig = statusBytes(f);
  assert.notEqual((await open(f, { area: 'missing-area' })).exitCode, 0);
  assert.ok(statusBytes(f).equals(withoutConfig));
  assert.equal(f.herdr.calls.length, 0);
  // Restore the fixture's own empty config directory, without touching a real account.
  mkdirSync(saved.configDir);
  const beforeBytes = statusBytes(f), before = stable(f);
  noEffectRefusal(f, beforeBytes, before, await open(f, { area: 'missing-area' }));
});

test(caseName('known future AREA is refused before persistence or native effects'), async t => {
  const f = await started(t), beforeBytes = statusBytes(f), before = stable(f);
  assert.equal(f.record().areas[1].name, 'build');
  noEffectRefusal(f, beforeBytes, before, await open(f, { area: 'build' }));
});

test(caseName('historical AREA with newSession is refused without changing any record'), async t => {
  const f = await inBuild(t), beforeBytes = statusBytes(f), before = stable(f);
  const original = chatFor(f.record(), 'plan'), message = readFileSync(original.messageFile);
  noEffectRefusal(f, beforeBytes, before, await open(f, { area: 'plan', newSession: true }));
  assert.ok(readFileSync(original.messageFile).equals(message));
  assert.deepEqual(chatFor(f.record(), 'plan'), original);
});

test(caseName('newSession refuses a caller in the selected chat pane'), async t => {
  const f = await inBuild(t), chat = chatFor(f.record(), 'build'), beforeBytes = statusBytes(f), before = stable(f);
  const ports = { ...f.ports, env: { ...f.ports.env, HERDR_ENV: '1', HERDR_PANE_ID: chat.paneId,
    HERDR_SOCKET_PATH: join(f.base, 'sessions/pdd/herdr.sock') } };
  noEffectRefusal(f, beforeBytes, before, await open(f, { newSession: true }, ports));
});

test(caseName('newSession replaces only the current chat and archives original artifacts'), async t => {
  const f = await inBuild(t, { completed: true, question: true }), before = stable(f), run = f.record();
  const original = chatFor(run, 'build'), plan = chatFor(run, 'plan'), message = readFileSync(original.messageFile);
  const result = await open(f, { newSession: true });
  assert.equal(result.exitCode, 0, result.message);
  const after = f.record(), replacement = chatFor(after, 'build');
  assert.notEqual(replacement.paneId, original.paneId, 'Explicit newSession installs a new current chat');
  assert.notEqual(replacement.tabId, original.tabId);
  assert.notEqual(replacement.session.id, original.session.id);
  assert.equal(after.chats.filter(chat => chat.area === 'build').length, 1);
  assert.deepEqual(chatFor(after, 'plan'), plan);
  assert.ok(f.herdr.tabs.some(tab => tab.tab_id === plan.tabId));
  assert.equal(f.herdr.tabs.some(tab => tab.tab_id === original.tabId), false);
  const closed = f.herdr.calls.filter(args => args[0] === 'tab' && args[1] === 'close');
  assert.deepEqual(closed.map(args => args[2]), [original.tabId], 'Close only the replaced owned tab');
  const closeIndex = f.herdr.calls.findIndex(args => args[0] === 'tab' && args[1] === 'close');
  const inspectIndex = f.herdr.calls.findIndex(args => args[0] === 'agent' && args[1] === 'get' && args[2] === original.paneId);
  assert.ok(inspectIndex >= 0 && inspectIndex < closeIndex, 'Inspect the selected native identity before closing');
  const archived = archivedChat(after, original);
  assert.equal(typeof archived.messageFile, 'string', 'Retain an accessible original message artifact');
  assert.ok(readFileSync(archived.messageFile).equals(message), 'The original message artifact is preserved');
  assert.equal(launchCalls(f).length, 1, 'Exactly one new native session');
  const command = launchCalls(f)[0][3];
  assert.match(command, /claude.*--session-id/);
  assert.doesNotMatch(command, /--resume/);
  assert.ok(command.includes(original.configDir));
  assert.equal(replacement.configDir, original.configDir);
  unchanged(f, before);
});

test(caseName('newSession brief carries current completed work and the pending question'), async t => {
  const f = await inBuild(t, { completed: true, question: true }), before = stable(f), run = f.record();
  const original = chatFor(run, 'build');
  const result = await open(f, { newSession: true });
  assert.equal(result.exitCode, 0, result.message);
  const replacement = chatFor(f.record(), 'build');
  assert.notEqual(replacement.paneId, original.paneId, 'Read a replacement brief only after a new chat exists');
  const brief = readFileSync(replacement.messageFile, 'utf8');
  assert.match(brief, /\bbuild\b/);
  assert.ok(brief.includes(run.done.change.summary.replace(/[.\s]+$/, '')), 'Carry completed work from this same area');
  assert.ok(brief.includes(run.question.text), 'Carry the open person question');
  assert.match(brief, /(?:do not|don't|never)[^\n]*(?:rerun|repeat)[^\n]*(?:completed|done|finished)/i);
  assert.match(brief, /(?:do not|don't|never)[^\n]*approve/i);
  unchanged(f, before);
});

test(caseName('newSession preserves a pending approval gate and explains completed current-area work'), async t => {
  const f = await started(t), run = f.record();
  f.tick();
  const finished = await stepDone({ step: 'scope', summary: 'Limit the change to the selected workflow area.', cwd: run.root }, f.agentPorts());
  assert.equal(finished.exitCode, 0, finished.message);
  const waiting = f.record(), original = chatFor(waiting, 'plan'), before = stable(f);
  assert.equal(waiting.gate.area, 'plan');
  assert.equal(waiting.decisions.length, 0, 'This fixture is waiting for its first approval');
  f.herdr.calls.length = 0;
  const result = await open(f, { newSession: true });
  assert.equal(result.exitCode, 0, result.message);
  const after = f.record(), replacement = chatFor(after, 'plan');
  assert.notEqual(replacement.paneId, original.paneId, 'A gated area can request a fresh native chat');
  const brief = readFileSync(replacement.messageFile, 'utf8');
  assert.ok(brief.includes(waiting.done.scope.summary.replace(/[.\s]+$/, '')));
  assert.match(brief, /gate|approval/i, 'Name the still-pending gate');
  assert.match(brief, /(?:do not|don't|never)[^\n]*(?:rerun|repeat)[^\n]*(?:completed|done|finished)/i);
  assert.match(brief, /(?:do not|don't|never)[^\n]*approve/i);
  assert.deepEqual(after.gate, waiting.gate);
  assert.deepEqual(after.waitingFor.decisions, ['approve', 'changes']);
  assert.equal(after.decisions.length, 0, 'A fresh session is never an approval');
  unchanged(f, before);
});

test(caseName('a lost replacement launch reply retains one unconfirmed chat and recovers without relaunch'), async t => {
  const f = await inBuild(t, { completed: true, question: true }), run = f.record(), before = stable(f);
  const original = chatFor(run, 'build'), healthy = f.ports.herdr;
  f.ports.herdr = async args => {
    const reply = await healthy(args);
    if (args[0] === 'pane' && args[1] === 'run') throw closedChannel();
    return reply;
  };
  const result = await open(f, { newSession: true });
  assert.notEqual(result.exitCode, 0, 'A lost replacement launch reply is not reported as success');
  const uncertain = f.record(), replacement = chatFor(uncertain, 'build');
  assert.notEqual(replacement.paneId, original.paneId);
  assert.equal(replacement.startUnconfirmed, true);
  assert.equal(uncertain.chats.filter(chat => chat.area === 'build').length, 1);
  archivedChat(uncertain, original);
  assert.equal(launchCalls(f).length, 1);
  // Chat failure state may change; progress, questions and approvals must not.
  // The existing chat-failure convention changes derived waitingFor while uncertain.
  const beforeBusiness = { ...before.business }; delete beforeBusiness.state; delete beforeBusiness.waitingFor;
  const uncertainState = uncertain.state, uncertainBusiness = business(uncertain);
  delete uncertainBusiness.state; delete uncertainBusiness.waitingFor;
  assert.deepEqual(uncertainBusiness, beforeBusiness);
  assert.equal(uncertainState, 'waiting');
  const tabCount = f.herdr.tabs.length;
  f.ports.herdr = healthy;
  const recovered = await open(f, {newSession:true});
  assert.equal(recovered.exitCode, 0, recovered.message);
  const after = f.record();
  assert.equal(chatFor(after, 'build').paneId, replacement.paneId);
  assert.equal(Boolean(chatFor(after, 'build').startUnconfirmed), false);
  assert.equal(launchCalls(f).length, 1, 'Observation of the dispatched agent must not launch again');
  assert.equal(f.herdr.tabs.length, tabCount);
  unchanged(f, before);
});
