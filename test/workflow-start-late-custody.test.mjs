// A dispatched startup retains its native identity when public progress moves on.
import test from 'node:test';
import assert from 'node:assert/strict';
import { startRun, stepDone, approveRun, openRun } from '../src/workflow-runner.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const fields = ['runId', 'state', 'area', 'done', 'gate', 'question', 'approvalRecord', 'decisions', 'changes', 'pr', 'prState', 'cancelled', 'chatReplacement', 'abandonedChats', 'chatFailure'];
const progress = run => Object.fromEntries(fields.map(key => [key, run[key]]));

for (const lost of [false, true]) test(`2627 late dispatched startup ${lost ? 'lost reply' : 'success'} retains historical chat custody`, async t => {
  const f = await fixture(t), healthy = f.ports.herdr;
  let enter, release, held = false, originalPane;
  const reached = new Promise(resolve => { enter = resolve; });
  const gate = new Promise(resolve => { release = resolve; });
  const starting = startRun({ name: 'small-change', issue: '17', agent: 'claude', cwd: f.source, packageRoot }, {
    ...f.ports, herdr: async args => {
      const response = await healthy(args);
      if (!held && args[0] === 'pane' && args[1] === 'run') {
        held = true; originalPane = args[2]; enter(); await gate;
        if (lost) throw Object.assign(Error('Reply lost after dispatch'), { code: 'server_unavailable' });
      }
      return response;
    },
  });
  assert.equal(await Promise.race([reached.then(() => true), starting.then(() => false)]), true, 'Startup must wait after the fake native launch dispatched');
  let expected;
  try {
    assert.ok(f.herdr.panes.find(pane => pane.pane_id === originalPane)?.agent, 'The original agent is already live before progress advances');
    assert.equal((await stepDone({ step: 'scope', summary: 'Completed in the original running agent', cwd: f.record().root }, f.agentPorts())).exitCode, 0);
    assert.equal((await approveRun({ ref: '17', cwd: f.source, packageRoot }, f.ports)).exitCode, 0);
    expected = f.record();
    assert.equal(expected.area, 1);
    assert.ok(expected.done.scope);
    assert.ok(expected.approvalRecord);
    assert.equal(expected.decisions.length, 1);
    assert.equal(expected.chats.length, 1);
    assert.equal(expected.chats[0].area, 'build');
  } finally { release(); }
  assert.equal((await starting).exitCode, lost ? 1 : 0);
  const saved = f.record();
  const historical = saved.chats.find(chat => chat.area === 'plan' && chat.paneId === originalPane);
  assert.ok(historical, 'A dispatched initial chat must retain its owned identity after concurrent area advancement');
  assert.deepEqual(progress(saved), progress(expected), 'Late startup must preserve every newer workflow field and current failure');
  assert.deepEqual(saved.chats.filter(chat => chat.area === 'build'), expected.chats, 'Late startup must preserve current chat custody');
  assert.equal(saved.chats.length, 2);
  const pane = f.herdr.paneOf(historical);
  assert.equal(historical.tabId, pane.tab_id);
  assert.equal(historical.terminalId, pane.terminal_id);
  assert.equal(historical.session.id, pane.agent.agent_session.value);
  assert.equal(Boolean(historical.startUnconfirmed), lost);
  const launches = f.herdr.calls.filter(args => args[0] === 'pane' && args[1] === 'run').length;
  const opened = await openRun({ ref: '17', area: 'plan', cwd: f.source, packageRoot }, f.ports);
  assert.equal(opened.exitCode, 0, opened.message);
  assert.equal(f.herdr.calls.filter(args => args[0] === 'pane' && args[1] === 'run').length, launches, 'Historical navigation must reuse the recorded live session');
  assert.deepEqual(progress(f.record()), progress(expected));
  assert.deepEqual(f.record().chats.filter(chat => chat.area === 'build'), expected.chats);
  assert.equal(f.record().chats.find(chat => chat.area === 'plan').startUnconfirmed, undefined);
});
