// Public navigation races, with scratch Git and native Herdr fakes only.
import test from 'node:test';
import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { openRun, stepDone, approveRun, cancelRun } from '../src/workflow-runner.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

function paused(f, predicate, failure = false) {
  let enter, release;
  const reached = new Promise(resolve => { enter = resolve; });
  const gate = new Promise(resolve => { release = resolve; });
  return { reached, release, ports: { ...f.ports, herdr: async args => {
    if (predicate(args)) {
      enter(); await gate;
      if (failure) throw Object.assign(Error('Lost resume reply'), { code: 'server_unavailable' });
    }
    return f.ports.herdr(args);
  } } };
}
async function checkpoint(pause, opening) {
  const reached = await Promise.race([
    pause.reached.then(() => true),
    opening.then(() => false, () => false),
  ]);
  if (!reached) pause.release();
  assert.equal(reached, true, 'AREA open must reach the selected native phase before completing');
}
const open = (f, ports) => openRun({ ref: '17', area: 'plan', cwd: f.source, packageRoot }, ports);
const progress = run => Object.fromEntries(['state', 'area', 'done', 'gate', 'question', 'approvalRecord', 'decisions', 'pr', 'cancelled', 'chatFailure', 'chatReplacement'].map(key => [key, run[key]]));

for (const cancel of [false, true]) test(`2627 AREA focus retains concurrent ${cancel ? 'cancellation' : 'done and gate'}`, async t => {
  const f = await fixture(t); await f.run();
  const pause = paused(f, args => args[0] === 'tab' && args[1] === 'focus');
  const opening = open(f, pause.ports);
  await checkpoint(pause, opening);
  const result = cancel
    ? await cancelRun({ ref: '17', cwd: f.source }, f.ports)
    : await stepDone({ step: 'scope', summary: 'Concurrent human progress', cwd: f.record().root }, f.agentPorts());
  assert.equal(result.exitCode, 0, result.message);
  const latest = progress(f.record());
  pause.release(); await opening;
  assert.deepEqual(progress(f.record()), latest, 'AREA navigation must preserve newer workflow progress');
});

for (const cancel of [false, true]) test(`2627 historical failed resume retains concurrent ${cancel ? 'cancellation' : 'done and gate'} and same-chat uncertainty`, async t => {
  const f = await fixture(t); await f.run();
  assert.equal((await stepDone({ step: 'scope', summary: 'Scope ready', cwd: f.record().root }, f.agentPorts())).exitCode, 0);
  assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  const chat = f.record().chats.find(item => item.area === 'plan');
  f.herdr.paneOf(chat).agent = null;
  const pause = paused(f, args => args[0] === 'pane' && args[1] === 'run' && args[2] === chat.paneId, true);
  const opening = open(f, pause.ports);
  await checkpoint(pause, opening);
  if (cancel) assert.equal((await cancelRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  else {
    // The existing public done interface records later progress while historical navigation waits.
    const result = await stepDone({ step: 'change', summary: 'Concurrent build progress', cwd: f.record().root }, f.agentPorts());
    assert.equal(result.exitCode, 0, result.message);
  }
  const latest = progress(f.record());
  pause.release(); assert.equal((await opening).exitCode, 1);
  assert.deepEqual(progress(f.record()), latest, 'Failed historical navigation must preserve newer workflow progress');
  if (!cancel) assert.equal(f.record().chats.find(item => item.area === 'plan').startUnconfirmed, true);
});

test('2627 AREA late observation cannot overwrite a newer selected chat', async t => {
  const f = await fixture(t); await f.run();
  const pause = paused(f, args => args[0] === 'tab' && args[1] === 'focus');
  const opening = open(f, pause.ports);
  await checkpoint(pause, opening);
  // Simulate another persisted owner of this area while the native reply waits.
  const latest = f.record();
  const selected = latest.chats.find(chat => chat.area === 'plan');
  selected.tabId = 'newer-tab'; selected.paneId = 'newer-pane';
  selected.session = { agent: latest.agent, id: '11111111-1111-4111-8111-111111111111' };
  writeFileSync(join(latest.runDir, 'status.json'), JSON.stringify(latest));
  pause.release(); await opening;
  assert.deepEqual(f.record().chats, latest.chats, 'A late AREA reply cannot replace newer chat custody');
});
