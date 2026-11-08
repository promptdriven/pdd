import test from 'node:test';
import assert from 'node:assert/strict';
import {writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {openRun, runStatus} from '../src/workflow-runner.mjs';
import {startChat} from '../src/workflow-chat.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';

const open = (f, extra = {}) => openRun({ref: '17', cwd: f.source, packageRoot, ...extra}, f.ports);
const effects = f => f.herdr.calls.filter(a => ['close', 'create', 'open', 'run'].includes(a[1]));
const launches = f => f.herdr.calls.filter(a => a[0] === 'pane' && a[1] === 'run');
async function started(t) {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  assert.equal((await runStatus({ref: '17', cwd: f.source}, f.ports)).exitCode, 0);
  return {f, run: f.record()};
}
function restart(f) {
  for (const pane of f.herdr.panes) { pane.terminal_id += '-restart'; pane.agent = null; }
  f.herdr.calls.length = 0;
}
function changeRoot(f, run, kind) {
  const root = f.herdr.panes.find(p => p.pane_id === run.layout.paneId);
  if (kind === 'pane') root.pane_id += '-changed';
  if (kind === 'tab') {
    const tab = f.herdr.tabs.find(t => t.tab_id === root.tab_id);
    tab.tab_id += '-changed'; root.tab_id = tab.tab_id;
  }
  if (kind === 'title') f.herdr.tabs.find(t => t.tab_id === root.tab_id).label = 'other-shell';
  if (kind === 'split') f.herdr.panes.push({...root, pane_id: 'split-pane', terminal_id: 'split-terminal'});
}

for (const newSession of [false, true]) test(`3084: open refreshes restart terminals and resumes the saved session (${newSession})`, async t => {
  const {f, run} = await started(t), before = run.chats.at(-1);
  restart(f);
  const result = await open(f, {newSession});
  assert.equal(result.exitCode, 0, result.message);
  const after = f.record(), chat = after.chats.at(-1);
  assert.equal(after.layout.terminalId, run.layout.terminalId + '-restart');
  assert.equal(chat.terminalId, f.herdr.paneOf(chat).terminal_id);
  assert.equal(chat.workspaceId, before.workspaceId);
  // --new keeps its explicit fresh-session semantics in an unchanged workspace.
  if (!newSession) assert.equal(chat.session.id, before.session.id);
  assert.equal(f.herdr.calls.filter(a => a[0] === 'workspace' && a[1] === 'close').length, 0);
  assert.equal(launches(f).length, 1);
  for (const key of ['runId', 'root', 'branch', 'area', 'done', 'gate', 'decisions']) assert.deepEqual(after[key], run[key]);
  f.herdr.calls.length = 0;
  assert.equal((await open(f)).exitCode, 0);
  assert.equal(effects(f).length, 0);
});

test('3084 replay: a restart between areas saves the legacy root identity and starts the next area once', async t => {
  const {f, run} = await started(t);
  delete run.layout.rootLabel;
  restart(f);
  const saved = [];
  const chat = await startChat({run, area: 'code', message: 'Continue the saved run.'}, {...f.ports,
    checkpoint: async (chat, layout) => { saved.push({chat: structuredClone(chat), layout: structuredClone(layout)}); }
  });
  assert.equal(chat.workspaceId, run.layout.workspaceId);
  assert.equal(chat.terminalId, f.herdr.paneOf(chat).terminal_id);
  assert.equal(launches(f).length, 1);
  assert.ok(saved.some(s => s.layout?.terminalId === run.layout.terminalId + '-restart'));
  assert.equal(f.herdr.tabs.filter(t => t.workspace_id === chat.workspaceId && t.label === 'code').length, 1);
  assert.equal(f.herdr.calls.filter(a => a[0] === 'workspace' && a[1] === 'close').length, 0);
});

for (const kind of ['pane', 'tab', 'title', 'split']) test(`3084: idle changed ${kind} rebuilds and resumes without losing progress`, async t => {
  const {f, run} = await started(t), chat = run.chats.at(-1);
  restart(f); changeRoot(f, run, kind);
  const peer = await f.herdr.herdr(['workspace', 'create', '--cwd', f.source, '--label', 'peer']);
  const peerBefore = structuredClone(peer.result);
  f.herdr.calls.length = 0;
  const result = await open(f);
  assert.equal(result.exitCode, 0, result.message);
  const after = f.record(), next = after.chats.at(-1);
  assert.notEqual(next.workspaceId, chat.workspaceId);
  assert.equal(next.session.id, chat.session.id);
  assert.equal(launches(f).length, 1);
  assert.ok(launches(f)[0][3].includes(chat.session.id));
  for (const key of ['runId', 'root', 'branch', 'area', 'done', 'gate', 'decisions']) assert.deepEqual(after[key], run[key]);
  assert.deepEqual(f.herdr.workspaces.find(w => w.workspace_id === peerBefore.workspace.workspace_id), peerBefore.workspace);
  assert.ok(f.herdr.panes.some(p => p.pane_id === peerBefore.root_pane.pane_id));
  f.herdr.calls.length = 0;
  assert.equal((await open(f)).exitCode, 0);
  assert.equal(effects(f).length, 0);
});

for (const guard of ['live', 'unknown', 'unconfirmed']) test(`3084: changed layout with ${guard} chat preserves the workspace`, async t => {
  const {f, run} = await started(t);
  if (guard !== 'live') restart(f);
  changeRoot(f, run, 'pane');
  if (guard === 'unconfirmed') {
    run.chats.at(-1).startUnconfirmed = true;
    writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
  }
  if (guard === 'unknown') {
    const herdr = f.ports.herdr;
    f.ports.herdr = async args => {
      if (args[0] === 'agent' && args[1] === 'get') throw Object.assign(Error('unavailable'), {code: 'connection_lost'});
      return herdr(args);
    };
  }
  const before = structuredClone({workspaces: f.herdr.workspaces, tabs: f.herdr.tabs, panes: f.herdr.panes});
  f.herdr.calls.length = 0;
  assert.notEqual((await open(f)).exitCode, 0);
  assert.equal(effects(f).length, 0);
  assert.deepEqual({workspaces: f.herdr.workspaces, tabs: f.herdr.tabs, panes: f.herdr.panes}, before);
});

test('3084: next-area recovery preserves a live earlier-area chat', async t => {
  const {f, run} = await started(t);
  changeRoot(f, run, 'pane'); f.herdr.calls.length = 0;
  await assert.rejects(startChat({run, area: 'code', message: 'Continue.'}, {...f.ports, checkpoint: async () => {}}), {code: 'herdr_layout_identity_changed'});
  assert.equal(effects(f).length, 0);
});

test('3084: changed idle layout can start the next area through the shared recovery path', async t => {
  const {f, run} = await started(t);
  restart(f); changeRoot(f, run, 'tab');
  const saved = [];
  const next = await startChat({run, area: 'code', message: 'Continue.'}, {...f.ports,
    checkpoint: async (chat, layout) => saved.push({chat, layout})});
  assert.notEqual(next.workspaceId, run.layout.workspaceId);
  assert.equal(launches(f).length, 1);
  assert.ok(saved.some(s => s.chat?.paneId === next.paneId));
  assert.equal(f.herdr.workspaces.some(w => w.workspace_id === run.layout.workspaceId), false);
});

test('3084: a lost close reply stops dispatch and retry rebuilds once', async t => {
  const {f, run} = await started(t);
  restart(f); changeRoot(f, run, 'pane');
  const herdr = f.ports.herdr;
  let lose = true;
  f.ports.herdr = async args => {
    const reply = await herdr(args);
    if (lose && args[0] === 'workspace' && args[1] === 'close') {
      lose = false;
      throw Object.assign(Error('lost close reply'), {code: 'connection_lost'});
    }
    return reply;
  };
  assert.notEqual((await open(f)).exitCode, 0);
  assert.equal(launches(f).length, 0);
  assert.equal(f.herdr.workspaces.some(w => w.workspace_id === run.layout.workspaceId), false);
  assert.equal((await open(f)).exitCode, 0);
  assert.equal(launches(f).length, 1);
  assert.equal(f.record().chats.at(-1).session.id, run.chats.at(-1).session.id);
});

test('3084: checkpoint failure stops terminal refresh before next-area dispatch', async t => {
  const {f, run} = await started(t);
  restart(f);
  await assert.rejects(startChat({run, area: 'code', message: 'Continue.'}, {...f.ports,
    checkpoint: async () => { throw Object.assign(Error('checkpoint unavailable'), {code: 'test_checkpoint_failed'}); }}), {code: 'test_checkpoint_failed'});
  assert.equal(effects(f).length, 0);
});

test('3084: duplicate matching workspaces prevent changed-layout closure', async t => {
  const {f, run} = await started(t);
  restart(f); changeRoot(f, run, 'pane');
  const row = f.herdr.workspaces.find(w => w.workspace_id === run.layout.workspaceId);
  f.herdr.workspaces.push({...structuredClone(row), workspace_id: 'duplicate-checkout'});
  f.herdr.calls.length = 0;
  const before = structuredClone(f.herdr.workspaces);
  assert.notEqual((await open(f)).exitCode, 0);
  assert.equal(effects(f).length, 0);
  assert.deepEqual(f.herdr.workspaces, before);
});

test('3084: checkpoint failure prevents closing a changed idle workspace', async t => {
  const {f, run} = await started(t);
  restart(f); changeRoot(f, run, 'pane');
  await assert.rejects(startChat({run, area: 'code', message: 'Continue.'}, {...f.ports,
    checkpoint: async () => { throw Object.assign(Error('checkpoint unavailable'), {code: 'test_checkpoint_failed'}); }}), {code: 'test_checkpoint_failed'});
  assert.equal(effects(f).length, 0);
  assert.ok(f.herdr.workspaces.some(w => w.workspace_id === run.layout.workspaceId));
});

for (const failure of ['area-allocation', 'changed-layout-close']) test(`3084: interrupted ${failure} saves root custody without inventing the next chat`, async t => {
  const {f, run} = await started(t);
  const nextArea = run.areas[1].name;
  run.area = 1; run.state = 'running'; run.gate = null;
  writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
  restart(f);
  if (failure === 'changed-layout-close') changeRoot(f, run, 'pane');
  const herdr = f.ports.herdr;
  let interrupt = true;
  f.ports.herdr = async args => {
    if (interrupt && (failure === 'area-allocation' ? args[0] === 'tab' && args[1] === 'create' : args[0] === 'workspace' && args[1] === 'close')) {
      interrupt = false;
      throw Object.assign(Error('injected recovery interruption'), {code: 'test_recovery_interrupted'});
    }
    return herdr(args);
  };
  const failed = await open(f);
  assert.notEqual(failed.exitCode, 0);
  const paused = f.record();
  assert.equal(paused.chats.filter(c => c.area === nextArea).length, 0, 'root-only recovery must not create an area-chat record');
  assert.equal(launches(f).length, 0);
  if (failure === 'area-allocation') assert.equal(paused.layout.terminalId, run.layout.terminalId + '-restart');
  const retry = await open(f);
  assert.equal(retry.exitCode, 0, retry.message);
  const after = f.record(), chat = after.chats.at(-1);
  assert.equal(chat.area, nextArea);
  assert.notEqual(chat.paneId, after.layout.paneId);
  assert.equal(launches(f).length, 1);
  assert.equal(launches(f)[0][2], chat.paneId);
});
