import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {existsSync, readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {runPdd} from '../src/pdd-cli.mjs';
import {openRun, runStatus, tidyRuns} from '../src/workflow-runner.mjs';
import {startChat, rebuildClosedChat} from '../src/workflow-chat.mjs';
import {tickAutopilot} from '../src/autopilot-launcher.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {healthyMachine} from './helpers/healthy-machine.mjs';
import {isolatedCheckCapacity} from './helpers/check-machine.mjs';
import {liveLayout, ownerFor, closeRun} from './helpers/live-herdr-layout.mjs';

const save = (f, run) => writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
const closes = f => f.herdr.calls.filter(a => ['workspace', 'tab'].includes(a[0]) && a[1] === 'close');
async function doneRun(t, state = 'completed') {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record(); run.state = state; run.chats[0].endedAt = f.clock;
  save(f, run); f.tick(16 * 60_000);
  for (const pane of f.herdr.panes) { pane.terminal_id += '-restart'; pane.agent = null; }
  f.herdr.calls.length = 0;
  return {f, run};
}
async function tidy(f, dryRun = false) {
  const output = {write() {}};
  return runPdd(['workflow', 'tidy', ...(dryRun ? ['--dry-run'] : [])], {
    cwd: f.source, env: f.ports.env, stdout: output, stderr: output, packageRoot,
    workflowRunner: {tidyRuns: input => tidyRuns(input, f.ports)}
  });
}
for (const state of ['completed', 'cancelled']) test(`3096 replay: tidy reclaims the ${state} run after restart and keeps session history`, async t => {
  const {f, run} = await doneRun(t, state), shell = f.herdr.paneOf(run.layout);
  const command = f.ports.herdr;
  f.ports.herdr = async args => {
    if (args[0] === 'workspace' && args[1] === 'close') {
      const saved = f.record().layout;
      assert.equal(saved.phase, 'close_intent');
      assert.equal(saved.terminalId, shell.terminal_id);
      assert.equal(saved.restartTerminal, true);
      assert.equal(saved.createdWorkspaceId, run.layout.workspaceId);
    }
    return command(args);
  };
  assert.equal(await tidy(f), 0);
  assert.equal(f.herdr.workspaces.some(w => w.workspace_id === run.layout.workspaceId), false, 'done workspace must release its restarted root pane');
  assert.equal(f.record().layout.phase, 'closed');
  assert.deepEqual(f.record().chats[0].session, run.chats[0].session);
  assert.ok(existsSync(run.runDir)); assert.ok(existsSync(run.root));
  assert.ok(existsSync(run.chats[0].messageFile));
  const count = closes(f).length;
  assert.equal(await tidy(f), 0); assert.equal(closes(f).length, count);
});

test('3096: status classifies restart panes, warns near capacity and lists unowned workspace commands without closing', async t => {
  const {f, run} = await doneRun(t);
  const foreign = {workspace_id: "personal'pane", label: 'personal'};
  f.herdr.workspaces.push(foreign);
  f.herdr.tabs.push({workspace_id: foreign.workspace_id, tab_id: 'personal-tab', label: '1'});
  f.herdr.panes.push({workspace_id: foreign.workspace_id, tab_id: 'personal-tab', pane_id: 'personal-pane', terminal_id: 'personal-terminal'});
  f.ports.env.PDD_HERDR_PANE_BUDGET = '4';
  const before = readFileSync(join(run.runDir, 'status.json'));
  const result = await runStatus({cwd: f.source, json: true}, f.ports);
  assert.equal(result.exitCode, 0);
  const status = JSON.parse(result.message).herdr;
  assert.deepEqual(status.owners, {working: 0, parked: 0, done: 2, unowned: 2});
  assert.ok(status.warning);
  assert.deepEqual(status.unownedWorkspaces, [{workspaceId: foreign.workspace_id, closeCommand: "herdr --session pdd workspace close 'personal'\\''pane'"}]);
  assert.deepEqual(readFileSync(join(run.runDir, 'status.json')), before);
  assert.equal(closes(f).length, 0);
  assert.equal(await tidy(f, true), 0);
  assert.equal(closes(f).length, 0);
  assert.deepEqual(readFileSync(join(run.runDir, 'status.json')), before);
  assert.equal(await tidy(f), 0);
  assert.ok(f.herdr.workspaces.includes(foreign));
  assert.equal(f.herdr.workspaces.some(w => w.workspace_id === run.layout.workspaceId), false);
});

for (const guard of ['caller', 'busy', 'unknown', 'agent', 'root-title', 'split', 'foreign-clone', 'unproved-creation', 'wrong-creation'])
  test(`3096: restart cleanup retains ${guard}`, async t => {
    const {f, run} = await doneRun(t), pane = f.herdr.paneOf(run.layout), command = f.ports.herdr;
    if (guard === 'caller') f.ports.env.HERDR_PANE_ID = pane.pane_id;
    if (guard === 'busy') pane.processInfo = {pane_id: pane.pane_id, shell_pid: 100, foreground_process_group_id: 200, foreground_processes: [{pid: 200, name: 'sleep'}]};
    if (guard === 'unknown') pane.processInfo = {pane_id: pane.pane_id};
    if (guard === 'agent') pane.agent = {agent: 'codex', agent_status: 'idle'};
    if (guard === 'root-title') f.herdr.tabs.find(t => t.tab_id === pane.tab_id).label = 'personal';
    if (guard === 'split') f.herdr.panes.push({...pane, pane_id: 'personal-split'});
    if (guard === 'foreign-clone') f.herdr.workspaces.find(w => w.workspace_id === run.layout.workspaceId).worktree.repo_key = f.source;
    if (guard === 'unproved-creation') { run.layout.createdWorkspaceId = null; save(f, run); }
    if (guard === 'wrong-creation') { run.layout.createdWorkspaceId = 'other-workspace'; save(f, run); }
    assert.equal(await tidy(f), 0);
    assert.ok(f.herdr.workspaces.some(w => w.workspace_id === run.layout.workspaceId));
    assert.equal(closes(f).filter(a => a[0] === 'workspace').length, 0);
    assert.ok(f.record().cleanupKept.length > 0);
    f.ports.herdr = command;
  });

for (const mutation of ['terminal', 'title', 'caller', 'busy']) test(`3096: restart cleanup rechecks ${mutation} after saving close intent`, async t => {
  const {f, run} = await doneRun(t), pane = f.herdr.paneOf(run.layout), command = f.ports.herdr;
  let changed = false;
  f.ports.herdr = async args => {
    if (!changed && f.record().layout.phase === 'close_intent') {
      changed = true;
      if (mutation === 'terminal') pane.terminal_id += '-again';
      if (mutation === 'title') f.herdr.tabs.find(t => t.tab_id === pane.tab_id).label = 'personal';
      if (mutation === 'caller') f.ports.env.HERDR_PANE_ID = pane.pane_id;
      if (mutation === 'busy') pane.agent = {agent: 'codex', agent_status: 'working'};
    }
    return command(args);
  };
  await tidy(f);
  assert.ok(changed, 'restart recovery must reach the saved close intent');
  assert.equal(f.record().layout.phase, 'close_intent');
  assert.ok(f.herdr.paneOf(run.layout));
  assert.equal(closes(f).filter(a => a[0] === 'workspace').length, 0);
});

test('3096: adoption does not authorize closing a person-created matching workspace', async t => {
  const f = await liveLayout(t), created = await f.open();
  // Another run adopts this already-open linked checkout. Its record did not create it.
  const adopted = await f.open({run: {runId: f.input.runId, chats: []}});
  await assert.rejects(closeRun(f, adopted), {code: 'layout_cleanup_uncertain'});
  assert.ok(f.herdr.workspaces.some(w => w.workspace_id === created.workspaceId));
  assert.equal(closes(f).filter(a => a[0] === 'workspace').length, 0);
});

test('3096: an enabled Autopilot tick reclaims done restart panes through the injected workflow Herdr port', async t => {
  const {f, run} = await doneRun(t);
  const stateFile = join(f.state, 'launcher.json');
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto', trust: []}}));
  writeFileSync(stateFile, JSON.stringify({enabled: true, defaultBranch: 'main', baseBranch: 'main', stateFile,
    cwd: f.source, repo: run.repo, packageRoot, coordinatorId: 'coordinator', machine: 'machine', activatedAt: 1,
    agent: {id: 'claude', kind: 'claude', command: 'claude'}, environment: f.ports.env, retryAt: f.clock + 86400000}));
  const result = await tickAutopilot(stateFile, {...healthyMachine, ...f.ports, workflowHerdr: f.herdr.herdr,
    checkCapacityPorts: isolatedCheckCapacity(f.base),
    run: async (file, args, options) => ({code: 0, ...await f.ports.execFile(file, args, options)}),
    sendDigest: async () => ({exitCode: 0}), warn() {}});
  assert.equal(result.exitCode, 0);
  assert.equal(f.herdr.workspaces.some(w => w.workspace_id === run.layout.workspaceId), false, 'tick must release the done run workspace');
  assert.equal(f.record().layout.phase, 'closed');
  assert.deepEqual(f.record().chats[0].session, run.chats[0].session);
});

for (const failure of ['lost-reply', 'rejected']) test(`3096: restart close ${failure} is reconciled on a later sweep`, async t => {
  const {f, run} = await doneRun(t), command = f.ports.herdr;
  let requests = 0;
  f.ports.herdr = async args => {
    if (args[0] === 'workspace' && args[1] === 'close') {
      requests++;
      if (failure === 'lost-reply') await command(args);
      throw Object.assign(Error('controlled close failure'), {code: 'herdr_failed'});
    }
    return command(args);
  };
  await tidy(f);
  assert.equal(requests, 1, 'restarted root must reach its close request');
  assert.equal(f.record().layout.phase, 'close_intent');
  f.ports.herdr = command;
  await tidy(f);
  assert.equal(f.record().layout.phase, 'closed');
  assert.equal(f.herdr.workspaces.some(w => w.workspace_id === run.layout.workspaceId), false);
});

test('3096: pane categories follow the saved live and parked states across terminal drift', async t => {
  const {f, run} = await doneRun(t);
  run.state = 'running'; save(f, run);
  const view = async () => JSON.parse((await runStatus({cwd: f.source, json: true}, f.ports)).message).herdr;
  assert.deepEqual((await view()).owners, {working: 2, parked: 0, done: 0, unowned: 1});
  const current = f.record(); current.parking = {phase: 'parked', at: f.clock, blocker: {kind: 'person'}}; save(f, current);
  assert.deepEqual((await view()).owners, {working: 0, parked: 2, done: 0, unowned: 1});
  assert.equal(closes(f).length, 0);
});

for (const flag of [true, undefined]) test(`3096: an intervening adoption with creation flag ${flag} cannot authorize closure`, async t => {
  const f = await liveLayout(t), command = f.ports.command;
  f.ports.command = async args => {
    const reply = await command(args);
    if (args[0] === 'worktree' && args[1] === 'open') {
      if (flag === undefined) delete reply.result.already_open;
      else reply.result.already_open = flag;
    }
    return reply;
  };
  const opened = await f.open();
  await assert.rejects(closeRun(f, opened), {code: 'layout_cleanup_uncertain'});
  assert.ok(f.herdr.workspaces.some(w => w.workspace_id === opened.workspaceId));
  assert.equal(closes(f).filter(a => a[0] === 'workspace').length, 0);
});

test('3096: restarted area cleanup rechecks the tab label after its durable checkpoint', async t => {
  const {f, run} = await doneRun(t), command = f.ports.herdr, chat = run.chats[0];
  let renamed = false;
  f.ports.herdr = async args => {
    if (!renamed && f.record().chats[0].closed) {
      renamed = true;
      f.herdr.tabs.find(tab => tab.tab_id === chat.tabId).label = 'personal';
    }
    return command(args);
  };
  await tidy(f);
  assert.ok(renamed);
  assert.ok(f.herdr.paneOf(chat), 'a tab renamed after the checkpoint must be retained');
  assert.equal(f.record().chats[0].closed.confirmedAt, undefined);
  assert.equal(closes(f).length, 0);
});

test('3096: a failed restart-root checkpoint sends no workspace close', async t => {
  const f = await liveLayout(t), opened = await f.open();
  f.herdr.paneOf(opened.root).terminal_id += '-restart';
  let checkpoints = 0;
  f.ports.checkpoint = async () => { checkpoints++; throw Object.assign(Error('controlled save failure'), {code: 'workflow_run_save_failed'}); };
  await assert.rejects(closeRun(f, opened), {code: 'workflow_run_save_failed'});
  assert.equal(checkpoints, 1);
  assert.ok(f.herdr.workspaces.some(w => w.workspace_id === opened.workspaceId));
  assert.equal(closes(f).filter(a => a[0] === 'workspace').length, 0);
});

test('3096: empty run status still lists unowned workspaces and capacity warnings', async t => {
  const f = await fixture(t);
  const opened = await f.herdr.herdr(['workspace', 'create', '--cwd', f.source, '--label', 'personal', '--no-focus']);
  f.ports.env.PDD_HERDR_PANE_BUDGET = '1';
  f.herdr.calls.length = 0;
  const status = JSON.parse((await runStatus({cwd: f.source, json: true}, f.ports)).message);
  assert.equal(status.runs.length, 0);
  assert.deepEqual(status.herdr.owners, {working: 0, parked: 0, done: 0, unowned: 1});
  assert.ok(status.herdr.warning);
  assert.deepEqual(status.herdr.unownedWorkspaces.map(w => w.workspaceId), [opened.result.workspace.workspace_id]);
  const human = await runStatus({cwd: f.source}, f.ports);
  assert.ok(human.message.includes(status.herdr.unownedWorkspaces[0].closeCommand));
  assert.ok(human.message.includes(status.herdr.warning));
  assert.equal(closes(f).length, 0);
});

for (const change of ['clone', 'agent', 'pane']) test(`3096: rebuild refuses a ${change} change after its checkpoint`, async t => {
  const f = await liveLayout(t), opened = await f.open(), owner = ownerFor(f, opened);
  f.herdr.paneOf(opened.root).pane_id += '-changed';
  let changed = false;
  f.ports.checkpoint = async () => {
    changed = true;
    if (change === 'clone') f.herdr.workspaces.find(w => w.workspace_id === opened.workspaceId).worktree.repo_key = f.source;
    if (change === 'agent') f.herdr.panes.find(p => p.workspace_id === opened.workspaceId).agent = {agent: 'codex', agent_status: 'working'};
    if (change === 'pane') f.herdr.panes.push({...f.herdr.panes.find(p => p.workspace_id === opened.workspaceId), pane_id: 'personal-pane'});
  };
  await assert.rejects(f.open({run: owner}));
  assert.ok(changed);
  assert.equal(closes(f).filter(a => a[0] === 'workspace').length, 0);
  assert.ok(f.herdr.workspaces.some(w => w.workspace_id === opened.workspaceId));
});

test('3096: allocation preserves restart cleanup custody and forced cleanup still requires agent absence', async t => {
  const f = await liveLayout(t), opened = await f.open(), owner = ownerFor(f, opened);
  owner.layout.restartTerminal = true;
  const allocated = await f.open({run: owner});
  assert.equal(allocated.restartTerminal, true);
  f.herdr.paneOf(opened.root).agent = {agent: 'codex', agent_status: 'idle'};
  f.ports.force = true;
  await assert.rejects(closeRun(f, allocated), {code: 'run_shell_busy'});
  assert.equal(closes(f).filter(a => a[0] === 'workspace').length, 0);
});

for (const operation of ['start', 'rebuild']) test(`3096: ${operation} checkpoints preserve flat-root restart cleanup custody`, async t => {
  const {f, run} = await doneRun(t);
  run.state = 'running'; run.layout.restartTerminal = true;
  const saved = [];
  const ports = {...f.ports, checkpoint: async (chat, layout) => { if (layout) saved.push(layout); }};
  if (operation === 'start') await startChat({run, area: 'next', message: 'Continue.'}, ports);
  else await rebuildClosedChat({run, chat: run.chats[0], message: 'Continue.'}, ports);
  assert.ok(saved.length > 0);
  assert.ok(saved.every(layout => layout.restartTerminal === true));
  assert.ok(saved.every(layout => layout.createdWorkspaceId === run.layout.workspaceId));
});

for (const when of ['before', 'checkpoint']) for (const guard of ['caller', 'busy', 'unknown'])
  test(`3096: changed-layout rebuild protects ${guard} area pane ${when}`, async t => {
    const f = await liveLayout(t), opened = await f.open(), owner = ownerFor(f, opened);
    f.ports.env = {};
    f.herdr.paneOf(opened.root).pane_id += '-changed';
    const areaPane = f.herdr.paneOf(opened);
    const protect = () => {
      if (guard === 'caller') f.ports.env.HERDR_PANE_ID = areaPane.pane_id;
      if (guard === 'busy') areaPane.processInfo = {pane_id: areaPane.pane_id, shell_pid: 100, foreground_process_group_id: 200, foreground_processes: [{pid: 200, name: 'sleep'}]};
      if (guard === 'unknown') areaPane.processInfo = {pane_id: areaPane.pane_id};
    };
    if (when === 'before') protect();
    else f.ports.checkpoint = async () => protect();
    await assert.rejects(f.open({run: owner}), {code: guard === 'caller' ? 'run_shell_caller' : guard === 'busy' ? 'run_shell_busy' : 'run_shell_unknown'});
    assert.equal(closes(f).filter(a => a[0] === 'workspace').length, 0);
    assert.ok(f.herdr.paneOf(opened));
  });


test('3096: opening a terminal-drifted root records restart cleanup custody', async t => {
  const f = await liveLayout(t), opened = await f.open(), owner = ownerFor(f, opened);
  f.herdr.paneOf(opened.root).terminal_id += '-restart';
  const allocated = await f.open({run: owner});
  assert.equal(allocated.restartTerminal, true);
  f.herdr.paneOf(opened.root).agent = {agent: 'codex', agent_status: 'idle'};
  f.ports.force = true;
  await assert.rejects(closeRun(f, allocated), {code: 'run_shell_busy'});
  assert.equal(closes(f).filter(a => a[0] === 'workspace').length, 0);
});

test('3096: replacement allocation saves refreshed root custody before creating its area tab', async t => {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record(), command = f.ports.herdr, root = f.herdr.paneOf(run.layout);
  let checked = false;
  f.ports.herdr = async args => {
    if (args[0] === 'tab' && args[1] === 'create') {
      checked = true;
      assert.equal(f.record().layout.terminalId, root.terminal_id);
      assert.equal(f.record().layout.restartTerminal, true);
      assert.equal(f.record().layout.createdWorkspaceId, run.layout.workspaceId);
    }
    const reply = await command(args);
    if (args[0] === 'tab' && args[1] === 'close' && args[2] === run.chats[0].tabId) root.terminal_id += '-restart';
    return reply;
  };
  const result = await openRun({ref: '17', newSession: true, cwd: f.source, packageRoot}, f.ports);
  assert.equal(result.exitCode, 0, result.message);
  assert.ok(checked);
  assert.equal(f.record().layout.terminalId, root.terminal_id);
  assert.equal(f.record().layout.restartTerminal, true);
  assert.equal(f.record().chatReplacement.phase, 'launched');
});

test('3096 integration: creation checkpoints retain root custody before area allocation', async t => {
  const f = await liveLayout(t), snapshots = [];
  f.ports.checkpoint = async value => {
    snapshots.push(structuredClone(value));
    if (!value.workspaceId) return;
    const shell = f.herdr.panes.find(p => p.workspace_id === value.workspaceId);
    assert.equal(value.createdWorkspaceId, value.workspaceId);
    assert.deepEqual([value.root?.tabId, value.root?.paneId, value.root?.terminalId],
      [shell.tab_id, shell.pane_id, shell.terminal_id]);
    if (!f.herdr.calls.some(a => a[0] === 'tab' && a[1] === 'create'))
      assert.equal(value.tabId, undefined, 'root custody cannot invent an area chat');
  };
  const opened = await f.open();
  assert.ok(snapshots.filter(value => value.workspaceId === opened.workspaceId).length >= 2);
});


test('3123 finished cleanup adopts genuine legacy creation and retains history', async t => {
  const {f, run} = await doneRun(t);
  delete run.layout.createdWorkspaceId; save(f, run);
  assert.equal(await tidy(f), 0);
  assert.equal(f.record().layout.createdWorkspaceId, run.layout.workspaceId);
  assert.equal(f.record().layout.phase, 'closed');
  assert.equal(f.herdr.workspaces.some(w => w.workspace_id === run.layout.workspaceId), false);
  assert.deepEqual(f.record().chats[0].session, run.chats[0].session);
  assert.ok(existsSync(run.root));
});
