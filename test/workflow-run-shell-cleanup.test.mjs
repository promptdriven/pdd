import test from 'node:test';
import assert from 'node:assert/strict';
import {writeFileSync} from 'node:fs';
import {join} from 'node:path';
import * as runner from '../src/workflow-runner.mjs';
import {fixture} from './helpers/workflow-runner-fixture.mjs';

async function completed(t) {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  run.state = 'completed'; run.chats[0].endedAt = f.clock;
  writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
  f.tick(16 * 60_000); f.herdr.idle(); f.herdr.calls.length = 0;
  return {f, run, shell:f.herdr.paneOf(run.layout)};
}
const sweep = f => runner.tidyRuns({}, f.ports);
const live = (f, run) => f.herdr.workspaces.some(w => w.workspace_id === run.layout.workspaceId);
const shellCloses = f => f.herdr.calls.filter(a => a[0] === 'workspace' && a[1] === 'close');
const agent = status => ({agent:'codex', agent_status:status});

for (const [condition, reason] of [
  ['caller', 'run_shell_caller'], ['working', 'run_shell_busy'], ['blocked', 'run_shell_busy'],
  ['unknown-agent', 'run_shell_unknown'], ['foreground-job', 'run_shell_busy'],
  ['unknown-process', 'run_shell_unknown'], ['unavailable-process', 'run_shell_unknown'],
  ['malformed-agent', 'run_shell_unknown']
]) test(`2709 repair: tidy retains the run shell with ${condition} and later releases it`, async t => {
  const {f, run, shell} = await completed(t), command = f.ports.herdr;
  if (condition === 'caller') f.ports.env.HERDR_PANE_ID = shell.pane_id;
  if (['working', 'blocked'].includes(condition)) shell.agent = agent(condition);
  if (condition === 'unknown-agent') shell.agent = agent('unknown');
  if (condition === 'foreground-job') shell.processInfo = {
    pane_id:shell.pane_id, shell_pid:100, foreground_process_group_id:200,
    foreground_processes:[{pid:200, name:'sleep'}]
  };
  if (condition === 'unknown-process') shell.processInfo = {pane_id:shell.pane_id};
  f.ports.herdr = async args => {
    if (args[0] === 'pane' && args[1] === 'process-info' && args.at(-1) === shell.pane_id && condition === 'unavailable-process')
      throw Object.assign(Error('inspection unavailable'), {code:'herdr_failed'});
    if (args[0] === 'agent' && args[1] === 'get' && args[2] === shell.pane_id && condition === 'malformed-agent')
      return {result:{agent:{pane_id:'another-pane', agent_status:'idle'}}};
    return command(args);
  };
  const result = await sweep(f);
  assert.equal(result.exitCode, 0);
  assert.ok(live(f, run), 'protected run shell must remain live');
  assert.equal(shellCloses(f).length, 0);
  assert.equal(result.closed, 1, 'the finished area chat can still close');
  assert.equal(result.kept, 1, 'tidy must count the retained shell');
  assert.deepEqual(f.record().cleanupKept, [{area:'run shell', reason}]);
  const status = await runner.runStatus({ref:'17', cwd:f.source}, f.ports);
  assert.ok(status.message.includes(reason));
  f.ports.herdr = command; delete f.ports.env.HERDR_PANE_ID;
  shell.agent = null; delete shell.processInfo;
  assert.equal((await sweep(f)).exitCode, 0);
  assert.equal(live(f, run), false);
  assert.equal(f.record().layout.phase, 'closed');
  assert.deepEqual(f.record().cleanupKept, []);
});

for (const change of ['caller', 'working', 'terminal', 'extra-tab', 'clone'])
  test(`2709 repair: shell cleanup rechecks ${change} after its durable intent`, async t => {
    const {f, run, shell} = await completed(t), command = f.ports.herdr;
    const workspace = f.herdr.workspaces.find(w => w.workspace_id === run.layout.workspaceId);
    let changed = false;
    f.ports.herdr = async args => {
      // Mutate at the first observation/effect after the persisted intent.
      if (!changed && f.record().layout.phase === 'close_intent') {
        changed = true;
        if (change === 'caller') f.ports.env.HERDR_PANE_ID = shell.pane_id;
        if (change === 'working') shell.agent = agent('working');
        if (change === 'terminal') shell.terminal_id = 'reused-terminal';
        if (change === 'extra-tab') f.herdr.tabs.push({workspace_id:workspace.workspace_id, tab_id:'personal-tab', label:'personal'});
        if (change === 'clone') workspace.worktree.repo_key = f.source;
      }
      return command(args);
    };
    await sweep(f);
    assert.ok(changed, 'the mutation must reach the saved close boundary');
    assert.ok(live(f, run), 'changed shell must survive the close checkpoint');
    assert.equal(shellCloses(f).length, 0);
    assert.equal(f.record().layout.phase, 'close_intent');
  });

for (const failure of ['rejected', 'lost-acknowledgement'])
  test(`2709 repair: tidy reconciles a ${failure} shell close on retry`, async t => {
    const {f, run} = await completed(t), command = f.ports.herdr;
    let closes = 0;
    f.ports.herdr = async args => {
      if (args[0] === 'workspace' && args[1] === 'close') {
        closes++;
        if (failure === 'lost-acknowledgement') await command(args);
        throw Object.assign(Error('temporary close failure'), {code:'herdr_failed'});
      }
      return command(args);
    };
    await sweep(f);
    assert.equal(closes, 1);
    assert.equal(f.record().layout.phase, 'close_intent');
    assert.equal(live(f, run), failure === 'rejected');
    f.ports.herdr = async args => {
      if (args[0] === 'workspace' && args[1] === 'close') closes++;
      return command(args);
    };
    const retried = await sweep(f);
    assert.equal(retried.exitCode, 0);
    assert.equal(live(f, run), false, 'a transient failure must not leak the run shell');
    assert.equal(f.record().layout.phase, 'closed', 'fresh absence must confirm the pending close');
    assert.equal(closes, failure === 'rejected' ? 2 : 1);
    assert.equal(retried.kept, 0);
  });

for (const change of ['terminal', 'clone', 'extra-tab', 'unknown-inventory'])
  test(`2709 repair: pending shell close retains ${change} until ownership is restored`, async t => {
    const {f, run, shell} = await completed(t), command = f.ports.herdr;
    f.ports.herdr = async args => {
      if (args[0] === 'workspace' && args[1] === 'close') throw Object.assign(Error('rejected'), {code:'herdr_failed'});
      return command(args);
    };
    await sweep(f);
    const workspace = f.herdr.workspaces.find(w => w.workspace_id === run.layout.workspaceId);
    const terminal = shell.terminal_id, clone = workspace.worktree.repo_key;
    if (change === 'terminal') shell.terminal_id = 'another-terminal';
    if (change === 'clone') workspace.worktree.repo_key = f.source;
    if (change === 'extra-tab') f.herdr.tabs.push({workspace_id:workspace.workspace_id, tab_id:'personal-tab', label:'personal'});
    f.ports.herdr = async args => change === 'unknown-inventory' && args[0] === 'workspace' && args[1] === 'list'
      ? {id:'cli:workspace:list', result:{type:'workspace_list'}} : command(args);
    f.herdr.calls.length = 0;
    await sweep(f);
    assert.ok(live(f, run)); assert.equal(shellCloses(f).length, 0);
    assert.equal(f.record().layout.phase, 'close_intent');
    f.ports.herdr = command; shell.terminal_id = terminal; workspace.worktree.repo_key = clone;
    f.herdr.tabs = f.herdr.tabs.filter(tab => tab.tab_id !== 'personal-tab');
    await sweep(f);
    assert.equal(live(f, run), false, 'restored original ownership must permit a safe retry');
    assert.equal(f.record().layout.phase, 'closed');
  });

test('2709 repair: cancellation protects its caller run shell and retries from another terminal', async t => {
  const {f, run, shell} = await completed(t);
  f.ports.env.HERDR_PANE_ID = shell.pane_id; shell.agent = agent('working');
  assert.equal((await runner.cancelRun({ref:'17', cwd:f.source}, f.ports)).exitCode, 0);
  assert.ok(live(f, run), 'cancellation must retain its caller shell');
  assert.equal(shellCloses(f).length, 0);
  delete f.ports.env.HERDR_PANE_ID;
  assert.equal((await runner.cancelRun({ref:'17', cwd:f.source}, f.ports)).exitCode, 0);
  assert.equal(live(f, run), false, 'explicit cancel can close the busy original shell from another terminal');
});

test('2709 repair: a skipped shell check preserves its last retained reason', async t => {
  const {f, run, shell} = await completed(t);
  // Seed the last known shell observation while this finished chat has fresh
  // open grace. The next sweep cannot recheck the shell until the chat closes.
  shell.agent = agent('working');
  run.cleanupKept = [{area:'run shell', reason:'run_shell_busy'}];
  run.chats[0].openedAt = f.clock;
  writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
  await sweep(f);
  assert.ok(live(f, run));
  assert.ok(f.record().cleanupKept.some(item => item.area === 'run shell' && item.reason === 'run_shell_busy'),
    'a skipped shell check must preserve its last observed retention reason');
  assert.ok(f.record().cleanupKept.some(item => item.area === run.chats[0].area && item.reason === 'grace'));
  assert.equal(f.herdr.calls.some(args => args[0] === 'agent' && args[1] === 'get' && args[2] === shell.pane_id), false);
  f.tick(16 * 60_000);
  await sweep(f);
  assert.deepEqual(f.record().cleanupKept, [{area:'run shell', reason:'run_shell_busy'}]);
  shell.agent = null;
  await sweep(f);
  assert.equal(f.record().layout.phase, 'closed');
  assert.deepEqual(f.record().cleanupKept, []);
});
