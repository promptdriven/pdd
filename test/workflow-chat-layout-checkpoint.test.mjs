import test from 'node:test';
import assert from 'node:assert/strict';
import {existsSync, mkdirSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {startChat} from '../src/workflow-chat.mjs';
import {openRun} from '../src/workflow-runner.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';

const allocations = h => h.calls.filter(a => a[0] === 'workspace' && a[1] === 'create' || a[0] === 'worktree' && a[1] === 'open' || a[0] === 'tab' && a[1] === 'create');
for (const stopAfter of [0, 1, 2, 3]) {
  test(`ordinary start stops after ${stopAfter} allocations when durable custody fails under lock`, async t => {
    const f = await fixture(t), root = join(f.base, 'assigned');
    f.git(f.source, 'worktree', 'add', '-qb', 'assigned', root);
    const runDir = join(f.base, 'record'); mkdirSync(runDir);
    const run = {runId:'run',repo:'example/project',sourceRoot:f.source,commonDir:f.git(f.source,'rev-parse','--path-format=absolute','--git-common-dir'),root,number:17,workflow:'bug',runDir,agent:'claude',chats:[]};
    const saved = [];
    await assert.rejects(startChat({run,area:'story',message:'begin'}, {...f.ports, checkpoint: async (chat, layout) => {
      assert.ok(existsSync(join(f.ports.layoutDirectory, 'lock')), 'Durability must be awaited while layout ownership is exclusive');
      const count = allocations(f.herdr).length;
      if (count >= 1) assert.equal(layout.repoWorkspaceId, f.herdr.workspaces[0].workspace_id);
      if (count >= 2) {
        assert.equal(layout.workspaceId, f.herdr.workspaces[1].workspace_id);
        const initial = f.herdr.panes.find(p => p.workspace_id === layout.workspaceId);
        assert.deepEqual([layout.tabId, layout.paneId, layout.terminalId], [initial.tab_id, initial.pane_id, initial.terminal_id]);
      }
      if (count >= 3) {
        const area = f.herdr.panes.at(-1);
        assert.deepEqual([chat.tabId, chat.paneId, chat.terminalId], [area.tab_id, area.pane_id, area.terminal_id]);
        assert.equal(chat.workspaceId, layout.workspaceId);
      }
      await Promise.resolve();
      if (count === stopAfter) throw Error('durability unavailable');
      saved.push(structuredClone({chat, layout}));
    }}), /durability unavailable/);
    assert.equal(allocations(f.herdr).length, stopAfter, 'Failed custody must prevent the next allocation');
    assert.equal(f.herdr.calls.filter(a => a[0] === 'pane' && a[1] === 'run').length, 0);
    assert.equal(existsSync(join(f.ports.layoutDirectory,'lock')), false);
    assert.ok(stopAfter === 0 || saved.length > 0);
  });
}

test('runner saves actual root and starting chat before subsequent effects and replaces stale layout hints', async t => {
  const f = await fixture(t), healthy = f.ports.herdr;
  const seen = [];
  f.ports.herdr = async args => {
    const operation = args.slice(0,2).join(' ');
    if (['worktree open','tab create','pane run'].includes(operation)) {
      const run = f.record();
      assert.ok(existsSync(join(f.ports.layoutDirectory, 'lock')) || operation === 'pane run');
      assert.equal(run.layout.repoWorkspaceId, f.herdr.workspaces[0].workspace_id);
      if (operation !== 'worktree open') {
        assert.equal(run.layout.workspaceId, f.herdr.workspaces[1].workspace_id);
        assert.equal(run.layout.paneId, f.herdr.panes.find(p => p.workspace_id === run.layout.workspaceId).pane_id);
      }
      if (operation === 'pane run') {
        assert.equal(run.chats.at(-1).paneId, args[2]);
        assert.equal(run.chats.at(-1).state, 'starting');
      }
      seen.push(operation);
    }
    return healthy(args);
  };
  assert.equal((await f.run()).exitCode, 0);
  assert.deepEqual(seen, ['worktree open','tab create','pane run']);
  const run = f.record(), actual = structuredClone(run.layout);
  // A unique verified live workspace supersedes saved IDs without reallocating.
  run.chats = []; run.layout = {...actual,workspaceId:'stale-workspace',tabId:'stale-tab',paneId:'stale-pane',terminalId:'stale-terminal'};
  writeFileSync(join(run.runDir,'status.json'), JSON.stringify(run));
  const count = allocations(f.herdr).length;
  const result = await openRun({ref:'17',cwd:f.source,packageRoot}, f.ports);
  assert.equal(result.exitCode, 0, result.stderr);
  assert.equal(allocations(f.herdr).length, count);
  assert.deepEqual(f.record().layout, actual);
});
