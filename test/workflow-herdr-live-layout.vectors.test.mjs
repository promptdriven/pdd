import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync, readFileSync, writeFileSync, existsSync} from 'node:fs';
import {join} from 'node:path';
import {liveLayout, mutations, ownerFor, closeRun} from './helpers/live-herdr-layout.mjs';
import {allRuns} from '../src/workflow-runs.mjs';
import fs from 'node:fs';
import {syncBuiltinESMExports} from 'node:module';
import {startChat} from '../src/workflow-chat.mjs';

const inventory = JSON.parse(readFileSync(new URL('./fixtures/workflow-herdr-live-layout.json', import.meta.url), 'utf8'));
const replay = {
  async 'legacy-linked-caller'(t, expected) {
    const f = await liveLayout(t), old = join(f.base, 'old'), source = join(f.base, 'new');
    for (const [path, branch] of [[old, 'old'], [source, 'new']]) f.git(f.source, 'worktree', 'add', '-qb', branch, path);
    mkdirSync(f.ports.directory, {recursive: true});
    const file = join(f.ports.directory, 'registry.json'), bytes = JSON.stringify({version: 1, repositories: [{sourceRoot: old, commonDir: f.input.commonDir, workspaceId: 'legacy'}], runs: [{phase: 'intent', runId: 'old'}]});
    writeFileSync(file, bytes);
    const legacy = {workspace_id: 'legacy', label: 'project'};
    f.herdr.workspaces.push(legacy);
    f.herdr.tabs.push({workspace_id: 'legacy', tab_id: 'old-tab', label: '1'});
    f.herdr.panes.push({workspace_id: 'legacy', tab_id: 'old-tab', pane_id: 'old-pane', terminal_id: 'old-terminal', cwd: old});
    const runDir = join(f.base, 'run-record'); mkdirSync(runDir);
    const run = {runId: 'run', repo: f.input.repository, sourceRoot: source, commonDir: f.input.commonDir, root: f.input.cwd, number: 17, workflow: 'bug', runDir, agent: 'claude', chats: []};
    let chat;
    await assert.doesNotReject(async () => { chat = await startChat({run, area: 'story', message: 'Begin.'}, {...f.ports, herdr: f.herdr.herdr, layoutDirectory: f.ports.directory}); }, 'Defect: stale registry must not block story dispatch');
    assert.equal(f.herdr.calls.filter(a => a[0] === 'pane' && a[1] === 'run').length, expected.chatDispatches);
    assert.equal(f.herdr.tabs.some(tab => tab.tab_id === chat.tabId && tab.label === 'story'), expected.storyTab);
    assert.equal(readFileSync(file, 'utf8') === bytes, expected.registryUnchanged);
    assert.equal(f.herdr.workspaces.find(w => w.workspace_id === 'legacy') === legacy, expected.legacyWorkspaceUnchanged);
  },
  async 'unique-live-run'(t, expected) {
    const f = await liveLayout(t), first = await f.open(), owner = ownerFor(f, first);
    owner.layout.workspaceId = 'stale'; owner.chats[0].workspaceId = 'stale';
    const at = f.herdr.calls.length, next = await f.open({run: owner});
    assert.equal(next.workspaceId === first.workspaceId, expected.reuseRun);
    assert.equal(next.tabId === first.tabId, expected.reuseTab);
    assert.equal(mutations({...f, herdr: {...f.herdr, calls: f.herdr.calls.slice(at)}}).length, expected.creates);
  },
  async 'area-label-wrong-cwd'(t, expected) {
    const f = await liveLayout(t), first = await f.open();
    const pane = f.herdr.paneOf(first); pane.cwd = f.source;
    const peer = structuredClone(pane), next = await f.open({run: ownerFor(f, first)});
    assert.equal(next.tabId === first.tabId, expected.adoptWrongTab);
    assert.equal(JSON.stringify(f.herdr.paneOf(first)) === JSON.stringify(peer), expected.preservePeer);
  },
  async 'already-open'(t, expected) {
    const f = await liveLayout(t), command = f.ports.command;
    let actual;
    f.ports.command = async args => {
      const reply = await command(args);
      if (args[0] === 'worktree') { actual = reply.result.workspace.workspace_id; return {...reply, result: {workspace: reply.result.workspace, already_open: true}}; }
      return reply;
    };
    let result;
    await assert.doesNotReject(async () => { result = await f.open(); }, 'Defect: verified already_open must be adopted');
    assert.equal(result.workspaceId === actual, expected.adoptActualIds);
    assert.equal(f.herdr.workspaces.filter(w => w.worktree.is_linked_worktree).length - 1, expected.duplicateWorkspaces);
  },
  async 'person-parent'(t, expected) {
    const f = await liveLayout(t), parent = await f.herdr.herdr(['workspace', 'create', '--cwd', f.source, '--label', 'My project', '--no-focus']);
    const before = structuredClone(parent.result.workspace), opened = await f.open();
    assert.equal(opened.repoWorkspaceId === before.workspace_id, expected.reuseParent);
    assert.equal(f.herdr.calls.some(a => a[1] === 'rename'), expected.renameParent);
    await closeRun(f, opened);
    await f.layout.closeHerdrRepoLayoutIfIdle(f.input, f.ports);
    assert.equal(f.herdr.calls.some(a => a[1] === 'close' && a[2] === before.workspace_id), expected.closeParent);
    assert.deepEqual(f.herdr.workspaces.find(w => w.workspace_id === before.workspace_id), before);
  },
  async 'independent-clone'(t, expected) {
    const f = await liveLayout(t), other = join(f.base, 'clone');
    f.git(f.base, 'clone', '-q', f.source, other);
    f.git(other, 'remote', 'set-url', 'origin', 'https://github.com/example/project.git');
    const peer = await f.herdr.herdr(['workspace', 'create', '--cwd', other, '--label', 'project', '--no-focus']);
    const before = structuredClone(peer.result.workspace), result = await f.open();
    assert.equal(result.repoWorkspaceId === before.workspace_id, expected.adoptOtherClone);
    assert.deepEqual(f.herdr.workspaces.find(w => w.workspace_id === before.workspace_id), before);
  },
  async 'ambiguous-run'(t, expected) {
    const f = await liveLayout(t), first = await f.open();
    f.herdr.workspaces.push({...structuredClone(f.herdr.workspaces.find(w => w.workspace_id === first.workspaceId)), workspace_id: 'peer'});
    f.herdr.calls.length = 0;
    await assert.rejects(f.open({run: ownerFor(f, first)}), {code: 'herdr_layout_identity_changed'});
    assert.equal(expected.refuse, true); assert.equal(mutations(f).length, expected.mutations);
  },
  async 'changed-run-identity'(t, expected) {
    for (const field of ['checkout_path', 'repo_key']) {
      const f = await liveLayout(t), first = await f.open();
      f.herdr.workspaces.find(w => w.workspace_id === first.workspaceId).worktree[field] = f.source;
      f.herdr.calls.length = 0;
      await assert.rejects(f.open({run: ownerFor(f, first)}), {code: 'herdr_layout_identity_changed'});
      assert.equal(expected.refuse, true); assert.equal(mutations(f).length, expected.mutations);
    }
  },
  async 'malformed-registry'(t, expected) {
    const f = await liveLayout(t), first = await f.open(), file = join(f.ports.directory, 'registry.json');
    writeFileSync(file, '{broken');
    let next;
    await assert.doesNotReject(async () => { next = await f.open({run: ownerFor(f, first)}); }, 'Defect: malformed obsolete registry must be ignored');
    assert.equal(next.workspaceId === first.workspaceId, expected.reuseRun);
    assert.equal(readFileSync(file, 'utf8') === '{broken', expected.registryUnchanged);
    assert.equal(f.herdr.calls.filter(a => a[1] === 'open').length === 1, expected.registryIgnored);
  },
  async 'status-index-only'(t, expected) {
    const f = await liveLayout(t), a = join(f.base, 'A', 'pdd', 'runs', '1'), b = join(f.base, 'B', 'pdd', 'runs', '2');
    for (const [runDir, number, repo] of [[a, 1, 'A'], [b, 2, 'B']]) {mkdirSync(runDir, {recursive: true}); writeFileSync(join(runDir, 'status.json'), JSON.stringify({v: 1, number, repo, runDir}));}
    writeFileSync(join(f.state, 'runs.json'), JSON.stringify({runs: [{number: 1, runDir: a}]}));
    mkdirSync(f.ports.directory, {recursive: true});
    const file = join(f.ports.directory, 'registry.json');
    writeFileSync(file, JSON.stringify({repositories: [{commonDir: join(f.base, 'B')}]}));
    const originalRead = fs.readFileSync, reads = [];
    t.mock.method(fs, 'readFileSync', (path, ...args) => {reads.push(path); return originalRead(path, ...args);});
    syncBuiltinESMExports();
    try {
      assert.deepEqual(allRuns({}, {stateDir: f.state, layoutDirectory: f.ports.directory}).map(run => run.repo), expected.listedClones);
      assert.equal(reads.includes(file), expected.registryRead);
    } finally {t.mock.restoreAll(); syncBuiltinESMExports();}
  },
  async 'adopted-parent-cleanup'(t, expected) {
    const f = await liveLayout(t), first = await f.open(); await closeRun(f, first);
    const result = await f.layout.closeHerdrRepoLayoutIfIdle(f.input, f.ports);
    assert.equal(result, expected.result);
    assert.equal(!f.herdr.workspaces.some(w => w.workspace_id === first.repoWorkspaceId), expected.parentClosed);
  },
  async 'changed-root-cleanup'(t, expected) {
    for (const kind of ['root', 'tab', 'pane']) {
      const f = await liveLayout(t), first = await f.open();
      await f.herdr.herdr(['tab', 'close', first.tabId]);
      const root = f.herdr.panes.find(p => p.pane_id === first.root.paneId);
      if (kind === 'root') root.terminal_id = 'changed';
      if (kind === 'tab') await f.herdr.herdr(['tab', 'create', '--workspace', first.workspaceId, '--cwd', f.input.cwd, '--label', 'personal', '--no-focus']);
      if (kind === 'pane') f.herdr.panes.push({...root, pane_id: 'split'});
      await assert.rejects(f.layout.closeHerdrRunLayout({...f.input, layout: first}, f.ports));
      assert.equal(!f.herdr.workspaces.some(w => w.workspace_id === first.workspaceId), expected.runClosed);
      assert.equal(!existsSync(f.input.cwd), expected.gitCheckoutRemoved);
    }
  }
};
for (const vector of inventory.cases) test(`native replay ${vector.id}: ${vector.criteria.join(', ')}`, async t => {
  assert.equal(typeof replay[vector.id], 'function', 'Every approved native case must execute a public boundary');
  await replay[vector.id](t, vector.expected);
});
