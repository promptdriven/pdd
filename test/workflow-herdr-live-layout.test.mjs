import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync, readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture} from './helpers/workflow-runner-fixture.mjs';
import {startChat} from '../src/workflow-chat.mjs';

// PR 1 deliberately keeps the native bug visible without making the public suite red.
// PR 2 removes this TODO once the real implementation satisfies the assertion.
const todo = process.env.PDD_ENFORCE_LIVE_LAYOUT === '1' ? false : 'Implementation belongs to PR 2; enforce with PDD_ENFORCE_LIVE_LAYOUT=1';
test('a different linked caller starts its story chat despite an obsolete layout registry', {todo}, async t => {
  const f = await fixture(t);
  const oldSource = join(f.base, 'old-topic'), source = join(f.base, 'new-topic'), root = join(f.base, 'fresh-run');
  for (const [path, branch] of [[oldSource, 'old-topic'], [source, 'new-topic'], [root, 'fresh-run']])
    f.git(f.source, 'worktree', 'add', '-qb', branch, path);
  const commonDir = f.git(source, 'rev-parse', '--path-format=absolute', '--git-common-dir');
  const directory = f.ports.layoutDirectory, runDir = join(f.base, 'new-run-record');
  mkdirSync(directory, {recursive: true}); mkdirSync(runDir);
  const legacy = {version: 1,
    repositories: [{key: 'example/project', repository: 'example/project', sourceRoot: oldSource, commonDir, workspaceId: 'legacy', phase: 'ready'}],
    runs: [{runId: 'old-run', repoWorkspaceId: 'legacy', commonDir, cwd: join(f.base, 'old-run'), label: 'project#16 bug', phase: 'intent'}]};
  const file = join(directory, 'registry.json'), bytes = JSON.stringify(legacy);
  writeFileSync(file, bytes);
  // Intentionally no Git metadata: its old linked cwd is not a verified parent.
  const workspace = {workspace_id: 'legacy', label: 'project'};
  f.herdr.workspaces.push(workspace);
  f.herdr.tabs.push({workspace_id: 'legacy', tab_id: 'legacy-tab', label: '1'});
  f.herdr.panes.push({workspace_id: 'legacy', tab_id: 'legacy-tab', pane_id: 'legacy-pane', terminal_id: 'legacy-terminal', cwd: oldSource});
  const run = {runId: 'new-run', repo: 'example/project', number: 17, workflow: 'bug', root, sourceRoot: source, commonDir,
    runDir, agent: 'claude', chats: [], done: {}, pr: []};
  let chat;
  await assert.doesNotReject(async () => { chat = await startChat({run, area: 'story', message: 'Start the story.'}, f.ports); },
    'A stale linked-checkout registry must not prevent the new story chat from starting');
  assert.equal(chat.area, 'story');
  const live = f.herdr.workspaces.find(w => w.workspace_id === chat.workspaceId);
  assert.equal(live.worktree.checkout_path, root);
  assert.equal(live.worktree.repo_key, commonDir);
  const tab = f.herdr.tabs.find(tab => tab.tab_id === chat.tabId);
  assert.equal(tab.label, 'story');
  assert.equal(f.herdr.paneOf(chat).cwd, root);
  assert.equal(f.herdr.paneOf(chat).agent.agent, 'claude');
  assert.equal(f.herdr.calls.filter(args => args[0] === 'pane' && args[1] === 'run').length, 1);
  assert.equal(readFileSync(file, 'utf8'), bytes, 'The registry remains untouched');
  assert.deepEqual(f.herdr.workspaces.find(w => w.workspace_id === 'legacy'), workspace);
  assert.equal(f.herdr.calls.filter(args => ['close', 'remove', 'rename'].includes(args[1])).length, 0);
});
