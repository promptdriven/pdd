import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync, writeFileSync, rmSync} from 'node:fs';
import {join} from 'node:path';
import {openRun, runStatus} from '../src/workflow-runner.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';

const open = (f, extra = {}) => openRun({ref: '17', cwd: f.source, packageRoot, ...extra}, f.ports);
const launches = f => f.herdr.calls.filter(a => a[0] === 'pane' && a[1] === 'run');
const effects = f => f.herdr.calls.filter(a => ['create', 'open', 'close', 'run'].includes(a[1]));
const save = (f, run) => writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
async function closed(t, agent = 'claude') {
  const f = await fixture(t, {agent});
  assert.equal((await f.run()).exitCode, 0);
  assert.equal((await runStatus({ref: '17', cwd: f.source}, f.ports)).exitCode, 0);
  const run = f.record(), chat = run.chats.at(-1);
  await f.herdr.herdr(['workspace', 'close', chat.workspaceId]);
  f.herdr.calls.length = 0;
  return {f, run, chat};
}

for (const agent of ['claude', 'codex']) for (const newSession of [false, true]) {
  test(`2905: closed workspace ${agent} ${newSession ? '--new' : 'open'} restores the same conversation and preserves peers`, async t => {
    const {f, run, chat} = await closed(t, agent);
    const bytes = readFileSync(chat.messageFile);
    if (newSession) {
      const refused = await openRun({ref: '17', cwd: f.source, packageRoot, newSession},
        {...f.ports, env: {...f.ports.env, PDD_AGENT_SESSION: '1'}});
      assert.notEqual(refused.exitCode, 0);
      assert.equal(f.herdr.calls.length, 0, 'caller safety precedes closed-workspace inspection');
    }
    const peer = await f.herdr.herdr(['workspace', 'create', '--cwd', f.source, '--label', 'peer']);
    const peerId = peer.result.workspace.workspace_id;
    const result = await open(f, {newSession});
    assert.equal(result.exitCode, 0, result.message);
    const after = f.record(), next = after.chats.at(-1);
    assert.notEqual(next.workspaceId, chat.workspaceId);
    assert.notEqual(next.tabId, chat.tabId);
    assert.notEqual(next.paneId, chat.paneId);
    assert.equal(next.terminalId, f.herdr.paneOf(next).terminal_id);
    assert.equal(after.layout.workspaceId, next.workspaceId);
    assert.ok(f.herdr.panes.some(p => p.pane_id === after.layout.paneId && p.workspace_id === next.workspaceId));
    assert.equal(next.session.id, chat.session.id);
    assert.equal(f.herdr.paneOf(next).agent.agent_session.value, chat.session.id);
    assert.equal(launches(f).length, 1);
    assert.ok(launches(f)[0][3].includes(chat.session.id));
    assert.match(launches(f)[0][3], /resume/);
    assert.ok(readFileSync(next.messageFile).equals(bytes));
    for (const key of ['root', 'branch', 'runId', 'area', 'done', 'pr', 'gate', 'decisions', 'configDir']) assert.deepEqual(after[key], run[key], key);
    assert.ok(f.herdr.workspaces.some(w => w.workspace_id === peerId));
    const workspace = f.herdr.workspaces.find(w => w.workspace_id === next.workspaceId);
    assert.equal(workspace.worktree.checkout_path, run.root);
    assert.equal(workspace.worktree.repo_key, run.commonDir);
    f.herdr.calls.length = 0;
    assert.equal((await open(f)).exitCode, 0);
    assert.equal(effects(f).length, 0, 'repeat open only focuses the saved chat');
    // A saved ID that is present with a foreign identity must never be rebuilt or adopted.
    workspace.worktree.checkout_path = f.source;
    f.herdr.calls.length = 0;
    assert.notEqual((await open(f, {newSession})).exitCode, 0);
    assert.equal(effects(f).length, 0);
  });
}

for (const newSession of [false, true]) test(`2905: conflicting saved layout ID refuses despite a matching workspace (${newSession ? '--new' : 'open'})`, async t => {
  const {f, run, chat} = await closed(t);
  const matching = await f.herdr.herdr(['worktree', 'open', '--workspace', run.layout.repoWorkspaceId,
    '--path', run.root, '--label', 'interrupted-recovery', '--no-focus']);
  const matchingId = matching.result.workspace.workspace_id;
  const foreign = await f.herdr.herdr(['workspace', 'create', '--cwd', f.source, '--label', 'foreign']);
  run.layout.workspaceId = foreign.result.workspace.workspace_id;
  save(f, run);
  const inventory = structuredClone({workspaces: f.herdr.workspaces, tabs: f.herdr.tabs, panes: f.herdr.panes});
  const message = readFileSync(chat.messageFile);
  f.herdr.calls.length = 0;

  const result = await open(f, {newSession});
  assert.notEqual(result.exitCode, 0, 'a live conflicting saved ID must refuse before adopting a match');
  assert.match(result.message, /herdr_layout_identity_changed/);
  assert.ok(result.message.includes(run.layout.workspaceId), result.message);
  assert.ok(result.message.includes(run.root), result.message);
  assert.ok(result.message.includes(f.source), result.message);
  for (const key of ['runId', 'root', 'branch', 'commonDir', 'layout', 'chats', 'area', 'done', 'pr', 'gate', 'decisions'])
    assert.deepEqual(f.record()[key], run[key], key);
  assert.deepEqual({workspaces: f.herdr.workspaces, tabs: f.herdr.tabs, panes: f.herdr.panes}, inventory);
  assert.ok(f.herdr.calls.every(a => a[0] === 'status' || ['list', 'get'].includes(a[1])), 'refusal makes only Herdr reads');
  assert.ok(readFileSync(chat.messageFile).equals(message));

  // A missing saved ID permits retry after an interrupted workspace allocation.
  run.layout.workspaceId = chat.workspaceId;
  save(f, run);
  f.herdr.calls.length = 0;
  const retry = await open(f, {newSession});
  assert.equal(retry.exitCode, 0, retry.message);
  assert.equal(f.record().layout.workspaceId, matchingId);
  assert.equal(f.record().chats.at(-1).session.id, chat.session.id);
  assert.equal(launches(f).length, 1);
  assert.equal(f.herdr.calls.filter(a => ['create', 'open'].includes(a[1]) && a[0] !== 'tab').length, 0);
  assert.deepEqual(f.herdr.workspaces, inventory.workspaces);
});

for (const newSession of [false, true]) test(`2905: closed workspace without a resumable session starts the area once (${newSession})`, async t => {
  const {f, run, chat} = await closed(t, 'gemini');
  chat.session = null;
  save(f, run);
  const result = await open(f, {newSession});
  assert.equal(result.exitCode, 0, result.message);
  const next = f.record().chats.at(-1), command = launches(f)[0][3];
  assert.notEqual(next.workspaceId, chat.workspaceId);
  assert.equal(launches(f).length, 1);
  assert.match(command, /gemini/);
  assert.doesNotMatch(command, /--resume/);
  assert.ok(command.includes(next.messageFile));
  assert.ok(readFileSync(next.messageFile, 'utf8').includes(run.issue.url));
  assert.deepEqual(f.record().done, run.done);
});

test('2905: status identifies the closed workspace in detail, list and JSON without creating anything', async t => {
  const {f} = await closed(t);
  for (const options of [{ref: '17'}, {}, {ref: '17', json: true}]) {
    const status = await runStatus({cwd: f.source, ...options}, f.ports);
    assert.equal(status.exitCode, 0, status.message);
    assert.match(status.message, /workspace.*closed/i);
    assert.match(status.message, /pdd workflow open 17/);
  }
  assert.equal(effects(f).length, 0);
});

for (const newSession of [false, true]) test(`2905: missing worktree refuses with its path and creates nothing (${newSession})`, async t => {
  const {f, run} = await closed(t);
  rmSync(run.root, {recursive: true});
  const result = await open(f, {newSession});
  assert.notEqual(result.exitCode, 0);
  assert.ok(result.message.includes(run.root), result.message);
  assert.match(result.message, /missing|restore/i);
  assert.equal(effects(f).length, 0);
});

test('2905: a lost rebuild launch reply saves the new custody and does not dispatch a second first message', async t => {
  const {f, chat} = await closed(t);
  const herdr = f.ports.herdr;
  f.ports.herdr = async args => {
    const reply = await herdr(args);
    if (args[0] === 'pane' && args[1] === 'run') throw Object.assign(Error('lost reply'), {code: 'connection_lost'});
    return reply;
  };
  const result = await open(f);
  assert.notEqual(result.exitCode, 0);
  const next = f.record().chats.at(-1);
  assert.notEqual(next.workspaceId, chat.workspaceId);
  assert.equal(next.startUnconfirmed, true);
  assert.equal(f.record().layout.workspaceId, next.workspaceId);
  f.ports.herdr = herdr;
  f.herdr.calls.length = 0;
  assert.equal((await open(f)).exitCode, 0);
  assert.equal(launches(f).length, 0);
  assert.equal(f.record().chats.at(-1).session.id, chat.session.id);
});

test('2905: recovery verifies the saved worktree assignment before opening a replacement workspace', async t => {
  const {f, run: codeRun} = await closed(t);
  // The ordinary PR 2 transition has a new saved branch in the same assigned worktree.
  f.git(codeRun.root, 'switch', '-qc', `${codeRun.branch}-code`);
  codeRun.branch += '-code';
  save(f, codeRun);
  assert.equal((await open(f)).exitCode, 0);
  const run = f.record();
  await f.herdr.herdr(['workspace', 'close', run.layout.workspaceId]);
  f.git(run.root, 'checkout', '-qb', 'foreign-run');
  f.herdr.calls.length = 0;
  const result = await open(f);
  assert.notEqual(result.exitCode, 0);
  assert.equal(effects(f).length, 0);
});

test('closed workspace recovery applies caller login unsets before resuming', async t => {
  const { f, run } = await closed(t, 'codex');
  assert.equal((await open(f)).exitCode, 0);
  const command = launches(f)[0][3];
  assert.ok(command.startsWith(`cd '${run.root}' && env `));
  for (const name of ['OPENAI_API_KEY', 'CODEX_API_KEY', 'CODEX_ACCESS_TOKEN', 'OPENAI_FEDERATION_RULE_ID', 'OPENAI_IDENTITY_TOKEN_FILE', 'OPENAI_WORKLOAD_IDENTITY_CONTEXT']) {
    assert.ok(command.includes(`-u ${name} `), name);
  }
});
