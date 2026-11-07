// Issue 2903: a `cd` in the person's shell startup file moves every new Herdr pane out of the run worktree.
// The chat must still start in the worktree, and a moved shell is not a changed pane. Real Herdr IDs still count.
import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdirSync, mkdtempSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync, spawnSync } from 'node:child_process';
import { chatCommand } from '../src/workflow-chat.mjs';
import { stepDone, approveRun, openRun, cancelRun, runStatus } from '../src/workflow-runner.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';
import { liveLayout, ownerFor, mutations } from './helpers/live-herdr-layout.mjs';

const id = '11111111-1111-4111-8111-111111111111';
const temp = t => { const path = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-2903-'))); t.after(() => rmSync(path, { recursive: true, force: true })); return path; };
const count = (text, word) => text.split(word).length - 1;
// A shell whose startup moved it: plain sh after a cd, and zsh with a .zshrc that cds (when zsh is installed).
function shells(root, elsewhere) {
  const zdot = join(root, 'zdot'); mkdirSync(zdot); writeFileSync(join(zdot, '.zshrc'), `cd '${elsewhere}'\n`);
  return [['sh', line => ['/bin/sh', ['-c', `cd '${elsewhere}'; ${line}`], {}]],
    ...(existsSync('/bin/zsh') ? [['zsh .zshrc', line => ['/bin/zsh', ['-i', '-c', line], { ZDOTDIR: zdot }]]] : [])];
}

test('2903: every chat line starts the agent in the worktree although the shell startup moved the shell elsewhere', t => {
  const root = temp(t), bin = join(root, 'bin'), elsewhere = join(root, 'elsewhere'), worktree = join(root, `work 'tree' $HOME "x" ;`);
  for (const dir of [bin, elsewhere, worktree]) mkdirSync(dir);
  for (const agent of ['claude', 'codex', 'gemini', 'agy'])
    writeFileSync(join(bin, agent), `#!${process.execPath}\nprocess.stdout.write(JSON.stringify({cwd:process.cwd()}));\n`, { mode: 0o755 });
  const messageFile = join(root, 'start.md'); writeFileSync(messageFile, 'Use the pdd-bug skill.');
  const forms = { start: { messageFile, sessionId: id }, resume: { resumeId: id } };
  for (const [shell, call] of shells(root, elsewhere)) for (const agent of ['claude', 'codex', 'gemini', 'agy']) for (const [form, options] of Object.entries(forms)) {
    const line = chatCommand({ agent, cwd: worktree, commonDir: join(root, '.git'), sourceRoot: root, addDirs: [root], ...options });
    const [file, args, env] = call(line);
    const out = execFileSync(file, args, { cwd: root, env: { PATH: `${bin}:/usr/bin:/bin`, HOME: root, ...env }, encoding: 'utf8' });
    assert.equal(JSON.parse(out.slice(out.indexOf('{'))).cwd, worktree, `${shell}, ${agent} ${form}: the agent starts in the run worktree`);
  }
  // Without the worktree the agent does not start at all, so it never works in the wrong folder.
  const missing = spawnSync('/bin/sh', ['-c', `cd '${elsewhere}'; ${chatCommand({ agent: 'claude', cwd: join(root, 'gone'), messageFile, sessionId: id })}`],
    { cwd: root, env: { PATH: `${bin}:/usr/bin:/bin` }, encoding: 'utf8' });
  assert.notEqual(missing.status, 0); assert.equal(missing.stdout, '', 'no agent ran');
});

test('2903: with a shell startup cd, start, open, the next area, a fresh session and cancel all work, and every chat runs in the worktree', async t => {
  const f = await fixture(t), elsewhere = join(f.base, 'elsewhere'); mkdirSync(elsewhere);
  f.herdr.shellStartFolder = elsewhere;
  const started = await f.run();
  assert.equal(started.exitCode, 0, started.message);
  let run = f.record();
  const rootShell = f.herdr.panes.find(p => p.pane_id === run.layout.paneId);
  assert.equal(rootShell.cwd, elsewhere, 'precondition: the run\'s own shell tab moved out of the worktree');
  const inWorktree = chat => {
    const pane = f.herdr.paneOf(chat);
    assert.ok(pane.commands.at(-1).startsWith(`cd '${run.root}' && env PDD_AGENT_SESSION=1 `), pane.commands.at(-1));
    assert.equal(pane.cwd, run.root, `the ${chat.area} agent runs in the worktree`);
    assert.equal(f.herdr.sessions.find(s => s.id === pane.agent.agent_session.value).root, run.root, `the ${chat.area} session belongs to the worktree`);
  };
  inWorktree(run.chats[0]);

  const opened = await openRun({ ref: '17', cwd: f.source, packageRoot }, f.ports);
  assert.equal(opened.exitCode, 0, opened.message);

  f.tick(); assert.equal((await stepDone({ step: 'scope', summary: 'Change value.mjs to 2.', cwd: run.root }, f.agentPorts())).exitCode, 0);
  f.tick(); const approved = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(approved.exitCode, 0, approved.message);
  run = f.record(); assert.equal(run.chats.length, 2); inWorktree(run.chats[1]);
  assert.equal((await openRun({ ref: '17', cwd: f.source, packageRoot }, f.ports)).exitCode, 0, 'the next area reopens');

  f.tick(); const fresh = await openRun({ ref: '17', cwd: f.source, packageRoot, newSession: true }, f.ports);
  assert.equal(fresh.exitCode, 0, fresh.message);
  run = f.record(); assert.equal(run.chatReplacement.phase, 'launched'); inWorktree(run.chats.at(-1));

  const workspaceId = run.layout.workspaceId;
  const cancelled = await cancelRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(cancelled.exitCode, 0, cancelled.message);
  assert.doesNotMatch(cancelled.message, /stays open/, cancelled.message);
  assert.equal(f.herdr.workspaces.some(w => w.workspace_id === workspaceId), false, 'the run workspace closed although its shell moved');
});

test('2903: with a shell startup cd, the run layout opens, a retry reuses the same area tab, and the next area gets its own tab', async t => {
  const f = await liveLayout(t), elsewhere = join(f.base, 'elsewhere'); mkdirSync(elsewhere);
  f.herdr.shellStartFolder = elsewhere;
  const first = await f.open();
  assert.equal(f.herdr.paneOf(first).cwd, elsewhere, 'precondition: the new area shell moved');
  const at = f.herdr.calls.length, again = await f.open({ run: ownerFor(f, first) });
  assert.deepEqual([again.workspaceId, again.tabId, again.paneId, again.terminalId], [first.workspaceId, first.tabId, first.paneId, first.terminalId]);
  assert.deepEqual(mutations({ ...f, herdr: { ...f.herdr, calls: f.herdr.calls.slice(at) } }), [], 'no new tab, workspace or launch');
  const next = await f.open({ run: ownerFor(f, first), stageId: 'plan' });
  assert.equal(next.workspaceId, first.workspaceId); assert.notEqual(next.tabId, first.tabId);
  assert.equal(f.herdr.tabs.filter(tab => tab.workspace_id === first.workspaceId && tab.label === 'story').length, 1);
});

test('2903: a real Herdr ID change still refuses, and start, approve, open and status say what changed and what to do', async t => {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  let run = f.record();
  f.herdr.panes.find(p => p.pane_id === run.layout.paneId).terminal_id = 'replaced-terminal';
  const effects = () => f.herdr.calls.filter(a => (a[0] === 'tab' && a[1] === 'create') || (a[0] === 'pane' && a[1] === 'run')).length, before = effects();
  const reason = /\(herdr_layout_identity_changed: Herdr session pdd, workspace "[^"]+": its first tab \(the run's own shell tab\) is gone or has other Herdr IDs\. Look at that workspace in Herdr, undo the change, then try again\.\)/;
  const readable = (message, what) => {
    assert.match(message, reason, what);
    assert.equal(count(message, 'herdr_layout_identity_changed'), 1, `${what}: the code appears once`);
    assert.doesNotMatch(message, /[{}]/, `${what}: no JSON`);
  };
  const details = (message, what) => {
    const lines = message.split('\n');
    assert.ok(lines.some(line => /^Expected root_pane: tabId "[^"]+", paneId "[^"]+", terminalId "[^"]+"$/.test(line)), `${what}: ${message}`);
    assert.ok(lines.some(line => /^Found root_pane: .*pane_id "[^"]+", terminal_id "replaced-terminal"/.test(line)), `${what}: ${message}`);
  };

  f.tick(); assert.equal((await stepDone({ step: 'scope', summary: 'Change value.mjs to 2.', cwd: run.root }, f.agentPorts())).exitCode, 0);
  f.tick(); const approved = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(approved.exitCode, 1); readable(approved.message, 'approve'); details(approved.message, 'approve');
  assert.match(approved.message, /Start it: pdd workflow open 17/);

  const opened = await openRun({ ref: '17', cwd: f.source, packageRoot }, f.ports);
  assert.equal(opened.exitCode, 1); readable(opened.message, 'open'); details(opened.message, 'open');
  assert.match(opened.message.split('\n')[0], /^pdd could not open the build chat \(/);

  const status = await runStatus({ ref: '17', cwd: f.source }, f.ports);
  readable(status.message, 'status');
  assert.equal(effects(), before, 'the refusal starts no tab and no agent');
  run = f.record(); assert.equal(run.chatFailure.code, 'herdr_layout_identity_changed');
  assert.doesNotMatch(run.chatFailure.message, /\n|Expected/, 'the saved reason is the first line');
});

test('2903: a fresh start with a changed Herdr ID prints the reason and its values, then the next step', async t => {
  const f = await fixture(t), herdr = f.ports.herdr;
  // Herdr reports a different pane in the new area tab than the one it said it made.
  f.ports.herdr = async args => {
    const reply = structuredClone(await herdr(args));
    if (args[0] === 'tab' && args[1] === 'create') f.herdr.panes.find(p => p.pane_id === reply.result.root_pane.pane_id).terminal_id = 'other-terminal';
    return reply;
  };
  const started = await f.run();
  assert.equal(started.exitCode, 1);
  const lines = started.message.split('\n'), at = lines.findIndex(line => line.includes('chat startup was not confirmed'));
  assert.match(lines[at], /\(herdr_layout_identity_changed: Herdr session pdd, workspace "[^"]+": the new area tab does not show the pane that Herdr made\. Look at that workspace in Herdr, undo the change, then try again\.\)\.$/);
  assert.equal(count(started.message, 'herdr_layout_identity_changed'), 1);
  assert.match(lines[at + 1], /^Expected area_pane: workspace_id "[^"]+", tab_id "[^"]+", pane_id "[^"]+", terminal_id "[^"]+"/);
  assert.match(lines[at + 2], /^Found area_pane: .*terminal_id "other-terminal"/);
  assert.equal(lines[at + 3], 'Start it with: pdd workflow open 17');
});
