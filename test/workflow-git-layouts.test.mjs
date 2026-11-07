// pdd workflow run in the four supported Git layouts, with real Herdr 0.9.1 identity rules (#2698, #3050).
// Real temporary Git repositories, a fake gh and a fake Herdr; no network.
import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { basename, dirname, join } from 'node:path';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';
import { startRun, runStatus, cancelRun, openRun } from '../src/workflow-runner.mjs';
import { agentDirs, chatCommand } from '../src/workflow-chat.mjs';

const ORIGIN = 'https://github.com/example/project.git';
// For each layout: the folder to start from, Git's primary registration R (the Herdr parent),
// the common Git directory and the documented run worktrees folder.
const LAYOUTS = {
  'normal clone': f => ({ cwd: f.source, root: f.source, common: join(f.source, '.git'), folder: join(f.base, 'project.pdd-worktrees') }),
  'linked worktree of a normal clone': f => {
    const cwd = join(f.base, 'caller'); f.git(f.source, 'worktree', 'add', '-q', '-b', 'caller', cwd, 'main');
    return { cwd, root: f.source, common: join(f.source, '.git'), folder: join(f.base, 'project.pdd-worktrees') };
  },
  'bare project.git with a linked worktree': f => {
    const root = join(f.base, 'project.git');
    return { ...bare(f, root, root), root, folder: join(f.base, 'project.git.pdd-worktrees') };
  },
  'bare repository in P/.git with a linked worktree': f => {
    const root = join(f.base, 'repository');
    return { ...bare(f, join(root, '.git'), root), root, folder: join(f.base, 'repository.pdd-worktrees') };
  },
  'bare P/.bare named by the P/.git file': f => {
    const holder = join(f.base, 'repository'), root = join(holder, '.bare');
    mkdirSync(holder); const made = bare(f, root, root, () => writeFileSync(join(holder, '.git'), 'gitdir: ./.bare\n'));
    return { ...made, root, folder: join(f.base, 'repository.pdd-worktrees') };
  },
};
// A bare clone of the fixture's repository with its origin, and a linked worktree outside it (as in #2698).
function bare(f, common, root, after = () => {}) {
  f.git(f.base, 'clone', '-q', '--bare', f.source, common); after();
  f.git(root, 'remote', 'set-url', 'origin', ORIGIN);
  f.git(root, 'update-ref', 'refs/remotes/origin/main', f.git(root, 'rev-parse', 'main'));
  const cwd = join(f.base, 'topic-worktree'); f.git(root, 'worktree', 'add', '-q', '-b', 'topic', cwd, 'main');
  return { cwd, common, bare: true };
}

async function layout(t, name) {
  const f = await fixture(t, { agent: 'codex' }), l = LAYOUTS[name](f), healthy = f.ports.herdr;
  // Real Herdr 0.9.1 identity rules: a new parent has no Git identity, and `worktree open --path` refuses a bare folder.
  f.herdr.realIdentity = true;
  // Herdr opens a linked worktree only from the repository parent workspace (Git's primary registration).
  f.ports.herdr = async args => {
    if (args[0] === 'worktree' && args[1] === 'open') {
      const parent = args[args.indexOf('--workspace') + 1], pane = f.herdr.panes.find(p => p.workspace_id === parent);
      if (pane?.cwd !== l.root) { f.herdr.calls.push(args); throw Object.assign(Error('New and open worktree actions start from the repo parent workspace.'), { code: 'linked_worktree_source' }); }
    }
    return healthy(args);
  };
  const record = () => JSON.parse(readFileSync(join(l.common, 'pdd/runs/17/status.json'), 'utf8'));
  const start = () => startRun({ name: 'small-change', issue: '17', agent: 'codex', cwd: l.cwd, packageRoot }, f.ports);
  return { f, ...l, record, start };
}

for (const name of Object.keys(LAYOUTS)) test(`2698: ${name}: run, Herdr parent, chat folder, status and cleanup`, async t => {
  const l = await layout(t, name), { f } = l;
  writeFileSync(join(l.cwd, 'value.mjs'), 'export const value = "unsaved";\n');
  const dirty = f.git(l.cwd, 'status', '--porcelain=v1');
  const coreBare = l.bare ? f.git(l.common, 'config', '--get', 'core.bare') : null;
  const started = await l.start();
  assert.equal(started.exitCode, 0, started.message);
  const run = l.record();
  assert.equal(run.sourceRoot, l.cwd); assert.equal(run.commonDir, l.common);
  assert.equal(dirname(run.root), l.folder, 'the run worktree is in the documented folder');
  assert.equal(f.git(run.root, 'rev-parse', '--show-toplevel'), run.root);
  assert.equal(f.git(l.cwd, 'status', '--porcelain=v1'), dirty, 'the invoking checkout is unchanged');
  if (l.bare) assert.equal(f.git(l.common, 'config', '--get', 'core.bare'), coreBare);
  // Herdr parent: one workspace at Git's primary registration; the run workspace opens from it. A normal parent is
  // attached to its own checkout first. A bare parent is never attached: it gets its identity from the run open.
  const creates = f.herdr.calls.filter(a => a[0] === 'workspace' && a[1] === 'create');
  assert.deepEqual(creates.map(a => a[a.indexOf('--cwd') + 1]), [l.root]);
  const parent = f.herdr.workspaces.find(w => w.workspace_id === run.chats[0].repoWorkspaceId);
  assert.deepEqual(parent.worktree, { checkout_path: l.root, repo_key: l.common, is_linked_worktree: false });
  const opened = f.herdr.calls.filter(a => a[0] === 'worktree' && a[1] === 'open');
  assert.deepEqual(opened.map(a => [a[a.indexOf('--workspace') + 1], a[a.indexOf('--path') + 1]]),
    [...l.bare ? [] : [[parent.workspace_id, l.root]], [parent.workspace_id, run.root]]);
  assert.equal(run.layout.repoCreateIntent, null); assert.equal(run.layout.repoWorkspaceId, parent.workspace_id);
  // Chat start folder: the area pane starts the agent in the run worktree.
  const pane = f.herdr.paneOf(run.chats[0]);
  assert.equal(pane.cwd, run.root); assert.equal(pane.commands.length, 1); assert.match(pane.commands[0], / codex /);
  assert.equal(f.herdr.panes.filter(p => p.agent).length, 1);
  // agy and Gemini chats read the run folder and the folder that really holds the run worktrees.
  assert.deepEqual(agentDirs(run), [join(l.common, 'pdd/runs'), l.folder]);
  const gemini = chatCommand({ agent: 'gemini', cwd: run.root, commonDir: run.commonDir, sourceRoot: run.sourceRoot, addDirs: agentDirs(run) });
  assert.ok(gemini.includes(`--include-directories '${l.folder}'`), gemini);
  // Status from the invoking checkout and from the run worktree.
  for (const cwd of [l.cwd, run.root]) {
    const status = await runStatus({ ref: '17', cwd }, f.ports);
    assert.equal(status.exitCode, 0, status.message);
    assert.ok(status.message.includes(`Worktree: ${run.root} (branch ${run.branch})`), status.message);
  }
  // Cleanup: cancel closes only the run workspace; the worktree, branch and parent stay.
  const cancelled = await cancelRun({ ref: '17', cwd: l.cwd }, f.ports);
  assert.equal(cancelled.exitCode, 0, cancelled.message);
  assert.deepEqual(f.herdr.calls.filter(a => a[0] === 'workspace' && a[1] === 'close'), [['workspace', 'close', run.chats[0].workspaceId]]);
  assert.ok(f.herdr.workspaces.some(w => w.workspace_id === parent.workspace_id));
  assert.equal(l.record().state, 'cancelled'); assert.ok(existsSync(run.root));
  assert.equal(f.git(l.cwd, 'branch', '--list', run.branch).replace(/^[*+] /, ''), run.branch);
  // A new run for the same issue frees the old claim and allocates again in the same folder.
  const again = await l.start();
  assert.equal(again.exitCode, 0, again.message);
  const next = l.record();
  assert.notEqual(next.runId, run.runId); assert.notEqual(next.root, run.root); assert.equal(dirname(next.root), l.folder);
  assert.equal(f.herdr.calls.filter(a => a[0] === 'workspace' && a[1] === 'create').length, 1, 'the same Herdr parent is reused');
  // The documented manual cleanup works from the invoking checkout.
  f.git(l.cwd, 'worktree', 'remove', run.root); f.git(l.cwd, 'branch', '-D', run.branch);
  assert.equal(existsSync(run.root), false);
  assert.equal(basename(next.root).length, 36);
});

test('2698: a separate Git directory refuses before any run record, claim, worktree or Herdr call', async t => {
  const f = await fixture(t, { agent: 'codex' }), separate = join(f.base, 'separate.git'), main = join(f.base, 'main'), cwd = join(f.base, 'linked');
  f.git(f.base, 'clone', '-q', '--separate-git-dir', separate, f.source, main);
  f.git(main, 'remote', 'set-url', 'origin', ORIGIN);
  f.git(main, 'update-ref', 'refs/remotes/origin/main', f.git(main, 'rev-parse', 'main'));
  f.git(main, 'worktree', 'add', '-q', '-b', 'linked', cwd, 'main');
  const before = f.git(cwd, 'worktree', 'list', '--porcelain'), original = f.ports.execFile;
  let adds = 0;
  f.ports.execFile = (file, args, options) => {
    if (file === 'git' && args[0] === 'worktree' && args[1] === 'add') adds++;
    return original(file, args, options);
  };
  const out = await startRun({ name: 'small-change', issue: '17', agent: 'codex', base: 'main', cwd, packageRoot }, f.ports);
  assert.equal(out.exitCode, 1); assert.equal(adds, 0);
  assert.match(out.message, /Cannot establish repository or allocation metadata identity\. Git registers the primary checkout at .*separate\.git", but Git finds no work tree there/);
  assert.match(out.message, /Run the workflow from a normal clone or from a linked worktree of a bare repository\. No allocation record or issue claim was saved\. No new worktree is confirmed\./);
  for (const path of ['pdd/runs/17', 'pdd/worktree-assignments/runs', 'pdd/worktree-assignments/issues/17.json'])
    assert.equal(existsSync(join(separate, path)), false, path);
  assert.equal(f.git(cwd, 'worktree', 'list', '--porcelain'), before);
  assert.deepEqual(f.herdr.calls, []); assert.deepEqual(f.pushes, []); assert.deepEqual(f.prs, []);
});

for (const name of ['bare repository in P/.git with a linked worktree', 'bare P/.bare named by the P/.git file']) test(`2698: ${name}: a failed run open keeps the bare parent pending; open retries from the same parent`, async t => {
  const l = await layout(t, name), { f } = l, herdr = f.ports.herdr;
  let refuse = true;
  f.ports.herdr = async args => {
    if (refuse && args[0] === 'worktree' && args[1] === 'open') { refuse = false; f.herdr.calls.push(args); throw Object.assign(Error('reply lost'), { code: 'herdr_failed' }); }
    return herdr(args);
  };
  const started = await l.start();
  assert.equal(started.exitCode, 1); assert.match(started.message, /plan chat startup was not confirmed/);
  const saved = l.record().layout, parent = f.herdr.workspaces.find(w => w.workspace_id === saved.repoWorkspaceId);
  // The parent exists at R without Git identity; its create intent and saved root stay pending.
  assert.equal(parent.worktree, undefined); assert.equal(saved.repoCreateIntent.parentRoot, l.root);
  assert.equal(saved.repoRoot.cwd, l.root);
  const opened = await openRun({ ref: '17', cwd: l.cwd, packageRoot }, f.ports);
  assert.equal(opened.exitCode, 0, opened.message);
  const run = l.record();
  assert.equal(run.layout.repoWorkspaceId, parent.workspace_id); assert.equal(run.layout.repoCreateIntent, null);
  assert.deepEqual(parent.worktree, { checkout_path: l.root, repo_key: l.common, is_linked_worktree: false });
  assert.equal(f.herdr.calls.filter(a => a[0] === 'workspace' && a[1] === 'create').length, 1);
  assert.equal(f.herdr.calls.some(a => a[0] === 'worktree' && a[1] === 'open' && a[a.indexOf('--path') + 1] === l.root), false);
  assert.equal(f.herdr.paneOf(run.chats.at(-1)).cwd, run.root);
});

test('2698: a bare parent that opens the run with another repository identity refuses and keeps custody', async t => {
  const l = await layout(t, 'bare repository in P/.git with a linked worktree'), { f } = l, herdr = f.ports.herdr;
  f.ports.herdr = async args => {
    const reply = await herdr(args);
    if (args[0] === 'worktree' && args[1] === 'open') {
      const source = f.herdr.workspaces.find(w => w.workspace_id === args[args.indexOf('--workspace') + 1]);
      source.worktree = { ...source.worktree, repo_key: join(f.base, 'elsewhere.git') };
    }
    return reply;
  };
  const started = await l.start();
  assert.equal(started.exitCode, 1); assert.match(started.message, /herdr_layout_identity_changed/);
  const saved = l.record().layout;
  assert.equal(saved.repoCreateIntent.parentRoot, l.root); assert.equal(saved.repoRoot.cwd, l.root);
  assert.equal(f.herdr.panes.some(p => p.commands), false, 'no agent starts');
});
