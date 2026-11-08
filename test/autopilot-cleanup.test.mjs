import test from 'node:test';
import assert from 'node:assert/strict';
import { cleanupWorktrees } from '../src/autopilot-cleanup.mjs';
function fixture() {
  const run = { runId: 'run-12', runDir: '/source/.git/pdd/runs/12', root: '/run-12', sourceRoot: '/source', branch: 'pdd/run-12', state: 'completed', repo: 'owner/repo' };
  const f = { rows: [run], run, calls: [], dirty: '', ahead: '0', upstream: 'a'.repeat(40), prs: [{ state: 'MERGED', headRefName: run.branch }], released: 0 };
  f.ports = { listRuns: async () => structuredClone(f.rows), readRun: async () => structuredClone(f.run), lock: async () => () => { f.released++; },
    lookup: async () => ({ state: 'ready', assignment: { runId: run.runId, branch: run.branch, worktreePath: run.root } }),
    execute: async (command, args, options) => {
      f.calls.push({ command, args, cwd: options.cwd });
      if (command === 'gh') return { code: 0, stdout: JSON.stringify(f.prs) };
      const stdout = args[0] === 'symbolic-ref' ? f.run.branch : args[0] === 'status' ? f.dirty : args[0] === 'rev-list' ? f.ahead
        : args[0] === 'rev-parse' ? args.at(-1) === 'HEAD' ? 'a'.repeat(40) : f.upstream : '';
      return { code: 0, stdout };
    } };
  f.cleanup = () => cleanupWorktrees({ cwd: '/source', repository: 'owner/repo' }, f.ports);
  f.removals = () => f.calls.filter(row => row.args[0] === 'worktree');
  return f;
}
test('cleanup removes a clean fully pushed ended branch after closure without force or branch deletion', async () => {
  for (const state of ['completed', 'cancelled']) for (const prState of ['MERGED', 'CLOSED']) {
    const f = fixture(); f.run.state = state; f.prs[0].state = prState;
    assert.deepEqual(await f.cleanup(), { removed: ['run-12'], kept: [] });
    assert.deepEqual(f.removals(), [{ command: 'git', args: ['worktree', 'remove', '/run-12'], cwd: '/source' }]);
    assert.equal(f.released, 1); assert.equal(f.calls.some(row => ['push', 'fetch', 'branch'].includes(row.args[0])), false);
  }
});
test('cleanup retains active, dirty, untracked, unpushed, unknown, open and mismatched worktrees', async () => {
  const mutations = [f => { f.run.state = 'waiting'; }, f => { f.run.state = 'running'; }, f => { f.run.state = 'paused'; },
    f => { f.run.gate = { kind: 'ask-code' }; }, f => { f.dirty = ' M file'; }, f => { f.dirty = '?? new-file'; },
    f => { f.ahead = '1'; }, f => { f.upstream = 'b'.repeat(40); }, f => { f.prs = []; }, f => { f.prs[0].state = 'OPEN'; },
    f => { f.prs[0].headRefName = 'other'; }, f => { f.ports.lookup = async () => ({ state: 'recovery_required' }); },
    f => { f.ports.lookup = async () => ({ state: 'ready', assignment: { runId: 'other', branch: f.run.branch, worktreePath: f.run.root } }); },
    f => { f.run.root = '/source'; }, f => { f.rows.push({ ...f.run, runId: 'active', state: 'running' }); },
    f => { f.ports.readRun = async () => ({ ...f.run, state: 'running' }); }, f => { f.ports.execute = async () => { throw Error('unavailable'); }; }];
  for (const mutate of mutations) {
    const f = fixture(); mutate(f); assert.deepEqual((await f.cleanup()).removed, []); assert.equal(f.removals().length, 0);
  }
});
test('cleanup rechecks ended identity after network reads and keeps a replaced run', async () => {
  const f = fixture(); let reads = 0;
  f.ports.readRun = async () => ++reads <= 2 ? f.run : { ...f.run, runId: 'replacement' };
  assert.deepEqual(await f.cleanup(), { removed: [], kept: ['run-12'] }); assert.equal(f.removals().length, 0);
  assert.equal(f.released, 1);
});

test('native cleanup verifies allocator identity and preserves dirty/unpushed files before removing pushed work', async t => {
  const { mkdtempSync, mkdirSync, writeFileSync, readFileSync, existsSync, renameSync, rmSync } = await import('node:fs');
  const { tmpdir } = await import('node:os'); const { join } = await import('node:path');
  const { execFileSync } = await import('node:child_process'); const { randomUUID } = await import('node:crypto');
  const { allocateIssueWorktree } = await import('../src/workflow-worktree.mjs');
  const base = mkdtempSync(join(tmpdir(), 'pdd-health-cleanup-')); t.after(() => rmSync(base, { recursive: true, force: true }));
  const cwd = join(base, 'repo'); mkdirSync(cwd);
  const git = (at, ...args) => execFileSync('git', args, { cwd: at, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }).trim();
  git(cwd, 'init', '-q', '--initial-branch=main'); git(cwd, 'config', 'user.name', 'Synthetic test'); git(cwd, 'config', 'user.email', 'test@example.invalid');
  writeFileSync(join(cwd, 'source'), 'base\n'); git(cwd, 'add', '.'); git(cwd, 'commit', '-qm', 'base');
  git(cwd, 'remote', 'add', 'origin', 'https://github.com/owner/repo.git');
  const runId = randomUUID();
  const allocation = await allocateIssueWorktree({ cwd, repository: 'owner/repo', runId, issueNumber: 12, workflowName: 'feature', baseRef: 'main' });
  assert.equal(allocation.state, 'ready'); const a = allocation.assignment;
  const runDir = join(cwd, '.git', 'pdd', 'runs', '12'); mkdirSync(runDir, { recursive: true });
  const run = { v: 1, runId, number: 12, runDir, root: a.worktreePath, sourceRoot: cwd, repo: 'owner/repo', branch: a.branch, state: 'completed' };
  writeFileSync(join(runDir, 'status.json'), JSON.stringify(run));
  git(cwd, 'update-ref', 'refs/remotes/origin/' + a.branch, 'HEAD');
  git(a.worktreePath, 'branch', '--set-upstream-to=origin/' + a.branch);
  const ports = { execute: async (command, args, options) => {
    if (command === 'gh') return { code: 0, stdout: JSON.stringify([{ state: 'MERGED', headRefName: a.branch }]) };
    try { return { code: 0, stdout: git(options.cwd, ...args) }; } catch (error) { return { code: error.status || 1, stdout: '' }; }
  } };
  const cleanup = () => cleanupWorktrees({ cwd, repository: 'owner/repo' }, ports);
  writeFileSync(join(a.worktreePath, 'untracked'), 'keep\n');
  assert.deepEqual((await cleanup()).removed, []); assert.equal(readFileSync(join(a.worktreePath, 'untracked'), 'utf8'), 'keep\n');
  git(a.worktreePath, 'add', '.'); git(a.worktreePath, 'commit', '-qm', 'unpushed');
  assert.deepEqual((await cleanup()).removed, []); assert.equal(existsSync(a.worktreePath), true);
  // A controlled local remote-tracking read represents an already pushed branch; no push or fetch occurs.
  git(cwd, 'update-ref', 'refs/remotes/origin/' + a.branch, git(a.worktreePath, 'rev-parse', 'HEAD'));
  // Cancellation can be archived when another run for this issue starts.
  run.state = 'cancelled'; writeFileSync(join(runDir, 'status.json'), JSON.stringify(run));
  const archive = runDir + '-cancelled-' + runId.slice(0, 8); renameSync(runDir, archive); mkdirSync(runDir);
  const replacement = { ...run, runId: randomUUID(), root: cwd, state: 'waiting' };
  writeFileSync(join(runDir, 'status.json'), JSON.stringify(replacement));
  assert.deepEqual((await cleanup()).removed, [runId]); assert.equal(existsSync(a.worktreePath), false);
  assert.deepEqual(JSON.parse(readFileSync(join(archive, 'status.json'))), run);
  assert.deepEqual(JSON.parse(readFileSync(join(runDir, 'status.json'))), replacement);
  assert.equal(git(cwd, 'rev-parse', '--verify', 'refs/heads/' + a.branch).length, 40);
});
