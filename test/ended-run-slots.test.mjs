import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { randomUUID } from 'node:crypto';
import { existsSync, linkSync, mkdirSync, mkdtempSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { createDependencyReadPorts } from '../src/issue-dependencies-github.mjs';
import { checkDependencyStart } from '../src/issue-dependencies-intake.mjs';

// A completed or cancelled run keeps its worktree-assignments/issues/N.json link as allocation
// evidence. That link must never hold a run slot or block a new start of the same issue.
// A link whose run has no ended record (a start in progress) still counts.

const repo = 'owner/repo';
const issueUrl = number => `https://github.com/${repo}/issues/${number}`;
const coordinator = { repository: repo, coordinatorId: 'coord-a', machine: 'machine-a', activation: 'activation-a', claim: { commentId: 'c-52', labelEventId: 'e-52' } };
const revision = 'a'.repeat(64);

function world(t) {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-ended-slots-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const cwd = join(root, 'repo');
  mkdirSync(cwd);
  execFileSync('git', ['init', '-q'], { cwd });
  execFileSync('git', ['remote', 'add', 'origin', `https://github.com/${repo}.git`], { cwd });
  const commonDir = realpathSync(join(cwd, '.git'));
  const runsDir = join(commonDir, 'pdd', 'runs');
  const assignmentRuns = join(commonDir, 'pdd', 'worktree-assignments', 'runs');
  const assignmentIssues = join(commonDir, 'pdd', 'worktree-assignments', 'issues');
  for (const dir of [runsDir, assignmentRuns, assignmentIssues]) mkdirSync(dir, { recursive: true });
  const execFile = async (file, args, options = {}) => {
    if (file === 'git') return { stdout: execFileSync(file, args, { cwd: options.cwd, encoding: 'utf8' }) };
    if (file === 'gh' && args[0] === 'repo') return { stdout: JSON.stringify({ nameWithOwner: repo, url: `https://github.com/${repo}`, defaultBranchRef: { name: 'main' } }) };
    throw Error(`Unexpected command: ${file} ${args.join(' ')}`);
  };
  const github = { issue: async () => { throw Error('Unexpected GitHub read'); }, page: async () => { throw Error('Unexpected GitHub read'); } };
  const supplied = { execFile, github, authority: { read: async () => ({ authority: 'trusted' }) }, now: () => 100_000 };
  const w = {
    cwd, commonDir,
    // The saved run record of an ended run (no chat custody is left).
    run(number, runId, state, fields = {}) {
      const runDir = join(runsDir, String(number));
      mkdirSync(runDir, { recursive: true });
      writeFileSync(join(runDir, 'status.json'), JSON.stringify({ v: 1, number, repo, runId, runDir, root: cwd, sourceRoot: cwd, commonDir,
        state, area: 0, agent: 'codex', areas: [{ name: 'code', steps: [], optional: [] }], chats: [], ...fields }));
    },
    // The allocator's hard-linked pair: runs/<runId>.json and issues/<N>.json.
    link(number, runId) {
      const runFile = join(assignmentRuns, `${runId}.json`);
      writeFileSync(runFile, JSON.stringify({ runId, repository: repo, commonDir, issueNumber: number }));
      linkSync(runFile, join(assignmentIssues, `${number}.json`));
    },
    issueLink: number => join(assignmentIssues, `${number}.json`),
    async local() {
      const native = createDependencyReadPorts({ cwd }, supplied);
      return JSON.parse((await native.owners.read({ repository: repo, issues: [] })).json);
    },
    async start(number, runs) {
      const key = issueUrl(number);
      const snapshot = { repository: repo, complete: true, capturedAt: '2026-01-01T00:00:00Z',
        issues: [{ key, nodeId: String(number), title: 'Ready issue', revision, state: 'open', authority: 'trusted', assignees: [], conditions: [],
          execution: 'running', holds: ['Claimed'], executionClaim: { coordinatorId: coordinator.coordinatorId, ...coordinator.claim } }],
        edges: [],
        reviews: [{ id: `review-${number}`, analysis: 'Independent issue', base: [], continuation: '', issue: key, inputs: [{ key, revision }],
          candidates: [{ key, revision }], outcome: 'complete', dependencies: [], questions: [], effects: 'none', authority: 'trusted', intact: true }],
        impacts: [], inputs: [{ key, revision }] };
      const claim = { issue: key, active: true, owner: coordinator.coordinatorId, coordinatorId: coordinator.coordinatorId, machine: coordinator.machine, ...coordinator.claim };
      return checkDependencyStart({ cwd, repository: repo, issue: key, coordinator: { ...coordinator, runs } }, {
        ...supplied,
        settings: { read: async () => ({ mode: 'auto', activation: coordinator.activation, runs }) },
        snapshots: { read: async () => ({ snapshot: structuredClone(snapshot) }) },
        owners: { read: async () => {
          const current = await w.local();
          return { json: JSON.stringify({ ...current, localOwner: coordinator.coordinatorId, claims: [claim] }) };
        } },
      });
    },
  };
  return w;
}

test('ended runs with leftover issue links take no run slot and keep their links', async t => {
  const w = world(t);
  w.run(52, 'run-52-completed', 'completed'); w.link(52, 'run-52-completed');
  w.run(53, 'run-53-cancelled', 'cancelled'); w.link(53, 'run-53-cancelled');
  const local = await w.local();
  assert.equal(local.runsKnown, true);
  assert.deepEqual(local.runs, []);
  // The same issue starts again under a one-run cap; its own stale link does not block it.
  assert.deepEqual(await w.start(52, 1), { allowed: true, reason: 'ok' });
  assert.deepEqual(await w.start(53, 1), { allowed: true, reason: 'ok' });
  // Admission is a read: the allocation evidence stays for worktree cleanup.
  assert.equal(existsSync(w.issueLink(52)), true);
  assert.equal(existsSync(w.issueLink(53)), true);
});

test('a link for a run with no ended record still counts as a starting run', async t => {
  const w = world(t);
  w.run(52, 'run-52-completed', 'completed'); w.link(52, 'run-52-completed');
  w.link(54, 'run-54-starting');
  const local = await w.local();
  assert.equal(local.runsKnown, true);
  assert.deepEqual(local.runs, [{ issue: issueUrl(54), runId: 'run-54-starting', state: 'starting' }]);
  assert.deepEqual(await w.start(52, 1), { allowed: false, reason: 'runs' });
  assert.deepEqual(await w.start(52, 2), { allowed: true, reason: 'ok' });
});

test('a new run of the same issue with a different runId still blocks that issue', async t => {
  const w = world(t);
  // A restart freed the old run's link and linked the new run, whose record is not saved yet.
  w.run(52, 'run-52-cancelled', 'cancelled'); w.link(52, 'run-52-new');
  const local = await w.local();
  assert.deepEqual(local.runs, [{ issue: issueUrl(52), runId: 'run-52-new', state: 'starting' }]);
  assert.deepEqual(await w.start(52, 2), { allowed: false, reason: 'dependency' });
});

test('the kept link of a completed run takes no slot and still lets cleanup find its worktree', async t => {
  const { allocateIssueWorktree } = await import('../src/workflow-worktree.mjs');
  const { cleanupWorktrees } = await import('../src/autopilot-cleanup.mjs');
  const w = world(t), git = (at, ...args) => execFileSync('git', args, { cwd: at, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }).trim();
  git(w.cwd, 'config', 'user.name', 'Synthetic test'); git(w.cwd, 'config', 'user.email', 'test@example.invalid');
  writeFileSync(join(w.cwd, 'source'), 'base\n'); git(w.cwd, 'add', '.'); git(w.cwd, 'commit', '-qm', 'base');
  const runId = randomUUID();
  const allocation = await allocateIssueWorktree({ cwd: w.cwd, repository: repo, runId, issueNumber: 52, workflowName: 'bug', baseRef: 'HEAD' });
  assert.equal(allocation.state, 'ready', allocation.message);
  const a = allocation.assignment;
  w.run(52, runId, 'completed', { root: a.worktreePath, branch: a.branch });
  assert.deepEqual((await w.local()).runs, []);
  assert.deepEqual(await w.start(52, 1), { allowed: true, reason: 'ok' });
  assert.equal(existsSync(w.issueLink(52)), true);
  // The pushed branch of a merged PR: cleanup needs the kept link to prove the allocation.
  git(w.cwd, 'update-ref', `refs/remotes/origin/${a.branch}`, 'HEAD');
  git(a.worktreePath, 'branch', `--set-upstream-to=origin/${a.branch}`);
  const execute = async (command, args, options) => {
    if (command === 'gh') return { code: 0, stdout: JSON.stringify([{ state: 'MERGED', headRefName: a.branch }]) };
    try { return { code: 0, stdout: git(options.cwd, ...args) }; } catch (error) { return { code: error.status || 1, stdout: '' }; }
  };
  assert.deepEqual(await cleanupWorktrees({ cwd: w.cwd, repository: repo }, { execute }), { removed: [runId], kept: [] });
  assert.equal(existsSync(a.worktreePath), false);
});
