import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import { existsSync, linkSync, mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, statSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { createDependencyReadPorts } from '../src/issue-dependencies-github.mjs';
import { checkDependencyStart } from '../src/issue-dependencies-intake.mjs';

test('completed registered turns yield capped capacity while retaining progress and claim', async () => {
const repo = 'owner/repo';
const runIssue = `https://github.com/${repo}/issues/51`;
const startIssue = `https://github.com/${repo}/issues/52`;
const coordinatorId = 'coordinator-a';
const machine = 'machine-a';
const commentId = 'claim-52';
const labelEventId = 'event-52';
const oldClaim = { repository: repo, coordinatorId: 'coordinator-old', machine: 'machine-old', labelEventId: 'event-51' };
const sessionId = randomUUID();
const revision = 'a'.repeat(64);
const sourceRunId = 'waiting-run-51';
const workspace = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-independent-capacity-')));
const cwd = join(workspace, 'repo');
const stateDir = join(workspace, 'state');

mkdirSync(cwd);
mkdirSync(stateDir);
execFileSync('git', ['init', '-q'], { cwd });
execFileSync('git', ['remote', 'add', 'origin', `https://github.com/${repo}.git`], { cwd });
const commonDir = realpathSync(join(cwd, '.git'));
const runDir = join(commonDir, 'pdd', 'runs', '51');
const assignmentRoot = join(commonDir, 'pdd', 'worktree-assignments');
const assignmentRuns = join(assignmentRoot, 'runs');
const assignmentIssues = join(assignmentRoot, 'issues');
mkdirSync(runDir, { recursive: true });
mkdirSync(assignmentRuns, { recursive: true });
mkdirSync(assignmentIssues, { recursive: true });

const autopilotStateDir = join(stateDir, 'autopilot');
mkdirSync(autopilotStateDir, { recursive: true });
const rootHash = createHash('sha256').update(cwd).digest('hex').slice(0, 20);
writeFileSync(join(autopilotStateDir, `${rootHash}.json`), JSON.stringify({
  repo,
  cwd,
  coordinatorId,
  enabled: true,
  activatedAt: 'activation-a',
  runs: 1,
}));

const assignmentPath = join(assignmentRuns, `${sourceRunId}.json`);
const issueAssignmentPath = join(assignmentIssues, '51.json');
const assignment = {
  runId: sourceRunId,
  repository: repo,
  commonDir,
  issueNumber: 51,
};
writeFileSync(assignmentPath, JSON.stringify(assignment));
linkSync(assignmentPath, issueAssignmentPath);
assert.equal(statSync(assignmentPath).nlink, 2, 'allocation index must be a valid current hard-link pair');

const chat = {
  area: 'code',
  agent: 'codex',
  paneId: 'worker-pane-51',
  state: 'running',
  startedAt: 1,
  session: { agent: 'codex', id: sessionId },
};
const execFile = async (file, args, options = {}) => {
  if (file === 'git') return { stdout: execFileSync(file, args, { cwd: options.cwd, encoding: 'utf8' }) };
  if (file === 'gh' && args[0] === 'repo') return { stdout: JSON.stringify({
    nameWithOwner: repo,
    defaultBranchRef: { name: 'main' },
    url: `https://github.com/${repo}`,
  }) };
  throw new Error(`Unexpected command in local replay: ${file} ${args.join(' ')}`);
};
const github = {
  issue: async ({ issue }) => ({ json: JSON.stringify({
    number: issue,
    labels: [{ name: 'pdd:working' }],
  }) }),
  page: async ({ kind }) => ({ json: JSON.stringify({
    items: kind === 'timeline' ? [{
      id: 'event-51',
      event: 'labeled',
      actor: { login: 'worker-51' },
      label: { name: 'pdd:working' },
    }] : kind === 'comments' ? [{
      id: 'comment-51',
      body: JSON.stringify(oldClaim),
      user: { login: 'worker-51' },
    }] : [],
    next: '',
  }) }),
};
const supplied = {
  execFile,
  github,
  authority: { read: async () => ({ authority: 'trusted' }) },
  herdr: async args => {
    assert.deepEqual(args, ['agent', 'get', chat.paneId]);
    return { result: { agent: {
      agent_status: 'done',
      agent_session: { kind: 'id', value: sessionId },
    } } };
  },
  now: () => 100_000,
  stateDir,
};

const graphSnapshot = {
  repository: repo,
  complete: true,
  capturedAt: '2026-01-01T00:00:00Z',
  issues: [{
    key: startIssue,
    nodeId: '52',
    title: 'Independent ready issue',
    revision,
    state: 'open',
    authority: 'trusted',
    assignees: [],
    conditions: [],
    execution: 'running',
    holds: ['Claimed'],
    executionClaim: { coordinatorId, commentId, labelEventId },
  }],
  edges: [],
  reviews: [{
    id: 'review-52',
    analysis: 'Independent issue',
    base: [],
    continuation: '',
    issue: startIssue,
    inputs: [{ key: startIssue, revision }],
    candidates: [{ key: startIssue, revision }],
    outcome: 'complete',
    dependencies: [],
    questions: [],
    effects: 'none',
    authority: 'trusted',
    intact: true,
  }],
  impacts: [],
  inputs: [{ key: startIssue, revision }],
};
const coordinator = {
  repository: repo,
  coordinatorId,
  machine,
  activation: 'activation-a',
  runs: 1,
  claim: { commentId, labelEventId },
};
const candidateClaim = {
  issue: startIssue,
  active: true,
  owner: coordinatorId,
  coordinatorId,
  machine,
  commentId,
  labelEventId,
};

try {
  for (const runState of ['waiting', 'stuck', 'question']) {
    writeFileSync(join(runDir, 'status.json'), JSON.stringify({
      v: 1,
      number: 51,
      repo,
      runId: sourceRunId,
      runDir,
      root: cwd,
      sourceRoot: cwd,
      commonDir,
      state: runState,
      area: 0,
      agent: 'codex',
      areas: [{ name: 'code', steps: [], optional: [] }],
      chats: [chat],
    }));

    const savedStatus = readFileSync(join(runDir, 'status.json'), 'utf8');
    const native = createDependencyReadPorts({ cwd }, supplied);
    const local = JSON.parse((await native.owners.read({ repository: repo, issues: [runIssue] })).json);
    assert.equal(local.runsKnown, true, 'a complete current allocation index must remain known');
    assert.deepEqual(local.claims, [{
      issue: runIssue,
      active: true,
      owner: oldClaim.coordinatorId,
      coordinatorId: oldClaim.coordinatorId,
      machine: oldClaim.machine,
      commentId: 'comment-51',
      labelEventId: 'event-51',
    }], 'native owner read must retain the old issue claim');
    assert.equal(local.runs.length, 1);
    assert.equal(local.runs[0].issue, runIssue);
    assert.equal(local.runs[0].runId, sourceRunId);
    assert.equal(local.runs[0].state, runState);
    assert.equal(local.runs[0].occupied, false);

    const startPorts = {
      ...supplied,
      settings: { read: async () => ({ mode: 'auto', activation: 'activation-a', runs: 1 }) },
      snapshots: { read: async () => ({ snapshot: structuredClone(graphSnapshot) }) },
      owners: { read: async () => {
        const current = JSON.parse((await native.owners.read({ repository: repo, issues: [runIssue] })).json);
        current.claims.push(candidateClaim);
        return { json: JSON.stringify(current) };
      } },
    };
    const capped = await checkDependencyStart({ cwd, repository: repo, issue: startIssue, coordinator }, startPorts);
    assert.deepEqual(capped, { allowed: true, reason: 'ok' });

    const uncapped = await checkDependencyStart({
      cwd,
      repository: repo,
      issue: startIssue,
      coordinator: { ...coordinator, runs: undefined },
    }, {
      ...startPorts,
      settings: { read: async () => ({ mode: 'auto', activation: 'activation-a' }) },
    });
    assert.deepEqual(uncapped, { allowed: true, reason: 'ok' });

    assert.equal(readFileSync(join(runDir, 'status.json'), 'utf8'), savedStatus, 'saved progress must remain unchanged');
    assert.equal(existsSync(issueAssignmentPath), true, 'waiting issue allocation must remain in place');
    assert.equal(readFileSync(issueAssignmentPath, 'utf8'), JSON.stringify(assignment));


  }

} finally {
  rmSync(workspace, { recursive: true, force: true });
}

});
