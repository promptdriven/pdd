import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { autopilotGithubWorld } from './helpers/autopilot-github-world.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';
import { startRun, stepDone, approveRun } from '../src/workflow-runner.mjs';
import { checkDependencyStart } from '../src/issue-dependencies-intake.mjs';

const packet = w => w.prompts.map(text => {
  try { return JSON.parse(text.trim().split('\n').at(-1)); } catch { return null; }
}).filter(Boolean).at(-1);
const offered = w => (packet(w)?.issues ?? []).map(issue => issue.number);
const automaticBody = '<!-- pdd-workflow:run-1:code -->\nAutopilot `auto` mode';
function pull(w, number, labels = ['area:cli'], extra = {}) {
  return w.github.add(number, { pull_request: {}, body: automaticBody, labels, reviewDecision: 'REVIEW_REQUIRED', ...extra });
}
async function world(t, limit, issues = 2, options = {}) {
  const w = await autopilotGithubWorld({ issues, ...options });
  t.after(w.cleanup);
  const herdr = w.ports.herdr;
  w.ports.herdr = async args => {
    const text = args.at(-1), artifact = args[0] === 'agent' && args[1] === 'prompt' && /Artifact path: (.+)/.exec(text);
    const content = artifact ? readFileSync(JSON.parse(artifact[1]), 'utf8') : text;
    const reply = await herdr(args);
    if (args[0] === 'agent' && args[1] === 'prompt') w.prompts[w.prompts.length - 1] = content;
    return reply;
  };
  w.ports.reconcileDependencyIntake = async () => ({ eligible: [...w.github.issues.values()].filter(x => !x.pull_request).map(x => `https://github.com/${w.repository}/issues/${x.number}`), queued: [], skipped: [] });
  const path = join(w.cwd, 'pdd.json');
  const config = JSON.parse(readFileSync(path, 'utf8'));
  if (limit !== undefined) config.autopilot.maxOpenPrs = limit;
  writeFileSync(path, JSON.stringify(config));
  w.github.label(1, 'area:cli');
  if (issues > 1) w.github.label(2, 'area:docs');
  return w;
}

test('full owner area holds new work, permits another area, and status reports the count', async t => {
  const w = await world(t, 2);
  pull(w, 11); pull(w, 12);
  assert.equal((await w.invoke('start')).exitCode, 0);
  assert.deepEqual(offered(w), [2]);
  const before = w.github.calls.length;
  const status = await w.invoke('status');
  assert.equal(status.exitCode, 0);
  assert.match(status.message, /area:cli.*waiting:.*2.*PRs.*review/i);
  assert.equal(w.github.calls.length, before, 'launcher status uses saved queue observations');
  assert.equal(w.state().seen?.[1], undefined, 'held fresh work is not acknowledged');
});

for (const release of ['closed', 'merged', 'approved']) test(`${release} frees a review slot on unchanged fresh issue`, async t => {
  const w = await world(t, 1, 1);
  const pr = pull(w, 11);
  await w.invoke('start');
  assert.deepEqual(offered(w), []);
  w.prompts.length = 0;
  if (release === 'approved') pr.reviewDecision = 'APPROVED';
  else { w.github.close(11); pr.merged = release === 'merged'; }
  w.time += 60_000;
  await w.tick();
  assert.deepEqual(offered(w), [1]);
});

test('manual PRs and PRs that wait only for CI do not consume review capacity', async t => {
  const w = await world(t, 1, 1);
  pull(w, 11, ['area:cli'], { body: '<!-- pdd-workflow:manual:code -->' });
  pull(w, 12, ['area:cli'], { reviewDecision: 'APPROVED', ci: 'pending' });
  pull(w, 13, ['area:cli'], { reviewDecision: null, ci: 'pending' });
  await w.invoke('start');
  assert.deepEqual(offered(w), [1]);
  pull(w, 14, ['area:cli'], { reviewDecision: null, reviewRequests: 1 });
  w.prompts.length = 0; w.time += 60_000;
  await w.tick();
  assert.deepEqual(offered(w), []);
});

test('default limit is five and an unchanged issue is held when the queue fills', async t => {
  const w = await world(t, undefined, 1);
  for (let n = 11; n < 15; n++) pull(w, n);
  await w.invoke('start');
  assert.deepEqual(offered(w), [1]);
  pull(w, 15);
  w.prompts.length = 0; w.time += 60_000;
  await w.tick();
  assert.deepEqual(offered(w), []);
  assert.equal(w.state().reviewQueue?.['area:cli'], 5);
});

test('review read failure holds fresh work but retries it after recovery', async t => {
  const w = await world(t, 1, 1);
  pull(w, 11, ['area:cli'], { reviewDecision: 'APPROVED' });
  const gh = w.github.gh;
  let fail = true;
  w.github.gh = async (args, options) => args.includes('graphql') && fail
    ? { code: 1, stdout: '', stderr: 'synthetic unavailable' } : gh(args, options);
  await w.invoke('start');
  assert.deepEqual(offered(w), []);
  assert.equal(w.state().reviewQueueUnknown, true);
  fail = false; w.prompts.length = 0; w.time += 60_000;
  await w.tick();
  assert.deepEqual(offered(w), [1]);
  assert.equal(w.state().reviewQueueUnknown, undefined);
});

test('unlabeled PRs share one repository area and later PR pages count', async t => {
  const w = await world(t, 1, 1);
  w.github.unlabel(1, 'area:cli');
  for (let n = 11; n <= 110; n++) pull(w, n, [], { body: 'Manual PR' });
  pull(w, 111, []);
  await w.invoke('start');
  assert.deepEqual(offered(w), []);
  assert.equal(w.state().reviewQueue?.repository, 1);
});

function admission(counts) {
  const repository = 'acme/widgets', issue = `https://github.com/${repository}/issues/1`, revision = 'a'.repeat(64);
  const coordinator = { repository, coordinatorId: 'local', machine: 'machine', activation: 'start', claim: { commentId: 'c', labelEventId: 'e' } };
  const claim = { issue, active: true, owner: 'local', coordinatorId: 'local', machine: 'machine', ...coordinator.claim };
  const snapshot = { repository, complete: true, capturedAt: '2026-11-07T00:00:00Z',
    issues: [{ key: issue, nodeId: '1', title: 'Ready', revision, state: 'open', authority: 'trusted', assignees: [], conditions: [], execution: 'idle', holds: [] }],
    edges: [], inputs: [{ key: issue, revision }], impacts: [], reviews: [{ id: 'r', analysis: 'Independent', base: [], continuation: '', issue, inputs: [{ key: issue, revision }], candidates: [{ key: issue, revision }], outcome: 'complete', dependencies: [], questions: [], effects: 'none', authority: 'trusted', intact: true }] };
  return { args: { repository, issue, coordinator }, ports: {
    settings: { read: async () => ({ mode: 'auto', activation: 'start', maxOpenPrs: 2 }) },
    owners: { read: async () => ({ json: JSON.stringify({ localOwner: 'local', claims: [claim], runsKnown: true, runs: [] }) }) },
    snapshots: { read: async () => ({ snapshot }) },
    github: { issue: async () => ({ json: JSON.stringify({ labels: [{ name: 'area:cli' }] }) }) },
    reviewQueue: { read: async () => ({ json: JSON.stringify(counts) }) },
  } };
}

test('automatic admission rechecks the area limit despite a prior coordinator packet', async () => {
  const { args, ports } = admission({ 'area:cli': 2 });
  assert.equal((await checkDependencyStart(args, ports)).reason, 'pr-review-limit');
  ports.reviewQueue.read = async () => ({ json: JSON.stringify({ 'area:cli': 1 }) });
  assert.equal((await checkDependencyStart(args, ports)).allowed, true);
});

test('automatic admission refuses unknown review observations', async () => {
  const { args, ports } = admission({});
  ports.reviewQueue.read = async () => { throw Error('unavailable'); };
  assert.equal((await checkDependencyStart(args, ports)).allowed, false);
});

for (const limit of [0, -1, 1.5, '1', null]) test(`invalid configured limit ${JSON.stringify(limit)} uses five without a save`, async t => {
  const w = await world(t, limit, 1);
  const before = readFileSync(join(w.cwd, 'pdd.json'), 'utf8');
  for (let n = 11; n < 16; n++) pull(w, n);
  await w.invoke('start');
  assert.deepEqual(offered(w), []);
  assert.equal(w.state().reviewQueueLimit, 5);
  assert.equal(readFileSync(join(w.cwd, 'pdd.json'), 'utf8'), before);
});

test('an unlabeled automatic PR inherits all closing-issue areas', async t => {
  const w = await world(t, 1);
  pull(w, 11, [], { closingIssuesReferences: { totalCount: 1, nodes: [{ labels: { totalCount: 2, nodes: [{ name: 'AREA:CLI' }, { name: 'area:docs' }] } }] } });
  await w.invoke('start');
  assert.deepEqual(offered(w), []);
  assert.deepEqual(w.state().reviewQueue, { 'area:cli': 1, 'area:docs': 1 });
});

test('a truncated owner-area connection cannot admit fresh work', async t => {
  const w = await world(t, 1, 1);
  pull(w, 11, [], { closingIssuesReferences: { totalCount: 101, nodes: [] } });
  await w.invoke('start');
  assert.deepEqual(offered(w), []);
  assert.equal(w.state().reviewQueueUnknown, true);
});

test('full review backlog keeps claimed work and review delivery active', async t => {
  const w = await world(t, 1);
  const reviews = [];
  w.ports.pullRequest = async () => ({ state: 'open', head: { sha: 'synthetic-head' } });
  const gh = w.github.gh;
  w.github.gh = async (args, options) => args.some(arg => /^repos\/.*\/pulls\/11\/reviews\?/.test(arg))
    ? { code: 0, stdout: `HTTP/2.0 200 OK\r\n\r\n${JSON.stringify(reviews)}`, stderr: '' } : gh(args, options);
  await w.invoke('start');
  w.github.claim(1);
  pull(w, 11, ['area:cli'], { body: `${automaticBody}\nFixes #1` });
  reviews.push({ id: 71, user: { login: 'acme' }, author_association: 'OWNER', state: 'CHANGES_REQUESTED',
    body: 'Cover the boundary value.', submitted_at: new Date(w.time).toISOString(), commit_id: 'synthetic-head' });
  w.prompts.length = 0; w.time += 60_000;
  await w.tick();
  assert.ok(offered(w).includes(1));
  assert.ok(offered(w).includes(2));
  assert.equal(packet(w).issues.find(issue => issue.number === 1).claimed, true);
  assert.deepEqual(packet(w).issues.find(issue => issue.number === 1).pullRequests[0].reviews, [{
    id: 71, author: 'acme', submittedAt: reviews[0].submitted_at, state: 'CHANGES_REQUESTED',
    body: reviews[0].body, commit: 'synthetic-head',
  }]);
  const status = await w.invoke('status');
  assert.match(status.message, /area:cli.*waiting:.*1.*review/i);
});

test('bounded admission: each limit 1 through 5 holds exactly counts at or above it', async () => {
  for (let limit = 1; limit <= 5; limit++) for (let count = 0; count <= 6; count++) {
    const { args, ports } = admission({ 'area:cli': count, 'area:docs': 100 });
    ports.settings.read = async () => ({ mode: 'auto', activation: 'start', maxOpenPrs: limit });
    const result = await checkDependencyStart(args, ports);
    assert.equal(result.allowed, count < limit, `limit=${limit}, cli=${count}`);
    if (count >= limit) assert.equal(result.reason, 'pr-review-limit');
  }
});

test('machine-marked automatic code PRs count without prose mode or labels', async t => {
  const w = await world(t, 1, 1);
  pull(w, 11, ['area:cli'], { body: '<!-- pdd-workflow:run-1:code -->\n<!-- pdd:autopilot-pr -->' });
  await w.invoke('start');
  assert.deepEqual(offered(w), []);
});

test('native automatic admission reads the queue through the counted GitHub adapter', async t => {
  const w = await world(t, 2, 1);
  pull(w, 11); pull(w, 12);
  const { args, ports } = admission({});
  delete ports.reviewQueue;
  ports.execFile = w.commandPorts().execFile;
  ports.github.page = async () => ({ json: JSON.stringify({ items: [
    { number: 11, pull_request: {}, body: automaticBody, labels: [{ name: 'area:cli' }] },
    { number: 12, pull_request: {}, body: automaticBody, labels: [{ name: 'area:cli' }] },
  ], next: '' }) });
  const result = await checkDependencyStart(args, ports);
  assert.equal(result.allowed, false);
  assert.equal(result.reason, 'pr-review-limit');
  assert.ok(w.github.calls.some(call => call.endpoint === 'graphql'));
});

test('workflow publication marks automatic PRs independently of mode and draft prose', async t => {
  for (const automatic of [false, true]) {
    const f = await fixture(t, { name: 'quota-fixture' });
    const execFile = f.ports.execFile;
    f.ports.execFile = async (file, args, options) => {
      const result = await execFile(file, args, options);
      if (file === 'gh' && args[0] === 'pr' && args[1] === 'create') f.prs.at(-1).isDraft = args.includes('--draft');
      return result;
    };
    const skill = join(f.ports.env.HOME, '.agents', 'skills', 'pdd-quota-fixture');
    mkdirSync(skill, { recursive: true });
    writeFileSync(join(skill, 'SKILL.md'), '# Synthetic one-step fixture\n');
    writeFileSync(join(skill, 'workflow.json'), JSON.stringify({ version: 2, areas: [{ name: 'build', steps: ['change'], optional: [], gate: 'pr' }] }));
    const start = await startRun({ name: 'quota-fixture', issue: '17', agent: 'claude', cwd: f.source, packageRoot, draft: true }, f.ports);
    assert.equal(start.exitCode, 0, start.message);
    const run = f.record();
    if (automatic) {
      run.automaticOrigin = { repository: run.repo, coordinatorId: 'synthetic-owner', machine: 'synthetic-machine', claim: { commentId: '1', labelEventId: '2' } };
      f.ports.owners = { read: async () => ({ json: JSON.stringify({ localOwner: 'synthetic-owner', claims: [{
        issue: run.issue.url, active: true, owner: 'synthetic-owner', coordinatorId: 'synthetic-owner', machine: 'synthetic-machine', commentId: '1', labelEventId: '2',
      }] }) }) };
      writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
      writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'observe' } }));
    }
    writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n');
    f.git(run.root, 'commit', '-qam', 'Synthetic quota fixture change');
    const result = await stepDone({ step: 'change', summary: 'Value changed', cwd: run.root }, f.agentPorts());
    assert.equal(result.exitCode, 0, result.message);
    assert.equal(f.prs.length, 1);
    assert.equal(f.prs[0].body.includes('<!-- pdd:autopilot-pr -->'), automatic);
    assert.equal(f.prs[0].body.includes('<!-- pdd:autopilot-issue:17 -->'), automatic);
  }
});

async function publishStack(t) {
  const f = await fixture(t, { name: 'quota-stack' });
  const execFile = f.ports.execFile;
  f.ports.execFile = async (file, args, options) => {
    const result = await execFile(file, args, options);
    if (file === 'gh' && args[0] === 'api' && args[1] === 'repos/example/project/issues/17') {
      return { ...result, stdout: JSON.stringify({ ...JSON.parse(result.stdout), labels: [{ name: 'area:cli' }] }) };
    }
    return result;
  };
  const skill = join(f.ports.env.HOME, '.agents', 'skills', 'pdd-quota-stack');
  mkdirSync(skill, { recursive: true });
  writeFileSync(join(skill, 'SKILL.md'), '# Synthetic spec and code fixture\n');
  writeFileSync(join(skill, 'workflow.json'), JSON.stringify({ version: 2, areas: [
    { name: 'prompt-pr', steps: ['spec'], optional: [], gate: 'pr', then: 'ask-code' },
    { name: 'code', steps: ['build'], optional: [], gate: 'pr' },
  ] }));
  const start = await startRun({ name: 'quota-stack', issue: '17', agent: 'claude', cwd: f.source, packageRoot }, f.ports);
  assert.equal(start.exitCode, 0, start.message);
  const run = f.record();
  run.automaticOrigin = { repository: run.repo, coordinatorId: 'synthetic-owner', machine: 'synthetic-machine', claim: { commentId: '1', labelEventId: '2' } };
  f.ports.owners = { read: async () => ({ json: JSON.stringify({ localOwner: 'synthetic-owner', claims: [{
    issue: run.issue.url, active: true, owner: 'synthetic-owner', coordinatorId: 'synthetic-owner', machine: 'synthetic-machine', commentId: '1', labelEventId: '2',
  }] }) }) };
  writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'observe' } }));
  writeFileSync(join(run.root, 'spec.md'), 'Synthetic specification.\n');
  f.git(run.root, 'add', 'spec.md'); f.git(run.root, 'commit', '-qm', 'Synthetic spec');
  const spec = await stepDone({ step: 'spec', summary: 'Specification ready', cwd: run.root }, f.agentPorts());
  assert.equal(spec.exitCode, 0, spec.message);
  // This synthetic workflow has no prompt files. This terminal fake only takes the code-choice gate.
  const code = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(code.exitCode, 0, code.message);
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n');
  f.git(run.root, 'commit', '-qam', 'Synthetic code');
  const built = await stepDone({ step: 'build', summary: 'Value changed', cwd: run.root }, f.agentPorts());
  assert.equal(built.exitCode, 0, built.message);
  assert.equal(f.prs.length, 2);
  assert.equal(f.prs[0].baseRefName, 'main');
  assert.equal(f.prs[1].baseRefName, f.prs[0].headRefName);
  assert.match(f.prs[0].body, /^Part of #17$/m);
  assert.match(f.prs[1].body, /^Closes #17$/m);
  return f.prs;
}

for (const [index, kind] of ['spec', 'stacked-code'].entries()) test(`published ${kind} PR holds its source issue area without a closing link`, async t => {
  const prs = await publishStack(t);
  const w = await world(t, 1, 2, { repository: 'example/project' });
  w.github.add(17, { labels: ['AREA:CLI', 'area:docs'] });
  // GitHub supplies no closing link for "Part of", or for a non-default target branch.
  for (const pr of index === 0 ? [prs[0]] : prs) {
    pull(w, pr.number, [], { body: pr.body, closingIssuesReferences: { totalCount: 0, nodes: [] } });
  }
  w.ports.pullRequest = async () => ({ state: 'open', head: { sha: prs[index].headRefOid } });
  const gh = w.github.gh;
  w.github.gh = async (args, options) => args.some(arg => /\/pulls\/\d+\/reviews\?/.test(arg))
    ? { code: 0, stdout: 'HTTP/2.0 200 OK\r\n\r\n[]', stderr: '' } : gh(args, options);
  await w.invoke('start');
  assert.equal(offered(w).includes(1), false, 'fresh CLI work waits for its published source-area PR');
  assert.equal(offered(w).includes(2), false, 'each source area consumes one slot');
  const count = index === 0 ? 1 : 2;
  assert.deepEqual(w.state().reviewQueue, { 'area:cli': count, 'area:docs': count });
  // Current issue labels govern later reads, even if the PR has not changed.
  w.github.unlabel(17, 'AREA:CLI'); w.prompts.length = 0; w.time += 60_000;
  await w.tick();
  assert.ok(offered(w).includes(1));
  assert.deepEqual(w.state().reviewQueue, { 'area:docs': count });
});

test('source lookup includes closed issues, is shared by a stack, and preserves PR area overrides', async t => {
  const w = await world(t, 2);
  w.github.add(17, { state: 'closed', labels: ['area:cli'] });
  const body = '<!-- pdd:autopilot-pr -->\n<!-- pdd:autopilot-issue:17 -->';
  pull(w, 21, [], { body }); pull(w, 22, [], { body });
  pull(w, 23, ['area:docs'], { body });
  let sourceReads = 0;
  const gh = w.github.gh;
  w.github.gh = async (args, options) => {
    if (args.includes('graphql') && options?.input?.includes('sourceIssue: issue(')) sourceReads++;
    return gh(args, options);
  };
  await w.invoke('start');
  assert.deepEqual(offered(w), [2]);
  assert.deepEqual(w.state().reviewQueue, { 'area:cli': 2, 'area:docs': 1 });
  assert.equal(sourceReads, 1);
});

for (const failure of ['missing', 'graphql-error', 'truncated', 'invalid-marker', 'conflicting-markers']) test(`source association ${failure} holds fresh work until repaired`, async t => {
  const w = await world(t, 1, 1);
  w.github.add(17, { labels: ['area:cli'] });
  let faulty = true;
  const body = '<!-- pdd:autopilot-pr -->\n<!-- pdd:autopilot-issue:17 -->';
  const pr = pull(w, 21, [], { body: failure === 'invalid-marker' ? body.replace('issue:17', 'issue:0')
    : failure === 'conflicting-markers' ? `${body}\n<!-- pdd:autopilot-issue:18 -->` : body });
  const gh = w.github.gh;
  w.github.gh = async (args, options) => {
    if (faulty && args.includes('graphql') && options?.input?.includes('sourceIssue: issue(')) {
      const result = failure === 'missing' ? { data: { repository: { sourceIssue: null } } }
        : failure === 'graphql-error' ? { errors: [{ type: 'FORBIDDEN' }] }
        : { data: { repository: { sourceIssue: { number: 17, labels: { totalCount: 101, nodes: [] } } } } };
      return { code: 0, stdout: JSON.stringify(result), stderr: '' };
    }
    return gh(args, options);
  };
  await w.invoke('start');
  assert.deepEqual(offered(w), []);
  assert.equal(w.state().reviewQueueUnknown, true);
  faulty = false; pr.body = body; w.prompts.length = 0; w.time += 60_000;
  await w.tick();
  assert.equal(w.state().reviewQueueUnknown, undefined);
  assert.deepEqual(w.state().reviewQueue, { 'area:cli': 1 });
  assert.deepEqual(offered(w), []);
});
