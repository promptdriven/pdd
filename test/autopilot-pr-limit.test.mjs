import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { autopilotGithubWorld } from './helpers/autopilot-github-world.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';
import { startRun, stepDone } from '../src/workflow-runner.mjs';
import { checkDependencyStart } from '../src/issue-dependencies-intake.mjs';

const packet = w => w.prompts.map(text => {
  try { return JSON.parse(text.trim().split('\n').at(-1)); } catch { return null; }
}).filter(Boolean).at(-1);
const offered = w => (packet(w)?.issues ?? []).map(issue => issue.number);
const automaticBody = '<!-- pdd-workflow:run-1:code -->\nAutopilot `auto` mode';
function pull(w, number, labels = ['area:cli'], extra = {}) {
  return w.github.add(number, { pull_request: {}, body: automaticBody, labels, reviewDecision: 'REVIEW_REQUIRED', ...extra });
}
async function world(t, limit, issues = 2) {
  const w = await autopilotGithubWorld({ issues });
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
  await w.invoke('start');
  w.github.claim(1);
  pull(w, 11);
  w.prompts.length = 0; w.time += 60_000;
  await w.tick();
  assert.ok(offered(w).includes(1));
  assert.ok(offered(w).includes(2));
  assert.equal(packet(w).issues.find(issue => issue.number === 1).claimed, true);
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
  }
});
