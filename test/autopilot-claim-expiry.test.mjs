import test from 'node:test';
import assert from 'node:assert/strict';
import { execFile as callbackExec, execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdirSync, mkdtempSync, readFileSync, readdirSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { promisify } from 'node:util';
import { readDependencySnapshot, createDependencyReadPorts, refreshClaimHeartbeat, withoutClaimHeartbeat } from '../src/issue-dependencies-github.mjs';
import { projectIssueGraph } from '../src/issue-dependencies.mjs';
import { checkDependencyStart } from '../src/issue-dependencies-intake.mjs';
import { runIssueGraph } from '../src/issue-dependency-graph.mjs';
import { startRun, stepDone, approveRun } from '../src/workflow-runner.mjs';
import { writeRun } from '../src/workflow-runs.mjs';
import { fixture as runnerFixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

// Issue #3032: claims carry a heartbeat, expire, and a lost claim stops work.
const repo = 'owner/repo', hour = 60 * 60 * 1000, minute = 60 * 1000;
const NOW = Date.parse('2026-11-06T12:00:00.000Z');
const at = ms => new Date(ms).toISOString();
const key = n => `https://github.com/${repo}/issues/${n}`;
const reply = value => ({ json: JSON.stringify(value) });
const sha = value => createHash('sha256').update(value).digest('hex');
const record = fields => ({ repository: repo, coordinatorId: 'coordinator-a', machine: 'machine-a', labelEventId: '701', ...fields });
const claimBody = (fields = {}, prose = 'Autopilot claim on machine-a.') => `${prose}\n\n\`\`\`json\n${JSON.stringify(record(fields))}\n\`\`\``;

function checkout(t) {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-claim-expiry-')));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const cwd = join(dir, 'repo'), stateRoot = join(dir, 'state');
  mkdirSync(cwd); mkdirSync(stateRoot);
  execFileSync('git', ['init', '-q'], { cwd });
  execFileSync('git', ['remote', 'add', 'origin', `https://github.com/${repo}.git`], { cwd });
  const execFile = async (file, args, options = {}) => {
    if (file === 'git') return { stdout: execFileSync(file, args, { cwd: options.cwd, encoding: 'utf8' }) };
    if (file === 'gh' && args[0] === 'repo') return { stdout: JSON.stringify({ nameWithOwner: repo, defaultBranchRef: { name: 'main' }, url: `https://github.com/${repo}` }) };
    throw Error(`unexpected process ${file} ${args.join(' ')}`);
  };
  const localOwner = coordinatorId => writeFileSync(join(stateRoot, `${sha(realpathSync(cwd)).slice(0, 20)}.json`), JSON.stringify({ repo, cwd: realpathSync(cwd), coordinatorId, enabled: true, activatedAt: 'activation' }));
  return { cwd, stateRoot, execFile, localOwner };
}

const issueRow = (n, extra = {}) => ({ id: 1000 + n, number: n, html_url: key(n), title: `Issue ${n}`, body: `Fix case ${n}.`, state: 'open',
  user: { login: 'owner' }, labels: [{ name: 'pdd:working' }], assignees: [], created_at: at(NOW - 72 * hour), updated_at: at(NOW - 30 * hour), ...extra });
function reviewComment(issue) {
  const row = { key: issue.html_url, revision: sha(JSON.stringify({ title: issue.title, body: issue.body })) };
  const review = { analysis: 'Reviewed for the claim expiry fixture.', base: [], continuation: '', issue: issue.html_url, inputs: [row], candidates: [row],
    outcome: 'complete', dependencies: [], questions: [], effects: 'none' };
  return { id: 501, user: { login: 'owner' }, created_at: at(NOW - 60 * hour), updated_at: at(NOW - 60 * hour),
    body: `Dependencies checked: none.\n\n<!-- pdd-dependency-review:v1 -->\n\`\`\`json\n${JSON.stringify({ schema_version: 'pdd.dependency-review.v1', review })}\n\`\`\`` };
}
const labeled = (id, created_at, event = 'labeled', name = 'pdd:working') => ({ id, event, label: { name }, actor: { login: 'owner' }, created_at });

function readPorts(world, { issue, timeline, comments, review = true }) {
  return {
    execFile: world.execFile, autopilotStateRoot: world.stateRoot,
    github: {
      issue: async ({ issue: n }) => reply(n === issue.number ? issue : { error: 'not_found', status: 404 }),
      page: async ({ kind, issue: n }) => reply({ items: kind === 'issues' ? [issue] : n !== issue.number ? [] : kind === 'comments' ? [...(review ? [reviewComment(issue)] : []), ...comments] : kind === 'timeline' ? timeline : [], next: '' }),
    },
    authority: { read: async () => ({ authority: 'trusted' }) },
    context: { read: async () => reply({ inputs: [], conditions: [], execution: [], nativeExecution: true }) },
    clock: { now: async () => ({ iso: at(world.now ?? NOW) }) },
  };
}
async function observe(world, facts) {
  const ports = readPorts(world, facts);
  const { snapshot } = await readDependencySnapshot({ cwd: world.cwd, repository: repo }, ports);
  const node = projectIssueGraph({ snapshot }).nodes.find(row => row.key === facts.issue.html_url);
  const owners = JSON.parse((await createDependencyReadPorts({ cwd: world.cwd }, ports).owners.read({ repository: repo, issues: [facts.issue.html_url] })).json);
  return { snapshot, node, claim: owners.claims[0], ports };
}

const expiredReason = time => `Expired claim, last seen ${at(time)}`;
// As on GitHub, a heartbeat edit sets the comment's updated_at to the time it writes.
const cases = [
  { name: 'a heartbeat 1 minute short of 4 hours keeps the claim live', lastSeen: NOW - 4 * hour + minute, expired: false },
  { name: 'a heartbeat 4 hours old expires the claim even with recent issue activity', lastSeen: NOW - 4 * hour, activity: NOW - 10 * minute, expired: true, seen: NOW - 4 * hour },
  { name: 'a new claim record with "lastSeen": "" is live 1 minute short of 4 hours after creation', marker: true, created: NOW - 4 * hour + minute, expired: false },
  { name: 'a new claim record with "lastSeen": "" expires 4 hours after creation even with recent issue activity', marker: true, created: NOW - 4 * hour, activity: NOW - 10 * minute, expired: true, seen: NOW - 4 * hour },
  // A claim record without lastSeen, as older pdd writes it, keeps the 24-hour rule.
  { name: 'a legacy claim with issue activity 23 hours ago stays live', activity: NOW - 23 * hour, expired: false },
  { name: 'a legacy claim with no issue activity for 24 hours expires', activity: NOW - 24 * hour, expired: true, seen: NOW - 24 * hour },
  { name: 'a prose claim with issue activity 23 hours ago stays live', prose: true, activity: NOW - 23 * hour, expired: false },
  { name: 'a prose claim with no issue activity for 24 hours expires', prose: true, activity: NOW - 24 * hour, expired: true, seen: NOW - 24 * hour },
  { name: 'a bare label with no claim comment expires after 24 hours without activity', bare: true, activity: NOW - 25 * hour, expired: true, seen: NOW - 25 * hour },
  { name: 'a claim with no readable time never expires', unknownTimes: true, expired: false },
];
for (const c of cases) test(`claim expiry: ${c.name}`, async t => {
  const world = checkout(t), activity = c.activity ?? Math.max(c.lastSeen ?? -Infinity, c.created ?? -Infinity, NOW - 30 * hour);
  const issue = issueRow(7, { updated_at: c.unknownTimes ? undefined : at(activity) });
  const claimAt = c.unknownTimes ? undefined : at(c.created ?? Math.min(activity, NOW - 26 * hour)), editAt = c.lastSeen === undefined ? claimAt : at(c.lastSeen);
  const comments = c.bare ? [] : [{ id: 901, user: { login: 'owner' }, created_at: claimAt, updated_at: editAt,
    body: c.prose ? 'Autopilot claim on machine-a.' : claimBody(c.lastSeen !== undefined ? { lastSeen: at(c.lastSeen) } : c.marker ? { lastSeen: '' } : {}) }];
  const timeline = [labeled(701, claimAt)];
  // A dependency review needs readable comment times, so the unknown-time case has none.
  const { node, claim, snapshot } = await observe(world, { issue, comments, timeline, review: !c.unknownTimes });
  assert.equal(claim.active, !c.expired);
  if (c.expired) {
    assert.equal(claim.expired, true);
    assert.equal(claim.lastSeen, at(c.seen));
    assert.ok(node.reasons.includes(expiredReason(c.seen)), node.reasons.join('; '));
    assert.ok(!node.reasons.includes('Claimed'));
    assert.equal(node.executionState, 'idle');
    assert.equal(node.eligible, true, 'an expired claim no longer holds the issue');
  } else {
    assert.ok(node.reasons.includes('Claimed'), node.reasons.join('; '));
    assert.ok(!node.reasons.some(reason => reason.startsWith('Expired claim')));
    assert.equal(node.eligible, false, 'a live claim stays skipped');
  }
  assert.equal(snapshot.complete, true, snapshot.warnings.join('; '));
});

test('pdd graph shows an expired claim with its last seen time and no hold', async t => {
  const world = checkout(t), lastSeen = NOW - 5 * hour, issue = issueRow(7, { updated_at: at(NOW - 5 * minute) });
  const comments = [{ id: 901, user: { login: 'owner' }, created_at: at(NOW - 30 * hour), updated_at: at(lastSeen), body: claimBody({ lastSeen: at(lastSeen) }) }];
  const ports = readPorts(world, { issue, comments, timeline: [labeled(701, at(NOW - 30 * hour))] });
  let saved = '';
  const view = await runIssueGraph({ cwd: world.cwd, repository: repo }, {
    snapshots: { read: args => readDependencySnapshot(args, ports) },
    cache: { read: async () => ({ json: saved }), write: async ({ json }) => { saved = json; return { ok: true }; } },
    refresh: { schedule: async () => ({ ok: true }) },
  });
  assert.equal(view.exitCode, 0, view.message);
  const lines = view.message.split('\n'), row = lines.findIndex(text => text.startsWith(`${key(7)} `));
  assert.match(lines[row], /\(no recorded open blocker\)/);
  assert.ok(lines.includes(`  ${expiredReason(lastSeen)}`), view.message);
  assert.ok(!lines.includes('  Claimed'));
});

test('claim expiry: a takeover starts a new claim era; the new owner may start and the old owner may not', async t => {
  const world = checkout(t), issue = issueRow(7, { updated_at: at(NOW - 5 * minute) });
  const oldClaim = { id: 901, user: { login: 'owner' }, created_at: at(NOW - 30 * hour), updated_at: at(NOW - 6 * hour), body: claimBody({ lastSeen: at(NOW - 6 * hour) }) };
  const before = await observe(world, { issue, comments: [oldClaim], timeline: [labeled(701, at(NOW - 30 * hour))] });
  assert.equal(before.claim.expired, true);
  const settings = { read: async () => ({ mode: 'auto', activation: 'activation' }) };
  const coordinatorA = { repository: repo, coordinatorId: 'coordinator-a', machine: 'machine-a', activation: 'activation', claim: { commentId: '901', labelEventId: '701' } };
  world.localOwner('coordinator-a');
  assert.deepEqual(await checkDependencyStart({ cwd: world.cwd, repository: repo, issue: issue.html_url, coordinator: coordinatorA }, { ...before.ports, settings }),
    { allowed: false, reason: 'owner' }, 'an expired claim does not admit its old owner');

  const takeover = { id: 902, user: { login: 'owner' }, created_at: at(NOW - 4 * minute), updated_at: at(NOW - 4 * minute),
    body: claimBody({ coordinatorId: 'coordinator-b', machine: 'machine-b', labelEventId: '703', lastSeen: at(NOW - 4 * minute) },
      `Took over an expired claim: coordinator-a on machine-a was last seen ${at(NOW - 6 * hour)}. Continuing from the saved branch and open PR.`) };
  const timeline = [labeled(701, at(NOW - 30 * hour)), labeled(702, at(NOW - 5 * minute), 'unlabeled'), labeled(703, at(NOW - 5 * minute))];
  const after = await observe(world, { issue, comments: [oldClaim, takeover], timeline });
  assert.deepEqual([after.claim.coordinatorId, after.claim.machine, after.claim.commentId, after.claim.labelEventId, after.claim.active], ['coordinator-b', 'machine-b', '902', '703', true]);
  assert.ok(after.node.reasons.includes('Claimed'));
  assert.equal(after.node.eligible, false, 'the new live claim is skipped by others');
  assert.deepEqual(await checkDependencyStart({ cwd: world.cwd, repository: repo, issue: issue.html_url, coordinator: coordinatorA }, { ...after.ports, settings }),
    { allowed: false, reason: 'owner' }, 'the old owner lost the claim');
  world.localOwner('coordinator-b');
  const coordinatorB = { ...coordinatorA, coordinatorId: 'coordinator-b', machine: 'machine-b', claim: { commentId: '902', labelEventId: '703' } };
  assert.deepEqual(await checkDependencyStart({ cwd: world.cwd, repository: repo, issue: issue.html_url, coordinator: coordinatorB }, { ...after.ports, settings }),
    { allowed: true, reason: 'ok' });
});

// The first lastSeen may come from a wrong clock (here a local time written with Z,
// 8 hours behind). GitHub's own comment times keep a fresh claim live.
test('claim expiry: a fresh claim comment with a stale lastSeen is live, and its owner may start', async t => {
  const world = checkout(t), created = NOW - 2 * minute, issue = issueRow(7, { updated_at: at(created) });
  const comments = [{ id: 901, user: { login: 'owner' }, created_at: at(created), updated_at: at(created), body: claimBody({ lastSeen: at(NOW - 8 * hour) }) }];
  const observed = await observe(world, { issue, comments, timeline: [labeled(701, at(NOW - 3 * minute))] });
  assert.equal(observed.claim.active, true);
  assert.equal(observed.claim.expired, undefined);
  assert.equal(observed.claim.lastSeen, at(created), 'the claim comment creation time is the last-seen time');
  assert.ok(observed.node.reasons.includes('Claimed'), observed.node.reasons.join('; '));
  world.localOwner('coordinator-a');
  const coordinator = { repository: repo, coordinatorId: 'coordinator-a', machine: 'machine-a', activation: 'activation', claim: { commentId: '901', labelEventId: '701' } };
  assert.deepEqual(await checkDependencyStart({ cwd: world.cwd, repository: repo, issue: issue.html_url, coordinator },
    { ...observed.ports, settings: { read: async () => ({ mode: 'auto', activation: 'activation' }) } }), { allowed: true, reason: 'ok' });
});

test('claim expiry: a lastSeen nested in another object is not read as the heartbeat', async t => {
  const world = checkout(t), claimAt = at(NOW - 26 * hour), issue = issueRow(7, { updated_at: claimAt });
  const comments = [{ id: 901, user: { login: 'owner' }, created_at: claimAt, updated_at: claimAt, body: claimBody({ previous: { lastSeen: at(NOW - minute) } }) }];
  const { claim } = await observe(world, { issue, comments, timeline: [labeled(701, claimAt)] });
  assert.equal(claim.expired, true, 'with no top-level lastSeen it is a legacy claim with no activity for 24 hours');
  assert.equal(claim.lastSeen, claimAt);
});

// Claims written by older pdd have no lastSeen: issue activity keeps them live for 24 hours.
test('claim expiry: an older claim record 5 hours old with a worker comment 10 minutes ago is live', async t => {
  const world = checkout(t), claimAt = at(NOW - 5 * hour), issue = issueRow(7, { updated_at: at(NOW - 10 * minute) });
  const comments = [{ id: 901, user: { login: 'owner' }, created_at: claimAt, updated_at: claimAt, body: claimBody() },
    { id: 902, user: { login: 'owner' }, created_at: at(NOW - 10 * minute), updated_at: at(NOW - 10 * minute), body: 'Progress: tests pass locally.' }];
  const { claim, node } = await observe(world, { issue, comments, timeline: [labeled(701, claimAt)] });
  assert.equal(claim.active, true);
  assert.equal(claim.expired, undefined);
  assert.equal(node.eligible, false, 'a live claim stays skipped');
});

test('claim expiry: an older claim record 23 hours old with activity 1 hour ago is live', async t => {
  const world = checkout(t), claimAt = at(NOW - 23 * hour), issue = issueRow(7, { updated_at: at(NOW - hour) });
  const comments = [{ id: 901, user: { login: 'owner' }, created_at: claimAt, updated_at: claimAt, body: claimBody() },
    { id: 902, user: { login: 'owner' }, created_at: at(NOW - hour), updated_at: at(NOW - hour), body: 'Waiting for review on the PR.' }];
  const { claim } = await observe(world, { issue, comments, timeline: [labeled(701, claimAt)] });
  assert.equal(claim.active, true);
  assert.equal(claim.expired, undefined);
});

// A recorded lastSeen never extends a claim: only the claim comment's GitHub time counts.
test('claim expiry: a lastSeen in the future does not keep a dead claim live', async t => {
  const world = checkout(t), lastEdit = NOW - 5 * hour, issue = issueRow(7, { updated_at: at(lastEdit) });
  const comments = [{ id: 901, user: { login: 'owner' }, created_at: at(NOW - 30 * hour), updated_at: at(lastEdit), body: claimBody({ lastSeen: at(NOW + 3 * 24 * hour) }) }];
  const facts = { issue, comments, timeline: [labeled(701, at(NOW - 30 * hour))] };
  world.now = lastEdit + 4 * hour - minute;
  const live = await observe(world, facts);
  assert.equal(live.claim.active, true);
  assert.equal(live.claim.lastSeen, at(lastEdit));
  world.now = NOW;
  const { claim, node } = await observe(world, facts);
  assert.equal(claim.expired, true, 'expired 4 hours after the last GitHub edit');
  assert.equal(claim.lastSeen, at(lastEdit));
  assert.ok(node.reasons.includes(expiredReason(lastEdit)), node.reasons.join('; '));
  assert.equal(node.eligible, true);
});

test('heartbeat: a writer clock 1 day ahead does not keep a stopped machine\'s claim live', async t => {
  const world = checkout(t), edit = NOW - 5 * hour, claimAt = at(NOW - 30 * hour);
  const service = commentService([{ id: 901, user: { login: 'owner' }, created_at: claimAt, updated_at: claimAt, body: claimBody() }], { serverTime: () => edit });
  const result = await refreshClaimHeartbeat({ repository: repo, claim: ownClaim(), coordinatorId: 'coordinator-a', machine: 'machine-a', at: at(edit + 24 * hour) }, { execFile: service.execFile });
  assert.deepEqual(result, { state: 'refreshed', lastSeen: at(edit + 24 * hour) });
  const saved = service.comments.get('901');
  assert.equal(saved.updated_at, at(edit), 'GitHub keeps its own edit time');
  const facts = { issue: issueRow(7, { updated_at: at(edit) }), comments: [saved], timeline: [labeled(701, claimAt)] };
  world.now = edit + 4 * hour - minute;
  assert.equal((await observe(world, facts)).claim.active, true);
  world.now = NOW;
  const { claim } = await observe(world, facts);
  assert.equal(claim.expired, true, 'the machine stopped 5 hours ago; the fast clock does not hold the claim');
  assert.equal(claim.lastSeen, at(edit));
});

// GitHub sets a comment's updated_at to its own (server) time on each edit.
function commentService(initial, { serverTime = () => NOW, lostReply = false } = {}) {
  const comments = new Map(initial.map(row => [String(row.id), structuredClone(row)])), patches = [];
  const execFile = async (file, args, options = {}) => {
    assert.equal(file, 'gh'); assert.equal(args[0], 'api');
    const method = args[3], endpoint = args[4], id = /^repos\/owner\/repo\/issues\/comments\/([0-9]+)$/.exec(endpoint)?.[1];
    assert.ok(id, `unexpected endpoint ${endpoint}`);
    if (method === 'PATCH') {
      const { body } = JSON.parse(options.input); patches.push({ id, body }); Object.assign(comments.get(id), { body, updated_at: at(serverTime()) });
      if (lostReply) return { stdout: 'HTTP/2.0 502 Bad Gateway\r\n\r\n{}' };
    } else assert.equal(method, 'GET');
    return { stdout: `HTTP/2.0 200 OK\r\n\r\n${JSON.stringify(comments.get(id))}` };
  };
  return { comments, patches, execFile };
}
const recordOf = body => JSON.parse(/```json\n([\s\S]*?)\n```/.exec(body)[1]);
const ownClaim = (extra = {}) => ({ issue: key(7), active: true, owner: 'coordinator-a', coordinatorId: 'coordinator-a', machine: 'machine-a', commentId: '901', labelEventId: '701', ...extra });

test('heartbeat: the owner updates only lastSeen in its own claim comment', async () => {
  const service = commentService([{ id: 901, user: { login: 'owner' }, body: claimBody() }]);
  const ports = { execFile: service.execFile };
  const first = await refreshClaimHeartbeat({ repository: repo, claim: ownClaim(), coordinatorId: 'coordinator-a', machine: 'machine-a', at: at(NOW) }, ports);
  assert.deepEqual(first, { state: 'refreshed', lastSeen: at(NOW) });
  const second = await refreshClaimHeartbeat({ repository: repo, claim: ownClaim(), coordinatorId: 'coordinator-a', machine: 'machine-a', at: at(NOW + 30 * minute) }, ports);
  assert.equal(second.lastSeen, at(NOW + 30 * minute));
  assert.equal(service.patches.length, 2);
  const body = service.comments.get('901').body;
  assert.ok(body.startsWith('Autopilot claim on machine-a.\n\n```json\n'), 'the readable text stays');
  const saved = JSON.parse(/```json\n([\s\S]*?)\n```/.exec(body)[1]);
  assert.deepEqual(saved, { ...record({}), lastSeen: at(NOW + 30 * minute) });
});

test('heartbeat: the first heartbeat writes a time into the "lastSeen": "" marker', async () => {
  const service = commentService([{ id: 901, user: { login: 'owner' }, body: claimBody({ lastSeen: '' }) }]);
  const result = await refreshClaimHeartbeat({ repository: repo, claim: ownClaim(), coordinatorId: 'coordinator-a', machine: 'machine-a', at: at(NOW) }, { execFile: service.execFile });
  assert.deepEqual(result, { state: 'refreshed', lastSeen: at(NOW) });
  assert.deepEqual(recordOf(service.comments.get('901').body), { ...record({}), lastSeen: at(NOW) });
});

test('heartbeat: another owner, another claim era or an expired claim is never edited', async () => {
  for (const [claim, coordinatorId, comment] of [
    [ownClaim({ coordinatorId: 'coordinator-b', owner: 'coordinator-b' }), 'coordinator-a', claimBody()],
    [ownClaim(), 'coordinator-a', claimBody({ coordinatorId: 'coordinator-b' })],
    [ownClaim({ labelEventId: '703' }), 'coordinator-a', claimBody()],
    [ownClaim({ active: false, expired: true }), 'coordinator-a', claimBody()],
  ]) {
    const service = commentService([{ id: 901, user: { login: 'owner' }, body: comment }]);
    const result = await refreshClaimHeartbeat({ repository: repo, claim, coordinatorId, machine: 'machine-a', at: at(NOW) }, { execFile: service.execFile });
    assert.equal(result.state, 'skipped');
    assert.equal(service.patches.length, 0);
    assert.equal(service.comments.get('901').body, comment);
  }
});

test('heartbeat: only the top-level lastSeen changes, never one nested in another object', async () => {
  const nested = { previous: { coordinatorId: 'coordinator-old', lastSeen: at(NOW - 9 * hour) } };
  // The nested member comes first in the text, so the first "lastSeen" is the wrong one.
  const withTop = `Took over.\n\n\`\`\`json\n${JSON.stringify({ ...nested, ...record({}), lastSeen: at(NOW - hour) })}\n\`\`\``;
  for (const body of [withTop, claimBody(nested)]) {
    const service = commentService([{ id: 901, user: { login: 'owner' }, body }]);
    const result = await refreshClaimHeartbeat({ repository: repo, claim: ownClaim(), coordinatorId: 'coordinator-a', machine: 'machine-a', at: at(NOW) }, { execFile: service.execFile });
    assert.deepEqual(result, { state: 'refreshed', lastSeen: at(NOW) });
    assert.deepEqual(recordOf(service.comments.get('901').body), { ...nested, ...record({}), lastSeen: at(NOW) });
  }
  const heartbeatBody = withTop.replace(at(NOW - hour), at(NOW));
  assert.deepEqual(recordOf(withoutClaimHeartbeat(heartbeatBody)), { ...nested, ...record({}) }, 'only the top-level lastSeen is left out');
  assert.equal(withoutClaimHeartbeat(withTop), withoutClaimHeartbeat(heartbeatBody), 'a heartbeat alone does not change the view');
  assert.equal(withoutClaimHeartbeat(claimBody(nested)), claimBody(nested));
});

test('heartbeat: a record whose lastSeen cannot be changed alone is not edited', async () => {
  const body = claimBody({ lastSeen: { at: at(NOW - hour) } });
  const service = commentService([{ id: 901, user: { login: 'owner' }, body }]);
  await assert.rejects(refreshClaimHeartbeat({ repository: repo, claim: ownClaim(), coordinatorId: 'coordinator-a', machine: 'machine-a', at: at(NOW) }, { execFile: service.execFile }),
    /cannot take a heartbeat/);
  assert.equal(service.patches.length, 0);
  assert.equal(service.comments.get('901').body, body);
});

// A writer clock 2 hours behind GitHub and a lost PATCH reply: the edit is saved, the
// recorded lastSeen is old, and the readback fails. The server edit time still counts.
test('heartbeat: after a failed readback the claim stays live for 4 hours after its last GitHub edit', async t => {
  const world = checkout(t), edit = NOW - 3 * hour, claimAt = at(NOW - 30 * hour);
  const service = commentService([{ id: 901, user: { login: 'owner' }, created_at: claimAt, updated_at: at(NOW - 3.5 * hour), body: claimBody({ lastSeen: at(NOW - 3.5 * hour) }) }],
    { serverTime: () => edit, lostReply: true });
  await assert.rejects(refreshClaimHeartbeat({ repository: repo, claim: ownClaim(), coordinatorId: 'coordinator-a', machine: 'machine-a', at: at(edit - 2 * hour) }, { execFile: service.execFile }),
    /GitHub observation unavailable/);
  assert.equal(recordOf(service.comments.get('901').body).lastSeen, at(edit - 2 * hour), 'the saved lastSeen is 2 hours behind the edit');
  const facts = { issue: issueRow(7, { updated_at: at(edit) }), comments: [service.comments.get('901')], timeline: [labeled(701, claimAt)] };
  world.now = edit + 4 * hour - minute;
  const live = await observe(world, facts);
  assert.equal(live.claim.active, true);
  assert.equal(live.claim.lastSeen, at(edit));
  world.now = edit + 4 * hour;
  const expired = await observe(world, facts);
  assert.equal(expired.claim.expired, true);
  assert.equal(expired.claim.lastSeen, at(edit));
});

// The no-AI tick, with the dependency intake supplying the observed claims.
async function tickFixture(t, { mode = 'auto' } = {}) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-claim-tick-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const cwd = join(dir, 'repo'), home = join(dir, 'home');
  mkdirSync(cwd); mkdirSync(home);
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode, trust: [] } }));
  const f = { time: NOW, prompts: [], patches: [], warnings: [], issues: [], issueComments: {}, claimComments: new Map(), status: 200, claims: () => [], eligible: () => [] };
  f.ports = {
    stateRoot: join(home, 'state'), now: () => f.time, readRunProgress: async () => [], warn: text => f.warnings.push(text),
    selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex', env: {} }), pathDiagnostic: () => [],
    run: async (command, args, options = {}) => {
      if (command === 'git') return { code: 0, stdout: cwd + '\n', stderr: '' };
      if (command === 'gh' && args[0] === 'repo') return { code: 0, stdout: '{"nameWithOwner":"owner/repo","url":"https://github.com/owner/repo"}', stderr: '' };
      if (command === 'gh' && args[0] === 'auth') return { code: 0, stdout: '', stderr: '' };
      if (command === 'gh' && args[0] === 'api') {
        const id = /^repos\/owner\/repo\/issues\/comments\/([0-9]+)$/.exec(args[4] ?? '')?.[1];
        if (id && f.claimComments.has(id)) {
          // Real GitHub: an edit sets the comment's updated_at and the issue's updated_at to the edit time.
          if (args[3] === 'PATCH') {
            const { body } = JSON.parse(options.input); f.patches.push({ id, body }); Object.assign(f.claimComments.get(id), { body, updated_at: at(f.time) });
            for (const row of f.issues) if ((f.issueComments[row.number] ?? []).some(comment => String(comment.id) === id)) row.updated_at = at(f.time);
          }
          return { code: 0, stdout: `HTTP/2.0 200 OK\r\n\r\n${JSON.stringify(f.claimComments.get(id))}`, stderr: '' };
        }
        if (args.some(x => String(x).includes('/reviews?'))) return { code: 0, stdout: 'HTTP/2.0 200 OK\r\n\r\n[]', stderr: '' };
        if (args.some(x => String(x).includes('/permission'))) return { code: 0, stdout: 'HTTP/2.0 200 OK\r\n\r\n{"permission":"none"}', stderr: '' };
        return { code: 0, stdout: '{}', stderr: '' };
      }
      if (command === 'herdr') return { code: 0, stdout: '1.0', stderr: '' };
      throw Error(`unexpected process ${command} ${args}`);
    },
    timer: async () => true,
    queryIssues: async () => ({ status: f.status, etag: '"one"', issues: structuredClone(f.issues) }),
    comments: async number => structuredClone((f.issueComments[number] ?? []).map(row => f.claimComments.get(String(row.id)) ?? row)),
    reconcileDependencyIntake: async () => { const state = f.state(); return { eligible: f.eligible(state), queued: [], skipped: [], claims: f.claims(state) }; },
    herdr: async args => {
      if (args[0] === 'status') return { running: true };
      const live = { pane_id: 'p1', workspace_id: 'w1', cwd, foreground_cwd: cwd, tab_id: 't1', terminal_id: 'term1', agent: 'codex', agent_status: 'idle', agent_session: 'session' };
      if (args[0] === 'workspace') return { result: { type: 'workspace_info', workspace: { workspace_id: 'w1' }, root_pane: { pane_id: 'p1' } } };
      if (args[0] === 'pane' && args[1] === 'get') return { result: { type: 'pane_info', pane: live } };
      if (args[0] === 'agent' && args[1] === 'get') { if (!f.agentStarted) throw Object.assign(Error('agent_not_found'), { code: 'agent_not_found' }); return { result: { type: 'agent_info', agent: live } }; }
      if (args[0] === 'pane' && args[1] === 'run') { f.agentStarted = true; return {}; }
      if (args[0] === 'pane' && args[1] === 'read') return '';
      if (args[0] === 'agent' && args[1] === 'prompt') { const instruction = args.at(-1), match = /Artifact path: (.+)/.exec(instruction); f.prompts.push(match ? readFileSync(JSON.parse(match[1]), 'utf8') : instruction); }
      return {};
    },
  };
  const launcher = await import('../src/autopilot-launcher.mjs');
  f.cwd = cwd;
  f.stateFile = () => join(f.ports.stateRoot, readdirSync(f.ports.stateRoot).find(x => x.endsWith('.json')));
  f.state = () => { try { return JSON.parse(readFileSync(f.stateFile(), 'utf8')); } catch { return {}; } };
  f.start = () => launcher.runAutopilotLauncher({ command: 'start', cwd, env: { HOME: home, PATH: process.env.PATH }, packageRoot: resolve('.'), issues: [] }, f.ports);
  f.tick = () => launcher.tickAutopilot(f.stateFile(), f.ports);
  f.packet = () => JSON.parse(f.prompts.at(-1).trim().split('\n').at(-1));
  // The claim comment names this launcher's coordinator, known after start.
  f.ownComment = (createdAt = at(NOW - 2 * minute)) => { const { coordinatorId, machine } = f.state();
    const row = { id: 901, user: { login: 'owner' }, created_at: createdAt, updated_at: createdAt, body: claimBody({ coordinatorId, machine }) };
    f.claimComments.set('901', structuredClone(row)); return row; };
  return f;
}
const tickIssue = (n, extra = {}) => ({ number: n, state: 'open', title: `Issue ${n}`, body: 'trusted body', user: { login: 'owner' }, author_association: 'OWNER',
  created_at: at(NOW - 48 * hour), updated_at: at(NOW - 2 * minute), comments: 0, labels: [{ name: 'pdd:working' }], assignees: [], html_url: key(n), ...extra });

const timeRules = (f, kind) => f.prompts.flatMap(text => JSON.parse(text.trim().split('\n').at(-1)).timeRules ?? []).filter(row => row.kind === kind);
// One own claim on issue 7, claimed at NOW; GitHub returns every change (status 200).
async function heartbeatTick(t) {
  const f = await tickFixture(t);
  f.issues = [tickIssue(7, { comments: 1, updated_at: at(NOW) })];
  f.claims = state => [ownClaim({ owner: state.coordinatorId, coordinatorId: state.coordinatorId, machine: state.machine })];
  assert.equal((await f.start()).exitCode, 0);
  // The new claim comment is new trusted work once; the first heartbeat edit makes the tick read it.
  f.issueComments = { 7: [f.ownComment(at(NOW))] }; f.status = 200; f.time += minute; await f.tick();
  assert.ok(f.prompts.some(text => /"number":7,/.test(text)), 'the claim comment was seen');
  f.prompts.length = 0; f.patches.length = 0;
  return f;
}

test('tick: the owner refreshes its live claim at each tick with no AI call, and a heartbeat edit is not new work', async t => {
  const f = await heartbeatTick(t);
  for (const i of [1, 2]) {
    f.time += 29 * minute; await f.tick();
    assert.equal(f.patches.length, i, 'one heartbeat for the one own claim');
    assert.equal(JSON.parse(/```json\n([\s\S]*?)\n```/.exec(f.patches.at(-1).body)[1]).lastSeen, at(f.time));
    assert.equal(f.issues[0].updated_at, at(f.time), 'like GitHub, the edit moved the issue update time');
  }
  assert.equal(f.prompts.length, 0, 'a heartbeat is neither an AI call nor new work');
});

// GitHub moves the issue updated_at to the edit time of a comment (measured on
// GitHub 2026-11-06), so each heartbeat changes the issue update time.
test('tick: with only heartbeats for 60 minutes the idle-claim rule fires once', async t => {
  const f = await heartbeatTick(t);
  f.time += 30 * minute; await f.tick();
  assert.equal(timeRules(f, 'idle-claim').length, 0, '30 minutes of heartbeats is not idle yet');
  f.time += 30 * minute; await f.tick();
  assert.deepEqual(timeRules(f, 'idle-claim').map(row => row.number), [7], 'heartbeats alone are not activity');
  for (let i = 0; i < 4; i++) { f.time += 30 * minute; await f.tick(); }
  assert.equal(timeRules(f, 'idle-claim').length, 1, 'the rule is sent once');
  assert.equal(f.patches.length, 6, 'the claim was refreshed at each tick');
});

test('tick: real progress on a heartbeat claim keeps the idle-claim rule quiet', async t => {
  const f = await heartbeatTick(t);
  const progress = (id, time) => { f.issueComments[7].push({ id, user: { login: 'owner' }, created_at: at(time), updated_at: at(time), body: `Progress ${id}.` });
    f.issues[0].comments += 1; f.issues[0].updated_at = at(time); };
  f.time += 30 * minute; await f.tick();
  progress(902, f.time + 15 * minute);
  f.time += 30 * minute; await f.tick();
  f.time += 30 * minute; await f.tick();
  assert.equal(timeRules(f, 'idle-claim').length, 0, 'a worker comment 45 minutes after the claim is activity');
  f.time += 30 * minute; await f.tick();
  assert.deepEqual(timeRules(f, 'idle-claim').map(row => row.number), [7], 'it fires 60 minutes after the last real progress');
  assert.equal(f.patches.length, 4, 'the claim was refreshed at each tick');
});

test('tick: in off mode this machine sends no heartbeat, so its claims expire like a stopped machine', async t => {
  const f = await heartbeatTick(t);
  writeFileSync(join(f.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'off', trust: [] } }));
  for (let i = 0; i < 3; i++) { f.time += 30 * minute; await f.tick(); }
  assert.equal(f.patches.length, 0, 'off mode writes no lastSeen');
  assert.equal(f.prompts.length, 0, 'off mode wakes no AI and releases nothing');
  writeFileSync(join(f.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [] } }));
  f.time += 30 * minute; await f.tick();
  assert.equal(f.patches.length, 1, 'back in auto mode the live claim is refreshed again');
});

test('tick: a live claim of another coordinator stays skipped; once it expires it is offered with its reason', async t => {
  const f = await tickFixture(t, { mode: 'observe' });
  f.issues = [tickIssue(8)];
  const other = { issue: key(8), owner: 'coordinator-old', coordinatorId: 'coordinator-old', machine: 'machine-old', commentId: '801', labelEventId: '601', lastSeen: at(NOW - 3 * hour) };
  f.claims = () => [{ ...other, active: true }];
  assert.equal((await f.start()).exitCode, 0);
  for (const prompt of f.prompts) assert.doesNotMatch(prompt, /"number":8,/);
  f.prompts.length = 0; f.status = 304;
  f.time += 30 * minute; await f.tick();
  assert.equal(f.prompts.length, 0, 'a live claim is never offered as work');
  f.claims = () => [{ ...other, active: false, expired: true, lastSeen: at(NOW - 4 * hour) }];
  f.eligible = () => [key(8)];
  f.time += 30 * minute; await f.tick();
  assert.equal(f.prompts.length, 1, 'the expired claim is offered once');
  const item = f.packet().issues.find(row => row.number === 8);
  assert.equal(item.eligible, true);
  assert.equal(item.claimed, true);
  assert.deepEqual(item.expiredClaim, { lastSeen: at(NOW - 4 * hour) });
  f.time += 30 * minute; await f.tick();
  assert.equal(f.prompts.length, 1, 'an unchanged expired claim stays quiet in observe mode');
  assert.equal(f.patches.length, 0, 'no coordinator edits another owner\'s claim');
});

test('tick: after 4 hours stuck the owner stops refreshing its claim and asks once to retry or alert', async t => {
  const f = await tickFixture(t);
  f.issues = [tickIssue(7, { labels: [{ name: 'pdd:working' }, { name: 'pdd:stuck' }] })];
  let stuckSince = at(NOW - 4 * hour + 30 * minute);
  f.claims = state => [ownClaim({ owner: state.coordinatorId, coordinatorId: state.coordinatorId, machine: state.machine, stuckSince })];
  assert.equal((await f.start()).exitCode, 0);
  f.ownComment(); f.prompts.length = 0; f.patches.length = 0; f.status = 304;
  f.time += 29 * minute; await f.tick();
  assert.equal(f.patches.length, 1, 'stuck for less than 4 hours: the claim is still refreshed');
  assert.equal(f.prompts.length, 0);
  f.time += minute; await f.tick();
  assert.equal(f.patches.length, 1, 'stuck for 4 hours: no more refresh, so the claim can expire');
  assert.equal(f.prompts.length, 1);
  const stuckRules = () => f.prompts.flatMap(text => JSON.parse(text.trim().split('\n').at(-1)).timeRules ?? []).filter(row => row.kind === 'stuck-claim');
  assert.equal(stuckRules()[0].number, 7);
  assert.match(stuckRules()[0].reason, /stuck for 4 hours.*changed approach.*alert channel/);
  for (let i = 0; i < 2; i++) { f.time += 30 * minute; await f.tick(); }
  assert.equal(stuckRules().length, 1, 'the stuck rule is sent once');
  stuckSince = undefined; f.time += 30 * minute; await f.tick();
  assert.equal(f.patches.length, 2, 'a retried issue that left pdd:stuck is refreshed again');
});

// A coordinator whose claim expired or was taken does not push to the issue.
test('workflow: an automatic run does not push or open its PR after its claim expired', async t => {
  const exec = promisify(callbackExec);
  const f = await runnerFixture(t, { name: 'small-change', agent: 'codex' });
  f.ports.env = { HOME: f.ports.env.HOME };
  assert.equal((await startRun({ name: 'small-change', issue: '17', agent: 'codex', cwd: f.source, packageRoot }, f.ports)).exitCode, 0);
  const run = f.record(); f.tick();
  await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  f.tick(); assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n'); f.git(run.root, 'commit', '-qam', 'two');
  for (const step of ['change', 'verify']) { f.tick(); assert.equal((await stepDone({ step, summary: step, cwd: run.root }, f.agentPorts())).exitCode, 0); }
  const origin = { repository: 'example/project', coordinatorId: 'coordinator-a', machine: 'machine-a', claim: { commentId: '11', labelEventId: '12' } };
  const saved = f.record(); saved.automaticOrigin = structuredClone(origin); writeRun(saved);
  const root = realpathSync(f.source), stateRoot = join(f.state, 'autopilot'); mkdirSync(stateRoot, { recursive: true });
  writeFileSync(join(stateRoot, `${sha(root).slice(0, 20)}.json`), JSON.stringify({ repo: 'example/project', cwd: root, coordinatorId: origin.coordinatorId }));
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [] } }));
  const fixturePath = join(f.base, 'reader.json'), logPath = join(f.base, 'gh.log');
  // As on GitHub, the claim comment has its creation time and its last heartbeat edit time.
  const claimedAt = at(f.clock - 30 * hour);
  const claimFor = lastSeen => writeFileSync(fixturePath, JSON.stringify({ labels: ['pdd:working'], events: [{ id: 12, event: 'labeled', label: { name: 'pdd:working' }, actor: { login: 'example' }, created_at: claimedAt }],
    comments: [{ id: 11, user: { login: 'example' }, created_at: claimedAt, updated_at: lastSeen, body: JSON.stringify({ repository: origin.repository, coordinatorId: origin.coordinatorId, machine: origin.machine, labelEventId: '12', lastSeen }) }] }));
  const original = f.ports.execFile;
  const execFile = (file, args, opts) => file === 'gh' && args[0] === 'api' && args[1] === '--include'
    ? exec(process.execPath, [join(packageRoot, 'test/helpers/continuation-fake-gh.mjs'), ...args], { ...opts, env: { ...process.env, READER_FIXTURE_FILE: fixturePath, READER_GH_LOG: logPath } })
    : original(file, args, opts);
  const ports = () => f.agentPorts({ execFile, autopilotStateRoot: stateRoot });
  claimFor(at(f.clock - 5 * hour));
  f.tick();
  const refused = await stepDone({ step: 'formal', summary: 'formal', cwd: run.root }, ports());
  assert.equal(refused.exitCode, 1);
  assert.match(refused.message, /claim ownership/);
  assert.equal(f.pushes.length, 0, 'no push after the claim expired');
  assert.equal(f.prs.length, 0);
  claimFor(at(f.clock));
  f.tick();
  const opened = await stepDone({ step: 'formal', summary: 'formal', cwd: run.root }, ports());
  assert.equal(opened.exitCode, 0, opened.message);
  assert.equal(f.pushes.length, 1);
  assert.equal(f.prs.length, 1);
});

// Issue #3041: per-issue ceilings for takeovers and for a long-running claim.
// Each era: the label event, its claim comment with a last GitHub edit, and how it ended.
// Each claim record is a heartbeat claim: its last heartbeat wrote lastSeen at that edit.
function claimHistory(eras) {
  const timeline = [], comments = [];
  eras.forEach((era, n) => {
    const label = 701 + 2 * n, coordinatorId = `coordinator-${n}`, machine = `machine-${n}`;
    timeline.push(labeled(label, at(era.from)));
    comments.push({ id: 901 + n, user: { login: 'owner' }, created_at: at(era.from), updated_at: at(era.seen),
      body: claimBody({ coordinatorId, machine, labelEventId: String(label), lastSeen: at(era.seen) }, n ? `Took over an expired claim of coordinator-${n - 1}.` : 'Autopilot claim.') });
    if (era.to !== undefined) timeline.push(labeled(label + 1, at(era.to), 'unlabeled'));
  });
  return { timeline, comments };
}
// Era n starts at T0 + 6n hours, its last heartbeat is 1 hour later, and the next
// coordinator takes it over 5 hours after that heartbeat (the claim expired after 4).
const T0 = NOW - 40 * hour;
const takenOver = count => Array.from({ length: count + 1 }, (_, n) => ({ from: T0 + 6 * n * hour, seen: T0 + (6 * n + 1) * hour, ...(n < count ? { to: T0 + 6 * (n + 1) * hour } : {}) }));

test('takeover ceiling: after 3 takeovers an expired claim is not taken over again, and pdd graph shows why', async t => {
  const world = checkout(t), issue = issueRow(7, { updated_at: at(NOW - 20 * hour) });
  const two = await observe(world, { issue, ...claimHistory(takenOver(2)) });
  assert.deepEqual([two.claim.takeovers, two.claim.expired, two.claim.claimedAt], [2, true, at(T0)], 'a takeover continues the claim chain');
  assert.equal(two.node.eligible, true, 'after 2 takeovers an expired claim can be taken over a 3rd time');

  const three = await observe(world, { issue, ...claimHistory(takenOver(3)) });
  assert.deepEqual([three.claim.takeovers, three.claim.expired], [3, true]);
  const reason = 'Taken over 3 times; take the stuck path, not another takeover';
  assert.ok(three.node.reasons.includes(reason), three.node.reasons.join('; '));
  assert.equal(three.node.eligible, false, 'no 4th takeover');

  let saved = '';
  const view = await runIssueGraph({ cwd: world.cwd, repository: repo }, {
    snapshots: { read: args => readDependencySnapshot(args, three.ports) },
    cache: { read: async () => ({ json: saved }), write: async ({ json }) => { saved = json; return { ok: true }; } },
    refresh: { schedule: async () => ({ ok: true }) },
  });
  assert.equal(view.exitCode, 0, view.message);
  assert.ok(view.message.split('\n').includes(`  ${reason}`), view.message);
});

test('takeover ceiling: the 3rd takeover may start; a 4th takeover made anyway is refused at start', async t => {
  const world = checkout(t), issue = issueRow(7, { updated_at: at(NOW - 5 * minute) });
  const settings = { read: async () => ({ mode: 'auto', activation: 'activation' }) };
  const startAs = async (history, n) => {
    const observed = await observe(world, { issue, ...claimHistory(history) });
    world.localOwner(`coordinator-${n}`);
    const coordinator = { repository: repo, coordinatorId: `coordinator-${n}`, machine: `machine-${n}`, activation: 'activation', claim: { commentId: String(901 + n), labelEventId: String(701 + 2 * n) } };
    return { observed, start: await checkDependencyStart({ cwd: world.cwd, repository: repo, issue: issue.html_url, coordinator }, { ...observed.ports, settings }) };
  };
  // The last takeover removes the expired label and adds it again at once.
  const live = history => history.map((era, n) => n === history.length - 1 ? { ...era, from: NOW - 10 * minute, seen: NOW - 5 * minute } : n === history.length - 2 ? { ...era, to: NOW - 10 * minute } : era);
  const third = await startAs(live(takenOver(3)), 3);
  assert.deepEqual([third.observed.claim.takeovers, third.observed.claim.active], [3, true]);
  assert.deepEqual(third.start, { allowed: true, reason: 'ok' });
  const fourth = await startAs(live(takenOver(4)), 4);
  assert.equal(fourth.observed.claim.takeovers, 4);
  assert.ok(fourth.observed.node.reasons.includes('Taken over 4 times; take the stuck path, not another takeover'), fourth.observed.node.reasons.join('; '));
  assert.deepEqual(fourth.start, { allowed: false, reason: 'dependency' });
});

test('takeover ceiling: a normal release of a live claim is not a takeover and starts a new claim chain', async t => {
  const world = checkout(t), issue = issueRow(7, { updated_at: at(NOW - 20 * hour) });
  // Era 0 ends 30 minutes after its last heartbeat: the run ended and its owner removed the label.
  const history = takenOver(3); history[0] = { ...history[0], to: history[0].seen + 30 * minute };
  const { claim, node } = await observe(world, { issue, ...claimHistory(history) });
  assert.equal(claim.takeovers, 2);
  assert.equal(claim.claimedAt, at(history[1].from), 'the chain starts after the normal release');
  assert.equal(node.eligible, true);
});

test('tick: after 3 takeovers the expired claim stays a hold and coordinators get one takeover-limit rule', async t => {
  const f = await tickFixture(t);
  f.issues = [tickIssue(8)];
  let claim = { issue: key(8), owner: 'coordinator-old', coordinatorId: 'coordinator-old', machine: 'machine-old', commentId: '801', labelEventId: '601', active: false, expired: true, lastSeen: at(NOW - 5 * hour), takeovers: 3 };
  f.claims = () => [claim];
  assert.equal((await f.start()).exitCode, 0);
  for (let i = 0; i < 3; i++) { f.time += 30 * minute; await f.tick(); }
  const rules = timeRules(f, 'takeover-limit');
  assert.deepEqual(rules.map(row => row.number), [8], 'one rule for the issue');
  assert.match(rules[0].reason, /taken over 3 times\. Do not take it over again: take the stuck path \(pdd:stuck, one comment with the cause, one stuck alert\)/);
  for (const text of f.prompts) for (const item of JSON.parse(text.trim().split('\n').at(-1)).issues ?? []) assert.equal(item.expiredClaim, undefined, 'never offered for a 4th takeover');
  assert.deepEqual(f.state().seen[8].selectionReasons, ['pdd:working', 'takeover-limit']);
  assert.equal(f.patches.length, 0);

  // With 2 takeovers the same expired claim is offered for takeover, as before.
  const g = await tickFixture(t);
  g.issues = [tickIssue(8)];
  g.claims = () => [{ ...claim, takeovers: 2 }];
  g.eligible = () => [key(8)];
  assert.equal((await g.start()).exitCode, 0);
  assert.equal(timeRules(g, 'takeover-limit').length, 0);
  assert.ok(g.prompts.some(text => (JSON.parse(text.trim().split('\n').at(-1)).issues ?? []).some(item => item.number === 8 && item.expiredClaim)), 'offered with expiredClaim');
});

test('tick: 24 hours after the claim with no merge, the owner gets one long-running rule and work continues', async t => {
  const f = await tickFixture(t);
  f.issues = [tickIssue(7, { comments: 1, updated_at: at(NOW) }), tickIssue(9, { state: 'closed' })];
  f.claims = state => [ownClaim({ owner: state.coordinatorId, coordinatorId: state.coordinatorId, machine: state.machine, claimedAt: at(NOW - 23 * hour) }),
    ownClaim({ issue: key(9), owner: state.coordinatorId, coordinatorId: state.coordinatorId, machine: state.machine, commentId: '909', claimedAt: at(NOW - 30 * hour) })];
  assert.equal((await f.start()).exitCode, 0);
  f.issueComments = { 7: [f.ownComment(at(NOW))] };
  f.time += 30 * minute; await f.tick();
  assert.equal(timeRules(f, 'long-running').length, 0, '23.5 hours after the claim is not due; a closed issue is not due');
  f.time += 30 * minute; await f.tick();
  const rules = timeRules(f, 'long-running');
  assert.deepEqual(rules.map(row => row.number), [7]);
  assert.match(rules[0].reason, /claimed 24 hours ago and has no merge yet\. Send one informational alert for it, then keep working; this is not a stop\./);
  const patches = f.patches.length;
  for (let i = 0; i < 3; i++) { f.time += 30 * minute; await f.tick(); }
  assert.equal(timeRules(f, 'long-running').length, 1, 'once per issue');
  assert.equal(f.patches.length, patches + 3, 'the claim is still refreshed: work continues');
});

// #3041 repair: what counts as a takeover, and how a person resets the count.
// Each era: {from, seen, to?, who, alerted?}. `who` names the coordinator and machine of
// its claim record. Extra timeline events (pdd:stuck) are merged in time order.
function eraHistory(eras, extra = []) {
  const events = [], comments = [];
  eras.forEach((era, n) => {
    const label = 701 + 2 * n;
    events.push(labeled(label, at(era.from)));
    comments.push({ id: 901 + n, user: { login: 'owner' }, created_at: at(era.from), updated_at: at(era.seen),
      body: claimBody({ coordinatorId: `coordinator-${era.who}`, machine: `machine-${era.who}`, labelEventId: String(label), lastSeen: at(era.seen), ...(era.alerted ? { longRunningAlertedAt: at(era.alerted) } : {}) }) });
    if (era.to !== undefined) events.push(labeled(label + 1, at(era.to), 'unlabeled'));
  });
  const timeline = [...events, ...extra].map((event, order) => ({ event, order })).sort((a, b) => Date.parse(a.event.created_at) - Date.parse(b.event.created_at) || a.order - b.order).map(row => row.event);
  return { timeline, comments };
}
// Three takeovers between different coordinators: era n starts at T0 + 6n hours, its last
// heartbeat is 1 hour later, and the next coordinator removes and adds the label at once.
const pingPong = (count, who = n => n) => Array.from({ length: count + 1 }, (_, n) => ({ from: T0 + 6 * n * hour, seen: T0 + (6 * n + 1) * hour, who: who(n), ...(n < count ? { to: T0 + 6 * (n + 1) * hour } : {}) }));
const localCoordinator = (world, coordinatorId, machine) => writeFileSync(join(world.stateRoot, `${sha(realpathSync(world.cwd)).slice(0, 20)}.json`),
  JSON.stringify({ repo, cwd: realpathSync(world.cwd), coordinatorId, machine, enabled: true, activatedAt: 'activation' }));
const LIMIT_HOLD = /^Taken over \d+ times/;

test('takeover count: a coordinator that takes back its own expired claim makes no takeover', async t => {
  const world = checkout(t), issue = issueRow(7, { updated_at: at(NOW - 20 * hour) });
  // One machine is off each night: 3 times its claim expires and it takes the claim back in the morning.
  const own = await observe(world, { issue, ...eraHistory(pingPong(3, () => 'a')) });
  assert.equal(own.claim.takeovers, undefined);
  assert.equal(own.claim.claimedAt, at(T0), 'a re-claim continues the claim chain');
  assert.equal(own.node.reasons.some(reason => LIMIT_HOLD.test(reason)), false);

  // After 3 real takeovers the last owner (coordinator-3) may take back its own expired claim; another coordinator may not.
  const facts = { issue, ...eraHistory(pingPong(3)) };
  localCoordinator(world, 'coordinator-3', 'machine-3');
  const self = await observe(world, facts);
  assert.equal(self.claim.takeovers, 3);
  assert.equal(self.node.reasons.some(reason => LIMIT_HOLD.test(reason)), false, 'its own re-claim is not a 4th takeover');
  assert.equal(self.node.eligible, true);
  localCoordinator(world, 'coordinator-3', 'machine-other');
  const otherMachine = await observe(world, facts);
  assert.ok(otherMachine.node.reasons.includes('Taken over 3 times; take the stuck path, not another takeover'), 'the same coordinator ID on another machine is another owner');
  assert.equal(otherMachine.node.eligible, false);
});

test('takeover count: a person removing pdd:stuck at the limit resets the count; an earlier removal does not', async t => {
  const world = checkout(t), issue = issueRow(7, { updated_at: at(NOW - 20 * hour) });
  const eras = pingPong(3);
  // The limit is reached and a coordinator took the stuck path; later a person removes pdd:stuck.
  const stuck = [labeled(801, at(NOW - 20 * hour), 'labeled', 'pdd:stuck'), labeled(802, at(NOW - 2 * hour), 'unlabeled', 'pdd:stuck')];
  const reset = await observe(world, { issue, ...eraHistory(eras, stuck) });
  assert.equal(reset.claim.takeovers, undefined, 'removing pdd:stuck resets the count');
  assert.equal(reset.claim.expired, true);
  assert.equal(reset.node.reasons.some(reason => LIMIT_HOLD.test(reason)), false);
  assert.equal(reset.node.eligible, true, 'Autopilot may take the issue over again');

  // A stuck episode that an owner ends before the limit (era 2, still live) does not reset the count.
  const early = [labeled(803, at(T0 + 12.2 * hour), 'labeled', 'pdd:stuck'), labeled(804, at(T0 + 12.5 * hour), 'unlabeled', 'pdd:stuck')];
  const kept = await observe(world, { issue, ...eraHistory(eras, early) });
  assert.equal(kept.claim.takeovers, 3);
  assert.equal(kept.node.eligible, false);
});

test('takeover count: a person removing an expired pdd:working is not a takeover, and a normal release resets the count', async t => {
  const world = checkout(t), issue = issueRow(7, { updated_at: at(NOW - 5 * minute) });
  world.localOwner('coordinator-4');
  const settings = { read: async () => ({ mode: 'auto', activation: 'activation' }) };
  const coordinator = { repository: repo, coordinatorId: 'coordinator-4', machine: 'machine-4', activation: 'activation', claim: { commentId: '905', labelEventId: '709' } };
  // After 3 takeovers the 4th owner's claim expired; a person removed its label; Autopilot claims again 2 days later.
  const cleanup = pingPong(3); cleanup[3] = { ...cleanup[3], to: T0 + 24 * hour };
  cleanup.push({ from: NOW - 10 * minute, seen: NOW - 5 * minute, who: 4 });
  const fresh = await observe(world, { issue, ...eraHistory(cleanup) });
  assert.equal(fresh.claim.takeovers, undefined, "a person's cleanup is not a 4th takeover");
  assert.equal(fresh.claim.claimedAt, at(NOW - 10 * minute), 'the cleanup ends the claim chain');
  assert.deepEqual(await checkDependencyStart({ cwd: world.cwd, repository: repo, issue: issue.html_url, coordinator }, { ...fresh.ports, settings }), { allowed: true, reason: 'ok' });

  // After 3 takeovers the 4th owner finished and released its live claim; a new claim days later starts at 0.
  const release = pingPong(3); release[3] = { ...release[3], to: release[3].seen + 20 * minute };
  release.push({ from: NOW - 6 * hour, seen: NOW - 5 * hour, who: 4 });
  const later = await observe(world, { issue, ...eraHistory(release) });
  assert.equal(later.claim.takeovers, undefined);
  assert.equal(later.claim.expired, true);
  assert.equal(later.node.eligible, true, 'one expiry after a normal release may be taken over');
});

test('long-running alert: a claim chain that already sent it carries longRunningAlertedAt to the next owner', async t => {
  const world = checkout(t), issue = issueRow(7, { updated_at: at(NOW - 20 * hour) });
  const eras = pingPong(1); eras[0] = { ...eras[0], alerted: T0 + 0.5 * hour };
  const taken = await observe(world, { issue, ...eraHistory(eras) });
  assert.equal(taken.claim.longRunningAlertedAt, at(T0 + 0.5 * hour), 'a takeover continues the chain and its alert');
  const released = pingPong(1); released[0] = { ...released[0], alerted: T0 + 0.5 * hour, to: released[0].seen + 20 * minute };
  const fresh = await observe(world, { issue, ...eraHistory(released) });
  assert.equal(fresh.claim.longRunningAlertedAt, undefined, 'a new chain sends its own alert');
});

test('tick: only one coordinator acts on the takeover limit, and the own expired claim is a re-claim', async t => {
  const limited = (state, extra) => ({ issue: key(8), owner: 'coordinator-old', coordinatorId: 'coordinator-old', machine: 'machine-old', commentId: '801', labelEventId: '601', active: false, expired: true, lastSeen: at(NOW - 5 * hour), takeovers: 3, ...extra });
  const run = async claims => {
    const f = await tickFixture(t);
    f.issues = [tickIssue(8)]; f.claims = claims; f.eligible = () => [key(8)];
    assert.equal((await f.start()).exitCode, 0);
    for (let i = 0; i < 2; i++) { f.time += 30 * minute; await f.tick(); }
    return f;
  };
  // The coordinator that was taken over last acts; any other coordinator does not.
  const previous = await run(state => [limited(state, { previousOwner: { coordinatorId: state.coordinatorId, machine: state.machine } })]);
  assert.deepEqual(timeRules(previous, 'takeover-limit').map(row => row.number), [8]);
  assert.match(timeRules(previous, 'takeover-limit')[0].reason, /Read the issue again first and skip it if it already has pdd:stuck\. A person removes pdd:stuck to reset the count\./);
  const other = await run(state => [limited(state, { previousOwner: { coordinatorId: 'coordinator-x', machine: 'machine-x' } })]);
  assert.equal(timeRules(other, 'takeover-limit').length, 0);
  // A 4th takeover made anyway: only the owner of that live claim acts.
  const live = extra => state => [limited(state, { active: true, expired: undefined, takeovers: 4, ...extra(state) })];
  assert.equal(timeRules(await run(live(state => ({ coordinatorId: state.coordinatorId, owner: state.coordinatorId, machine: state.machine }))), 'takeover-limit').length, 1);
  assert.equal(timeRules(await run(live(() => ({}))), 'takeover-limit').length, 0);
  // Its own expired claim after 3 takeovers: offered to take back, with no takeover-limit rule.
  const own = await run(state => [limited(state, { owner: state.coordinatorId, coordinatorId: state.coordinatorId, machine: state.machine })]);
  assert.equal(timeRules(own, 'takeover-limit').length, 0);
  assert.ok(own.prompts.some(text => (JSON.parse(text.trim().split('\n').at(-1)).issues ?? []).some(item => item.number === 8 && item.expiredClaim)), 'offered with expiredClaim');
});

test('tick: the 24-hour alert is recorded in the own claim comment and skipped when the chain already has it', async t => {
  const f = await tickFixture(t);
  f.issues = [tickIssue(7, { comments: 1, updated_at: at(NOW) })];
  // Not due at start; due at the next tick, when the claim comment is there.
  f.claims = state => [ownClaim({ owner: state.coordinatorId, coordinatorId: state.coordinatorId, machine: state.machine, claimedAt: at(NOW - 23.75 * hour) })];
  assert.equal((await f.start()).exitCode, 0);
  f.issueComments = { 7: [f.ownComment(at(NOW))] };
  f.time += 30 * minute; await f.tick();
  assert.equal(timeRules(f, 'long-running').length, 1);
  const marked = f.patches.map(patch => recordOf(patch.body)).filter(value => value.longRunningAlertedAt);
  assert.equal(marked.length, 1, 'the delivered alert is recorded once');
  assert.equal(marked[0].longRunningAlertedAt, at(f.time));
  const { coordinatorId, machine } = f.state();
  assert.equal(withoutClaimHeartbeat(f.claimComments.get('901').body), claimBody({ coordinatorId, machine }), 'the record is a tick write, not new work');
  for (let i = 0; i < 2; i++) { f.time += 30 * minute; await f.tick(); }
  assert.equal(timeRules(f, 'long-running').length, 1, 'once per issue');

  // Another machine took the claim over: its chain already has the alert, so it sends none.
  const g = await tickFixture(t);
  g.issues = [tickIssue(7, { comments: 1, updated_at: at(NOW) })];
  g.claims = state => [ownClaim({ owner: state.coordinatorId, coordinatorId: state.coordinatorId, machine: state.machine, claimedAt: at(NOW - 25 * hour), longRunningAlertedAt: at(NOW - hour) })];
  assert.equal((await g.start()).exitCode, 0);
  g.issueComments = { 7: [g.ownComment(at(NOW))] };
  for (let i = 0; i < 2; i++) { g.time += 30 * minute; await g.tick(); }
  assert.equal(timeRules(g, 'long-running').length, 0);
});

test('tick: after a ceiling the 4-hour stuck rule asks for no retry and at most the one stuck alert', async t => {
  // Both ceilings at once (#3041 review S2): the rule names both and keeps the cancel step of the repair limit.
  for (const ceiling of ['repair limit', 'takeover limit', 'takeover limit and the repair limit']) {
    const repair = ceiling.includes('repair limit'), takeover = ceiling.includes('takeover limit');
    const f = await tickFixture(t);
    f.issues = [tickIssue(7, { labels: [{ name: 'pdd:working' }, { name: 'pdd:stuck' }] })];
    const stuckSince = at(NOW - 3.75 * hour); // due at the first tick after start
    f.claims = state => [ownClaim({ owner: state.coordinatorId, coordinatorId: state.coordinatorId, machine: state.machine, stuckSince, ...(takeover ? { takeovers: 4 } : {}) })];
    assert.equal((await f.start()).exitCode, 0);
    if (repair) {
      mkdirSync(join(f.cwd, 'pdd', 'runs', '7'), { recursive: true });
      writeFileSync(join(f.cwd, 'pdd', 'runs', '7', 'status.json'), JSON.stringify({ v: 1, number: 7, repo: f.state().repo, state: 'stuck', parkReason: 'Repair limit reached in build: take the stuck path', repairLimit: { area: 'build', step: 'build', at: NOW } }));
    }
    for (let i = 0; i < 3; i++) { f.time += 30 * minute; await f.tick(); }
    const rules = timeRules(f, 'stuck-claim');
    assert.equal(rules.length, 1, `${ceiling}: one rule`);
    assert.match(rules[0].reason, new RegExp(`stuck for 4 hours after the ${ceiling}\\. Do not retry it, do not remove pdd:stuck and write no new comment; send the one stuck alert only if this stop has none yet\\. `));
    assert.ok(rules[0].reason.includes(repair
      ? 'To let Autopilot try again, a person removes pdd:stuck and pdd:working, then runs pdd workflow cancel 7 in the checkout that holds the stuck run; the next tick starts a new run with a fresh repair count.'
      : 'A person removes pdd:stuck and pdd:working to let Autopilot try again.'), rules[0].reason);
    assert.doesNotMatch(rules[0].reason, /changed approach/);
  }
});
