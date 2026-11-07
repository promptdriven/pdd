import test from 'node:test';
import assert from 'node:assert/strict';
import { execFile as callbackExec, execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdirSync, mkdtempSync, readFileSync, readdirSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { promisify } from 'node:util';
import { readDependencySnapshot, createDependencyReadPorts, refreshClaimHeartbeat } from '../src/issue-dependencies-github.mjs';
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
    clock: { now: async () => ({ iso: at(NOW) }) },
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
const cases = [
  { name: 'a heartbeat 1 minute short of 4 hours keeps the claim live', lastSeen: NOW - 4 * hour + minute, expired: false },
  { name: 'a heartbeat 4 hours old expires the claim even with recent issue activity', lastSeen: NOW - 4 * hour, activity: NOW - 10 * minute, expired: true, seen: NOW - 4 * hour },
  { name: 'a legacy claim with issue activity 23 hours ago stays live', activity: NOW - 23 * hour, expired: false },
  { name: 'a legacy claim with no issue activity for 24 hours expires', activity: NOW - 24 * hour, expired: true, seen: NOW - 24 * hour },
  { name: 'a bare label with no claim comment expires after 24 hours without activity', bare: true, activity: NOW - 25 * hour, expired: true, seen: NOW - 25 * hour },
  { name: 'a legacy claim with no readable activity time never expires', unknownTimes: true, expired: false },
];
for (const c of cases) test(`claim expiry: ${c.name}`, async t => {
  const world = checkout(t), activity = c.activity ?? NOW - 30 * hour;
  const issue = issueRow(7, { updated_at: c.unknownTimes ? undefined : at(activity) });
  const claimAt = c.unknownTimes ? undefined : at(Math.min(activity, NOW - 26 * hour));
  const comments = c.bare ? [] : [{ id: 901, user: { login: 'owner' }, created_at: claimAt, updated_at: claimAt,
    body: claimBody(c.lastSeen === undefined ? {} : { lastSeen: at(c.lastSeen) }) }];
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

function commentService(initial) {
  const comments = new Map(initial.map(row => [String(row.id), structuredClone(row)])), patches = [];
  const execFile = async (file, args, options = {}) => {
    assert.equal(file, 'gh'); assert.equal(args[0], 'api');
    const method = args[3], endpoint = args[4], id = /^repos\/owner\/repo\/issues\/comments\/([0-9]+)$/.exec(endpoint)?.[1];
    assert.ok(id, `unexpected endpoint ${endpoint}`);
    if (method === 'PATCH') { const { body } = JSON.parse(options.input); patches.push({ id, body }); comments.get(id).body = body; }
    else assert.equal(method, 'GET');
    return { stdout: `HTTP/2.0 200 OK\r\n\r\n${JSON.stringify(comments.get(id))}` };
  };
  return { comments, patches, execFile };
}
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
          if (args[3] === 'PATCH') { const { body } = JSON.parse(options.input); f.patches.push({ id, body }); f.claimComments.get(id).body = body; }
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
    comments: async number => structuredClone(f.issueComments[number] ?? []),
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

test('tick: the owner refreshes its live claim at each tick with no AI call, and a heartbeat edit is not new work', async t => {
  const f = await tickFixture(t);
  f.issues = [tickIssue(7, { comments: 1, updated_at: at(NOW) })];
  f.claims = state => [ownClaim({ owner: state.coordinatorId, coordinatorId: state.coordinatorId, machine: state.machine })];
  assert.equal((await f.start()).exitCode, 0);
  f.issueComments = { 7: [f.ownComment(at(NOW))] }; f.issues[0].updated_at = at(NOW + 500); f.status = 200; await f.tick();
  f.prompts.length = 0; f.patches.length = 0;
  for (const [i, step] of [[1, 29], [2, 29]]) {
    f.time += step * minute; f.status = 304;
    await f.tick();
    assert.equal(f.patches.length, i, 'one heartbeat for the one own claim');
    assert.equal(JSON.parse(/```json\n([\s\S]*?)\n```/.exec(f.patches.at(-1).body)[1]).lastSeen, at(f.time));
  }
  assert.equal(f.prompts.length, 0, 'a heartbeat is not an AI call');
  // GitHub returns the edited comment with a new edit time (the issue list shows a new update time, so comments are reread).
  f.status = 200; f.issues[0].updated_at = at(NOW + 1000);
  f.issueComments[7] = [{ ...structuredClone(f.claimComments.get('901')), updated_at: at(f.time) }];
  f.time += minute; await f.tick();
  assert.equal(f.prompts.length, 0, 'a heartbeat edit alone does not wake the coordinator');
  // Nor does it count as activity: the 60-minute idle-claim observation still comes.
  f.time += 2 * minute; await f.tick();
  assert.equal(f.prompts.length, 1);
  assert.deepEqual(f.packet().timeRules.map(row => [row.kind, row.number]), [['idle-claim', 7]]);
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
  const claimFor = lastSeen => writeFileSync(fixturePath, JSON.stringify({ labels: ['pdd:working'], events: [{ id: 12, event: 'labeled', label: { name: 'pdd:working' }, actor: { login: 'example' } }],
    comments: [{ id: 11, user: { login: 'example' }, body: JSON.stringify({ repository: origin.repository, coordinatorId: origin.coordinatorId, machine: origin.machine, labelEventId: '12', lastSeen }) }] }));
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
