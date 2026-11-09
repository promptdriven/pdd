import test from 'node:test';
import { createHash } from 'node:crypto';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { tickAutopilot, runAutopilotLauncher, autopilotLaunchFingerprint } from '../src/autopilot-launcher.mjs';
import { createDependencyReadPorts } from '../src/issue-dependencies-github.mjs';
import { healthyMachine } from './helpers/healthy-machine.mjs';
import { isolatedCheckCapacity } from './helpers/check-machine.mjs';
import { writeRun } from '../src/workflow-runs.mjs';
import { startRun, stepDone, approveRun, runStatus } from '../src/workflow-runner.mjs';
import { fixture as runnerFixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const repo = 'example/project', issue = `https://github.com/${repo}/issues/17`;
const hour = 3600000, NOW = Date.parse('2026-11-08T12:00:00Z'), at = n => new Date(n).toISOString();
const read = path => JSON.parse(readFileSync(path, 'utf8'));
const metadata = row => JSON.parse(/```json\n([\s\S]*?)\n```/.exec(row.body)[1]);

// All GitHub, Herdr and timer operations are fakes. Only the isolated Git checkout
// and run/state files are real. Server edit times drive the native claim reader.
function world(t, existing) {
  const dir = existing?.base ?? mkdtempSync(join(tmpdir(), 'pdd-restart-claims-'));
  if (!existing) t.after(() => rmSync(dir, { recursive: true, force: true }));
  const cwd = existing?.source ?? join(dir, 'repo'), home = existing?.ports.env.HOME ?? join(dir, 'restart-home'), stateRoot = join(dir, 'autopilot');
  mkdirSync(home, { recursive: true }); mkdirSync(stateRoot);
  if (!existing) { mkdirSync(cwd); execFileSync('git', ['init', '-q'], { cwd }); execFileSync('git', ['remote', 'add', 'origin', `https://github.com/${repo}.git`], { cwd }); }
  const commonDir = execFileSync('git', ['rev-parse', '--path-format=absolute', '--git-common-dir'], { cwd, encoding: 'utf8' }).trim();
  const runDir = join(commonDir, 'pdd', 'runs', '17'); mkdirSync(runDir, { recursive: true });
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [] } }));
  const f = { dir, cwd, home, stateRoot, commonDir, runDir, stateFile: join(stateRoot, `${createHash('sha256').update(cwd).digest('hex').slice(0, 20)}.json`), time: NOW, writes: [], warnings: [], launches: [], activePane: 'p1', claimProse: 'Claim context #17' };
  f.record = () => read(join(runDir, 'status.json'));
  f.state = () => read(f.stateFile);
  f.saveState = state => writeFileSync(f.stateFile, JSON.stringify(state));
  f.resetClaim = ({ owner = 'old', machine = 'machine-a', seen = f.time - hour, event = '701', recovered = false } = {}) => {
    f.events = [{ id: Number(event), event: 'labeled', label: { name: 'pdd:working' }, actor: { login: 'example' }, created_at: at(NOW - 8 * hour) }];
    f.claim = { id: 901, user: { login: 'example' }, created_at: at(NOW - 8 * hour), updated_at: at(seen), body: `${f.claimProse}\n\n\`\`\`json\n${JSON.stringify({ repository: repo, coordinatorId: owner, machine, labelEventId: event, lastSeen: at(seen), extra: { preserved: true }, ...(recovered ? { coordinatorRestartRecoveredAt: at(NOW - 6 * hour) } : {}) })}\n\`\`\`` };
    f.comments = [f.claim];
  };
  f.resetClaim();
  const origin = { repository: repo, coordinatorId: 'old', machine: 'machine-a', claim: { commentId: '901', labelEventId: '701' } };
  if (existing) { const run = f.record(); run.automaticOrigin = origin; writeRun(run, { stateDir: join(dir, 'index'), env: { HOME: home } }); }
  else writeRun({ v: 1, number: 17, repo, runDir, commonDir, sourceRoot: cwd, root: cwd, issue: { url: issue }, state: 'running', automaticOrigin: origin,
    areas: [{ name: 'code', steps: ['build'], optional: [] }], area: 0, chats: [], done: { build: { summary: 'Finished work', at: NOW - hour } } }, { stateDir: join(dir, 'index'), env: { HOME: home } });
  const agent = { id: 'codex', kind: 'codex', command: 'codex' };
  const profile = { agent: { id: 'codex', kind: 'codex' }, home, definitionHome: home, configHome: null };
  f.saveState({ enabled: true, cwd, repo, stateFile: f.stateFile, coordinatorId: 'new', machine: 'machine-a', activatedAt: at(NOW - 8 * hour),
    agent, environment: { HOME: home }, definitionHome: home, recipeDelivered: true, packageRoot,
    paneId: 'p1', workspaceId: 'w1', ownerLaunch: { paneId: 'p1', startedAt: NOW - hour, coordinator: { version: 'pdd.autopilot-coordinator.v1', repository: repo, coordinatorId: 'new', machine: 'machine-a', activation: at(NOW - 8 * hour) }, profile } });
  f.execFile = async (command, args, options = {}) => {
    if (command === 'git') return { code: 0, stdout: execFileSync(command, args, { cwd: options.cwd ?? cwd, encoding: 'utf8' }) };
    if (command === 'herdr' || command === 'gh' && args[0] === 'auth') return { code: 0, stdout: '' };
    if (command === 'gh' && args[0] === 'repo') return { code: 0, stdout: JSON.stringify({ nameWithOwner: repo, defaultBranchRef: { name: 'main' }, url: `https://github.com/${repo}` }) };
    assert.equal(command, 'gh'); assert.equal(args[0], 'api');
    const endpoint = args[4], method = args[3]; let value;
    if (endpoint === `repos/${repo}`) value = { owner: { login: 'example' } };
    else if (endpoint === `repos/${repo}/collaborators?per_page=100`) value = [];
    else if (endpoint === `repos/${repo}/issues/17`) value = { labels: f.issueLabels ?? [{ name: 'pdd:working' }] };
    else if (endpoint === `repos/${repo}/issues/17/timeline?per_page=100`) value = f.events;
    else if (endpoint === `repos/${repo}/issues/17/comments?per_page=100`) value = f.comments;
    else if (endpoint === `repos/${repo}/issues/comments/901`) {
      if (method === 'PATCH') {
        f.beforePatch?.();
        const { body } = JSON.parse(options.input); f.writes.push({ method, body });
        Object.assign(f.claim, { body, updated_at: at(f.time) });
        if (f.losePatch) { f.losePatch = false; throw Error('Lost accepted PATCH reply'); }
      }
      value = f.claim;
    } else if (endpoint === `repos/${repo}/issues/17/comments` && method === 'POST') {
      value = { id: 1000 + f.comments.length, user: { login: 'example' }, created_at: at(f.time), ...JSON.parse(options.input) };
      f.comments.push(value); f.writes.push({ method, body: value.body });
      if (f.losePost) { f.losePost = false; throw Error('Lost accepted POST reply'); }
    } else throw Error(`Unexpected fake endpoint ${method} ${endpoint}`);
    return { code: 0, stdout: `HTTP/1.1 200 OK\n\n${JSON.stringify(value)}` };
  };
  f.ports = { ...healthyMachine, checkCapacityPorts: isolatedCheckCapacity(dir), env: { HOME: home }, stateRoot, stateDir: join(dir, 'index'), now: () => f.time, run: f.execFile, execFile: f.execFile,
    allocationCheck: async () => ({ state: 'ready' }), pathDiagnostic: () => [], selectAgent: async () => agent, timer: async () => true,
    allRuns: () => [], readRunProgress: async () => [], queryIssues: async () => ({ status: 304 }), warn: text => f.warnings.push(text),
    reconcileDependencyIntake: async () => {
      const value = metadata(f.claim), expired = f.time - Date.parse(f.claim.updated_at) >= 4 * hour;
      return { eligible: [], queued: [], skipped: [], claims: [{ issue, owner: value.coordinatorId, coordinatorId: value.coordinatorId, machine: value.machine,
        commentId: '901', labelEventId: value.labelEventId, active: !expired, ...(expired ? { expired: true } : {}), lastSeen: f.claim.updated_at }] };
    },
    herdr: async args => {
      if (args[0] === 'status') return { running: true };
      if (args[0] === 'workspace') { f.activePane = 'p2'; return { result: { workspace: { workspace_id: 'w2' }, root_pane: { pane_id: 'p2' } } }; }
      const pane = { pane_id: args[2], workspace_id: args[2] === 'p1' ? 'w1' : 'w2', cwd, foreground_cwd: cwd, tab_id: 'tab', terminal_id: args[2], agent: 'codex', agent_status: 'idle', agent_session: 'session' };
      if (args[0] === 'pane' && args[1] === 'get') return { result: { type: 'pane_info', pane } };
      if (args[0] === 'agent' && args[1] === 'get') {
        if (args[2] === 'p2' && !f.launched) throw Object.assign(Error('agent_not_found'), { code: 'agent_not_found' });
        return { result: { type: 'agent_info', agent: pane } };
      }
      if (args[0] === 'pane' && args[1] === 'run') { f.launched = true; f.launches.push(args); }
      if (args[0] === 'pane' && args[1] === 'read') return '';
      return {};
    } };
  const initial = f.state(); initial.ownerLaunch.fingerprint = autopilotLaunchFingerprint(initial); f.saveState(initial);
  f.tick = () => tickAutopilot(f.stateFile, f.ports);
  f.start = extra => runAutopilotLauncher({ command: 'start', cwd, env: { HOME: home, PATH: process.env.PATH }, packageRoot, issues: [], ...extra }, f.ports);
  return f;
}


for (const changedOwner of [false, true]) test(`release restart: open run keeps its claim and resumes its chat (owner changed: ${changedOwner})`, async t => {
  const runner = await runnerFixture(t, {agent: 'claude'});
  runner.clock = NOW - hour;
  assert.equal((await runner.run()).exitCode, 0);
  assert.equal((await runStatus({ref: '17', cwd: runner.source}, runner.ports)).exitCode, 0);
  const before = runner.record(), chat = before.chats.at(-1);
  runner.herdr.paneOf(chat).agent = null;
  runner.herdr.calls.length = 0;
  runner.clock = NOW;
  const f = world(t, runner), coordinatorHerdr = f.ports.herdr;
  if (!changedOwner) {
    const state = f.state(); state.coordinatorId = 'old';
    state.ownerLaunch.coordinator.coordinatorId = 'old'; f.saveState(state);
  }
  Object.assign(f.ports, {findNativeSessions: runner.ports.findNativeSessions,
    layoutDirectory: runner.ports.layoutDirectory, autopilotStateRoot: f.stateRoot,
    workflowHerdr: runner.herdr.herdr,
    herdr: args => ['p1', 'p2'].includes(args[2]) ? coordinatorHerdr(args) : runner.herdr.herdr(args)});
  const finished = f.record().done;
  assert.equal((await f.tick()).exitCode, 0);
  const after = f.record(), owner = changedOwner ? 'new' : 'old';
  assert.equal(metadata(f.claim).coordinatorId, owner);
  assert.equal(metadata(f.claim).lastSeen, at(NOW));
  assert.equal(after.automaticOrigin.coordinatorId, owner);
  assert.deepEqual(after.automaticOrigin.claim, {commentId: '901', labelEventId: '701'});
  assert.equal(f.comments.length, 1);
  assert.deepEqual(after.done, finished);
  assert.equal(after.runId, before.runId);
  assert.equal(after.chats.at(-1).session.id, chat.session.id);
  assert.equal(runner.herdr.calls.filter(args => args[0] === 'pane' && args[1] === 'run').length, 1,
    `same-tick chat recovery must follow claim recovery: ${f.warnings.join('; ')}`);
  runner.herdr.calls.length = 0;
  f.time += 1000; runner.clock = f.time;
  await f.tick();
  assert.equal(runner.herdr.calls.filter(args => args[0] === 'pane' && args[1] === 'run').length, 0);
});

test('start again with open runs retains the repository owner when capacity replaces the coordinator pane', async t => {
  const f = world(t); const state = f.state(); state.coordinatorId = 'old'; state.recipeDelivered = false;
  state.ownerLaunch.coordinator.coordinatorId = 'old'; f.saveState(state);
  const finished = f.record().done;
  const result = await f.start({ runs: '2' });
  assert.equal(result.exitCode, 0, result.message);
  assert.equal(f.state().coordinatorId, 'old', 'a replacement chat keeps the claim owner');
  assert.equal(f.record().automaticOrigin.coordinatorId, 'old');
  assert.equal(metadata(f.claim).lastSeen, at(NOW), 'open run receives a heartbeat');
  assert.deepEqual(f.record().done, finished);
});

for (const reason of ['crash', 'machine restart']) test(`${reason}: a new tick recovers a stranded live claim and preserves finished steps`, async t => {
  const f = world(t), finished = f.record().done;
  if (reason === 'machine restart') {
    const state = f.state(); state.recipeDelivered = false; f.saveState(state);
    const herdr = f.ports.herdr;
    f.ports.herdr = args => {
      if (args[2] === 'p1' && ['agent', 'pane'].includes(args[0]) && args[1] === 'get')
        throw Object.assign(Error('pane_not_found'), { code: 'pane_not_found' });
      return herdr(args);
    };
  }
  assert.equal((await f.tick()).exitCode, 0);
  if (reason === 'machine restart') assert.equal(f.state().paneId, 'p2', 'the vanished pane is replaced');
  assert.equal(f.record().automaticOrigin.coordinatorId, 'new', JSON.stringify(f.warnings));
  assert.equal(metadata(f.claim).coordinatorId, 'new');
  assert.deepEqual(f.record().done, finished);
  assert.deepEqual(metadata(f.claim).extra, { preserved: true });
  assert.ok(f.claim.body.startsWith(f.claimProse));
  f.time += hour; assert.equal((await f.tick()).exitCode, 0);
  assert.equal(metadata(f.claim).lastSeen, at(f.time));
  assert.equal(f.comments.length, 1, 'live recovery needs no expiry comment');
});

test('expired coordinator-change claim is recovered once with one comment and matching run custody', async t => {
  const f = world(t); f.resetClaim({ seen: NOW - 5 * hour });
  assert.equal((await f.tick()).exitCode, 0);
  assert.equal(f.record().automaticOrigin.coordinatorId, 'new');
  assert.equal(metadata(f.claim).coordinatorRestartRecoveredAt, at(NOW));
  assert.equal(f.comments.length, 2);
  f.time += hour; await f.tick(); assert.equal(f.comments.length, 2);
  const state = f.state(); state.coordinatorId = 'third'; f.saveState(state); f.time += 5 * hour;
  await f.tick();
  assert.equal(f.record().automaticOrigin.coordinatorId, 'new', 'a second expired recovery is refused');
  assert.equal(f.comments.length, 2);
});

// Keep the existing takeover ceiling. Recovery changes no label era and adds
// no takeover, but a claim already beyond the ceiling must remain blocked.
for (const count of [0, 1, 2, 3, 4]) test(`expired recovery preserves the takeover boundary at ${count}`, async t => {
  const f = world(t); f.resetClaim({ seen: NOW - 5 * hour });
  const earlier = [];
  for (let n = 0; n < count; n++) {
    const start = NOW - (8 + 6 * (count - n)) * hour, event = 501 + 2 * n;
    earlier.push({ id: event, event: 'labeled', label: { name: 'pdd:working' }, actor: { login: 'example' }, created_at: at(start) },
      { id: event + 1, event: 'unlabeled', label: { name: 'pdd:working' }, actor: { login: 'example' }, created_at: at(start + 6 * hour) });
    f.comments.push({ id: 800 + n, user: { login: 'example' }, created_at: at(start), updated_at: at(start + hour), body: JSON.stringify({ repository: repo,
      coordinatorId: `previous-${n}`, machine: `previous-machine-${n}`, labelEventId: String(event), lastSeen: at(start + hour) }) });
  }
  f.events = [...earlier, ...f.events];
  await f.tick();
  assert.equal(f.record().automaticOrigin.coordinatorId, count <= 3 ? 'new' : 'old');
  assert.equal(f.writes.filter(row => row.method === 'POST').length, count <= 3 ? 1 : 0);
});

test('recovery preserves a takeover from the target coordinator and later self re-claims', async t => {
  const f = world(t); f.resetClaim({ seen: NOW - 5 * hour });
  const priorStart = NOW - 14 * hour;
  f.events.unshift({ id: 501, event: 'labeled', label: { name: 'pdd:working' }, actor: { login: 'example' }, created_at: at(priorStart) },
    { id: 502, event: 'unlabeled', label: { name: 'pdd:working' }, actor: { login: 'example' }, created_at: at(NOW - 8 * hour) });
  f.comments.push({ id: 800, user: { login: 'example' }, created_at: at(priorStart), updated_at: at(priorStart + hour),
    body: JSON.stringify({ repository: repo, coordinatorId: 'new', machine: 'machine-a', labelEventId: '501', lastSeen: at(priorStart + hour) }) });
  const observed = async () => JSON.parse((await createDependencyReadPorts({ cwd: f.cwd }, { ...f.ports, autopilotStateRoot: f.stateRoot }).owners.read({ repository: repo, issues: [issue] })).json).claims[0];
  assert.equal((await observed()).takeovers, 1);
  await f.tick();
  assert.equal(f.record().automaticOrigin.coordinatorId, 'new');
  assert.equal((await observed()).takeovers, 1, 'changing the current coordinator preserves the earlier takeover');
  f.time += 5 * hour;
  f.events.push({ id: 702, event: 'unlabeled', label: { name: 'pdd:working' }, actor: { login: 'example' }, created_at: at(f.time) },
    { id: 703, event: 'labeled', label: { name: 'pdd:working' }, actor: { login: 'example' }, created_at: at(f.time) });
  f.comments.push({ id: 902, user: { login: 'example' }, created_at: at(f.time), updated_at: at(f.time),
    body: JSON.stringify({ repository: repo, coordinatorId: 'new', machine: 'machine-a', labelEventId: '703', lastSeen: at(f.time) }) });
  assert.equal((await observed()).takeovers, 1, 'the recovered owner taking back its own claim adds no takeover');
});

for (const lost of ['losePatch', 'losePost']) test(`recovery retries after ${lost} without duplicate comments or lost custody`, async t => {
  const f = world(t); f.resetClaim({ seen: NOW - 5 * hour }); f[lost] = true;
  await f.tick();
  assert.equal(f.record().automaticOrigin.coordinatorId, 'old');
  await f.tick();
  assert.equal(f.record().automaticOrigin.coordinatorId, 'new');
  assert.equal(f.comments.length, 2);
});

for (const expired of [false, true]) test(`another machine's ${expired ? 'expired' : 'live'} claim wins after restart`, async t => {
  const f = world(t); f.resetClaim({ owner: 'other', machine: 'machine-b', seen: NOW - (expired ? 5 : 1) * hour, event: '703' });
  const before = structuredClone(f.record().automaticOrigin);
  await f.tick();
  assert.deepEqual(f.record().automaticOrigin, before);
  assert.equal(f.writes.length, 0);
  assert.equal(metadata(f.claim).coordinatorId, 'other');
});

test('a stale intake cannot recover a claim another machine took in the meantime', async t => {
  const f = world(t), intake = await f.ports.reconcileDependencyIntake();
  f.ports.reconcileDependencyIntake = async () => intake;
  f.resetClaim({ owner: 'other', machine: 'machine-b', event: '703' });
  await f.tick();
  assert.equal(f.record().automaticOrigin.coordinatorId, 'old');
  assert.equal(metadata(f.claim).coordinatorId, 'other');
  assert.equal(f.writes.length, 0);
});

test('a legacy structured claim remains readable and gains a heartbeat during recovery', async t => {
  const f = world(t), value = metadata(f.claim); delete value.lastSeen;
  f.claim.body = `${f.claimProse}\n\n\`\`\`json\n${JSON.stringify(value)}\n\`\`\``;
  await f.tick();
  assert.equal(f.record().automaticOrigin.coordinatorId, 'new');
  assert.equal(metadata(f.claim).lastSeen, at(NOW));
  assert.deepEqual(metadata(f.claim).extra, { preserved: true });
  assert.ok(f.claim.body.startsWith(f.claimProse));
});

test('coordinator recovery leaves a claim stuck for four hours to expire', async t => {
  const f = world(t); f.resetClaim({ seen: NOW - 5 * hour });
  f.issueLabels = [{ name: 'pdd:working' }, { name: 'pdd:stuck' }];
  f.events.push({ id: 801, event: 'labeled', label: { name: 'pdd:stuck' }, actor: { login: 'example' }, created_at: at(NOW - 4 * hour) });
  await f.tick();
  assert.equal(f.record().automaticOrigin.coordinatorId, 'old');
  assert.equal(f.writes.length, 0);
});

for (const legacy of [false, true]) test(`another machine wins a recovery race without changing ${legacy ? 'legacy' : 'heartbeat'} expiry history`, async t => {
  const f = world(t); f.resetClaim({ seen: NOW - 5 * hour });
  if (legacy) {
    const value = metadata(f.claim); delete value.lastSeen;
    f.claim.body = `${f.claimProse}\n\n\`\`\`json\n${JSON.stringify(value)}\n\`\`\``;
  }
  f.beforePatch = () => { f.events.push({ id: 702, event: 'unlabeled', label: { name: 'pdd:working' }, actor: { login: 'example' }, created_at: at(NOW) },
    { id: 703, event: 'labeled', label: { name: 'pdd:working' }, actor: { login: 'example' }, created_at: at(NOW) });
    f.comments.push({ id: 902, user: { login: 'example' }, created_at: at(NOW), updated_at: at(NOW), body: JSON.stringify({ repository: repo, coordinatorId: 'other', machine: 'machine-b', labelEventId: '703', lastSeen: at(NOW) }) }); };
  await f.tick();
  assert.equal(f.record().automaticOrigin.coordinatorId, 'old');
  assert.equal(f.comments.length, 2);
  const current = JSON.parse((await createDependencyReadPorts({ cwd: f.cwd }, { ...f.ports, autopilotStateRoot: f.stateRoot }).owners.read({ repository: repo, issues: [issue] })).json).claims[0];
  assert.equal(current.coordinatorId, 'other');
  assert.equal(current.takeovers ?? 0, legacy ? 0 : 1, 'the recovery edit preserves the prior expiry rule');
});

// Use the existing workflow fake to reach actual workflow done / PR publication.
test('workflow done publishes finished work after the tick recovers its expired claim', async t => {
  const runner = await runnerFixture(t, { name: 'small-change', agent: 'codex' });
  runner.ports.env = { HOME: runner.ports.env.HOME, PDD_INTERPRETER_QUEUE: runner.ports.env.PDD_INTERPRETER_QUEUE };
  assert.equal((await startRun({ name: 'small-change', issue: '17', agent: 'codex', cwd: runner.source, packageRoot }, runner.ports)).exitCode, 0);
  const run = runner.record(); runner.tick();
  await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, runner.agentPorts());
  runner.tick(); assert.equal((await approveRun({ ref: '17', cwd: runner.source }, runner.ports)).exitCode, 0);
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n'); runner.git(run.root, 'commit', '-qam', 'two');
  for (const step of ['change', 'verify']) { runner.tick(); assert.equal((await stepDone({ step, summary: step, cwd: run.root }, runner.agentPorts())).exitCode, 0); }
  const f = world(t, runner); f.resetClaim({ seen: NOW - 5 * hour });
  const originalExec = runner.ports.execFile;
  const ports = () => runner.agentPorts({ autopilotStateRoot: f.stateRoot, execFile: (file, args, opts) => file === 'gh' && (args[0] === 'repo' || args[1] === '--include') ? f.execFile(file, args, opts) : originalExec(file, args, opts) });
  const refused = await stepDone({ step: 'formal', summary: 'formal', cwd: run.root }, ports());
  assert.equal(refused.exitCode, 1); assert.equal(runner.pushes.length, 0);
  await f.tick();
  const opened = await stepDone({ step: 'formal', summary: 'formal', cwd: run.root }, ports());
  assert.equal(opened.exitCode, 0, opened.message);
  assert.equal(runner.pushes.length, 1); assert.equal(runner.prs.length, 1);
});
