import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {existsSync, readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {healthyMachine} from './helpers/healthy-machine.mjs';
import {isolatedCheckCapacity} from './helpers/check-machine.mjs';
import {tickAutopilot, runAutopilotLauncher} from '../src/autopilot-launcher.mjs';
import {runStatus, parkAutomaticRun, changeRun, startRun, openRun} from '../src/workflow-runner.mjs';
import {createDependencyReadPorts} from '../src/issue-dependencies-github.mjs';
import {checkDependencyStart} from '../src/issue-dependencies-intake.mjs';

const save = (f, run) => writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
const launches = f => f.herdr.calls.filter(args => args[0] === 'pane' && args[1] === 'run');
const deliveries = f => f.herdr.calls.filter(args => args[0] === 'agent' && args[1] === 'prompt');
async function setup(t, agent = 'claude') {
  const f = await fixture(t, {agent});
  assert.equal((await f.run()).exitCode, 0);
  assert.equal((await runStatus({ref: '17', cwd: f.source}, f.ports)).exitCode, 0);
  const run = f.record();
  run.automaticOrigin = {repository: run.repo, coordinatorId: 'park-owner', machine: 'park-machine', claim: {commentId: '11', labelEventId: '12'}};
  save(f, run);
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto', trust: []}}));
  const stateFile = join(f.state, 'launcher.json');
  writeFileSync(stateFile, JSON.stringify({enabled: true, defaultBranch: 'main', baseBranch: 'main', stateFile,
    cwd: f.source, repo: run.repo, packageRoot, runs: 1, coordinatorId: 'park-owner', machine: 'park-machine', activatedAt: 1,
    agent: {id: agent, kind: agent, command: agent}, environment: f.ports.env, retryAt: f.clock + 86400000}));
  const warnings = [];
  const ports = {...healthyMachine, ...f.ports, sendDigest: async () => ({exitCode: 0}),
    checkCapacityPorts: isolatedCheckCapacity(f.base), run: async (file, args, options) => ({code: 0, ...await f.ports.execFile(file, args, options)}),
    warn: message => warnings.push(message)};
  f.herdr.calls.length = 0;
  return {f, run, stateFile, ports, warnings, tick: () => tickAutopilot(stateFile, ports)};
}
for (const agent of ['claude', 'codex']) for (const kind of ['interpreter', 'person', 'pdd'])
  test(`3091 releases blocked ${kind} resources and retains ${agent} disk custody`, async t => {
    const {f, run, tick, warnings, stateFile} = await setup(t, agent);
    const held = f.record();
    if (kind === 'interpreter') {held.state = 'paused'; held.runtimeWait = {at: f.clock, reason: 'no verdict', cause: 'service', batch: null};}
    if (kind === 'person') {held.state = 'waiting'; held.question = {at: f.clock, text: 'Choose the case'};}
    if (kind === 'pdd') {held.state = 'paused'; held.blockedOn = {kind: 'pdd', until: '99.0.0'};}
    save(f, held);
    await tick();
    assert.deepEqual(warnings, []);
    assert.equal(f.herdr.panes.filter(pane => pane.workspace_id === run.layout.workspaceId).length, 0,
      '3091: blocked run must use no chat or shell pane');
    const parked = f.record();
    assert.equal(parked.parking?.phase, 'parked');
    for (const key of ['runId', 'root', 'branch', 'done', 'gate', 'question', 'runtimeWait', 'automaticOrigin'])
      assert.deepEqual(parked[key], held[key], `parking preserves ${key}`);
    assert.equal(parked.chats.at(-1).session.id, held.chats.at(-1).session.id);
    assert.ok(existsSync(run.root)); assert.ok(existsSync(join(run.runDir, 'status.json')));
    assert.deepEqual(JSON.parse(readFileSync(stateFile)).parking.working, 0);
    assert.equal(JSON.parse(readFileSync(stateFile)).parking.parked, 1);
    await tick(); assert.equal(launches(f).length, 0, 'blocked sessions must stay closed across ticks');
  });

test('3091 confirmed parked occupancy backfills native admission and refuses a duplicate run', async t => {
  const {f, tick} = await setup(t);
  const held = f.record(); held.state = 'paused'; held.runtimeWait = {at: f.clock, reason: 'no verdict', cause: 'service'}; save(f, held);
  await tick();
  const owners = JSON.parse((await createDependencyReadPorts({cwd: f.source}, {...f.ports}).owners.read({repository: held.repo, issues: []})).json);
  const old = owners.runs.find(row => row.runId === held.runId);
  assert.equal(old?.occupied, false, '3091: parked claims must free capped capacity');
  const repository = held.repo, issue = `https://github.com/${repository}/issues/18`, revision = 'a'.repeat(64);
  const coordinator = {repository, coordinatorId: 'park-owner', machine: 'park-machine', activation: 1, runs: 1, claim: {commentId: '1', labelEventId: '2'}};
  const ports = {
    settings: {read: async () => ({mode: 'auto', activation: 1, runs: 1})},
    owners: {read: async () => ({json: JSON.stringify({...owners, localOwner: 'park-owner', claims: [{issue, owner: 'park-owner', coordinatorId: 'park-owner', machine: 'park-machine', commentId: '1', labelEventId: '2', active: true}]})})},
    snapshots: {read: async () => ({snapshot: {repository, complete: true, issues: [{key: issue, nodeId: '18', title: 'Independent work', revision, state: 'open', authority: 'trusted', assignees: [], conditions: [], execution: 'idle', holds: []}], edges: [], reviews: [{id: 'r', issue, authority: 'trusted', intact: true, outcome: 'complete', analysis: 'Independent', base: [], continuation: '', inputs: [{key: issue, revision}], candidates: [{key: issue, revision}], dependencies: [], questions: [], effects: 'none'}], impacts: [], inputs: []}})},
  };
  assert.equal((await checkDependencyStart({repository, issue, coordinator}, ports)).allowed, true);
  ports.settings.read = async () => ({mode: 'auto', activation: 1, runs: 1, parkingWakePending: [17]});
  assert.equal((await checkDependencyStart({repository, issue, coordinator}, ports)).reason, 'runs', 'ready parked wakes must precede native fresh admission');
  ports.settings.read = async () => ({mode: 'auto', activation: 1, runs: 1});
  // Its own run is already saved. It must go through resume, even with a free slot.
  ports.owners.read = async () => ({json: JSON.stringify({...owners, localOwner: 'park-owner', claims: [{issue: held.issue.url, owner: 'park-owner', coordinatorId: 'park-owner', machine: 'park-machine', commentId: '1', labelEventId: '2', active: true}]})});
  assert.equal((await checkDependencyStart({repository, issue: held.issue.url, coordinator}, ports)).allowed, false);
});

for (const damage of ['session', 'terminal', 'foreign', 'process', 'check']) test(`3091 unknown ${damage} custody remains occupied`, async t => {
  const {f, tick, ports} = await setup(t);
  const held = f.record(); held.state = 'waiting'; held.question = {at: f.clock, text: 'Choose the case'};
  if (damage === 'session') held.chats.at(-1).session = null;
  if (damage === 'terminal') f.herdr.paneOf(held.chats.at(-1)).terminal_id = 'unrelated';
  if (damage === 'foreign') held.automaticOrigin.coordinatorId = 'other';
  if (damage === 'process') {const pane = f.herdr.paneOf(held.chats.at(-1)); pane.agent = null; pane.processInfo = {pane_id: pane.pane_id, shell_pid: 100, foreground_process_group_id: 999, foreground_processes: [{pid: 999, name: 'unrelated'}]};}
  if (damage === 'check') ports.readSuiteProgress = () => ({state: 'running', pausedMs: 0});
  save(f, held); await tick();
  assert.ok(f.herdr.panes.some(pane => pane.workspace_id === held.layout.workspaceId));
  assert.notEqual(f.record().parking?.phase, 'parked');
});

for (const agent of ['claude', 'codex']) test(`3091 recorded reply reopens the same ${agent} session once`, async t => {
  const {f, tick, warnings} = await setup(t, agent);
  const held = f.record(); held.state = 'waiting'; held.question = {at: f.clock, text: 'Choose the case'}; save(f, held);
  await tick();
  assert.equal(f.record().parking?.phase, 'parked', '3091: reply test requires a resource-free park');
  const result = await changeRun({ref: '17', cwd: f.source, text: 'Use the first case', packageRoot}, f.ports);
  assert.equal(result.exitCode, 0, result.message);
  assert.deepEqual(warnings, []);
  assert.equal(launches(f).length, 1);
  assert.equal(f.record().chats.at(-1).session.id, held.chats.at(-1).session.id);
  assert.equal(f.record().parking, undefined);
  assert.equal(deliveries(f).length, 1);
  await tick(); assert.equal(launches(f).length, 1); assert.equal(deliveries(f).length, 1);
});

test('3091 explicit installed-release and reset blockers are stored with clearing evidence', async t => {
  const {f} = await setup(t);
  for (const [blocker, until] of [['pdd', '99.0.0'], ['dependency', '2897'], ['account', '2026-11-10T12:00:00Z']]) {
    const result = await parkAutomaticRun({cwd: f.record().root, reason: 'Controlled external wait', blocker, until}, {...f.ports, owners: {read: async () => ({json: JSON.stringify({localOwner: 'park-owner', runsKnown: true, runs: [], claims: [{issue: f.record().issue.url, active: true, owner: 'park-owner', coordinatorId: 'park-owner', machine: 'park-machine', commentId: '11', labelEventId: '12'}]})})}});
    assert.equal(result.exitCode, 0, result.message);
    assert.deepEqual(f.record().blockedOn, {kind: blocker, until}, '3091: preserve the explicit clearing condition');
  }
});

async function anotherRun(f, number) {
  const execute = f.ports.execFile;
  f.ports.execFile = async (file, args, options) => {
    if (file === 'gh' && args[0] === 'api' && args[1] === `repos/example/project/issues/${number}`)
      return {stdout: JSON.stringify({number, html_url: `https://github.com/example/project/issues/${number}`, title: 'Independent work', body: 'Use another value.'})};
    return execute(file, args, options);
  };
  assert.equal((await startRun({name: 'small-change', issue: String(number), agent: 'claude', cwd: f.source, packageRoot}, f.ports)).exitCode, 0);
  assert.equal((await runStatus({ref: String(number), cwd: f.source}, f.ports)).exitCode, 0);
  const path = join(f.record().commonDir, 'pdd', 'runs', String(number), 'status.json');
  const run = JSON.parse(readFileSync(path)); run.automaticOrigin = f.record().automaticOrigin;
  run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: '99.0.0'};
  save(f, run);
  return () => JSON.parse(readFileSync(path));
}

test('3091 installed release wakes oldest first and holds other ready wakes for the working cap', async t => {
  const {f, tick, ports, stateFile, warnings} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: '99.0.0'}; save(f, run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  const other = await anotherRun(f, 18); f.tick(1000); await tick();
  assert.equal(other().parking?.phase, 'parked');
  f.herdr.calls.length = 0; ports.packageVersion = '99.0.0'; await tick();
  assert.equal(launches(f).length, 1);
  assert.equal(f.record().parking, undefined, 'oldest run must resume first');
  assert.equal(other().parking.phase, 'parked');
  const summary = JSON.parse(readFileSync(stateFile)).parking;
  assert.deepEqual([summary.working, summary.parked, summary.wakePending], [1, 1, [18]]);
  await tick(); assert.equal(launches(f).length, 1, 'cap must hold the other wake');
});

test('3091 failed resume reserves capacity and retries the same saved session', async t => {
  const {f, tick, ports, stateFile, warnings} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: '99.0.0'}; save(f, run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  const herdr = ports.herdr; let fail = true;
  ports.herdr = async args => {if (fail && args[0] === 'pane' && args[1] === 'run') {fail = false; throw Object.assign(Error('unsent fixture resume'), {code: 'agent_not_found'});} return herdr(args);};
  ports.packageVersion = '99.0.0'; await tick();
  assert.equal(f.record().parking?.phase, 'waking');
  assert.equal(JSON.parse(readFileSync(stateFile)).parking.working, 1);
  f.tick(60001); await tick();
  assert.equal(f.record().parking, undefined, JSON.stringify({warnings, chat: f.record().chats.at(-1), failure: f.record().chatFailure}));
  assert.equal(f.record().chats.at(-1).session.id, run.chats.at(-1).session.id);
});

test('3091 health pause keeps ready parked sessions closed', async t => {
  const {f, tick, ports} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: '99.0.0'}; save(f, run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  ports.packageVersion = '99.0.0'; ports.machineHealth = async () => ({healthy: false, causes: ['controlled memory pressure'], resources: null});
  await tick();
  assert.equal(f.record().parking.phase, 'parked'); assert.equal(launches(f).length, 0);
});

function fullTicks(f, stateFile, ports) {
  const state = JSON.parse(readFileSync(stateFile)); delete state.retryAt; state.recipeDelivered = true;
  writeFileSync(stateFile, JSON.stringify(state));
  ports.reconcileDependencyIntake = async () => ({eligible: [], claims: [], groups: [], queued: [], skipped: []});
  ports.queryIssues = async () => ({status: 200, issues: []});
  ports.comments = async () => [];
  const herdr = ports.herdr;
  ports.herdr = async args => {
    if (args[0] === 'pane' && args[1] === 'get') {
      const pane = f.herdr.panes.find(pane => pane.pane_id === args[2]);
      if (!pane) throw Object.assign(Error('pane_not_found'), {code: 'pane_not_found'});
      return {result: {type: 'pane_info', pane: {...pane, foreground_cwd: pane.cwd, ...pane.agent}}};
    }
    return herdr(args);
  };
  ports.runtimeHealth = async () => ({state: 'healthy', detail: 'controlled health'});
  ports.sendAlert = async () => ({exitCode: 0});
}

test('3091 park timeout releases once, keeps branch and returns local allocation to the existing queue', async t => {
  const {f, tick, stateFile, ports, warnings} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: '99.0.0'}; save(f, run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  fullTicks(f, stateFile, ports);
  let releases = 0; ports.releaseParkedClaim = async input => {releases++; assert.equal(input.branch, run.branch); return {state: 'released'};};
  f.tick(48 * 3600000 - 1); await tick(); assert.equal(releases, 0);
  f.tick(1); await tick();
  assert.equal(releases, 1); assert.equal(f.record().state, 'cancelled', JSON.stringify(warnings));
  assert.ok(existsSync(run.root)); assert.ok(f.git(f.source, 'rev-parse', '--verify', run.branch));
  assert.equal(existsSync(join(run.commonDir, 'pdd/worktree-assignments/issues/17.json')), false);
  await tick(); assert.equal(releases, 1);
});

test('3091 parked-count limit releases the oldest surplus run', async t => {
  const {f, tick, stateFile, ports} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: '99.0.0'}; save(f, run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  const other = await anotherRun(f, 18); f.tick(); await tick(); assert.equal(other().parking?.phase, 'parked');
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto', trust: [], parking: {maxParked: 1}}}));
  fullTicks(f, stateFile, ports);
  const released = []; ports.releaseParkedClaim = async input => {released.push(input.runId); return {state: 'released'};};
  await tick(); assert.deepEqual(released, [run.runId]); assert.equal(other().parking.phase, 'parked');
});

test('3091 same-group intake joins the existing journal without restoring a blocked chat', async t => {
  const {f, tick, stateFile, ports, warnings} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: '99.0.0'}; save(f, run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  fullTicks(f, stateFile, ports);
  const issue = {number: 18, html_url: 'https://github.com/example/project/issues/18', title: 'Same cause', body: 'Same problem', state: 'open', labels: ['pdd:autopilot'], user: {login: 'example'}, comments: 0, updated_at: new Date(f.clock).toISOString()};
  ports.queryIssues = async () => ({status: 200, issues: [issue]});
  ports.reconcileDependencyIntake = async () => ({eligible: [issue.html_url], claims: [], groups: [{members: [run.issue.url, issue.html_url], umbrella: run.issue.url, rootCause: 'shared cause'}], queued: [], skipped: []});
  await tick();
  const journal = join(run.runDir, 'delivery-journal.json');
  assert.ok(existsSync(journal), JSON.stringify(warnings));
  assert.equal(JSON.parse(readFileSync(journal)).requests.length, 1);
  assert.equal(f.record().parking.phase, 'parked'); assert.equal(launches(f).length, 0);
  await tick(); assert.equal(JSON.parse(readFileSync(journal)).requests.length, 1, 'one join across intake ticks');
  ports.packageVersion = '99.0.0'; await tick();
  assert.equal(f.record().parking, undefined);
  assert.ok(readFileSync(join(run.runDir, `${run.chats.at(-1).area}-resume.md`), 'utf8').includes(issue.html_url), 'saved group request reaches canonical resume input');
});

test('3091 interpreter test mode requires three no-verdict observations and clears on a verdict', async t => {
  const {f, tick, stateFile, ports} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.runtimeWait = {at: f.clock, reason: 'no verdict', cause: 'service'}; save(f, run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  fullTicks(f, stateFile, ports);
  let verdict = false;
  ports.readRuntimeWaits = async () => [{number: 40, at: 1, cause: 'service', mark: 'tests:1'}];
  ports.readRuntimeProbe = async () => verdict ? 'verdict' : 'pending';
  ports.runtimeHealth = async () => ({state: 'unavailable', detail: 'controlled unavailable'});
  await tick(); assert.equal(JSON.parse(readFileSync(stateFile)).interpreterPattern.testMode, undefined);
  // Keep the same first observation identity; only one extra no-verdict is new.
  ports.readRuntimeWaits = async () => [{number: 40, at: 1, cause: 'service', mark: 'tests:1'}, {number: 41, at: 2, cause: 'service', mark: 'tests:1'}];
  await tick(); assert.equal(JSON.parse(readFileSync(stateFile)).interpreterPattern.testMode, undefined);
  ports.readRuntimeWaits = async () => [40, 41, 42].map((number, i) => ({number, at: i + 1, cause: 'service', mark: 'tests:1'}));
  await tick();
  assert.equal(JSON.parse(readFileSync(stateFile)).interpreterPattern.testMode, true);
  const capacity = JSON.parse(readFileSync(join(f.ports.env.PDD_INTERPRETER_QUEUE, 'capacity.json')));
  assert.equal(Object.keys(capacity.testOwners).length, 1, 'test uses the existing interpreter queue');
  ports.runtimeHealth = async () => ({state: 'healthy', detail: 'controlled healthy'}); await tick();
  assert.equal(JSON.parse(readFileSync(stateFile)).runtime.outage.probe.number, 40);
  verdict = true; await tick();
  assert.equal(JSON.parse(readFileSync(stateFile)).interpreterPattern.testMode, false);
  assert.equal(JSON.parse(readFileSync(join(f.ports.env.PDD_INTERPRETER_QUEUE, 'capacity.json'))).testOwners, undefined);
});

test('3091 account health parks a failed chat until its actual reset', async t => {
  const {f, tick, ports} = await setup(t);
  const resetAt = f.clock + 3600000;
  ports.chatHealth = async () => ({kind: 'usage-limit', until: resetAt, message: 'controlled provider limit'});
  await tick();
  assert.equal(f.record().parking?.phase, 'parked');
  assert.equal(f.record().parking.blocker.kind, 'account');
  f.tick(3599999); await tick(); assert.equal(launches(f).length, 0);
  ports.chatHealth = async () => null; f.tick(1); await tick();
  assert.equal(f.record().parking, undefined); assert.equal(launches(f).length, 1);
});

test('3091 native release is idempotent after a lost comment reply and preserves a newer claim', async t => {
  const {f, tick} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: '99.0.0'}; save(f, run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  const {createGithubRepoFake} = await import('./helpers/github-repo-fake.mjs');
  const {releaseParkedClaim} = await import('../src/issue-dependencies-github.mjs');
  const github = createGithubRepoFake({repository: run.repo, owner: 'example', issues: 17, now: () => f.clock});
  const comment = github.claim(17, {coordinatorId: 'park-owner', machine: 'park-machine'});
  const claim = {issue: run.issue.url, coordinatorId: 'park-owner', machine: 'park-machine', commentId: comment.id, labelEventId: github.issues.get(17).timeline.at(-1).id};
  let loseReply = true;
  const ports = {...f.ports, authority: {read: async () => ({authority: 'trusted'})}, execFile: async (file, args, options) => {
    if (file !== 'gh') return f.ports.execFile(file, args, options);
    if (args.includes('DELETE') && args.some(arg => arg.endsWith('/labels/pdd%3Aworking'))) {
      github.unlabel(17, 'pdd:working'); return {code: 0, stdout: 'HTTP/2.0 204 OK\r\n\r\n'};
    }
    const reply = await github.gh(args, options);
    if (loseReply && args.includes('POST') && args.some(arg => arg.endsWith('/issues/17/comments'))) {loseReply = false; throw Error('controlled lost reply');}
    return reply;
  }};
  const input = {cwd: f.source, repository: run.repo, claim, coordinatorId: 'park-owner', machine: 'park-machine', runId: run.runId, branch: run.branch};
  await assert.rejects(releaseParkedClaim(input, ports), /controlled lost reply/);
  assert.equal((await releaseParkedClaim(input, ports)).state, 'released');
  assert.equal((await releaseParkedClaim(input, ports)).state, 'released');
  assert.equal(github.issues.get(17).comments.filter(comment => comment.body.includes('<!-- pdd:park-release:')).length, 1);
  assert.ok(!github.issues.get(17).labels.includes('pdd:working'));
  github.claim(17, {coordinatorId: 'new-owner', machine: 'other-machine'});
  assert.equal((await releaseParkedClaim(input, ports)).state, 'skipped');
  assert.ok(github.issues.get(17).labels.includes('pdd:working'));
});

test('3091 shared interpreter admission is serial in test mode and concurrent after a verdict', async t => {
  const {f, tick, stateFile, ports} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.runtimeWait = {at: f.clock, reason: 'no verdict', cause: 'service'}; save(f, run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  fullTicks(f, stateFile, ports);
  ports.readRuntimeWaits = async () => [40, 41, 42].map((number, i) => ({number, at: i + 1, cause: 'service', mark: 'tests:1'}));
  ports.runtimeHealth = async () => ({state: 'unavailable', detail: 'controlled outage'});
  await tick();
  const {acquireInterpreterSlot, observeInterpreterRequest} = await import('../src/interpreter-queue.mjs');
  const env = f.ports.env, queuePorts = {now: () => f.clock, alive: () => true, sleep: () => new Promise(resolve => setTimeout(resolve, 2))};
  const request = requestId => ({cwd: f.source, origin: 'https://controlled.invalid', requestId, kind: 'check', env});
  const settle = requestId => observeInterpreterRequest({...request(requestId), outcome: 'verdict', terminal: true}, queuePorts);
  await acquireInterpreterSlot(request('one'), queuePorts);
  let admitted = false;
  const second = acquireInterpreterSlot(request('two'), queuePorts).then(value => {admitted = true; return value;});
  t.after(async () => {await settle('one'); await second; await settle('two'); await settle('three');});
  await new Promise(resolve => setTimeout(resolve, 20));
  assert.equal(admitted, false, 'test mode must hold the second interpreter request');
  await settle('one'); await second;
  const third = await acquireInterpreterSlot(request('three'), queuePorts);
  assert.ok(third, 'after the verdict two interpreter requests can hold slots together');
});

test('3091 process shutdown follows saved-session custody and frees panes only after confirmation', async t => {
  const {f, tick, ports} = await setup(t);
  const run = f.record(); run.state = 'waiting'; run.question = {at: f.clock, text: 'Choose the case'}; save(f, run);
  const stopped = [];
  ports.processes = {closeChat: async input => {
    assert.equal(f.record().chats.find(chat => chat.paneId === input.paneId).session.id, input.sessionId);
    assert.ok(f.record().chats.find(chat => chat.paneId === input.paneId).closed, 'session custody must be saved before process shutdown');
    assert.notEqual(f.record().parking.phase, 'parked', 'slot must remain occupied before confirmed shutdown');
    stopped.push(input.sessionId); await f.herdr.herdr(['tab', 'close', input.tabId]);
  }};
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  assert.deepEqual(stopped, run.chats.map(chat => chat.session.id));
  await tick(); assert.equal(stopped.length, run.chats.length);
});

test('3091 dependency wakes only for a closed issue with a merged closing PR', async t => {
  const {f, tick, stateFile, ports} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'dependency', until: '2897'}; save(f, run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  fullTicks(f, stateFile, ports);
  let closed = false, merged = false, closing = false;
  const execute = f.ports.execFile;
  f.ports.execFile = async (file, args, options) => {
    const api = `https://api.github.com/repos/${run.repo}/pulls/23`;
    if (file === 'gh' && args[0] === 'api') {
      if (args[1] === `repos/${run.repo}/issues/2897`) return {stdout: JSON.stringify({state: closed ? 'closed' : 'open'})};
      if (args[1].endsWith('/issues/2897/timeline?per_page=100')) return {stdout: JSON.stringify([[{event: 'cross-referenced', source: {issue: {pull_request: {url: api}}}}]])};
      if (args[1] === api) return {stdout: JSON.stringify({merged, body: closing ? 'Fixes #2897' : 'Related to #2897'})};
    }
    return execute(file, args, options);
  };
  for (const advance of [() => {}, () => {closed = true;}, () => {merged = true;}]) {
    advance(); await tick(); assert.equal(f.record().parking.phase, 'parked'); assert.equal(launches(f).length, 0);
  }
  closing = true; await tick(); assert.equal(f.record().parking, undefined); assert.equal(launches(f).length, 1);
});

for (const kind of ['ci', 'review']) test(`3091 ${kind} wake needs a completed result`, async t => {
  const {f, tick, stateFile, ports} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind, until: null};
  const url = 'https://github.com/example/project/pull/23'; run.pr = [{stage: run.chats.at(-1).area, url, number: 23}]; save(f, run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  fullTicks(f, stateFile, ports);
  let done = false;
  const execute = f.ports.execFile;
  f.ports.execFile = async (file, args, options) => {
    if (file === 'gh' && args[0] === 'pr' && args[1] === 'view' && args[2] === url)
      return {stdout: JSON.stringify({state: 'OPEN', statusCheckRollup: [{status: done ? 'COMPLETED' : 'IN_PROGRESS', conclusion: done ? 'FAILURE' : null}], reviewDecision: done ? 'CHANGES_REQUESTED' : 'REVIEW_REQUIRED'})};
    return execute(file, args, options);
  };
  await tick(); assert.equal(f.record().parking.phase, 'parked'); assert.equal(launches(f).length, 0);
  done = true; await tick(); assert.equal(f.record().parking, undefined); assert.equal(launches(f).length, 1);
});

// Repair 1: AC3/AC6. A release and a reply must not both acquire the run.
test('3091 repair release serializes a reply during remote claim removal', async t => {
  const {f, tick, stateFile, ports} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: '99.0.0'}; save(f, run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  fullTicks(f, stateFile, ports);
  let reply;
  ports.releaseParkedClaim = async () => {
    reply = await changeRun({ref: '17', cwd: f.source, text: 'Continue with the saved work', packageRoot}, f.ports);
    return {state: 'released'};
  };
  f.tick(48 * 3600000); await tick();
  assert.ok(reply, 'timeout must reach the remote release');
  assert.notEqual(reply.recovery, 'resumed', 'a releasing run must refuse a concurrent reply wake');
  assert.equal(f.record().state, 'cancelled');
  assert.equal(launches(f).length, 0);
});

test('3091 repair unknown release retains custody and retries after restart', async t => {
  const {f, tick, stateFile, ports} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: '99.0.0'}; save(f, run);
  await tick(); fullTicks(f, stateFile, ports);
  let attempts = 0;
  ports.releaseParkedClaim = async () => (++attempts === 1 ? {state: 'unavailable'} : {state: 'released'});
  f.tick(48 * 3600000); await tick();
  assert.equal(f.record().parking?.phase, 'releasing', 'unknown claim release must reserve custody');
  assert.equal(JSON.parse(readFileSync(stateFile)).parking.working, 1);
  const reply = await changeRun({ref: '17', cwd: f.source, text: 'Continue with the saved work', packageRoot}, f.ports);
  assert.notEqual(reply.recovery, 'resumed'); assert.equal(launches(f).length, 0);
  assert.equal((await openRun({ref: '17', cwd: f.source, packageRoot}, f.ports)).exitCode, 1);
  await tick(); assert.equal(attempts, 2); assert.equal(f.record().state, 'cancelled');
});

// AC3: both clear in the same tick, with only one working slot.
for (const budgetDeferred of [false, true]) test(`3091 repair oldest ready interpreter wakes before younger release wait (deferred=${budgetDeferred})`, async t => {
  const {f, tick, stateFile, ports} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.runtimeWait = {at: f.clock, reason: 'no verdict', cause: 'service'}; save(f, run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  const other = await anotherRun(f, 18); f.tick(1000); await tick();
  assert.equal(other().parking?.phase, 'parked');
  fullTicks(f, stateFile, ports);
  if (budgetDeferred) {
    const state = JSON.parse(readFileSync(stateFile)); state.retryAt = f.clock + 3600000; writeFileSync(stateFile, JSON.stringify(state));
    ports.queryIssues = async () => assert.fail('GitHub reads must remain deferred');
  }
  f.herdr.calls.length = 0; ports.packageVersion = '99.0.0'; await tick();
  assert.equal(f.record().parking, undefined, 'oldest ready park must own the last slot across blocker kinds');
  assert.equal(other().parking.phase, 'parked');
  assert.equal(launches(f).length, 1);
  assert.deepEqual(JSON.parse(readFileSync(stateFile)).parking.wakePending, [18]);
});

// AC1/AC3: the park command cannot invent a completed person wait.
test('3091 repair explicit person blocker requires a pending question or gate', async t => {
  const {f, tick} = await setup(t);
  const before = f.record();
  const ports = {...f.ports, owners: {read: async () => ({json: JSON.stringify({localOwner: 'park-owner', runsKnown: true, runs: [], claims: [{issue: before.issue.url, active: true, owner: 'park-owner', coordinatorId: 'park-owner', machine: 'park-machine', commentId: '11', labelEventId: '12'}]})})}};
  const result = await parkAutomaticRun({cwd: before.root, reason: 'Need a person to decide', blocker: 'person'}, ports);
  assert.equal(result.exitCode, 1, 'unbound person blocker must be refused');
  assert.deepEqual(f.record(), before);
  const waiting = f.record(); waiting.question = {at: f.clock, text: 'Choose the case'}; save(f, waiting);
  assert.equal((await parkAutomaticRun({cwd: before.root, reason: 'Need a person to decide', blocker: 'person'}, ports)).exitCode, 0);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  await tick(); assert.equal(f.record().parking?.phase, 'parked'); assert.equal(launches(f).length, 0);
  assert.equal((await changeRun({ref: '17', cwd: f.source, text: 'Use the first case', packageRoot}, f.ports)).recovery, 'resumed');
});

test('3091 repair unbound saved person wait cannot clear without a reply', async t => {
  const {f, tick, stateFile, ports} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'person', until: null}; save(f, run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  fullTicks(f, stateFile, ports); await tick();
  assert.equal(f.record().parking?.phase, 'parked', 'absence of a question is not a recorded reply');
  assert.equal(launches(f).length, 0);
});

// AC4: use the native wait reader and real saved check batches in the fixture home.
for (const hadTestMode of [false, true]) for (const laterFailures of [0, 2, 3]) test(`3091 repair verdict cutoff excludes older failures and counts ${laterFailures} newer waits (testMode=${hadTestMode})`, async t => {
  const {f, tick, stateFile, ports} = await setup(t);
  const at = f.clock;
  const run = f.record(); run.state = 'paused'; run.runtimeWait = {at: at + 1, reason: 'no verdict', cause: 'service'}; save(f, run);
  for (const [i, number] of [18, 19, 20, 21, 22].entries()) {
    const read = await anotherRun(f, number), row = read();
    delete row.blockedOn; row.runtimeWait = {at: at + (i < 2 ? 2 * (i + 1) : i + 3), reason: 'no verdict', cause: 'service'};
    if (i >= 2 && i - 2 >= laterFailures) {delete row.runtimeWait; row.state = 'running';}
    save(f, row);
  }
  const batch = '20261108-120000-abcd', folder = join(f.ports.env.HOME, '.pdd/runtime/batches', batch);
  const {mkdirSync} = await import('node:fs'); mkdirSync(folder, {recursive: true});
  writeFileSync(join(folder, 'batch.json'), JSON.stringify({batch, root: run.root, intent: 'check', rows: [{state: 'passed', ended_at: at + 4}, {state: 'failed', ended_at: at + 2}]}));
  const state = JSON.parse(readFileSync(stateFile)); state.interpreterPattern = {streak: 2, seen: {}, observedAt: at, testMode: hadTestMode};
  if (hadTestMode) state.runtime = {outage: {since: at, first: 17, issues: [], probed: [17], probe: {number: 17, at: at + 1, offeredAt: at + 3}}};
  writeFileSync(stateFile, JSON.stringify(state)); fullTicks(f, stateFile, ports);
  ports.runtimeHealth = async () => ({state: 'unavailable', detail: 'controlled outage'});
  f.tick(10000); await tick();
  let pattern = JSON.parse(readFileSync(stateFile)).interpreterPattern;
  assert.equal(pattern.streak, laterFailures, 'only no-verdict waits after the newest verdict belong to the streak');
  assert.equal(Boolean(pattern.testMode), laterFailures >= 3);
  // The same saved waits must not reappear as new failures on another tick.
  f.tick(); await tick(); pattern = JSON.parse(readFileSync(stateFile)).interpreterPattern;
  assert.equal(pattern.streak, laterFailures); assert.equal(Boolean(pattern.testMode), laterFailures >= 3);
});

for (const changed of ['runId', 'at', 'phase']) test(`3091 repair release revalidates ${changed} after remote effects`, async t => {
  const {f, tick, stateFile, ports} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: '99.0.0'}; save(f, run);
  await tick(); fullTicks(f, stateFile, ports);
  let released = false;
  ports.releaseParkedClaim = async () => {
    released = true;
    // Model a writer that uses progress custody rather than the chat-open lock.
    const current = f.record();
    if (changed === 'runId') current.runId += '-replacement';
    if (changed === 'at') current.parking.at++;
    if (changed === 'phase') current.parking.phase = 'waking';
    save(f, current);
    return {state: 'released'};
  };
  f.tick(48 * 3600000); await tick();
  assert.equal(released, true);
  assert.notEqual(f.record().state, 'cancelled', 'changed run custody must stop local release and cancellation');
  assert.ok(existsSync(join(run.commonDir, 'pdd/worktree-assignments/issues/17.json')), 'local allocation must retain changed custody');
});

// Repair 2: AC2/AC6. Check admission can occur after chat shutdown.
for (const custody of ['native-running', 'suite-waiting', 'interpreter-unavailable']) test(`3091 repair2 post-park ${custody} retains occupancy through timeout`, async t => {
  const {f, tick, stateFile, ports} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: '99.0.0'}; save(f, run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  fullTicks(f, stateFile, ports);
  let settle;
  if (custody === 'native-running') {
    const {acquireInterpreterSlot, observeInterpreterRequest} = await import('../src/interpreter-queue.mjs');
    const request = {cwd: run.root, origin: 'https://controlled.invalid', requestId: 'post-park', kind: 'check', env: f.ports.env};
    await acquireInterpreterSlot(request, {now: () => f.clock});
    settle = () => observeInterpreterRequest({...request, outcome: 'not_sent', terminal: true}, {now: () => f.clock});
    t.after(settle);
  } else {
    const key = custody === 'suite-waiting' ? 'readSuiteProgress' : 'readInterpreterProgress';
    ports[key] = () => ({state: custody === 'suite-waiting' ? 'waiting' : 'unavailable'});
    settle = () => {delete ports[key];};
  }
  // Read admission before the next tick can save a check reservation.
  const owners = JSON.parse((await createDependencyReadPorts({cwd: f.source}, {...f.ports,
    readSuiteProgress: ports.readSuiteProgress, readInterpreterProgress: ports.readInterpreterProgress}).owners.read({repository: run.repo, issues: []})).json);
  assert.equal(owners.runs.find(row => row.runId === run.runId)?.occupied, true, 'post-park check must block native admission');
  await tick();
  assert.equal(JSON.parse(readFileSync(stateFile)).parking.working, 1, 'post-park check consumes working capacity');
  assert.equal(JSON.parse(readFileSync(stateFile)).parking.parked, 0);
  let releases = 0; ports.releaseParkedClaim = async () => {releases++; return {state: 'released'};};
  f.tick(48 * 3600000); await tick();
  assert.equal(releases, 0, 'active or uncertain checks cannot lose their claim at timeout');
  assert.notEqual(f.record().state, 'cancelled'); assert.equal(launches(f).length, 0);
  await settle(); await tick();
  assert.equal(releases, 1, 'positive idle evidence permits the overdue release');
  assert.equal(f.record().state, 'cancelled');
});

// The release boundary must protect itself even without a prior reconciliation.
test('3091 repair2 release rechecks native check custody under the run lock', async t => {
  const {f, tick} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: '99.0.0'}; save(f, run);
  await tick();
  const {acquireInterpreterSlot, observeInterpreterRequest} = await import('../src/interpreter-queue.mjs');
  const request = {cwd: run.root, origin: 'https://controlled.invalid', requestId: 'release-check', kind: 'check', env: f.ports.env};
  await acquireInterpreterSlot(request, {now: () => f.clock});
  t.after(() => observeInterpreterRequest({...request, outcome: 'not_sent', terminal: true}, {now: () => f.clock}));
  const {releaseParkedRun} = await import('../src/workflow-runner.mjs');
  let releases = 0;
  const result = await releaseParkedRun({ref: '17', cwd: f.source, runId: run.runId, at: f.record().parking.at,
    coordinatorId: 'park-owner', machine: 'park-machine'}, {...f.ports,
    releaseParkedClaim: async () => {releases++; return {state: 'released'};}});
  assert.equal(releases, 0, 'release must read current check custody before claim effects');
  assert.equal(result.recovery, 'skipped'); assert.notEqual(f.record().state, 'cancelled');
});

const parkCommandPorts = f => ({...f.ports, owners: {read: async () => ({json: JSON.stringify({
  localOwner: 'park-owner', runsKnown: true, runs: [], claims: [{issue: f.record().issue.url, active: true,
    owner: 'park-owner', coordinatorId: 'park-owner', machine: 'park-machine', commentId: '11', labelEventId: '12'}],
})})}});

// AC1/AC3. Replacing the wait must replace its clearing condition.
test('3091 repair2 park command replaces the blocker without losing session or age', async t => {
  const {f, tick, stateFile, ports} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: '99.0.0'}; save(f, run);
  await tick(); const parked = f.record();
  const result = await parkAutomaticRun({cwd: run.root, reason: 'Wait for the dependency', blocker: 'dependency', until: '2897'}, parkCommandPorts(f));
  assert.equal(result.exitCode, 0);
  ports.packageVersion = '99.0.0'; await tick();
  assert.equal(f.record().parking?.phase, 'parked', 'the old installed release cannot clear a replacement dependency');
  assert.deepEqual(f.record().parking.blocker, {kind: 'dependency', until: '2897'});
  assert.equal(f.record().parking.at, parked.parking.at);
  assert.equal(f.record().chats.at(-1).session.id, parked.chats.at(-1).session.id);
  assert.equal(launches(f).length, 0);
  fullTicks(f, stateFile, ports); ports.blockerCleared = async () => true; await tick();
  assert.equal(f.record().parking, undefined); assert.equal(launches(f).length, 1);
  assert.equal(f.record().chats.at(-1).session.id, parked.chats.at(-1).session.id);
});

test('3091 repair2 automatic wake rejects a blocker replaced during readiness observation', async t => {
  const {f, tick, stateFile, ports} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'dependency', until: '2897'}; save(f, run);
  await tick(); fullTicks(f, stateFile, ports);
  let observations = 0;
  ports.blockerCleared = async () => {
    if (++observations === 1) {
      assert.equal((await parkAutomaticRun({cwd: run.root, reason: 'Wait for another dependency', blocker: 'dependency', until: '2898'}, parkCommandPorts(f))).exitCode, 0);
    }
    return true;
  };
  await tick();
  assert.equal(f.record().parking?.phase, 'parked', 'stale readiness cannot clear the replacement blocker');
  assert.deepEqual(f.record().blockedOn, {kind: 'dependency', until: '2898'});
  assert.equal(launches(f).length, 0);
});

// AC4. Late saved verdicts reorder events already observed on a previous tick.
for (const laterFailures of [2, 3]) test(`3091 repair2 late native verdict preserves ${laterFailures} already counted newer failures`, async t => {
  const {f, tick, stateFile, ports} = await setup(t);
  const at = f.clock, run = f.record();
  run.state = 'paused'; run.runtimeWait = {at: at + 10, reason: 'no verdict', cause: 'service'}; save(f, run);
  for (let i = 1; i < laterFailures; i++) {
    const row = (await anotherRun(f, 17 + i))(); delete row.blockedOn;
    row.runtimeWait = {at: at + 10 + i, reason: 'no verdict', cause: 'service'}; save(f, row);
  }
  fullTicks(f, stateFile, ports);
  ports.runtimeHealth = async () => ({state: 'unavailable', detail: 'controlled outage'});
  const {mkdirSync} = await import('node:fs');
  const batch = '20261108-120000-abcd', folder = join(f.ports.env.HOME, '.pdd/runtime/batches', batch);
  mkdirSync(folder, {recursive: true});
  const saved = {batch, root: run.root, intent: 'check', rows: [{state: 'passed', ended_at: at + 1}]};
  writeFileSync(join(folder, 'batch.json'), JSON.stringify(saved));
  f.tick(100); await tick();
  assert.equal(JSON.parse(readFileSync(stateFile)).interpreterPattern.streak, laterFailures);
  // This verdict ended before those failures, but its result becomes visible now.
  saved.rows.push({state: 'failed', ended_at: at + 5}); writeFileSync(join(folder, 'batch.json'), JSON.stringify(saved));
  f.tick(); await tick();
  let pattern = JSON.parse(readFileSync(stateFile)).interpreterPattern;
  assert.equal(pattern.streak, laterFailures, 'a late verdict must preserve already seen post-verdict failures');
  assert.equal(Boolean(pattern.testMode), laterFailures >= 3); assert.equal(pattern.verdictAt, at + 5);
  f.tick(); await tick(); pattern = JSON.parse(readFileSync(stateFile)).interpreterPattern;
  assert.equal(pattern.streak, laterFailures, 'a later tick must not count these failures twice');
});

// AC4. A scan without a result must not exclude the first late completion.
for (const injected of [false, true]) test(`3091 integration first late verdict clears test mode (injected=${injected})`, async t => {
  const {f, tick, stateFile, ports} = await setup(t);
  const at = f.clock, run = f.record();
  for (let i = 0; i < 3; i++) {
    const row = i ? (await anotherRun(f, 17 + i))() : run;
    delete row.blockedOn;
    row.state = 'paused'; row.runtimeWait = {at: at + 10 + i, reason: 'no verdict', cause: 'service'}; save(f, row);
  }
  fullTicks(f, stateFile, ports);
  ports.runtimeHealth = async () => ({state: 'unavailable', detail: 'controlled outage'});
  const {mkdirSync} = await import('node:fs');
  const {latestCheckVerdict} = await import('../src/workflow-results.mjs');
  const batch = '20261108-120000-abcd', folder = join(f.ports.env.HOME, '.pdd/runtime/batches', batch);
  mkdirSync(folder, {recursive: true});
  const cutoffs = [];
  if (injected) ports.readInterpreterVerdict = async since => {
    cutoffs.push(since);
    return latestCheckVerdict({root: run.root, since}, {env: f.ports.env});
  };
  f.tick(100); await tick();
  let pattern = JSON.parse(readFileSync(stateFile)).interpreterPattern;
  assert.equal(pattern.streak, 3); assert.equal(pattern.testMode, true);
  assert.equal(pattern.verdictAt, undefined);
  writeFileSync(join(folder, 'batch.json'), JSON.stringify({batch, root: run.root, intent: 'check', rows: [{state: 'passed', ended_at: at + 11}]}));
  assert.equal(latestCheckVerdict({root: run.root, since: 0}, {env: f.ports.env}), at + 11);
  f.tick(); await tick();
  pattern = JSON.parse(readFileSync(stateFile)).interpreterPattern;
  assert.equal(pattern.streak, 1); assert.equal(pattern.testMode, false); assert.equal(pattern.verdictAt, at + 11);
  if (injected) assert.deepEqual(cutoffs, [0, 0]);
  f.tick(); await tick();
  assert.equal(JSON.parse(readFileSync(stateFile)).interpreterPattern.streak, 1);
});
