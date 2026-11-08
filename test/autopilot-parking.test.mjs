import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {existsSync, readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {healthyMachine} from './helpers/healthy-machine.mjs';
import {isolatedCheckCapacity} from './helpers/check-machine.mjs';
import {tickAutopilot, runAutopilotLauncher} from '../src/autopilot-launcher.mjs';
import {runStatus, parkAutomaticRun, changeRun, startRun} from '../src/workflow-runner.mjs';
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
