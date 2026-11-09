import './helpers/test-home.mjs';
import test from 'node:test';
import {createHash} from 'node:crypto';
import assert from 'node:assert/strict';
import {existsSync, mkdirSync, readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {healthyMachine} from './helpers/healthy-machine.mjs';
import {isolatedCheckCapacity} from './helpers/check-machine.mjs';
import {readRunResults} from '../src/workflow-results.mjs';
import {tickAutopilot, runAutopilotLauncher} from '../src/autopilot-launcher.mjs';
import {runStatus, parkAutomaticRun, changeRun, startRun, openRun} from '../src/workflow-runner.mjs';
import {createDependencyReadPorts} from '../src/issue-dependencies-github.mjs';
import {checkDependencyStart} from '../src/issue-dependencies-intake.mjs';

const save = (f, run) => writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
const launches = f => f.herdr.calls.filter(args => args[0] === 'pane' && args[1] === 'run');
const deliveries = f => f.herdr.calls.filter(args => args[0] === 'agent' && args[1] === 'prompt');

for (const [kind,field] of [['interface-missing','/interface'],['undefined-call-bound','/limits/max_model_calls'],['undefined-call-bound','/calls/0/max_calls'],['recursive-call-bound','/calls']])
  test(`3114 repair: local ${kind} ${field} cannot become an interpreter blocker or park`, async t => {
    const {f,tick,ports,stateFile} = await setup(t);
    fullTicks(f,stateFile,ports);
    const held=f.record(),batch='20261101-120000-abcd';
    const reason={code:'check-plan-prerequisite',message:`Repair ${kind}: value.prompt.md ${field}; run a fresh pdd test.`};
    const rows=[{test:'tests/value.json',story:'value',state:'not run',reason,unsent:true,calls:0,request_ids:[]}];
    const folder=join(f.ports.env.HOME,'.pdd/runtime/batches',batch);mkdirSync(folder,{recursive:true});
    writeFileSync(join(folder,'batch.json'),JSON.stringify({version:1,batch,root:held.root,intent:'check',created_at:new Date(f.clock).toISOString(),rows}));
    writeFileSync(join(folder,'summary.json'),JSON.stringify({batch,rows}));
    ports.readRunResults=()=>[{kind:'pdd test',batch,at:f.clock,states:rows,summary:reason.message}];
    held.state='waiting';held.gate={kind:'approve-pr',area:held.areas[held.area].name};held.done.check='Local full check blocked';save(f,held);
    const before=f.record();
    const refused=await parkAutomaticRun({runtime:true,reason:reason.message,cwd:held.root},{...f.agentPorts(),readRunResults:ports.readRunResults});
    assert.equal(refused.exitCode,1,'3114_LOCAL_PARK_ACCEPTED');
    assert.deepEqual(f.record(),before);
    await tick();
    assert.notEqual(f.record().parking?.blocker?.kind,'interpreter','3114_LOCAL_BLOCKER_MISCLASSIFIED');
    assert.equal(f.record().runtimeWait,undefined);
    assert.equal(f.record().parking?.interpreterWait,undefined);
  });

test('3091 repair 2 person park becomes one stable inferred interpreter wait', async t => {
  const {f, tick, ports, stateFile, warnings} = await setup(t);
  fullTicks(f, stateFile, ports);
  ports.runtimeHealth = async () => ({state: 'unavailable', detail: 'controlled outage'});
  const held = f.record(); held.state = 'waiting';
  held.question = {at: f.clock, text: 'Which product option?'}; save(f, held);
  await tick(); assert.equal(f.record().parking.blocker.kind, 'person');
  const age = f.record().parking.at;
  f.tick();
  const changed = f.record(); delete changed.question; changed.state = 'stuck';
  changed.gate = {kind: 'approve-pr', area: changed.areas[changed.area].name};
  changed.parkReason = 'Interpreter saved read is unknown (runner-stopped).'; changed.updatedAt = f.clock; save(f, changed);
  const identities = [];
  for (let i = 0; i < 3; i++) {
    f.tick(); await tick();
    const state = JSON.parse(readFileSync(stateFile));
    identities.push(Object.keys(state.interpreterPattern.seen));
    assert.equal(state.interpreterPattern.streak, 1, 'one saved wait counts once across tick writes');
    assert.ok(!state.interpreterPattern.testMode);
    assert.deepEqual([state.parking.working, state.parking.parked], [0, 1]);
  }
  assert.deepEqual(identities[1], identities[0]); assert.deepEqual(identities[2], identities[0]);
  const parked = f.record();
  assert.equal(parked.parking.blocker.kind, 'interpreter');
  assert.ok(Number.isFinite(parked.parking.interpreterWait.at));
  assert.deepEqual(parked.parking.interpreterGate, changed.gate);
  assert.equal(parked.parking.at, age);
  assert.equal(parked.parking.personWait, undefined);
  for (const key of ['root', 'branch', 'gate', 'question', 'done', 'automaticOrigin']) assert.deepEqual(parked[key], changed[key]);
  assert.equal(parked.chats.at(-1).session.id, held.chats.at(-1).session.id);
  assert.equal(launches(f).length, 0); assert.equal(deliveries(f).length, 0);
  assert.deepEqual(warnings, []);
});

for (const throughPerson of [true, false])
  test(`3091 repair 2 replacement interpreter wait reads current batch through person ${throughPerson}`, async t => {
    const {f, tick, ports, stateFile, warnings} = await setup(t);
    fullTicks(f, stateFile, ports);
    const alerts=[]; ports.sendAlert=async input=>{alerts.push(input);return {exitCode:0};};
    ports.runtimeHealth = async () => ({state: 'unavailable', detail: 'controlled outage'});
    const oldBatch = '20261101-120000-abcd', newBatch = '20261102-120000-efgh';
    const held = f.record(); held.state = 'stuck';
    held.parkReason = `Interpreter saved read ${oldBatch} is unknown (runner-stopped).`; save(f, held);
    await tick();
    assert.equal(f.record().parking.interpreterWait.batch, oldBatch);
    const age = f.record().parking.at, oldWait = f.record().parking.interpreterWait;
    if (throughPerson) {
      f.tick(); const question = f.record(); question.question = {at: f.clock, text: 'Which independent product option?'};
      save(f, question); await tick(); assert.equal(f.record().parking.blocker.kind, 'person');
      assert.deepEqual(f.record().question, question.question);
      assert.equal(f.record().parking.interpreterWait, undefined);
      assert.equal(f.record().parking.interpreterGate, undefined);
    }
    f.tick(); const changed = f.record(); delete changed.question;
    changed.gate = {kind: 'approve-pr', area: changed.areas[changed.area].name};
    changed.parkReason = `Interpreter saved read ${newBatch} is unknown (runner-stopped).`; changed.updatedAt = f.clock; save(f, changed);
    await tick();
    const parked = f.record();
    assert.equal(parked.parking.interpreterWait.batch, newBatch, 'replacement owns the current saved batch');
    assert.notEqual(parked.parking.interpreterWait.at, oldWait.at);
    assert.equal(parked.parking.at, age);
    assert.deepEqual(parked.parking.interpreterGate, changed.gate);
    const wait = parked.parking.interpreterWait;
    f.tick(); await tick(); assert.deepEqual(f.record().parking.interpreterWait, wait);
    ports.runtimeHealth = async () => ({state: 'healthy', detail: 'controlled recovery'});
    await tick();
    assert.equal(f.record().parking.phase, 'parked', 'lost verdict waits for a recorded person decision');
    assert.deepEqual(f.record().gate, changed.gate);
    assert.deepEqual(f.record().decisions, changed.decisions);
    assert.equal(f.record().chats.at(-1).session.id, held.chats.at(-1).session.id);
    assert.equal(launches(f).length, 0); assert.equal(deliveries(f).length, 0);
    const decision=alerts.find(row=>row.kind==='decision');assert.ok(decision);
    assert.ok(decision.text.includes(newBatch));assert.ok(!decision.text.includes(oldBatch));
    await tick(); assert.equal(deliveries(f).length, 0);
    assert.deepEqual(warnings, []);
  });

// #3091 final review: exercise saved-batch inference through the production reader.
for (const previous of ['person', 'interpreter'])
  test(`3091 integration finished check replaces existing ${previous} park with current batch`, async t => {
    const {f, tick, ports, stateFile, warnings} = await setup(t, 'claude', 'feature');
    fullTicks(f, stateFile, ports);
    const alerts=[]; ports.sendAlert=async input=>{alerts.push(input);return {exitCode:0};};
    ports.runtimeHealth = async () => ({state: 'unavailable', detail: 'controlled outage'});
    const oldBatch = '20261101-120000-abcd', newBatch = '20261102-120000-efgh';
    const savedBatch = batch => {
      const folder = join(f.ports.env.HOME, '.pdd/runtime/batches', batch);
      mkdirSync(folder, {recursive: true});
      writeFileSync(join(folder, 'batch.json'), JSON.stringify({batch, root: f.record().root,
        intent: 'check', created_at: new Date(f.clock).toISOString(),
        rows: [{test: 'tests/value.json', state: 'partial', reason: {code: 'runner-stopped'}}]}));
    };
    const held = f.record(); held.area = 1; held.state = 'waiting';
    for (const chat of held.chats) chat.area = held.areas[held.area].name;
    if (previous === 'person') held.question = {at: f.clock, text: 'Which product option?'};
    else {
      held.gate = {kind: 'approve-pr', area: held.areas[held.area].name, at: f.clock};
      held.done.check = {at: f.clock};
    }
    save(f, held);
    if (previous === 'interpreter') savedBatch(oldBatch);
    await tick();
    assert.equal(f.record().parking.blocker.kind, previous);
    if (previous === 'interpreter') assert.equal(f.record().parking.interpreterWait.batch, oldBatch);
    const age = f.record().parking.at;
    f.tick();
    const changed = f.record(); delete changed.question;
    changed.gate = {kind: 'approve-pr', area: changed.areas[changed.area].name, at: f.clock};
    changed.done.check = {at: f.clock}; changed.updatedAt = f.clock; save(f, changed);
    savedBatch(newBatch);
    await tick();
    const parked = f.record();
    assert.equal(parked.parking.blocker.kind, 'interpreter');
    assert.equal(parked.parking.interpreterWait.batch, newBatch);
    assert.deepEqual(parked.parking.interpreterGate, changed.gate);
    assert.equal(parked.parking.personWait, undefined);
    assert.equal(parked.parking.at, age);
    assert.equal(parked.parking.phase, 'parked');
    for (const key of ['root', 'branch', 'gate', 'question', 'done', 'decisions', 'automaticOrigin'])
      assert.deepEqual(parked[key], changed[key]);
    assert.equal(parked.chats.at(-1).session.id, held.chats.at(-1).session.id);
    assert.equal(launches(f).length, 0); assert.equal(deliveries(f).length, 0);
    f.tick(); await tick();
    assert.deepEqual(f.record().parking.interpreterWait, parked.parking.interpreterWait);
    assert.deepEqual(f.record().parking.interpreterGate, changed.gate);
    // A named person blocker still wins over the same inferred saved-check evidence.
    const explicit = f.record(); explicit.blockedOn = {kind: 'person', until: null}; save(f, explicit);
    await tick();
    assert.deepEqual(f.record().parking.blocker, explicit.blockedOn);
    assert.equal(f.record().parking.interpreterWait, undefined);
    assert.equal(f.record().parking.at, age);
    assert.deepEqual(f.record().gate, changed.gate);
    const inferred = f.record(); delete inferred.blockedOn; save(f, inferred);
    await tick();
    assert.equal(f.record().parking.blocker.kind, 'interpreter');
    assert.equal(f.record().parking.interpreterWait.batch, newBatch);
    assert.deepEqual(f.record().parking.interpreterGate, changed.gate);
    ports.runtimeHealth = async () => ({state: 'healthy', detail: 'controlled recovery'});
    await tick();
    assert.equal(f.record().parking.phase, 'parked', 'lost verdict waits for a recorded person decision');
    assert.deepEqual(f.record().gate, changed.gate);
    assert.deepEqual(f.record().decisions, changed.decisions);
    assert.deepEqual(f.record().automaticOrigin, changed.automaticOrigin);
    assert.equal(f.record().chats.at(-1).session.id, held.chats.at(-1).session.id);
    assert.equal(launches(f).length, 0); assert.equal(deliveries(f).length, 0);
    const decision=alerts.find(row=>row.kind==='decision');assert.ok(decision);
    assert.ok(decision.text.includes(newBatch));assert.ok(!decision.text.includes(oldBatch));
    await tick(); assert.equal(deliveries(f).length, 0);
    assert.deepEqual(warnings, []);
  });

// #3091: saved-check identity must be current even when only one input changes.
for (const change of ['batch', 'check', 'result', 'verdict'])
  test(`3091 batch refresh ${change} evidence at an inferred interpreter park`, async t => {
    const {f, tick, ports, stateFile, warnings} = await setup(t, 'claude', 'feature');
    fullTicks(f, stateFile, ports);
    const alerts=[]; ports.sendAlert=async input=>{alerts.push(input);return {exitCode:0};};
    ports.runtimeHealth = async () => ({state: 'unavailable', detail: 'controlled outage'});
    const oldBatch = '20261101-120000-abcd', newBatch = '20261102-120000-efgh';
    const held = f.record(); held.area = 1; held.state = 'waiting';
    for (const chat of held.chats) chat.area = held.areas[held.area].name;
    held.gate = {kind: 'approve-pr', area: held.areas[held.area].name, at: f.clock};
    held.done.check = {at: f.clock}; save(f, held);
    const created = new Date(f.clock).toISOString();
    const savedBatch = (batch, state = 'partial', code = 'runner-stopped') => {
      const folder = join(f.ports.env.HOME, '.pdd/runtime/batches', batch);
      mkdirSync(folder, {recursive: true});
      writeFileSync(join(folder, 'batch.json'), JSON.stringify({batch, root: held.root,
        intent: 'check', created_at: created,
        rows: [{test: 'tests/value.json', state, reason: {code}}]}));
    };
    savedBatch(oldBatch);
    await tick();
    const original = f.record(), age = original.parking.at, oldWait = original.parking.interpreterWait;
    assert.equal(oldWait.batch, oldBatch);
    assert.equal(original.parking.blocker.kind, 'interpreter');
    f.tick(); await tick();
    assert.deepEqual(f.record().parking.interpreterWait, oldWait);
    assert.equal(f.record().parking.at, age);
    f.tick();
    const changed = f.record();
    // Change only the named input. In particular, leave updatedAt and the gate
    // intact for a replacement saved batch or an updated result in that batch.
    if (change === 'check') changed.done.check = {...changed.done.check, at: f.clock};
    save(f, changed);
    if (change === 'batch') savedBatch(newBatch);
    if (change === 'result') savedBatch(oldBatch, 'partial', 'no-server-verdict');
    if (change === 'verdict') savedBatch(oldBatch, 'failed', 'check-failed');
    const batch = change === 'batch' ? newBatch : oldBatch;
    const current = readRunResults({root: held.root, since: held.startedAt}, {env: f.ports.env})
      .find(row => row.kind === 'pdd test');
    assert.equal(current.batch, batch);
    if (change === 'result') assert.equal(current.states[0].reason.code, 'no-server-verdict');
    await tick();
    const parked = f.record();
    assert.equal(parked.parking.at, age);
    assert.equal(parked.parking.phase, 'parked');
    for (const key of ['root', 'branch', 'gate', 'question', 'done', 'decisions', 'automaticOrigin'])
      assert.deepEqual(parked[key], changed[key]);
    assert.equal(parked.chats.at(-1).session.id, held.chats.at(-1).session.id);
    assert.equal(launches(f).length, 0); assert.equal(deliveries(f).length, 0);
    if (change === 'verdict') {
      assert.equal(parked.parking.blocker.kind, 'person');
      assert.equal(parked.parking.interpreterWait, undefined);
      assert.equal(parked.parking.interpreterCheck, undefined);
      ports.runtimeHealth = async () => ({state: 'healthy', detail: 'controlled recovery'});
      await tick();
      assert.equal(f.record().parking.blocker.kind, 'person');
      assert.equal(deliveries(f).length, 0);
    } else {
      assert.equal(parked.parking.interpreterWait.batch, batch);
      assert.deepEqual(parked.parking.interpreterGate, changed.gate);
      assert.notEqual(parked.parking.interpreterWait.at, oldWait.at, 'changed evidence has a new wait identity');
      const wait = parked.parking.interpreterWait;
      const pattern = JSON.parse(readFileSync(stateFile)).interpreterPattern;
      assert.equal(pattern.streak, 2);
      if (change === 'check') {
        // Refresh a different gate at the same clock value and saved batch.
        changed.gate = {...changed.gate, at: f.clock};
        const nextGate = f.record(); nextGate.gate = changed.gate; save(f, nextGate);
        await tick();
        const rebound = f.record();
        assert.equal(rebound.parking.interpreterWait.batch, batch);
        assert.notEqual(rebound.parking.interpreterWait.at, wait.at);
        assert.deepEqual(rebound.parking.interpreterGate, changed.gate);
        assert.equal(rebound.parking.at, age);
        f.tick(); await tick();
        assert.deepEqual(f.record().parking.interpreterWait, rebound.parking.interpreterWait);
      } else {
        f.tick(); await tick();
        assert.deepEqual(f.record().parking.interpreterWait, wait);
      }
      ports.runtimeHealth = async () => ({state: 'healthy', detail: 'controlled recovery'});
      await tick();
      assert.equal(f.record().parking.phase, 'parked', 'lost verdict waits for a recorded person decision');
      for (const key of ['gate', 'decisions', 'automaticOrigin']) assert.deepEqual(f.record()[key], changed[key]);
      assert.equal(f.record().chats.at(-1).session.id, held.chats.at(-1).session.id);
      assert.equal(launches(f).length, 0); assert.equal(deliveries(f).length, 0);
      const decision=alerts.find(row=>row.kind==='decision');assert.ok(decision);
      assert.ok(decision.text.includes(batch));
      if (change === 'batch') assert.ok(!decision.text.includes(oldBatch));
      await tick(); assert.equal(deliveries(f).length, 0);
    }
    assert.deepEqual(warnings, []);
  });

async function setup(t, agent = 'claude', name = 'small-change') {
  const f = await fixture(t, {agent, name});
  assert.equal((await f.run()).exitCode, 0);
  assert.equal((await runStatus({ref: '17', cwd: f.source}, f.ports)).exitCode, 0);
  f.herdr.idle(); // This fixture represents a stopped worker, not a busy turn.
  const run = f.record();
  run.automaticOrigin = {repository: run.repo, coordinatorId: 'park-owner', machine: 'park-machine', claim: {commentId: '11', labelEventId: '12'}};
  save(f, run);
  f.ports.owners = {read: async input => ({json: JSON.stringify({localOwner: 'park-owner',
    claims: input.issues.map(issue => ({issue, active: true, owner: 'park-owner', coordinatorId: 'park-owner',
      machine: 'park-machine', commentId: '11', labelEventId: '12'}))})})};
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
    if (kind === 'pdd') {held.state = 'paused'; held.blockedOn = {kind: 'pdd', until: 'capability:fixture-fix'};}
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
  const owners = JSON.parse((await createDependencyReadPorts({cwd: f.source}, {...f.ports, owners: undefined}).owners.read({repository: held.repo, issues: []})).json);
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
  if (damage === 'session') {
    held.chats.at(-1).session = null; f.herdr.paneOf(held.chats.at(-1)).agent = null;
    ports.findNativeSessions = async () => [];
  }
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
  assert.equal(launches(f).length, 0);
  await tick();
  assert.deepEqual(warnings, []);
  assert.equal(launches(f).length, 1);
  assert.equal(f.record().chats.at(-1).session.id, held.chats.at(-1).session.id);
  assert.equal(f.record().parking, undefined);
  assert.equal(deliveries(f).length, 1);
  await tick(); assert.equal(launches(f).length, 1); assert.equal(deliveries(f).length, 1);
});

test('3091 explicit installed-release and reset blockers are stored with clearing evidence', async t => {
  const {f} = await setup(t);
  for (const [blocker, until] of [['pdd', 'capability:fixture-fix'], ['dependency', '2897'], ['account', '2026-11-10T12:00:00Z']]) {
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
  f.herdr.idle(); // The additional run is also stopped before parking.
  const run = JSON.parse(readFileSync(path)); run.automaticOrigin = f.record().automaticOrigin;
  run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: 'capability:fixture-fix'};
  save(f, run);
  return () => JSON.parse(readFileSync(path));
}

test('3091 installed release wakes oldest first and holds other ready wakes for the working cap', async t => {
  const {f, tick, ports, stateFile, warnings} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: 'capability:fixture-fix'}; save(f, run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  const other = await anotherRun(f, 18); f.tick(1000); await tick();
  assert.equal(other().parking?.phase, 'parked');
  f.herdr.calls.length = 0; ports.installedPddCapabilities = ['fixture-fix']; await tick();
  assert.equal(launches(f).length, 1);
  assert.equal(f.record().parking, undefined, 'oldest run must resume first');
  assert.equal(other().parking.phase, 'parked');
  const summary = JSON.parse(readFileSync(stateFile)).parking;
  assert.deepEqual([summary.working, summary.parked, summary.wakePending], [1, 1, [18]]);
  await tick(); assert.equal(launches(f).length, 1, 'cap must hold the other wake');
});

test('3091 failed resume reserves capacity and retries the same saved session', async t => {
  const {f, tick, ports, stateFile, warnings} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: 'capability:fixture-fix'}; save(f, run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  const herdr = ports.herdr; let fail = true;
  ports.herdr = async args => {if (fail && args[0] === 'pane' && args[1] === 'run') {fail = false; throw Object.assign(Error('unsent fixture resume'), {code: 'agent_not_found'});} return herdr(args);};
  ports.installedPddCapabilities = ['fixture-fix']; await tick();
  assert.equal(f.record().parking?.phase, 'waking');
  assert.equal(JSON.parse(readFileSync(stateFile)).parking.working, 1);
  f.tick(60001); await tick();
  assert.equal(f.record().parking, undefined, JSON.stringify({warnings, chat: f.record().chats.at(-1), failure: f.record().chatFailure}));
  assert.equal(f.record().chats.at(-1).session.id, run.chats.at(-1).session.id);
});

test('3091 health pause keeps ready parked sessions closed', async t => {
  const {f, tick, ports} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: 'capability:fixture-fix'}; save(f, run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  ports.installedPddCapabilities = ['fixture-fix']; ports.machineHealth = async () => ({healthy: false, causes: ['controlled memory pressure'], resources: null});
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
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: 'capability:fixture-fix'}; save(f, run);
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
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: 'capability:fixture-fix'}; save(f, run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  const other = await anotherRun(f, 18); f.tick(); await tick(); assert.equal(other().parking?.phase, 'parked');
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto', trust: [], parking: {maxParked: 1}}}));
  fullTicks(f, stateFile, ports);
  const released = []; ports.releaseParkedClaim = async input => {released.push(input.runId); return {state: 'released'};};
  await tick(); assert.deepEqual(released, [run.runId]); assert.equal(other().parking.phase, 'parked');
});

test('3091 same-group intake joins the existing journal without restoring a blocked chat', async t => {
  const {f, tick, stateFile, ports, warnings} = await setup(t);
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: 'capability:fixture-fix'}; save(f, run);
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
  ports.installedPddCapabilities = ['fixture-fix']; await tick();
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
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: 'capability:fixture-fix'}; save(f, run);
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
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: 'capability:fixture-fix'}; save(f, run);
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
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: 'capability:fixture-fix'}; save(f, run);
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
  f.herdr.calls.length = 0; ports.installedPddCapabilities = ['fixture-fix']; await tick();
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
  assert.equal((await changeRun({ref: '17', cwd: f.source, text: 'Use the first case', packageRoot}, f.ports)).exitCode, 0);
  assert.equal(f.record().parking.phase, 'parked'); assert.equal(launches(f).length, 0);
  await tick(); assert.equal(f.record().parking, undefined); assert.equal(launches(f).length, 1);
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
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: 'capability:fixture-fix'}; save(f, run);
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
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: 'capability:fixture-fix'}; save(f, run);
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
    owners: undefined, readSuiteProgress: ports.readSuiteProgress, readInterpreterProgress: ports.readInterpreterProgress}).owners.read({repository: run.repo, issues: []})).json);
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
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: 'capability:fixture-fix'}; save(f, run);
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
  const run = f.record(); run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: 'capability:fixture-fix'}; save(f, run);
  await tick(); const parked = f.record();
  const result = await parkAutomaticRun({cwd: run.root, reason: 'Wait for the dependency', blocker: 'dependency', until: '2897'}, parkCommandPorts(f));
  assert.equal(result.exitCode, 0);
  ports.installedPddCapabilities = ['fixture-fix']; await tick();
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

// AC2/AC3. A reply after backfill must join admission, not launch over capacity.
for (const competing of [false, true]) test(`3091 integration parked reply respects backfill and oldest ready wait (competing=${competing})`, async t => {
  const {f, tick, ports, stateFile} = await setup(t);
  const held = f.record(); held.state = 'waiting'; held.question = {at: f.clock, text: 'Choose the case'}; save(f, held);
  await tick();
  let older;
  if (competing) {
    older = await anotherRun(f, 19); await tick();
    // Independent wait is older than the person wait and must win the next free slot.
    const row = older(); row.parking.at = held.question.at - 1; save(f, row);
  }
  const other = await anotherRun(f, 18);
  const working = other(); delete working.blockedOn; working.state = 'running'; save(f, working);
  f.herdr.calls.length = 0;
  const reply = {ref: '17', cwd: f.source, text: 'Use the first case', packageRoot};
  const result = await changeRun(reply, f.ports);
  assert.equal(result.exitCode, 0, result.message);
  assert.equal(launches(f).length, 0, 'a normal reply must not bypass the working cap');
  assert.equal(deliveries(f).length, 0);
  assert.equal(f.record().parking.phase, 'parked');
  assert.deepEqual(f.record().question, held.question);
  // Retrying the reply before admission is durable and deduplicated.
  assert.equal((await changeRun(reply, f.ports)).exitCode, 0);
  if (competing) ports.installedPddCapabilities = ['fixture-fix'];
  await tick();
  let summary = JSON.parse(readFileSync(stateFile)).parking;
  assert.equal(summary.working, 1); assert.equal(launches(f).length, 0);
  assert.deepEqual(summary.wakePending, competing ? [19, 17] : [17]);
  assert.equal((await runStatus({ref: '17', cwd: f.source, json: true}, f.ports)).exitCode, 0);
  const pending = JSON.parse((await runStatus({ref: '17', cwd: f.source, json: true}, f.ports)).message).runs[0].pendingRequests;
  assert.equal(pending.filter(entry => entry.text === reply.text).length, 1);
  const ended = other(); ended.state = 'completed'; save(f, ended);
  f.herdr.calls.length = 0; await tick();
  assert.equal(launches(f).length, 1);
  if (competing) {
    assert.equal(older().parking, undefined);
    assert.equal(f.record().parking.phase, 'parked'); assert.equal(deliveries(f).filter(args => JSON.stringify(args).includes(reply.text)).length, 0);
    const finished = older(); finished.state = 'completed'; save(f, finished);
    await tick(); assert.equal(launches(f).length, 2);
  }
  assert.equal(f.record().parking, undefined); assert.equal(f.record().question, null);
  assert.equal(f.record().changes.filter(entry => entry.answer && entry.text === reply.text).length, 1);
  assert.equal(f.record().chats.at(-1).session.id, held.chats.at(-1).session.id);
  assert.equal(deliveries(f).filter(args => JSON.stringify(args).includes(reply.text)).length, 1);
  const count = launches(f).length; await tick();
  assert.equal(launches(f).length, count);
  assert.equal(deliveries(f).filter(args => JSON.stringify(args).includes(reply.text)).length, 1);
});

test('3091 integration parked reply survives an unsent resume and delivers its saved request once', async t => {
  const {f, tick, ports} = await setup(t);
  const held = f.record(); held.state = 'waiting'; held.question = {at: f.clock, text: 'Choose the case'}; save(f, held);
  await tick();
  const text = 'Use the second case';
  assert.equal((await changeRun({ref: '17', cwd: f.source, text, packageRoot}, f.ports)).exitCode, 0);
  assert.equal(launches(f).length, 0);
  const transport = ports.herdr; let reject = true;
  ports.herdr = async args => {
    if (reject && args[0] === 'pane' && args[1] === 'run') {reject = false; throw Object.assign(Error('unsent resume'), {code: 'agent_not_found'});}
    return transport(args);
  };
  await tick();
  assert.equal(f.record().parking.phase, 'waking');
  assert.equal(deliveries(f).length, 0);
  assert.deepEqual(f.record().question, held.question);
  const journal = JSON.parse(readFileSync(join(held.runDir, 'delivery-journal.json')));
  const reply = journal.requests.find(entry => entry.text === text);
  assert.equal(reply.state, 'pending');
  f.tick(60001); await tick();
  assert.equal(f.record().parking, undefined);
  assert.equal(f.record().question, null);
  assert.equal(f.record().changes.filter(entry => entry.answer && entry.text === text).length, 1);
  const delivered = JSON.parse(readFileSync(join(held.runDir, 'delivery-journal.json'))).requests.find(entry => entry.id === reply.id);
  assert.equal(delivered.state, 'delivered');
  assert.equal(deliveries(f).filter(args => JSON.stringify(args).includes(text)).length, 1);
  await tick(); assert.equal(deliveries(f).filter(args => JSON.stringify(args).includes(text)).length, 1);
});

// #3091 gap: these records were stopped before the installed coordinator knew parking.
for (const reason of [
  'pdd:no-verdict',
  'Saved batch read is unknown (runner-stopped).',
  'Interpreter check returned no verdict.',
  'Interpreter saved read 20261101-120000-abcd is unknown (runner-stopped).',
  'Interpreter recovery read still reports UNKNOWN. No check was resent.',
]) test(`3091 backfill legacy interpreter stop: ${reason}`, async t => {
  const {f, tick, stateFile} = await setup(t);
  const held = f.record(); held.state = 'stuck'; held.parkReason = reason; save(f, held);
  await tick();
  const parked = f.record();
  assert.equal(parked.parking?.phase, 'parked', 'legacy interpreter stop must close without a migration');
  assert.equal(parked.parking.blocker.kind, 'interpreter');
  assert.equal(f.herdr.panes.filter(pane => pane.workspace_id === held.layout.workspaceId).length, 0);
  assert.equal(parked.chats.at(-1).session.id, held.chats.at(-1).session.id);
  assert.deepEqual(parked.automaticOrigin, held.automaticOrigin);
  assert.deepEqual(JSON.parse(readFileSync(stateFile)).parking.blockers, {interpreter: 1});
  assert.equal(JSON.parse(readFileSync(stateFile)).parking.working, 0);
  const at = parked.parking.interpreterWait.at;
  f.tick(); await tick(); assert.equal(f.record().parking.interpreterWait.at, at);
});

for (const wait of ['stop', 'question']) test(`3091 backfill missing PR1 route ${wait} wakes on installed capability once`, async t => {
  const {f, tick, ports, stateFile, warnings} = await setup(t);
  ports.installedPddCapabilities = [];
  const held = f.record();
  if (wait === 'stop') {held.state = 'stuck'; held.parkReason = 'Installed PDD has no supported PR1 current-main integration route.';}
  else {held.state = 'waiting'; held.question = {at: f.clock, text: 'Which supported native recovery returns this run to PR 1 prompt approval and integrates main?'};}
  save(f, held); await tick();
  assert.equal(f.record().parking?.phase, 'parked', 'missing route must be a named park');
  assert.deepEqual(f.record().parking.blocker, {kind: 'pdd', until: '#2897'});
  ports.packageVersion = '999.0.0'; await tick();
  assert.equal(launches(f).length, 0, 'a newer version alone cannot prove the route exists');
  ports.installedPddCapabilities = ['prompt-reentry']; await tick();
  assert.deepEqual(warnings, []);
  assert.equal(f.record().parking, undefined, 'installed re-entry capability must clear the legacy wait');
  assert.equal(launches(f).length, 1); assert.equal(deliveries(f).length, 1);
  const text = JSON.stringify(deliveries(f)[0]);
  assert.match(text, /#2897/); assert.match(text, /re-entry/);
  assert.equal(f.record().chats.at(-1).session.id, held.chats.at(-1).session.id);
  assert.deepEqual(f.record().question, held.question, 'fix notice must not record a person answer');
  assert.equal(JSON.parse(readFileSync(stateFile)).parking.working, 1);
  await tick(); assert.equal(launches(f).length, 1); assert.equal(deliveries(f).length, 1);
});

test('3091 backfill finished PR1 lost check stays parked for a person decision without approval', async t => {
  const {f, tick, ports, stateFile, warnings} = await setup(t);
  fullTicks(f, stateFile, ports);
  const alerts=[];ports.sendAlert=async input=>{alerts.push(input);return {exitCode:0};};
  ports.runtimeHealth = async () => ({state: 'unavailable', detail: 'controlled outage'});
  const held = f.record(); held.state = 'waiting'; held.gate = {kind: 'approve-pr', area: held.areas[held.area].name};
  held.done.check = {at: f.clock}; save(f, held);
  ports.readRunResults = () => [{kind: 'pdd test', batch: '20261101-120000-abcd', states: [{state: 'partial', reason: {code: 'runner-stopped'}}]}];
  await tick();
  assert.equal(f.record().parking?.blocker.kind, 'interpreter');
  ports.runtimeHealth = async () => ({state: 'healthy', detail: 'controlled recovery'});
  await tick();
  assert.deepEqual(warnings, []);assert.equal(f.record().parking.phase,'parked');
  assert.deepEqual(f.record().gate, held.gate);assert.equal(deliveries(f).length,0);
  const decisions=()=>alerts.filter(row=>row.kind==='decision');
  assert.equal(decisions().length,1);assert.ok(decisions()[0].text.includes('20261101-120000-abcd'));
  await tick();assert.equal(decisions().length,1);assert.equal(deliveries(f).length,0);
});

test('3091 backfill three lost legacy verdicts enter test mode and wait for one grouped decision', async t => {
  const {f, tick, ports, stateFile} = await setup(t);
  fullTicks(f, stateFile, ports);
  const alerts=[];ports.sendAlert=async input=>{alerts.push(input);return {exitCode:0};};
  const second = await anotherRun(f, 18), third = await anotherRun(f, 19);
  for (const [i, get] of [f.record, second, third].entries()) {
    const run = get(); delete run.blockedOn; run.state = 'stuck';
    run.parkReason = 'Interpreter saved read is unknown (runner-stopped).'; run.updatedAt = f.clock - 3000 + i * 1000; save(f, run);
  }
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto', trust: [], parking: {maxParked: 10}}}));
  ports.runtimeHealth = async () => ({state: 'unavailable', detail: 'controlled outage'});
  f.herdr.calls.length = 0;await tick();
  let state = JSON.parse(readFileSync(stateFile));assert.equal(state.parking.parked,3);
  assert.equal(state.interpreterPattern.streak,3);assert.equal(state.interpreterPattern.testMode,true);
  ports.runtimeHealth = async () => ({state: 'healthy', detail: 'controlled recovery'});await tick();
  state = JSON.parse(readFileSync(stateFile));
  assert.equal(launches(f).length,0);assert.equal(deliveries(f).length,0);
  assert.equal(state.runtime.outage.probe,undefined);assert.deepEqual([state.parking.working,state.parking.parked],[0,3]);
  const decisions=()=>alerts.filter(row=>row.kind==='decision');assert.equal(decisions().length,1);
  assert.match(decisions()[0].text,/resend 17 18 19 --said/);
  await tick();assert.equal(decisions().length,1);
  ports.readInterpreterVerdict=async()=>f.clock;await tick();
  state=JSON.parse(readFileSync(stateFile));assert.equal(state.interpreterPattern.testMode,false);
  assert.equal(launches(f).length,0,'another verdict does not authorize these lost checks');
});

test('3091 backfill unknown stopped cause closes resources and alerts once across ticks', async t => {
  const {f, tick, ports, stateFile} = await setup(t);
  const held = f.record(); held.state = 'stuck'; held.parkReason = 'A local condition has no saved classification.'; save(f, held);
  const alerts = []; ports.sendAlert = async input => {alerts.push(input); return {exitCode: 0};};
  await tick(); await tick();
  assert.equal(f.record().state, 'stuck');
  assert.equal(f.record().parking?.phase, 'parked', 'unknown stopped work must not use a worker process');
  assert.equal(alerts.filter(row => row.kind === 'stuck').length, 1);
  assert.deepEqual(JSON.parse(readFileSync(stateFile)).parking.blockers, {unknown: 1});
  assert.equal(JSON.parse(readFileSync(stateFile)).parking.working, 0);
  assert.equal(launches(f).length, 0);
});

for (const [reason, kind, until] of [
  ['Waiting for issue #321 to merge.', 'dependency', '321'],
  ['Account usage-limit until 2026-11-10T12:00:00Z.', 'account', '2026-11-10T12:00:00Z'],
  ['GitHub rate limit has no saved reset.', 'github', null],
  ['Waiting for CI result.', 'ci', null],
  ['Waiting for the review lease.', 'review', null],
]) test(`3091 backfill legacy ${kind} cause names its blocker`, async t => {
  const {f, tick} = await setup(t);
  const held = f.record(); held.state = 'stuck'; held.parkReason = reason; save(f, held);
  await tick();
  assert.equal(f.record().parking?.phase, 'parked', 'saved external stop must close its panes');
  assert.deepEqual(f.record().parking.blocker, {kind, until});
});

test('3091 backfill legacy release number never substitutes for installed fix evidence', async t => {
  const {f, tick, ports} = await setup(t);
  const held = f.record(); held.state = 'paused'; held.blockedOn = {kind: 'pdd', until: '1.2.3'}; save(f, held);
  await tick();
  ports.packageVersion = '999.0.0'; await tick();
  assert.equal(f.record().parking?.phase, 'parked', 'release number alone must not wake a saved PDD fix wait');
  assert.equal(launches(f).length, 0);
});

test('3091 backfill installed workflow capability clears a saved route stop without a version override', async t => {
  const {f, tick} = await setup(t);
  const held = f.record(); held.state = 'stuck'; held.parkReason = 'Waiting for missing PDD feature #2897.'; save(f, held);
  await tick();
  assert.equal(f.record().state, 'running', 'the invoked workflow module contains the re-entry route');
  assert.equal(f.record().parking, undefined);
  assert.equal(launches(f).length, 1); assert.equal(deliveries(f).length, 1);
  assert.match(JSON.stringify(deliveries(f)[0]), /re-entry/);
});

test('3091 backfill installed commit evidence uses the package checkout instead of the run checkout', async t => {
  const {f, tick, ports} = await setup(t);
  const held = f.record(); held.state = 'paused'; held.blockedOn = {kind: 'pdd', until: 'commit:' + 'f'.repeat(40)}; save(f, held);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  const head = f.git(packageRoot, 'rev-parse', 'HEAD');
  const result = await parkAutomaticRun({cwd: held.root, reason: 'Wait for the installed fix', blocker: 'pdd', until: `commit:${head}`}, parkCommandPorts(f));
  assert.equal(result.exitCode, 0, 'commit evidence must be accepted through the park boundary');
  await tick();
  assert.equal(f.record().parking, undefined, 'installed ancestor commit must clear its blocker');
  assert.equal(launches(f).length, 1);
});

test('3091 backfill status excludes idle stopped work and shows parked blockers after tick', async t => {
  const {f, tick, ports, stateFile} = await setup(t);
  const held = f.record(); held.state = 'stuck'; held.parkReason = 'Interpreter saved read is unknown (runner-stopped).'; save(f, held);
  const statusPath = join(f.state, createHash('sha256').update(f.source).digest('hex').slice(0, 20) + '.json');
  const status = async () => {
    writeFileSync(statusPath, readFileSync(stateFile));
    return runAutopilotLauncher({command: 'status', cwd: f.source, env: f.ports.env, packageRoot},
      {...ports, stateRoot: f.state, timer: async () => false, allocationCheck: async () => ({state: 'ready'}), alertStatusLine: () => ''});
  };
  const before = await status(); assert.equal(before.exitCode, 0, before.message);
  assert.match(before.message, /working 0 of 1/);
  ports.readSuiteProgress = () => ({state: 'running'});
  const active = await status(); assert.equal(active.exitCode, 0, active.message);
  assert.match(active.message, /working 1 of 1/, 'an active check is real working capacity');
  delete ports.readSuiteProgress;
  await tick();
  const parked = await status(); assert.equal(parked.exitCode, 0, parked.message);
  assert.match(parked.message, /working 0 of 1/); assert.match(parked.message, /parked 1 \(interpreter 1\)/);
});

test('3091 backfill a queued legacy interpreter probe stays pending until worker room exists', async t => {
  const {f, tick, ports, stateFile} = await setup(t);
  fullTicks(f, stateFile, ports);
  const second = await anotherRun(f, 18), third = await anotherRun(f, 19), worker = await anotherRun(f, 20);
  for (const [i, get] of [f.record, second, third].entries()) {
    const run = get(); delete run.blockedOn; run.state = 'stuck';
    run.parkReason = 'Interpreter outage before the check was sent.'; run.updatedAt = f.clock - 3000 + i * 1000; save(f, run);
  }
  const active = worker(); delete active.blockedOn; active.state = 'running'; save(f, active);
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto', trust: [], parking: {maxParked: 10}}}));
  f.herdr.calls.length = 0;
  await tick();
  assert.equal(JSON.parse(readFileSync(stateFile)).parking.parked, 3, 'legacy interpreter waits must park behind the active worker');
  const probe = JSON.parse(readFileSync(stateFile)).runtime.outage.probe;
  assert.equal(probe.number, 17);
  await tick();
  assert.deepEqual(JSON.parse(readFileSync(stateFile)).runtime.outage.probe, probe);
  assert.equal(launches(f).filter(args => args.at(-1).includes('--resume')).length, 0);
});

test('3091 backfill an independent question replaces an inferred interpreter wait', async t => {
  const {f, tick} = await setup(t);
  const held = f.record(); held.state = 'stuck'; held.parkReason = 'Interpreter saved read is unknown (runner-stopped).'; save(f, held);
  await tick(); assert.equal(f.record().parking?.blocker.kind, 'interpreter', 'legacy interpreter evidence must first park');
  const question = f.record(); question.question = {at: f.clock, text: 'Which independent product option should this run use?'}; save(f, question);
  await tick();
  assert.equal(f.record().parking.blocker.kind, 'person');
  assert.deepEqual(f.record().parking.personWait.question, question.question);
  assert.equal(launches(f).length, 0);
});

for (const cause of ['pdd', 'interpreter reason', 'stuckCause', 'interpreter reason and stuckCause'])
  test(`3091 repair 1 ${cause} wake retires its cause before a later person gate`, async t => {
    const {f, tick, ports, stateFile, warnings} = await setup(t);
    const held = f.record(); held.state = 'stuck';
    if (cause === 'pdd') held.parkReason = 'Waiting for missing PDD feature #2897.';
    else {
      fullTicks(f, stateFile, ports);
      ports.runtimeHealth = async () => ({state: 'unavailable', detail: 'controlled outage'});
      if (cause.includes('reason')) held.parkReason = 'Interpreter outage before the check was sent.';
      if (cause.includes('stuckCause')) held.stuckCause = 'interpreter';
    }
    save(f, held);
    await tick();
    if (cause !== 'pdd') {
      assert.equal(f.record().parking?.blocker.kind, 'interpreter');
      ports.runtimeHealth = async () => ({state: 'healthy', detail: 'controlled recovery'});
      await tick();
    }
    assert.equal(f.record().state, 'running');
    assert.equal(f.record().parking, undefined);
    assert.equal(launches(f).length, 1); assert.equal(deliveries(f).length, 1);
    assert.equal(f.record().chats.at(-1).session.id, held.chats.at(-1).session.id);

    f.tick(60001);
    const waiting = f.record(); waiting.state = 'waiting';
    waiting.gate = {kind: 'ask-code', area: waiting.areas[waiting.area].name, at: f.clock};
    save(f, waiting); f.herdr.idle(); f.herdr.calls.length = 0;
    await tick(); await tick();
    const parked = f.record();
    assert.equal(parked.parking?.blocker.kind, 'person', 'consumed recovery must not own a later person gate');
    assert.equal(parked.parking.phase, 'parked');
    assert.equal(parked.state, 'waiting'); assert.deepEqual(parked.gate, waiting.gate);
    assert.deepEqual(parked.decisions, waiting.decisions);
    assert.equal(launches(f).length, 0); assert.equal(deliveries(f).length, 0);
    assert.deepEqual(JSON.parse(readFileSync(stateFile)).parking.blockers, {person: 1});
    assert.equal(JSON.parse(readFileSync(stateFile)).parking.working, 0);
    assert.equal(parked.parkReason, undefined); assert.equal(parked.stuckCause, undefined);
    assert.deepEqual(warnings, []);

    // A new saved cause must still replace that person wait, without consuming its gate/question.
    const changed = f.record(); changed.state = 'stuck';
    changed.parkReason = 'Waiting for issue #321 to merge.'; changed.stuckCause = 'work';
    changed.question = {at: f.clock, text: 'Waiting for issue #321 to merge.'};
    save(f, changed); await tick();
    assert.deepEqual(f.record().parking.blocker, {kind: 'dependency', until: '321'});
    assert.equal(f.record().parkReason, changed.parkReason); assert.equal(f.record().stuckCause, 'work');
    assert.deepEqual(f.record().gate, changed.gate); assert.deepEqual(f.record().question, changed.question);

    if (cause === 'pdd') {
      const retry = f.record(); retry.blockedOn = {kind: 'pdd', until: '#2897'};
      save(f, retry);
      const herdr = ports.herdr;
      let replacement;
      ports.herdr = async args => {
        const result = await herdr(args);
        if (args[0] === 'agent' && args[1] === 'prompt') {
          replacement = f.record(); replacement.state = 'stuck';
          replacement.parkReason = 'Waiting for issue #322 to merge.'; replacement.stuckCause = 'work';
          replacement.blockedOn = {kind: 'dependency', until: '322'};
          save(f, replacement);
        }
        return result;
      };
      await tick();
      assert.ok(replacement, 'save a new stop during recovery notice delivery');
      assert.equal(f.record().parkReason, replacement.parkReason); assert.equal(f.record().stuckCause, 'work');
      assert.deepEqual(f.record().gate, retry.gate); assert.deepEqual(f.record().question, retry.question);
      f.herdr.calls.length = 0; await tick();
      assert.deepEqual(f.record().parking.blocker, {kind: 'dependency', until: '322'});
      assert.equal(launches(f).length, 0); assert.equal(deliveries(f).length, 0);
    }
  });

for (const hold of ['paused', 'idle', 'resume']) test(`3091 integration: preserve existing ${hold} custody without a new blocker`, async t => {
  const {f, tick, ports} = await setup(t), run = f.record(), alerts = [];
  if (hold === 'paused') run.state = 'paused';
  else {
    run.state = 'stuck'; run.parkReason = 'Controlled native recovery ceiling.';
    run[hold === 'idle' ? 'chatIdleLimit' : 'chatResumeLimit'] = {area: run.chats.at(-1).area, at: f.clock};
  }
  save(f, run);
  ports.sendAlert = async input => {alerts.push(input); return {exitCode: 0};};
  await tick(); await tick();
  assert.equal(f.record().parking, undefined, 'existing recovery custody must not become an unknown park');
  for (const key of ['state', 'parkReason', 'chatIdleLimit', 'chatResumeLimit', 'gate', 'question', 'done', 'chats'])
    assert.deepEqual(f.record()[key], run[key]);
  assert.equal(f.herdr.calls.filter(a => ['tab', 'workspace'].includes(a[0]) && a[1] === 'close').length, 0);
  if (hold === 'paused') assert.equal(alerts.length, 0);
  assert.equal(launches(f).length, 0); assert.equal(deliveries(f).length, 0);
  // A separate observed limit still uses the existing named-blocker route.
  const until = f.clock + 3600000;
  ports.chatHealth = async () => ({kind: 'usage-limit', until});
  await tick();
  assert.equal(f.record().parking?.phase, 'parked');
  assert.deepEqual(f.record().parking.blocker, {kind: 'account', until: new Date(until).toISOString()});
});


for(const facts of [{reason:{code:'binding-missing'}},{refusals:[{code:'binding-missing'}]},
  {compatibility:{association:'matched',state:'missing-binding'}}])
  test(`3135: a completed check with ${Object.keys(facts)[0]} binding refusal parks at its automatic gate`,async t=>{
    const {f,tick,ports,stateFile}=await setup(t);fullTicks(f,stateFile,ports);
    const held=f.record();held.state='waiting';held.gate={kind:'approve-pr',area:held.areas[held.area].name};held.done.check='No binding verdict';save(f,held);
    ports.readRunResults=()=>[{kind:'pdd test',batch:'20261101-120000-abcd',at:f.clock,states:[{test:'tests/value.json',state:'not run',...facts}]}];
    await tick();assert.equal(f.record().parking?.blocker.kind,'binding','3135_SAVED_RESULT_BINDING');
    f.tick();await tick();assert.equal(f.record().parking?.blocker.kind,'binding');
  });
