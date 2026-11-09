import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {healthyMachine} from './helpers/healthy-machine.mjs';
import {isolatedCheckCapacity} from './helpers/check-machine.mjs';
import {tickAutopilot, runAutopilotLauncher} from '../src/autopilot-launcher.mjs';
import {runPdd} from '../src/pdd-cli.mjs';
import {parkAutomaticRun} from '../src/workflow-runner.mjs';

const save = run => writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
async function setup(t, {full = false} = {}) {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  f.herdr.idle(); // A stopped worker has completed its native turn.
  const run = f.record();
  run.automaticOrigin = {repository: run.repo, coordinatorId: 'route-owner', machine: 'route-machine', claim: {commentId: '11', labelEventId: '12'}};
  save(run);
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto', trust: []}}));
  const stateFile = join(f.state, 'launcher.json');
  writeFileSync(stateFile, JSON.stringify({enabled: true, defaultBranch: 'main', baseBranch: 'main', stateFile,
    cwd: f.source, repo: run.repo, packageRoot, runs: 1, coordinatorId: 'route-owner', machine: 'route-machine', activatedAt: 1,
    agent: {id: 'claude', kind: 'claude', command: 'claude'}, environment: f.ports.env,
    ...(full ? {recipeDelivered: true} : {retryAt: f.clock + 86400000})}));
  const warnings = [], creates = [];
  const ports = {...healthyMachine, ...f.ports, sendDigest: async () => ({exitCode: 0}),
    installedPddCapabilities: [], checkCapacityPorts: isolatedCheckCapacity(f.base),
    run: async (file, args, options) => ({code: 0, ...await f.ports.execFile(file, args, options)}),
    warn: message => warnings.push(message), reconcileDependencyIntake: async () => ({eligible: [], claims: [], groups: [], queued: [], skipped: []}),
    queryIssues: async () => ({status: 200, issues: []}), comments: async () => [],
    runtimeHealth: async () => ({state: 'healthy', detail: 'controlled health'}), sendAlert: async () => ({exitCode: 0}),
    createRouteIssue: async input => {creates.push(input); return {url: 'https://github.com/promptdriven/pdd/issues/9999'};}};
  f.herdr.calls.length = 0;
  ports.owners = {read: async () => ({json: JSON.stringify({localOwner: 'route-owner', claims: [{issue: f.record().issue.url, active: true, owner: 'route-owner', coordinatorId: 'route-owner', machine: 'route-machine', commentId: '11', labelEventId: '12'}]})})};
  return {f, ports, creates, warnings, tick: () => tickAutopilot(stateFile, ports), state: () => JSON.parse(readFileSync(stateFile))};
}
const ask = (f, text) => {const run = f.record(); run.state = 'waiting'; run.question = {text, at: f.clock, area: run.areas[run.area].name}; save(run);};
const drafting = 'Which supported native PDD command should draft the executable interface? The installed CLI has no drafting route.';
const replay = 'Which supported native-only verification and approved-case replay route should this run use? The prompt has no established executable Runtime operation.';

for (const [kind, question] of [['interface-drafting', drafting], ['native-replay', replay]])
  test(`3112 legacy ${kind} questions park and count once through repeated ticks`, async t => {
    const {f, tick, state, creates, warnings} = await setup(t);
    ask(f, question);
    await tick(); await tick();
    assert.deepEqual(f.record().parking?.blocker, {kind: 'pdd-route', until: `capability:route-${kind}`});
    assert.deepEqual([state().parking.working, state().parking.parked], [0, 1]);
    assert.equal(state().parking.blockers['missing PDD route'], 1);
    assert.equal(state().routeQuestions.records.length, 1);
    assert.deepEqual(state().routeQuestions.records.map(r => [r.kind, r.run, r.question]), [[kind, 17, question]]);
    assert.equal(state().routeQuestions.groups[0].count, 1);
    assert.equal(creates.length, 0);
    assert.deepEqual(warnings, []);
  });

test('3112 repeated kinds open one grouped issue and retain records across ticks', async t => {
  const {f, tick, state, creates, warnings} = await setup(t, {full: true});
  ask(f, drafting); await tick();
  f.tick(); ask(f, `${drafting} No drafting command is installed.`); await tick();
  await tick();
  assert.equal(creates.length, 1);
  assert.equal(creates[0].kind, 'interface-drafting');
  assert.ok(creates[0].body.includes(drafting));
  assert.ok(creates[0].body.includes('17'));
  assert.equal(state().routeQuestions.groups[0].count, 2);
  assert.equal(state().routeQuestions.groups[0].issue.state, 'opened');
  f.tick(); ask(f, replay); await tick();
  assert.deepEqual(state().routeQuestions.groups.map(g => [g.kind, g.count]), [['interface-drafting', 2], ['native-replay', 1]]);
  assert.equal(creates.length, 1);
  assert.deepEqual(warnings, []);
});

test('3112 uncertain issue creation is not repeated after a later tick', async t => {
  const {f, tick, state, ports} = await setup(t, {full: true});
  let calls = 0; ports.createRouteIssue = async () => {calls++; throw Error('reply lost');};
  ask(f, drafting); await tick(); f.tick(); ask(f, `${drafting} No tool is installed.`);
  await tick(); await tick();
  assert.equal(calls, 1);
  assert.equal(state().routeQuestions.groups[0].issue.state, 'unknown');
  assert.equal(f.record().parking.phase, 'parked');
});

test('3112 explicit route record preserves its identity and rejects mixed park modes', async t => {
  const {f} = await setup(t);
  const commandPorts = {...f.ports, owners: {read: async () => ({json: JSON.stringify({localOwner: 'route-owner', claims: [{issue: f.record().issue.url, active: true, owner: 'route-owner', coordinatorId: 'route-owner', machine: 'route-machine', commentId: '11', labelEventId: '12'}]})})}};
  const input = {cwd: f.record().root, route: 'custom-route', reason: 'Which supported PDD route can renew this evidence?'};
  assert.equal((await parkAutomaticRun(input, commandPorts)).exitCode, 0);
  const record = f.record();
  assert.equal(record.blockedOn?.kind, 'pdd-route');
  assert.equal(record.routeWait.question, input.reason);
  f.tick(); assert.equal((await parkAutomaticRun(input, commandPorts)).exitCode, 0);
  assert.deepEqual(f.record().routeWait, record.routeWait);
  for (const extra of [{runtime: true}, {blocker: 'pdd'}, {route: '../bad'}, {until: '999.0.0'}, {step: 'alien-step'}]) {
    const before = f.record();
    assert.equal((await parkAutomaticRun({...input, ...extra}, commandPorts)).exitCode, 1);
    assert.deepEqual(f.record(), before);
  }
});

for (const native of [false, true]) test(`3112 installed capability wakes once; package versions and issue closure do not wake (native=${native})`, async t => {
  const {f, tick, ports, state, warnings} = await setup(t);
  ask(f, drafting); const original = f.record(); await tick();
  ports.packageVersion = '999.0.0'; ports.blockerCleared = async () => true;
  await tick(); assert.equal(f.record().parking.phase, 'parked');
  if (native) delete ports.installedPddCapabilities;
  else ports.installedPddCapabilities = ['route-interface-drafting'];
  await tick();
  assert.equal(f.record().parking, undefined);
  assert.equal(f.record().question, undefined);
  assert.equal(state().routeQuestions.records[0].question, drafting);
  assert.equal(f.record().chats.at(-1).session.id, original.chats.at(-1).session.id);
  const launches = () => f.herdr.calls.filter(a => a[0] === 'pane' && a[1] === 'run').length;
  assert.equal(launches(), 1); await tick(); assert.equal(launches(), 1);
  assert.deepEqual(warnings, []);
});

test('3112 independent product questions and foreign coordinator records retain their custody', async t => {
  const {f, tick, state, ports, creates} = await setup(t);
  ask(f, 'Which supported payment option should the product offer?'); await tick();
  assert.equal(f.record().parking.blocker.kind, 'person');
  assert.equal((state().routeQuestions?.records ?? []).length, 0);
  const run = f.record(); run.automaticOrigin.coordinatorId = 'other-owner';
  run.question.text = drafting; save(run); await tick();
  assert.equal((state().routeQuestions?.records ?? []).length, 0); assert.equal(creates.length, 0);
  assert.equal(f.record().question.text, drafting);
});

test('3112 separate route reports survive another park before the next tick', async t => {
  const {f, ports, tick, state, creates} = await setup(t, {full: true});
  const input = {cwd: f.record().root, route: 'interface-drafting', reason: drafting};
  assert.equal((await parkAutomaticRun(input, ports)).exitCode, 0);
  f.tick();
  assert.equal((await parkAutomaticRun({...input, reason: `${drafting} Also missing from tools.`}, ports)).exitCode, 0);
  assert.equal((await parkAutomaticRun({cwd: input.cwd, blocker: 'pdd', until: 'capability:another-fix', reason: 'Another external wait'}, ports)).exitCode, 0);
  await tick();
  assert.equal(state().routeQuestions?.records?.length, 2);
  assert.equal(state().routeQuestions.groups[0].count, 2);
  assert.equal(creates.length, 1);
  await tick(); assert.equal(state().routeQuestions.records.length, 2);
});

for (const question of ['Which supported PDD version should the product require?',
  'Which supported native PDD verification route should the product prefer?'])
  test('3112 route vocabulary in an independent decision never supplies missing-route evidence: ' + question, async t => {
    const {f, tick, ports, state} = await setup(t);
    ask(f, question); await tick();
    ports.installedPddCapabilities = ['route-supported-route', 'route-native-replay'];
    await tick();
    assert.equal(f.record().parking.blocker.kind, 'person');
    assert.equal(f.record().question.text, question);
    assert.equal((state().routeQuestions?.records ?? []).length, 0);
  });

test('3112 installed route wake preserves an independent question and gate', async t => {
  const {f, tick, ports} = await setup(t);
  const run = f.record();
  run.question = {text: 'Choose a product option', at: f.clock, area: run.areas[run.area].name};
  run.gate = {kind: 'approve', area: run.areas[run.area].name, at: f.clock}; save(run);
  assert.equal((await parkAutomaticRun({cwd: run.root, route: 'interface-drafting', reason: drafting}, ports)).exitCode, 0);
  await tick(); ports.installedPddCapabilities = ['route-interface-drafting']; await tick();
  assert.equal(f.record().parking, undefined);
  assert.deepEqual(f.record().question, run.question);
  assert.deepEqual(f.record().gate, run.gate);
  assert.deepEqual(f.record().decisions, run.decisions);
  assert.equal(f.record().state, 'waiting');
});

test('3112 CLI forwards route fields through the real parser and dispatcher', async t => {
  const {f} = await setup(t);
  let observed;
  const stream = {write() {}};
  const exit = await runPdd(['workflow', 'park', '--route', 'custom-route', '--reason', 'Missing custom native route', '--until', 'capability:custom', '--step', 'plan'],
    {cwd: f.record().root, env: f.ports.env, stdout: stream, stderr: stream,
      workflowRunner: {parkAutomaticRun: async input => {observed = input; return {exitCode: 0, message: 'saved'};}}});
  assert.equal(exit, 0);
  assert.equal(observed.route, 'custom-route'); assert.equal(observed.until, 'capability:custom'); assert.equal(observed.step, 'plan');
});

test('3112 JSON status exposes the local ledger without GitHub calls', async t => {
  const {f, tick, state} = await setup(t);
  ask(f, drafting); await tick();
  const result = await runAutopilotLauncher({command: 'status', json: true, cwd: f.source, env: f.ports.env},
    {stateRoot: f.state, costRuns: async () => [], run: async () => assert.fail('Status must not call a program')});
  assert.equal(result.exitCode, 0, result.message);
  const report = JSON.parse(result.message);
  assert.equal(report.routeQuestions?.length, 1);
  assert.deepEqual(report.routeQuestions[0].records, state().routeQuestions.records);
});

test('3112 native issue adapter sends one structured PDD issue write through the fake program port', async t => {
  const {f, tick, ports, state} = await setup(t, {full: true});
  delete ports.createRouteIssue;
  const original = ports.run, writes = [];
  ports.run = async (file, args, options) => {
    if (file === 'gh' && args.includes('POST') && args.includes('repos/promptdriven/pdd/issues')) {
      writes.push(args);
      return {code: 0, stdout: JSON.stringify({html_url: 'https://github.com/promptdriven/pdd/issues/9999'}), stderr: ''};
    }
    return original(file, args, options);
  };
  ask(f, drafting); await tick(); f.tick(); ask(f, `${drafting} No tool is available.`); await tick(); await tick();
  assert.equal(writes.length, 1);
  assert.ok(writes[0].some(arg => arg.startsWith('body=') && arg.includes(drafting)));
  assert.equal(state().routeQuestions.groups[0].issue.state, 'opened');
});


test('3131 installed code-only checker wakes a saved route once and keeps independent questions', async t => {
  const {f, tick, ports, state, warnings} = await setup(t);
  const question = 'How can a correct unchanged prompt receive a code-only checker verdict?';
  ask(f, 'Which product cases should the next release include?');
  assert.equal((await parkAutomaticRun({cwd: f.record().root, route: 'code-only-checker', reason: question}, ports)).exitCode, 0);
  const original = f.record(); await tick();
  assert.equal(f.record().parking?.phase, 'parked');
  assert.equal(f.record().parking.blocker.until, 'capability:route-code-only-checker');
  delete ports.installedPddCapabilities; // Use installed package evidence, not an override.
  await tick();
  assert.equal(f.record().parking, undefined);
  assert.equal(f.record().routeWait, undefined);
  assert.deepEqual(f.record().question, original.question);
  assert.deepEqual(f.record().done, original.done);
  assert.deepEqual(f.record().approvals, original.approvals);
  assert.equal(f.record().chats.at(-1).session.id, original.chats.at(-1).session.id);
  assert.equal(state().routeQuestions.records[0].question, question);
  assert.equal(f.record().routeReports.length, 1);
  const launches = () => f.herdr.calls.filter(a => a[0] === 'pane' && a[1] === 'run').length;
  assert.equal(launches(), 1); await tick(); assert.equal(launches(), 1);
  assert.deepEqual(warnings, []);
});


test('integration 013: grouped route subjects use numeric authority and retain held work', async t => {
  const rows = [];
  for (const authority of ['clear', 'held', 'unknown']) {
    const {f, ports, tick, creates} = await setup(t, {full: true});
    ask(f, drafting); await tick();
    const observations = [];
    ports.readManualHold = async input => {
      observations.push(input.issue);
      return {known: authority !== 'unknown', held: authority === 'held'};
    };
    // An active check retains custody while the person hold suppresses new work.
    ports.readSuiteProgress = () => ({state: 'running'});
    f.tick(); ask(f, `${drafting} No drafting tool is available.`);
    await tick(); await tick();
    rows.push({authority, creates: creates.length,
      numeric: observations.length > 0 && observations.every(number => number === 17)});
  }
  assert.deepEqual(rows, [
    {authority: 'clear', creates: 1, numeric: true},
    {authority: 'held', creates: 0, numeric: true},
    {authority: 'unknown', creates: 0, numeric: true},
  ]);
});
