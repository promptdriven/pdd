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

