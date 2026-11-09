import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {existsSync, readFileSync, writeFileSync, cpSync, mkdirSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {automaticFixture} from './helpers/autopilot-run-base-fixture.mjs';
import {approveRun, stepDone} from '../src/workflow-runner.mjs';
import {captureSource} from '../src/runtime-preflight.mjs';
import {renderJson} from '../src/runtime-output.mjs';
import {join, dirname} from 'node:path';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {healthyMachine} from './helpers/healthy-machine.mjs';
import {isolatedCheckCapacity} from './helpers/check-machine.mjs';
import {githubLedger} from '../src/github-calls.mjs';
import {tickAutopilot, runAutopilotLauncher} from '../src/autopilot-launcher.mjs';

test('manual hold waits for check custody and retains the run', async t => {
  const f = await fixture(t, {agent:'claude', name:'small-change'});
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  run.automaticOrigin = {repository:run.repo, coordinatorId:'owner', machine:'machine', claim:{commentId:'11', labelEventId:'12'}};
  writeFileSync(join(run.runDir,'status.json'), JSON.stringify(run));
  f.ports.owners = {read:async input => ({json:JSON.stringify({localOwner:'owner', claims:input.issues.map(issue => ({issue, active:true, owner:'owner', coordinatorId:'owner', machine:'machine', commentId:'11', labelEventId:'12'}))})})};
  writeFileSync(join(f.source,'pdd.json'), JSON.stringify({autopilot:{mode:'auto',trust:[]}}));
  const stateFile = join(f.state,'launcher.json');
  writeFileSync(stateFile, JSON.stringify({enabled:true,defaultBranch:'main',baseBranch:'main',stateFile,cwd:f.source,repo:run.repo,packageRoot,runs:1,coordinatorId:'owner',machine:'machine',activatedAt:1,agent:{id:'claude',kind:'claude',command:'claude'},environment:f.ports.env}));
  let busy = true, released = 0, reads = 0, observed = {known:true,held:true};
  const ports = {...healthyMachine,...f.ports,sendDigest:async()=>({exitCode:0}),checkCapacityPorts:isolatedCheckCapacity(f.base),
    run:async(file,args,options)=>({code:0,...await f.ports.execFile(file,args,options)}),warn:()=>{},
    queryIssues:async()=>({status:429,resetAt:f.clock-1}), comments:async()=>[], readManualHold:async()=>{reads++; return typeof observed === 'function' ? observed() : observed;}, readSuiteProgress:()=>({state:busy?'running':'finished'}),
    releaseParkedClaim:async()=>{released++; if (released === 1) { observed = {known:true,held:false}; return {state:'unknown'}; } return {state:'released'};}};
  const waiting = JSON.parse(readFileSync(stateFile));
  waiting.retryAt = f.clock + 86400000;
  writeFileSync(stateFile, JSON.stringify(waiting));
  await tickAutopilot(stateFile,ports);
  assert.equal(reads, 0);
  delete waiting.retryAt;
  writeFileSync(stateFile, JSON.stringify(waiting));
  observed = {known:false};
  await tickAutopilot(stateFile,ports);
  assert.deepEqual(JSON.parse(readFileSync(stateFile)).manualIssues ?? [], []);
  observed = {known:true,held:true};
  await tickAutopilot(stateFile,ports);
  assert.equal(released,0); assert.equal(f.record().runId,run.runId); assert.ok(existsSync(run.root));
  observed = {known:false};
  await tickAutopilot(stateFile,ports);
  assert.deepEqual(JSON.parse(readFileSync(stateFile)).manualIssues, [run.number]);
  observed = {known:true,held:true};
  busy=false; await tickAutopilot(stateFile,ports);
  assert.equal(released,0); assert.equal(f.record().parking,undefined);
  for (const pane of f.herdr.panes) if (pane.agent) pane.agent.agent_status = 'unknown';
  await tickAutopilot(stateFile,ports); assert.equal(released,0);
  f.herdr.idle(); await tickAutopilot(stateFile,ports);
  assert.equal(released,1); assert.equal(f.record().parking.phase,'releasing');
  const legacy = f.record();
  delete legacy.parking.releaseAttempted;
  writeFileSync(join(run.runDir,'status.json'), JSON.stringify(legacy));
  await tickAutopilot(stateFile,ports);
  assert.equal(released,2); assert.equal(f.record().state,'cancelled');
  assert.equal(f.record().branch,run.branch); assert.deepEqual(f.record().done,run.done); assert.ok(existsSync(run.root));
  assert.deepEqual(JSON.parse(readFileSync(stateFile)).manualIssues,[]);
});

test('manual release respects the reserve budget', async t => {
  const f = await fixture(t, {agent:'claude', name:'small-change'});
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  run.automaticOrigin = {repository:run.repo, coordinatorId:'owner', machine:'machine', claim:{commentId:'11', labelEventId:'12'}};
  writeFileSync(join(run.runDir,'status.json'), JSON.stringify(run));
  f.ports.owners = {read:async input => ({json:JSON.stringify({localOwner:'owner', claims:input.issues.map(issue => ({issue, active:true, owner:'owner', coordinatorId:'owner', machine:'machine', commentId:'11', labelEventId:'12'}))})})};
  writeFileSync(join(f.source,'pdd.json'), JSON.stringify({autopilot:{mode:'auto',trust:[]}}));
  const stateFile = join(f.state,'launcher.json');
  writeFileSync(stateFile, JSON.stringify({enabled:true,defaultBranch:'main',baseBranch:'main',stateFile,cwd:f.source,repo:run.repo,packageRoot,runs:1,coordinatorId:'owner',machine:'machine',activatedAt:1,agent:{id:'claude',kind:'claude',command:'claude'},environment:f.ports.env}));
  let busy = true, released = 0, reads = 0, observed = {known:true,held:true};
  const ports = {...healthyMachine,...f.ports,sendDigest:async()=>({exitCode:0}),checkCapacityPorts:isolatedCheckCapacity(f.base),
    run:async(file,args,options)=>({code:0,...await f.ports.execFile(file,args,options)}),warn:()=>{},
    queryIssues:async()=>({status:429,resetAt:f.clock-1}), comments:async()=>[], readManualHold:async()=>{reads++; return typeof observed === 'function' ? observed() : observed;}, readSuiteProgress:()=>({state:busy?'running':'finished'}),
    releaseParkedClaim:async()=>{released++; if (released === 1) { observed = {known:true,held:false}; return {state:'unknown'}; } return {state:'released'};}};
  githubLedger({root:f.state, repository:run.repo}).record({at:f.clock,api:'rest',purpose:'other',status:200,resource:'core',remaining:10,limit:5000,resetAt:f.clock+3600000});
  f.herdr.idle(); busy = false;
  await tickAutopilot(stateFile, ports);
  assert.equal(reads, 0);
  assert.equal(released, 0);
  assert.equal(f.record().parking, undefined);
  f.tick(3600001);
  await tickAutopilot(stateFile, ports);
  assert.equal(released, 1);
  await tickAutopilot(stateFile, ports);
  assert.equal(released, 2);
  assert.equal(f.record().state, 'cancelled');
  assert.equal(f.record().branch, run.branch);
  assert.ok(existsSync(run.root));
});

test('removing the label before remote release recovers the saved run', async t => {
  const f = await fixture(t, {agent:'claude', name:'small-change'});
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  run.automaticOrigin = {repository:run.repo, coordinatorId:'owner', machine:'machine', claim:{commentId:'11', labelEventId:'12'}};
  writeFileSync(join(run.runDir,'status.json'), JSON.stringify(run));
  f.ports.owners = {read:async input => ({json:JSON.stringify({localOwner:'owner', claims:input.issues.map(issue => ({issue, active:true, owner:'owner', coordinatorId:'owner', machine:'machine', commentId:'11', labelEventId:'12'}))})})};
  writeFileSync(join(f.source,'pdd.json'), JSON.stringify({autopilot:{mode:'auto',trust:[]}}));
  const stateFile = join(f.state,'launcher.json');
  writeFileSync(stateFile, JSON.stringify({enabled:true,defaultBranch:'main',baseBranch:'main',stateFile,cwd:f.source,repo:run.repo,packageRoot,runs:1,coordinatorId:'owner',machine:'machine',activatedAt:1,agent:{id:'claude',kind:'claude',command:'claude'},environment:f.ports.env}));
  let busy = true, released = 0, reads = 0, observed = {known:true,held:true};
  const ports = {...healthyMachine,...f.ports,sendDigest:async()=>({exitCode:0}),checkCapacityPorts:isolatedCheckCapacity(f.base),
    run:async(file,args,options)=>({code:0,...await f.ports.execFile(file,args,options)}),warn:()=>{},
    queryIssues:async()=>({status:429,resetAt:f.clock-1}), comments:async()=>[], readManualHold:async()=>{reads++; return typeof observed === 'function' ? observed() : observed;}, readSuiteProgress:()=>({state:busy?'running':'finished'}),
    releaseParkedClaim:async()=>{released++; if (released === 1) { observed = {known:true,held:false}; return {state:'unknown'}; } return {state:'released'};}};
  f.herdr.idle(); busy = false;
  let count = 0;
  observed = () => ({known:true, held:++count < 3});
  await tickAutopilot(stateFile, ports);
  assert.equal(released, 0);
  assert.equal(f.record().parking?.phase, 'releasing');
  observed = {known:true, held:false};
  await tickAutopilot(stateFile, ports);
  assert.equal(released, 0);
  assert.equal(f.record().runId, run.runId);
  assert.notEqual(f.record().parking?.phase, 'releasing');
  assert.notEqual(f.record().state, 'cancelled');
});

const STORY = 'user_stories/place-order.md', TEST = 'tests/place-order.json', PROMPT = 'prompts/place_order.prompt.md';
let batches = 0;
function saveCheck(f, {state = 'passed', criteria = {passed: 3, total: 3}} = {}) {
  const batch = `20261027-170000-${String(++batches).padStart(4, '0')}`, folder = join(f.ports.env.PDD_STATE_DIR, 'batches', batch);
  const capture = captureSource(f.run.root, {tests: [TEST], appMap: null});
  mkdirSync(folder, {recursive: true});
  writeFileSync(join(folder, 'batch.json'), JSON.stringify({version: 1, batch, root: f.run.root, created_at: new Date(f.clock).toISOString(), intent: 'check',
    source_sha256: capture.sha256, files: capture.files.map(file => file.path), contract_snapshots: capture.stories, rows: [{test: TEST, state, request_ids: []}]}));
  writeFileSync(join(folder, 'summary.json'), JSON.stringify(renderJson({batch, repo: f.run.root, sourceSha256: capture.sha256,
    exitCode: state === 'passed' ? 0 : 1, rows: [{test: TEST, story: STORY, state, criteria}], summaryLine: 'synthetic check'})));
  return batch;
}
async function gateSetup(t, {registered = false, beforeApproval} = {}) {
  const f = await automaticFixture(t);
  assert.equal((await f.begin()).exitCode, 0);
  f.run = f.record();
  f.ports.env.PDD_STATE_DIR = join(f.state, 'runtime');
  f.automaticPorts.env.PDD_STATE_DIR = f.ports.env.PDD_STATE_DIR;
  f.done = async (step, extra = {}) => {
    f.tick();
    if (registered) await runStatus({ref: '17', cwd: f.source}, f.automaticPorts);
    const result = await stepDone({step, summary: `synthetic ${step}`, cwd: f.run.root, ...extra}, f.automaticPorts);
    assert.equal(result.exitCode, 0, result.message);
    return result;
  };
  await f.done('reproduce');
  const harbor = join(packageRoot, 'test/fixtures/harbor');
  for (const path of [STORY, TEST, PROMPT]) {
    mkdirSync(join(f.run.root, path.slice(0, path.lastIndexOf('/'))), {recursive: true});
    cpSync(join(harbor, path), join(f.run.root, path));
  }
  f.git(f.run.root, 'add', '.'); f.git(f.run.root, 'commit', '-qm', 'Synthetic Story');
  await f.done('prompt-story');
  beforeApproval?.(f);
  const approved = await approveRun({ref: '17', cwd: f.run.root, packageRoot}, f.automaticPorts);
  assert.equal(approved.exitCode, 0, approved.message);
  await f.done('check');
  await f.done('try', {skipped: 'Autopilot optional default'});
  assert.equal(f.record().gate.kind, 'approve-pr');
  const id = createHash('sha256').update(f.source).digest('hex').slice(0, 20);
  f.stateFile = join(f.automaticPorts.autopilotStateRoot, `${id}.json`);
  const state = JSON.parse(readFileSync(f.stateFile, 'utf8'));
  Object.assign(state, {stateFile: f.stateFile, defaultBranch: 'main', baseBranch: 'main', packageRoot,
    agent: {id: 'codex', kind: 'codex', command: 'codex'}, environment: f.automaticPorts.env, recipeDelivered: true});
  writeFileSync(f.stateFile, JSON.stringify(state));
  f.warnings = []; f.intakes = 0;
  f.tickPorts = {...healthyMachine, ...f.automaticPorts, checkCapacityPorts: isolatedCheckCapacity(f.base),
    run: async (file, args, opts) => ({code: 0, ...await f.automaticPorts.execFile(file, args, opts)}),
    warn: text => f.warnings.push(text), sendDigest: async () => ({exitCode: 0}),
    reconcileDependencyIntake: async () => {f.intakes++; f.onIntake?.(); return {eligible: [], queued: [], skipped: []};},
    queryIssues: async () => ({status: 304, issues: []}),
  };
  f.herdr.idle(); // The saved gate follows the worker's completed turn.
  f.scan = () => tickAutopilot(f.stateFile, f.tickPorts);
  f.status = async () => JSON.parse((await runStatus({ref: '17', cwd: f.source, json: true}, f.automaticPorts)).message).runs[0];
  return f;
}

test('manual observation crossing reserve defers PR 1 until the budget resets', async t => {
  const f = await gateSetup(t); saveCheck(f);
  let reads = 0;
  f.tickPorts.readManualHold = async () => {
    reads++;
    githubLedger({root:dirname(f.stateFile), repository:f.run.repo}).record({at:f.clock,api:'rest',purpose:'dependencies',status:200,resource:'core',remaining:10,limit:5000,resetAt:f.clock+3600000});
    return {known:true,held:false};
  };
  await f.scan();
  assert.ok(reads > 0);
  assert.equal(f.prs.length, 0);
  assert.equal(f.record().gate.kind, 'approve-pr');
  f.tick(3600001);
  f.tickPorts.readManualHold = async () => ({known:true,held:false});
  await f.scan();
  assert.equal(f.prs.length, 1, f.warnings.join('\n'));
});

test('fresh clearance of a cached label makes an ended issue eligible again', async t => {
  const f = await gateSetup(t);
  const ended = f.record(); ended.state = 'cancelled';
  writeFileSync(join(ended.runDir, 'status.json'), JSON.stringify(ended));
  const issue = {number:17,state:'open',title:'Ready again',body:'Repair it',user:{login:'example'},author_association:'OWNER',created_at:new Date(f.clock).toISOString(),updated_at:new Date(f.clock).toISOString(),comments:0,labels:['pdd:manual'],html_url:'https://github.com/example/project/issues/17'};
  const saved = JSON.parse(readFileSync(f.stateFile));
  saved.cachedIssues = [issue];
  writeFileSync(f.stateFile, JSON.stringify(saved));
  const status = () => runAutopilotLauncher({command:'status',all:true,cwd:f.source,env:f.automaticPorts.env}, {...f.tickPorts,stateRoot:dirname(f.stateFile)});
  let held = true;
  f.tickPorts.readManualHold = async () => ({known:true, held});
  f.tickPorts.reconcileDependencyIntake = async () => ({eligible:[issue.html_url],queued:[],skipped:[]});
  const events = [];
  f.tickPorts.metricsAppendEvents = async input => events.push(...input.events);
  const originalHerdr = f.tickPorts.herdr;
  f.tickPorts.herdr = async args => args[0] === 'agent' && args[1] === 'get' && args[2] === 'coordinator-pane'
    ? {result:{agent:null}} : originalHerdr(args);
  await f.scan();
  assert.match((await status()).message, /Kept for a person:.*#17/);
  assert.ok(!events.some(event => event.issue === 17 && event.type === 'selection' && event.data.state === 'ready'));
  held = false;
  await f.scan();
  const after = JSON.parse(readFileSync(f.stateFile));
  assert.deepEqual(after.manualIssues, []);
  assert.doesNotMatch((await status()).message, /Kept for a person:.*#17/);
  assert.ok(events.some(event => event.issue === 17 && event.type === 'selection' && event.data.state === 'ready'), 'the cleared issue reaches ordinary intake');
});
