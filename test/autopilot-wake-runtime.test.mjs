import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {join} from 'node:path';
import {fixture,packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {healthyMachine} from './helpers/healthy-machine.mjs';
import {isolatedCheckCapacity} from './helpers/check-machine.mjs';
import {tickAutopilot} from '../src/autopilot-launcher.mjs';
import {runStatus} from '../src/workflow-runner.mjs';
const save=(f,run)=>writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run));
const deliveries=f=>f.herdr.calls.filter(a=>a[0]==='agent'&&a[1]==='prompt');
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


async function world(t) {
  const w=await setup(t,'codex','bug');const {f,ports,stateFile}=w;fullTicks(f,stateFile,ports);
  const issues=new Map(),writes=[];let next=500;
  const exec=ports.run;
  ports.run=async(file,args,opts)=>{
    if(file!=='gh')return exec(file,args,opts);
    const flag=k=>args[args.indexOf(k)+1];
    if(args[0]==='label')return {code:0,stdout:''};
    if(args[0]==='issue') {
      if(args[1]==='list')return {code:0,stdout:JSON.stringify([...issues.values()].filter(i=>i.body.includes(flag('--search').split('"')[1])))};
      writes.push(args);
      if(args[1]==='create') {const i={number:++next,url:`https://github.com/example/project/issues/${next}`,body:flag('--body'),state:'open'};issues.set(next,i);return {code:0,stdout:i.url};}
      const i=issues.get(Number(args[2]));assert.ok(i);
      if(args[1]==='edit')i.body=flag('--body');
      if(args[1]==='reopen')i.state='open';
      return {code:0,stdout:''};
    }
    if(args[0]==='api' && /\/issues\/\d+$/.test(args[1]))return {code:0,stdout:JSON.stringify(issues.get(Number(args[1].split('/').at(-1)))??{state:'open'})};
    return exec(file,args,opts);
  };
  return {...w,issues,writes};
}
const check=(f,code='runner-stopped',batch='20261101-120000-abcd')=>({kind:'pdd test',batch,at:f.clock,tests:['tests/value.json'],states:[{test:'tests/value.json',state:'partial',reason:{code}}]});
for(const kind of ['dependency','pdd','pdd-route','runtime'])test(`3147 any issue close wakes ${kind} once`,async t=>{
  const {f,tick,ports,issues,warnings}=await world(t);
  issues.set(321,{number:321,state:'open',body:''});ports.installedPddCapabilities=[];
  const held=f.record();held.state='paused';held.blockedOn={kind,until:kind==='pdd'||kind==='pdd-route'?'#321':'321'};save(f,held);
  await tick();assert.equal(f.record().parking?.phase,'parked');
  issues.get(321).state='closed';await tick();
  assert.equal(f.record().parking,undefined,'3147_CLOSED_ISSUE_MUST_WAKE');
  const sent=deliveries(f).length;await tick();assert.equal(deliveries(f).length,sent);assert.deepEqual(warnings,[]);
});
for(const code of ['runner-stopped','graph-provider-failure','step_timeout','service-restarted'])test(`3147 ${code} gets Runtime cause issue despite absent health`,async t=>{
  const {f,tick,ports,issues,writes,warnings}=await world(t);ports.runtimeHealth=async()=>({state:'access',detail:'HTTP 401'});
  writeFileSync(join(f.source,'pdd.json'),JSON.stringify({autopilot:{mode:'auto',trust:[],runtimeOwner:'runtime-team'}}));
  const held=f.record();held.state='waiting';held.gate={kind:'approve-pr',area:held.areas[held.area].name};held.done.check={at:f.clock};save(f,held);
  ports.readRunResults=()=>[check(f,code)];
  await tick();
  assert.equal(f.record().parking?.blocker.kind,'runtime','3147_RUNTIME_MUST_PARK_ON_CAUSE');
  assert.equal(issues.size,1);assert.ok(writes.find(a=>a[1]==='create').includes('runtime-team'));
  assert.ok([...issues.values()][0].body.includes('Run #17'));assert.ok([...issues.values()][0].body.includes('20261101-120000-abcd'));
  await tick();assert.equal(issues.size,1);assert.equal(writes.filter(a=>a[1]==='create').length,1);
  issues.values().next().value.state='closed';await tick();
  assert.equal(f.record().parking,undefined,'3147_RUNTIME_CLOSURE_MUST_WAKE');
  assert.equal(f.record().done.check,undefined);assert.deepEqual(f.record().gate,held.gate);assert.deepEqual(warnings,[]);
});
for(const changed of ['value.prompt.md','pdd-bindings.json'])test(`3147 binding wakes only when base ${changed} changes`,async t=>{
  const {f,tick,ports,warnings}=await world(t);const held=f.record();held.state='stuck';held.parkReason='binding-missing';save(f,held);
  mkdirSync(join(held.root,'tests'),{recursive:true});writeFileSync(join(held.root,'tests/value.json'),JSON.stringify({steps:[{entry_path:'value.prompt.md'}]}));
  ports.readRunResults=()=>[{kind:'pdd test',tests:['tests/value.json'],states:[{test:'tests/value.json',state:'not run',reason:{code:'binding-missing'}}]}];
  await tick();assert.equal(f.record().parking?.blocker.kind,'binding');
  f.git(f.source,'update-ref','refs/remotes/origin/main',f.git(f.source,'rev-parse','HEAD'));
  writeFileSync(join(f.source,'unrelated.txt'),'safe');f.git(f.source,'add','.');f.git(f.source,'commit','-m','Unrelated base edit');f.git(f.source,'update-ref','refs/remotes/origin/main','HEAD');
  await tick();assert.equal(f.record().parking?.phase,'parked');
  writeFileSync(join(f.source,changed),'Changed binding contract');f.git(f.source,'add','.');f.git(f.source,'commit','-m','Owning contract edit');f.git(f.source,'update-ref','refs/remotes/origin/main','HEAD');
  await tick();assert.equal(f.record().parking,undefined,'3147_BINDING_BASE_MUST_WAKE');assert.equal(deliveries(f).length,1);assert.deepEqual(warnings,[]);
});

test('3147 three failures of one cause within 30 minutes serialize checks and a later verdict recovers',async t=>{
  const {f,tick,ports,issues,warnings}=await world(t);let current=check(f);const modes=[];
  ports.configureInterpreterTestMode=async input=>modes.push(input.enabled);
  ports.readRunResults=()=>[current];
  const held=f.record();held.state='stuck';held.parkReason='Runtime no-verdict';save(f,held);
  await tick();assert.equal(modes.at(-1),false);assert.equal(issues.size,1);
  for(const [n,code] of [[2,'graph-provider-failure'],[3,'runner-stopped'],[4,'runner-stopped']]) {
    f.tick(1000);current=check(f,code,`20261101-12000${n}-abcd`);await tick();
    assert.equal(modes.at(-1),n===4,'3147_THROTTLE_SAME_CAUSE_ONLY');
  }
  assert.equal(issues.size,2);const sends=deliveries(f).length;
  await tick();assert.equal(modes.at(-1),true);assert.equal(deliveries(f).length,sends);
  f.tick(1000);current={...check(f,'runner-stopped','20261101-120005-abcd'),states:[{test:'tests/value.json',state:'passed'}]};
  await tick();assert.equal(f.record().parking,undefined,'3147_LATER_VERDICT_MUST_WAKE');assert.equal(modes.at(-1),false);
  await tick();assert.equal(deliveries(f).length,sends+1);assert.deepEqual(warnings,[]);
});

test('3147 old failures expire from the 30 minute check throttle',async t=>{
  const {f,tick,ports}=await world(t);let current=check(f);const modes=[];ports.configureInterpreterTestMode=async input=>modes.push(input.enabled);ports.readRunResults=()=>[current];
  const held=f.record();held.state='stuck';held.parkReason='Runtime no-verdict';save(f,held);
  for(let i=1;i<=3;i++){current=check(f,'runner-stopped',`20261101-12000${i}-abcd`);await tick();f.tick(1000);}
  assert.equal(modes.at(-1),true,'3147_THREE_FAILURES_MUST_SERIALIZE');
  f.tick(1800000);await tick();assert.equal(modes.at(-1),false);
});

test('3147 binding issue closure and status expose the current wake condition',async t=>{
  const {f,tick,issues,stateFile}=await world(t);issues.set(321,{number:321,state:'open',body:''});
  const held=f.record();held.state='stuck';held.blockedOn={kind:'binding',until:'321'};save(f,held);
  await tick();const status=JSON.parse(readFileSync(stateFile));assert.ok(status.parking.waits?.some(row=>row.number===17&&row.condition.includes('321')),'3147_STATUS_WAKE_CONDITION');
  issues.get(321).state='closed';await tick();assert.equal(f.record().parking,undefined,'3147_BINDING_ISSUE_CLOSE_WAKE');
});

test('3147 confirmed issue creation rejection retries while an uncertain creation reconciles its marker',async t=>{
  const {f,tick,ports,issues,writes}=await world(t);ports.readRunResults=()=>[check(f)];
  const held=f.record();held.state='stuck';held.parkReason='Runtime no verdict';save(f,held);
  const run=ports.run;let rejected=false,lost=false;
  ports.run=async(file,args,opts)=>{
    if(file==='gh'&&args[0]==='issue'&&args[1]==='create'&&!rejected){rejected=true;return {code:1,stdout:'',stderr:'HTTP 422: temporary rejected create'};}
    const result=await run(file,args,opts);
    if(file==='gh'&&args[0]==='issue'&&args[1]==='create'&&!lost){lost=true;throw Error('response lost after create');}
    return result;
  };
  await tick();assert.equal(issues.size,0);
  await tick();assert.equal(issues.size,1,'3147_CONFIRMED_REJECTION_RETRY');
  await tick();assert.equal(f.record().parking?.blocker.kind,'runtime','3147_UNCERTAIN_CREATE_RECONCILES');
  assert.equal(writes.filter(a=>a[1]==='create').length,1);await tick();assert.equal(issues.size,1);
});

test('3147 a binding hold tracks a separate declared interface file on the base',async t=>{
  const {f,tick,ports}=await world(t);const held=f.record();held.state='stuck';held.parkReason='binding-missing';save(f,held);
  const batch='20261101-120000-abcd',folder=join(f.ports.env.HOME,'.pdd/runtime/batches',batch);mkdirSync(folder,{recursive:true});
  writeFileSync(join(folder,'batch.json'),JSON.stringify({batch,root:held.root,intent:'check',created_at:new Date(f.clock).toISOString(),rows:[{test:'tests/value.json',state:'not run',reason:{code:'binding-missing',prompt:'value.prompt.md',interface_path:'value.interface.json'}}]}));
  await tick();assert.equal(f.record().parking?.blocker.kind,'binding');
  writeFileSync(join(f.source,'value.interface.json'),'{"value":2}');f.git(f.source,'add','.');f.git(f.source,'commit','-m','Restore separate interface');f.git(f.source,'update-ref','refs/remotes/origin/main','HEAD');
  await tick();assert.equal(f.record().parking,undefined,'3147_SEPARATE_INTERFACE_MUST_WAKE');
});

test('3147 an offered health cause groups different batch symptoms and preserves other blockers',async t=>{
  const {f,tick,ports,issues}=await world(t);let current=check(f);ports.readRunResults=()=>[current];ports.runtimeHealth=async()=>({state:'unavailable',cause:{code:'provider-unavailable'}});
  const held=f.record();held.state='stuck';held.parkReason='Runtime no verdict';save(f,held);
  await tick();assert.equal(f.record().parking?.blocker.cause,'provider-unavailable','3147_HEALTH_CAUSE');
  f.tick();current=check(f,'graph-provider-failure','20261101-120001-abcd');await tick();assert.equal(issues.size,1);
  const independent=f.record();independent.question={at:f.clock,text:'Choose the product option'};save(f,independent);
  await tick();assert.equal(f.record().parking.blocker.kind,'person');assert.deepEqual(f.record().question,independent.question);
});
