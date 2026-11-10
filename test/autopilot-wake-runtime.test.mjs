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
import {classifyRuntimeFailure, reconcileRuntimeIncidents} from '../src/autopilot-runtime.mjs';
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
  const issues=new Map(),writes=[],reports=[];let next=500;
  ports.reportRuntimeCause=async input=>{
    reports.push(structuredClone(input));
    let issue=[...issues.values()].find(row=>row.body.includes(input.marker));
    if(!issue){const number=++next;issue={number,url:`https://github.com/example/project/issues/${number}`,repository:'example/project',body:'',state:'open',assignee:input.runtimeOwner};issues.set(number,issue);}
    issue.body=`${input.marker}\n\n${input.runs.map(row=>`- Run #${row.number}, batch ${row.batch}`).join('\n')}`;issue.state='open';
    return {number:issue.number,url:issue.url,repository:issue.repository};
  };
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
  return {...w,issues,writes,reports};
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
for(const code of ['runner-stopped','graph-provider-failure','step_timeout','service-restarted'])test(`3147 ${code} reports a Runtime cause through the shared port despite absent health`,async t=>{
  const {f,tick,ports,issues,writes,reports,warnings}=await world(t);ports.runtimeHealth=async()=>({state:'access',detail:'HTTP 401'});
  writeFileSync(join(f.source,'pdd.json'),JSON.stringify({autopilot:{mode:'auto',trust:[],runtimeOwner:'runtime-team'}}));
  const held=f.record();held.state='waiting';held.gate={kind:'approve-pr',area:held.areas[held.area].name};held.done.check={at:f.clock};save(f,held);
  ports.readRunResults=()=>[check(f,code)];
  await tick();
  assert.equal(f.record().parking?.blocker.kind,'runtime','3147_RUNTIME_MUST_PARK_ON_CAUSE');
  assert.equal(issues.size,1);assert.equal(reports.length,1);assert.equal(reports[0].runtimeOwner,'runtime-team');
  assert.equal(reports[0].marker,`<!-- pdd:runtime-cause:${f.record().parking.blocker.cause} -->`);
  assert.deepEqual(reports[0].runs,[{number:17,batch:'20261101-120000-abcd'}]);
  assert.ok([...issues.values()][0].body.includes('Run #17'));assert.ok([...issues.values()][0].body.includes('20261101-120000-abcd'));
  await tick();assert.equal(issues.size,1);assert.equal(reports.length,1);assert.equal(writes.length,0);
  issues.values().next().value.state='closed';await tick();
  assert.equal(f.record().parking,undefined,'3147_RUNTIME_CLOSURE_MUST_WAKE');
  assert.equal(f.record().done.check,undefined);assert.deepEqual(f.record().gate,held.gate);
  const sent=deliveries(f).length;await tick();assert.equal(f.record().parking,undefined,'3147_RUNNING_APPROVE_PR_RETRY_IS_NOT_A_PERSON_BLOCKER');
  assert.equal(deliveries(f).length,sent,'3147_RUNTIME_WAKE_MUST_NOT_LOOP');assert.deepEqual(warnings,[]);
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

test('3147 binding wake retries an inferred approve-pr check before person approval',async t=>{
  const {f,tick,ports,warnings}=await world(t),held=f.record();
  held.state='waiting';held.gate={kind:'approve-pr',area:held.areas[held.area].name};held.done.check={at:f.clock,summary:'stale'};
  held.parkReason='binding-missing: owning value.prompt.md interface';save(f,held);
  mkdirSync(join(held.root,'tests'),{recursive:true});writeFileSync(join(held.root,'tests/value.json'),JSON.stringify({steps:[{entry_path:'value.prompt.md'}]}));
  ports.readRunResults=()=>[{kind:'pdd test',tests:['tests/value.json'],states:[{test:'tests/value.json',state:'not run',reason:{code:'binding-missing',prompt:'value.prompt.md'}}]}];
  await tick();assert.equal(f.record().parking?.blocker.kind,'binding');
  f.git(f.source,'update-ref','refs/remotes/origin/main',f.git(f.source,'rev-parse','HEAD'));
  writeFileSync(join(f.source,'value.prompt.md'),'Updated binding contract');f.git(f.source,'add','.');f.git(f.source,'commit','-m','Update owning binding');f.git(f.source,'update-ref','refs/remotes/origin/main','HEAD');
  await tick();
  assert.equal(f.record().parking,undefined,'3147_BINDING_APPROVE_PR_MUST_WAKE');
  assert.equal(f.record().done.check,undefined,'3147_BINDING_WAKE_MUST_CLEAR_OLD_CHECK');
  assert.deepEqual(f.record().gate,held.gate);assert.equal(deliveries(f).length,1);
  assert.match(deliveries(f)[0][3],/binding contract changed/);
  const sent=deliveries(f).length;await tick();
  assert.equal(f.record().parking,undefined,'3147_BINDING_RETRY_GATE_IS_NOT_A_PERSON_BLOCKER');
  assert.equal(deliveries(f).length,sent,'3147_BINDING_WAKE_MUST_NOT_LOOP');assert.deepEqual(warnings,[]);
});

test('3147 binding baseline includes lint paths and run stop reason paths',async t=>{
  const a=await world(t),held=a.f.record();held.state='stuck';held.parkReason='binding-missing: owning value.prompt.md interface';save(a.f,held);
  a.ports.readRunResults=()=>[{kind:'pdd lint',batch:'20261101-120000-abcd',files:['tests/value.json'],
    states:[{test:'tests/value.json',state:'not run',reason:{code:'binding-missing',prompt:'lint.prompt.md',interface_path:'lint.interface.json'}}]}];
  await a.tick();
  const lintPaths=a.f.record().parking?.blocker.paths ?? [];
  assert.ok(lintPaths.includes('lint.prompt.md'),'3147_LINT_PROMPT_PATH');
  assert.ok(lintPaths.includes('lint.interface.json'),'3147_LINT_INTERFACE_PATH');

  const b=await world(t),reason=b.f.record();reason.state='stuck';reason.parkReason='binding-missing: owning fallback.prompt.md interface';save(b.f,reason);
  b.ports.readRunResults=()=>[];await b.tick();
  assert.ok(b.f.record().parking?.blocker.paths.includes('fallback.prompt.md'),'3147_STOP_REASON_PATH_FALLBACK');
});

test('3147 repeated Runtime causes do not configure a client queue',async t=>{
  const {f,tick,ports,reports}=await world(t);let current=check(f);const queue=[];
  ports.configureInterpreterTestMode=async input=>queue.push(input);
  ports.readRunResults=()=>[current];
  const held=f.record();held.state='stuck';held.parkReason='Runtime no-verdict';save(f,held);
  for(const [n,code] of [[1,'runner-stopped'],[2,'graph-provider-failure'],[3,'runner-stopped']]) {
    current=check(f,code,`20261101-12000${n}-abcd`);await tick();f.tick(1000);
  }
  assert.equal(reports.length,3);assert.equal(reports.at(-1).runs.length,2,'3147_REPORT_RETAINS_EVERY_CAUSE_BATCH');
  assert.equal(queue.some(input=>String(input.owner).includes('runtime-causes')),false);
  assert.equal(f.record().parking?.blocker.kind,'runtime');
});

test('3147 binding issue closure and status expose the current wake condition',async t=>{
  const {f,tick,issues,stateFile}=await world(t);issues.set(321,{number:321,state:'open',body:''});
  const held=f.record();held.state='stuck';held.blockedOn={kind:'binding',until:'321'};save(f,held);
  await tick();const status=JSON.parse(readFileSync(stateFile));assert.ok(status.parking.waits?.some(row=>row.number===17&&row.condition.includes('321')),'3147_STATUS_WAKE_CONDITION');
  issues.get(321).state='closed';await tick();assert.equal(f.record().parking,undefined,'3147_BINDING_ISSUE_CLOSE_WAKE');
});

test('3147 Runtime reporting is injected and never writes an issue directly',async t=>{
  const {f,tick,ports,issues,writes,reports}=await world(t);ports.readRunResults=()=>[check(f)];
  const held=f.record();held.state='stuck';held.parkReason='Runtime no verdict';save(f,held);
  await tick();
  assert.equal(issues.size,1);assert.equal(reports.length,1);assert.deepEqual(writes,[]);
  assert.equal(f.record().parking?.blocker.until,'501');
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


test('3147 classifier rejects mixed failed expectations and file-rule refusals',()=>{
  assert.equal(classifyRuntimeFailure({states:[
    {test:'tests/value.json',state:'failed',reason:{code:'expectation-failed'}},
    {test:'tests/timeout.json',state:'not run',reason:{code:'runner-stopped'}},
  ]}),null);
  assert.equal(classifyRuntimeFailure({states:[
    {test:'tests/timeout.json',state:'refused',reason:{code:'file-rule',message:'file rule blocked the file'}},
  ]}),null);
  assert.equal(classifyRuntimeFailure({states:[
    {test:'tests/timeout.json',state:'partial',reason:{code:'expectation-pending'}},
  ]}),'no-verdict','3147_FILENAME_TIMEOUT_MUST_NOT_CREATE_TIMEOUT_CAUSE');
  for(const code of ['provider-call-cap','call-cap-reached']) assert.equal(classifyRuntimeFailure({states:[{test:'tests/value.json',state:'unknown',reason:{code}}]}),null,'3147_EXHAUSTED_TEST_BUDGET_IS_NOT_RUNTIME');
  assert.equal(classifyRuntimeFailure({states:[
    {test:'tests/value.json',state:'refused',reason:{code:'graph-provider-failure'}},
  ]}),'provider-error');
});

test('3147 failure observation time prevents an overlapping older batch from recovering',async()=>{
  const state={repo:'example/project'},runs=[
    {number:17,runId:'failed-run',state:'stuck'},
    {number:18,runId:'overlap-run',state:'stuck'},
  ];
  const checks=new Map([[17,check({clock:10000},'runner-stopped','20261101-120000-abcd')],
    [18,{kind:'pdd test',batch:'20261101-120001-abcd',at:9000,states:[{test:'tests/value.json',state:'passed'}]}]]);
  const ports={now:()=>10000,busy:async()=>false,readCheck:async run=>checks.get(run.number),health:async()=>null,
    save:async()=>true,reportRuntimeCause:async()=>({number:501,url:'https://github.com/example/project/issues/501',repository:'example/project'}),
    issueClosed:async()=>false};
  await reconcileRuntimeIncidents(state,ports,{},runs);
  assert.equal(state.runtimeIncidents.causes['runner-stopped'].recoveredAt,null,'3147_OLDER_OVERLAP_MUST_NOT_RECOVER');
});

test('3147 failed issue reopen cannot leave the cause recovered',async()=>{
  const state={repo:'example/project'},run={number:17,runId:'failed-run',state:'stuck'};
  let now=10000,checkRow=check({clock:9000},'runner-stopped','20261101-120000-abcd'),closed=false,failReopen=false;
  const ports={now:()=>now,busy:async()=>false,readCheck:async()=>checkRow,health:async()=>null,save:async()=>true,
    reportRuntimeCause:async()=>{if(failReopen)throw Error('report update unavailable');return {number:501,url:'https://github.com/example/project/issues/501',repository:'example/project'};},
    issueClosed:async()=>closed};
  await reconcileRuntimeIncidents(state,ports,{},[run]);
  now=12000;checkRow={...checkRow,batch:'20261101-120002-abcd',at:11000,states:[{test:'tests/value.json',state:'passed'}]};
  await reconcileRuntimeIncidents(state,ports,{},[run]);
  assert.equal(state.runtimeIncidents.causes['runner-stopped'].recoveredAt,12000);
  now=13000;checkRow=check({clock:9000},'runner-stopped','20261101-120000-abcd');closed=true;failReopen=true;
  await reconcileRuntimeIncidents(state,ports,{},[run]);
  assert.equal(state.runtimeIncidents.causes['runner-stopped'].recoveredAt,null,'3147_FAILED_REOPEN_MUST_CANCEL_RECOVERY');
  assert.equal(state.runtimeIncidents.causes['runner-stopped'].dirty,true);
});

test('3147 one shared report receives all runs with the same cause',async()=>{
  const state={repo:'example/project'},runs=[
    {number:17,runId:'run-17',state:'stuck'},
    {number:18,runId:'run-18',state:'waiting'},
  ],checks=new Map([[17,check({clock:10000},'runner-stopped','20261101-120000-abcd')],
    [18,check({clock:10000},'runner-stopped','20261101-120001-abcd')]]),reports=[];
  const ports={now:()=>10000,busy:async()=>false,readCheck:async run=>checks.get(run.number),health:async()=>null,save:async()=>true,
    reportRuntimeCause:async input=>{reports.push(input);return {number:501,url:'https://github.com/example/project/issues/501',repository:'example/project'};},
    issueClosed:async()=>false};
  const blockers=await reconcileRuntimeIncidents(state,ports,{runtimeOwner:'runtime-team'},runs);
  assert.equal(reports.length,1);assert.deepEqual(reports[0].runs,[{number:17,batch:'20261101-120000-abcd'},{number:18,batch:'20261101-120001-abcd'}]);
  assert.equal(reports[0].runtimeOwner,'runtime-team');assert.equal(blockers.get(17).until,'501');assert.equal(blockers.get(18).until,'501');
});
