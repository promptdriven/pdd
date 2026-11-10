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
import {classifyRuntimeFailure, reconcileRuntimeIncidents, runtimeEvidence} from '../src/autopilot-runtime.mjs';
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
    if(args[0]==='api' && args.includes('graphql')) {
      const issueNumber=Number(JSON.parse(opts.input).variables.issue),issue=issues.get(issueNumber);
      const row=issue?{state:issue.state==='closed'?'CLOSED':'OPEN',timelineItems:{nodes:issue.mergedUrl?[{closer:{__typename:'PullRequest',url:issue.mergedUrl,merged:true}}]:[]}}:null;
      return {code:0,stdout:JSON.stringify({data:{repository:{issue:row}}})};
    }
    if(args[0]==='api' && /\/issues\/\d+$/.test(args[1]))return {code:0,stdout:JSON.stringify(issues.get(Number(args[1].split('/').at(-1)))??{state:'open'})};
    return exec(file,args,opts);
  };
  return {...w,issues,writes,reports};
}
const check=(f,code='runner-stopped',batch='20261101-120000-abcd')=>({kind:'pdd test',batch,at:f.clock,tests:['tests/value.json'],states:[{test:'tests/value.json',state:'partial',reason:{code}}]});
test('3147 a closed dependency issue stays parked until a merged pull request closes it',async t=>{
  const {f,tick,ports,issues,warnings}=await world(t);
  issues.set(321,{number:321,state:'open',body:''});
  const held=f.record();held.state='paused';held.blockedOn={kind:'dependency',until:'321'};save(f,held);
  await tick();assert.equal(f.record().parking?.phase,'parked');
  issues.get(321).state='closed';await tick();
  assert.equal(f.record().parking?.phase,'parked','3147_CLOSED_UNMERGED_DEPENDENCY_STAYS_PARKED');
  issues.get(321).mergedUrl='https://github.com/example/project/pull/654';await tick();
  assert.equal(f.record().parking,undefined,'3147_MERGED_CLOSING_PR_WAKES_DEPENDENCY');
  const sent=deliveries(f).length;await tick();assert.equal(deliveries(f).length,sent);assert.deepEqual(warnings,[]);
});

for(const kind of ['pdd','pdd-route'])test('3147 a closed '+kind+' issue waits for installed capability evidence',async t=>{
  const {f,tick,ports,issues,warnings}=await world(t);
  issues.set(321,{number:321,state:'open',body:''});ports.installedPddCapabilities=[];
  const held=f.record();held.state='paused';held.blockedOn={kind,until:'#321'};save(f,held);
  await tick();assert.equal(f.record().parking?.phase,'parked');
  issues.get(321).state='closed';await tick();
  assert.equal(f.record().parking?.phase,'parked','3147_ISSUE_CLOSE_IS_NOT_INSTALLED_ROUTE_EVIDENCE');
  ports.installedPddCapabilities=['issue-321'];await tick();
  assert.equal(f.record().parking,undefined,'3147_INSTALLED_CAPABILITY_WAKES_PDD');
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
  assert.deepEqual(f.record().done.check,held.done.check,'3147_RUNTIME_WAKE_PRESERVES_SAVED_CHECK_ID');
  assert.deepEqual(f.record().gate,held.gate);
  assert.match(deliveries(f)[0][3],/pdd test --read 20261101-120000-abcd/,'3147_RUNTIME_WAKE_READS_SAME_BATCH');
  assert.match(deliveries(f)[0][3],/pdd workflow resend 17 --said -/,'3147_RUNTIME_WAKE_REQUIRES_PERSON_AUTHORIZATION');
  assert.doesNotMatch(deliveries(f)[0][3],/--cache-clear/,'3147_RUNTIME_WAKE_NEVER_RECOMMENDS_AUTOMATIC_RESEND');
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

test('3147 binding issue closure does not wake, and status names the base or reply condition',async t=>{
  const {f,tick,issues,stateFile}=await world(t);issues.set(321,{number:321,state:'open',body:''});
  const held=f.record();held.state='stuck';held.blockedOn={kind:'binding',until:'321'};held.parkReason='binding refusal in value.prompt.md';save(f,held);
  await tick();const status=JSON.parse(readFileSync(stateFile));assert.ok(status.parking.waits?.some(row=>row.number===17&&/base|reply/i.test(row.condition)),'3147_STATUS_WAKE_CONDITION');
  issues.get(321).state='closed';await tick();assert.equal(f.record().parking?.phase,'parked','3147_BINDING_ISSUE_CLOSE_IS_NOT_EVIDENCE');
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

test('3147 dirty Runtime report cannot use an old closed issue to wake',async t=>{
  const {f,tick,ports,issues,stateFile}=await world(t),held=f.record();
  held.state='stuck';held.parkReason='Runtime no verdict';held.done.check={batch:'20261101-120000-abcd',summary:'saved check'};
  held.parking={phase:'parked',at:f.clock,blocker:{kind:'runtime',until:'501',cause:'runner-stopped',batch:'20261101-120000-abcd',
    checkKind:'pdd test',evidence:runtimeEvidence(held),repository:'example/project'}};save(f,held);
  const issue={number:501,url:'https://github.com/example/project/issues/501',repository:'example/project',state:'closed',body:''};issues.set(501,issue);
  const state=JSON.parse(readFileSync(stateFile));state.runtimeIncidents={seen:{},causes:{'runner-stopped':{
    cause:'runner-stopped',checkKind:'pdd test',lastFailureAt:f.clock-100,failures:{},runs:{},issue:{number:501,url:issue.url,repository:issue.repository},dirty:true,recoveredAt:null,
  }}};writeFileSync(stateFile,JSON.stringify(state));
  ports.readRunResults=()=>[];ports.reportRuntimeCause=async()=>{throw Error('reopen not confirmed');};
  const delivered=deliveries(f).length;
  await tick();
  assert.equal(f.record().parking?.phase,'parked','3147_DIRTY_CAUSE_IGNORES_OLD_CLOSED_ISSUE');
  assert.equal(f.record().parking?.blocker.until,'501');
  assert.deepEqual(f.record().done.check,held.done.check,'3147_DIRTY_CAUSE_PRESERVES_SAVED_CHECK');
  assert.equal(JSON.parse(readFileSync(stateFile)).runtimeIncidents.causes['runner-stopped'].dirty,true);
  assert.equal(deliveries(f).length,delivered,'3147_DIRTY_CAUSE_DOES_NOT_DELIVER_WAKE');
});

test('3147 later terminal Runtime verdict wakes even while report update is dirty',async t=>{
  const {f,tick,ports,issues,stateFile}=await world(t),held=f.record();
  held.state='stuck';held.parkReason='Runtime no verdict';held.done.check={batch:'20261101-120000-abcd',summary:'saved check'};
  held.parking={phase:'parked',at:f.clock,blocker:{kind:'runtime',until:'501',cause:'runner-stopped',batch:'20261101-120000-abcd',
    checkKind:'pdd test',evidence:runtimeEvidence(held),repository:'example/project'}};save(f,held);
  const issue={number:501,url:'https://github.com/example/project/issues/501',repository:'example/project',state:'open',body:''};issues.set(501,issue);
  const state=JSON.parse(readFileSync(stateFile));state.runtimeIncidents={seen:{},causes:{'runner-stopped':{
    cause:'runner-stopped',checkKind:'pdd test',lastFailureAt:f.clock-100,failures:{},runs:{},issue:{number:501,url:issue.url,repository:issue.repository},dirty:true,recoveredAt:null,
  }}};writeFileSync(stateFile,JSON.stringify(state));
  ports.readRunResults=()=>[{kind:'pdd test',batch:'20261101-120001-abcd',at:f.clock-50,states:[{test:'tests/value.json',state:'passed'}]}];
  ports.reportRuntimeCause=async()=>{throw Error('report update not confirmed');};
  const beforeDeliveries=deliveries(f).length;
  await tick();
  assert.equal(f.record().parking,undefined,'3147_AUTHORITATIVE_VERDICT_WAKES_DIRTY_CAUSE');
  assert.deepEqual(f.record().done.check,held.done.check,'3147_HEALTHY_WAKE_PRESERVES_SAVED_CHECK');
  assert.match(deliveries(f).at(-1)[3],/pdd test --read 20261101-120000-abcd/);
  assert.doesNotMatch(deliveries(f).at(-1)[3],/--cache-clear/);
  assert.equal(deliveries(f).length,beforeDeliveries+1,'3147_HEALTHY_WAKE_DELIVERS_ONE_READ_NOTICE');
  assert.equal(JSON.parse(readFileSync(stateFile)).runtimeIncidents.causes['runner-stopped'].dirty,true);
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

test('3147 first successful binding refresh fills a missing baseline',async t=>{
  const {f,tick,ports}=await world(t);
  const held=f.record();held.state='stuck';held.parkReason='binding-missing: value.prompt.md';save(f,held);
  ports.readRunResults=()=>[{kind:'pdd test',tests:['tests/value.json'],states:[{test:'tests/value.json',state:'not run',reason:{code:'binding-missing'}}]}];
  const execute=ports.run;let failFetch=true;
  ports.run=async(file,args,opts)=>{
    if(file==='git'&&args[0]==='fetch'&&failFetch){failFetch=false;return {code:1,stdout:'',stderr:'temporary fetch error'};}
    return execute(file,args,opts);
  };
  await tick();
  assert.equal(f.record().parking?.phase,'parked');
  assert.equal(f.record().parking?.blocker.revision,undefined,'3147_FAILED_REFRESH_HAS_NO_BASELINE');
  await tick();
  const baseline=f.record().parking?.blocker.revision;
  assert.match(baseline,/^[a-f0-9]{64}$/,'3147_FIRST_SUCCESSFUL_REFRESH_SAVES_BASELINE');
  writeFileSync(join(f.source,'value.prompt.md'),'changed on the base');
  f.git(f.source,'add','.');f.git(f.source,'commit','-m','Change the owning prompt');
  f.git(f.source,'update-ref','refs/remotes/origin/main','HEAD');
  await tick();
  assert.equal(f.record().parking,undefined,'3147_CHANGED_BASE_WAKES_AFTER_BASELINE');
});

test('3147 provider call caps in error.code stay local after result projection',()=>{
  for(const code of ['provider-call-cap','call-cap-reached']) {
    const result=classifyRuntimeFailure({states:[{test:'tests/value.json',state:'partial',error:{code,message:'configured cap reached'}}]});
    assert.equal(result,null,'3147_ERROR_CODE_CAP_IS_NOT_RUNTIME');
  }
});

test('3147 confirmed issue URL supplies repository; mismatched identity stays parked',async()=>{
  const baseCheck={kind:'pdd test',batch:'20261110-120000-abcd',at:1,states:[{state:'partial',reason:{code:'runner-stopped'}}]};
  const run={number:17,runId:'runtime-run',state:'stuck',parkReason:'Runtime check stopped'};
  const portsFor=reported=>{
    let closedReads=0;
    const ports={now:()=>10,busy:async()=>false,readCheck:async()=>baseCheck,health:async()=>null,save:async()=>true,
      reportRuntimeCause:async()=>reported,issueClosed:async issue=>{closedReads++;return false;}};
    return {ports,closedReads:()=>closedReads};
  };
  const valid=portsFor({number:501,url:'https://github.com/team/private-runtime/issues/501'});
  const state={repo:'example/project'};
  const blockers=await reconcileRuntimeIncidents(state,valid.ports,{},[run]);
  assert.equal(blockers.get(17).repository,'team/private-runtime','3147_REPORTER_URL_DERIVES_PRIVATE_REPOSITORY');
  assert.equal(state.runtimeIncidents.causes['runner-stopped'].issue.repository,'team/private-runtime');
  assert.equal(valid.closedReads(),1);

  const invalid=portsFor({number:501,url:'https://github.com/team/private-runtime/issues/501',repository:'promptdriven/pdd'});
  const state2={repo:'example/project'};
  const refused=await reconcileRuntimeIncidents(state2,invalid.ports,{},[run]);
  assert.equal(refused.get(17).until,null,'3147_MISMATCHED_REPORTER_IDENTITY_IS_NOT_CONFIRMED');
  assert.equal(state2.runtimeIncidents.causes['runner-stopped'].dirty,true);
  assert.equal(state2.runtimeIncidents.causes['runner-stopped'].issue,null);
  assert.equal(invalid.closedReads(),0);

  const incomplete=portsFor({number:501,repository:'team/private-runtime'});
  const state3={repo:'example/project'};
  const missingUrl=await reconcileRuntimeIncidents(state3,incomplete.ports,{},[run]);
  assert.equal(missingUrl.get(17).until,null,'3147_REPORTER_WITHOUT_CONFIRMED_URL_STAYS_PARKED');
  assert.equal(state3.runtimeIncidents.causes['runner-stopped'].dirty,true);
  assert.equal(state3.runtimeIncidents.causes['runner-stopped'].issue,null);
  assert.equal(incomplete.closedReads(),0);
});
