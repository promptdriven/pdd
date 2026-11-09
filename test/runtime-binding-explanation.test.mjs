import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,appendFileSync,existsSync} from 'node:fs';
import {join} from 'node:path';
import {spawnSync} from 'node:child_process';
import {runPdd} from '../src/pdd-cli.mjs';
import {runCheck} from '../src/runtime-client.mjs';
import {captureSource,interfaceBlocks,proseSha256} from '../src/runtime-preflight.mjs';
import {blockerFor,idleParkingBlocker,reconcileParking} from '../src/autopilot-parking.mjs';
import {harbor,portsFor,fakeRuntime,PLACE} from './runtime-fake.mjs';
import {mutate} from './runtime-compatibility/replay.mjs';

const TEST='tests/place-order.json', STORY='user_stories/place-order.md', OTHER='prompts/runner.prompt.md';
const read=(f,path)=>readFileSync(join(f.repo,path),'utf8');
const save=(f,path,value)=>writeFileSync(join(f.repo,path),typeof value==='string'?value:JSON.stringify(value));
const editPrompt=(f,path,edit,prose='')=>{
  const text=read(f,path),block=interfaceBlocks(text)[0],iface=JSON.parse(block[1]);edit(iface);
  const next=text.replace(block[1],JSON.stringify(iface)).replace('None.',prose||'None.');
  iface.prose_sha256=proseSha256(next);
  save(f,path,next.replace(interfaceBlocks(next)[0][1],JSON.stringify(iface)));
};
const schema={type:'object',properties:{},required:[],additionalProperties:false};
const resource=(name,operations)=>({name,kind:'port',operations:operations.map(name=>({name,arguments_schema:schema,result_schema:schema}))});
const fixture={action:'fixture.lookup',cases:[{args:{},result:{}}]};
function setup(t,{boundary=false,wrong=false,steps=1,outside=true}={}) {
  const f=harbor(t);
  if(outside) {
    save(f,OTHER,read(f,PLACE));
    editPrompt(f,OTHER,iface=>{iface.resources=[resource('files',['read'])];iface.entries[0].operation='changeRun';});
  }
  editPrompt(f,PLACE,iface=>{iface.resources=[resource('dispatch',['changeRun'])];},outside?'[Runner](runner.prompt.md)':'');
  if(boundary)appendFileSync(join(f.repo,STORY),'\n## Runtime boundary\n\n[CLI](../prompts/place_order.prompt.md)\n');
  const doc=JSON.parse(read(f,TEST));
  doc.simulation={[wrong?'dispatch.change':'dispatch.changeRun']:fixture};
  doc.steps=Array.from({length:steps},(_,index)=>({...doc.steps[0],step_id:`action-${index+1}`}));
  save(f,TEST,doc);
  return f;
}
const localPorts=f=>portsFor({HOME:f.home,XDG_CONFIG_HOME:join(f.home,'config'),PDD_STATE_DIR:f.state},
  {gh:()=>{throw Error('must not authenticate');},fetch:()=>{throw Error('must not send');}}).ports;
const explain=(f,ports,json=true)=>runPdd(['test','--explain-bindings','place-order',...(json?['--json']:[])],{cwd:f.repo,env:ports.env,stdout:ports.stdout,stderr:ports.stderr});
const getPlan=(f)=>captureSource(f.repo,{tests:[TEST]}).bindingPlans?.[0];

test('3135: read-only CLI plan selects an exact lookup without authentication or state writes',async t=>{
  const f=setup(t,{boundary:true}),ports=localPorts(f);
  const code=await runPdd(['test','--explain-bindings','place-order','--json'],{cwd:f.repo,env:ports.env,stdout:ports.stdout,stderr:ports.stderr,});
  assert.equal(code,0,'3135_EXPLAIN_ROUTE');
  const result=JSON.parse(ports.stdout.text);
  assert.equal(result.schema_version,'pdd.binding-plans.v1');
  assert.equal(result.plans[0].edges[0].state,'bound');
  assert.deepEqual(result.plans[0].edges[0].candidates.filter(row=>row.cause==='selected'),[{kind:'simulation',name:'dispatch.changeRun',cause:'selected'}]);
  assert.equal(existsSync(f.state),false);
});

test('3135: wrong lookup operation gives step, edge, candidate cause and smallest repair',async t=>{
  const f=setup(t,{wrong:true,boundary:true}),ports=localPorts(f);
  assert.equal(await explain(f,ports),4,'3135_WRONG_OPERATION');
  const plan=JSON.parse(ports.stdout.text).plans[0],edge=plan.edges[0];
  assert.equal(edge.step_id,'action-1');assert.equal(edge.prompt_path,PLACE);
  assert.equal(edge.key,'dispatch.changeRun');assert.equal(edge.state,'missing');
  assert.ok(edge.candidates.some(row=>row.name==='dispatch.change'&&row.cause==='wrong-operation'));
  assert.ok(edge.candidates.some(row=>row.name===`${OTHER}#changeRun`&&row.cause==='out-of-boundary'));
  assert.match(edge.repair,/dispatch\.changeRun/);
  assert.equal(existsSync(f.state),false);
});

test('3135: declared boundary omits outside executable edges and projects context without changing authored files',t=>{
  const f=setup(t,{boundary:true}),original=read(f,OTHER),capture=captureSource(f.repo,{tests:[TEST]});
  assert.ok(capture.bindingPlans,'3135_STORY_CLOSURE');
  const plan=capture.bindingPlans[0];assert.deepEqual(plan.steps[0].closure,[PLACE]);
  assert.deepEqual(plan.edges.map(row=>row.key),['dispatch.changeRun']);
  assert.ok(plan.edges.every(row=>row.state==='bound'));
  const context=capture.sources.find(row=>row.path===OTHER);
  assert.ok(context);assert.equal(interfaceBlocks(context.bytes.toString()).length,0,'3135_OUTSIDE_INTERFACE');
  assert.match(context.bytes.toString(),/Harbor/);assert.equal(read(f,OTHER),original);
  assert.equal(capture.files.find(row=>row.path===OTHER).size,context.bytes.length);
});

test('3135: unscoped closure follows calls while context entry candidates remain outside execution',t=>{
  const f=setup(t),plan=getPlan(f);assert.ok(plan,'3135_PLAN_MISSING');
  assert.deepEqual(plan.steps[0].closure,[PLACE]);
  assert.ok(plan.edges[0].candidates.some(row=>row.name===`${OTHER}#changeRun`&&row.cause==='not-in-dependency-closure'));
  editPrompt(f,PLACE,iface=>{iface.calls=[{operation:'runner',target:OTHER,max_calls:1}];});
  const called=getPlan(f);assert.deepEqual(called.steps[0].closure,[PLACE,OTHER].sort());
  assert.equal(called.edges.find(row=>row.key==='files.read').state,'missing');
});

test('3135: an actual call crossing the Story boundary refuses before any paid work',async t=>{
  const f=setup(t,{boundary:true});editPrompt(f,PLACE,iface=>{iface.calls=[{operation:'runner',target:OTHER,max_calls:1}];});
  assert.throws(()=>captureSource(f.repo,{tests:[TEST]}),error=>error.code==='binding-boundary-invalid'&&error.message.includes(OTHER),'3135_CALL_CROSSING');
  const ports=localPorts(f);
  assert.equal(await explain(f,ports,false),4);
  assert.match(ports.stderr.text,/out-of-boundary/);
});

for(const body of ['', '[Outside](../../outside.prompt.md)', '[Remote](https://example.invalid/a.prompt.md)', '[Wrong](../prompts/file.txt)', '[Encoded](../prompts/%2e%2e/private.prompt.md)'])
  test(`3135: malformed boundary refuses locally (${body||'empty'})`,t=>{
    const f=setup(t);appendFileSync(join(f.repo,STORY),`\n## Runtime boundary\n\n${body}\n`);
    assert.throws(()=>captureSource(f.repo,{tests:[TEST]}),error=>error.code==='binding-boundary-invalid','3135_INVALID_BOUNDARY');
  });

test('3135: step override wins and wrong resource names remain explicit candidates',t=>{
  const f=setup(t,{steps:2,outside:false}),doc=JSON.parse(read(f,TEST));
  doc.simulation={'dispatcher.changeRun':fixture,'dispatch.change':fixture};
  doc.steps[1].simulation_overrides={'dispatch.changeRun':fixture};save(f,TEST,doc);
  const plan=getPlan(f);assert.ok(plan,'3135_OVERRIDES');
  assert.deepEqual(plan.edges.map(row=>row.state),['missing','bound']);
  assert.deepEqual(plan.edges[0].candidates.map(row=>row.cause),['wrong-name','wrong-operation']);
});

test('3135: synthetic 19-step 15-edge shape retains every named cause and supplied lookup',async t=>{
  const f=setup(t,{steps:19,outside:false});
  editPrompt(f,PLACE,iface=>{iface.resources=[resource('dispatch',['changeRun',...Array.from({length:14},(_,i)=>`other${i}`)])];});
  const ports=localPorts(f);
  assert.equal(await explain(f,ports),4);
  const plan=JSON.parse(ports.stdout.text).plans?.[0];assert.ok(plan,'3135_SHAPE');
  assert.equal(plan.edges.length,285);assert.equal(plan.edges.filter(row=>row.state==='bound').length,19);
  assert.equal(plan.edges.filter(row=>row.state==='missing').length,266);
  for(const edge of plan.edges.filter(row=>row.state==='missing')) {
    assert.equal(edge.candidates[0].cause,'wrong-operation');assert.ok(edge.step_id&&edge.key&&edge.repair);
  }
});

for(const reason of ['binding-missing: dispatch.changeRun','CHECK has an unresolved binding contract; no verdict','missing-binding after compatibility'])
  test(`3135: saved refusal parks with binding cause (${reason})`,async()=>{
    const run={repo:'synthetic/repo',automaticOrigin:{coordinator:'owner'},runId:'synthetic',number:12,state:'stuck',parkReason:reason,updatedAt:0};
    assert.deepEqual(idleParkingBlocker(run,60000),{kind:'binding',until:null},'3135_NAMED_BINDING');
    let parked;
    await reconcileParking({repo:'synthetic/repo',coordinator:'owner'}, {checkProgress:async()=>false,list:async()=>[run],now:()=>60000,park:async(_,blocker)=>{parked=blocker;},alertUnknown:async()=>{throw Error('must not alert unknown');}});
    assert.equal(parked.kind,'binding');
    assert.equal(blockerFor({...run,question:{text:'Choose the product behavior',at:1}}).kind,'person');
    assert.equal(blockerFor({...run,blockedOn:{kind:'dependency',until:'22'}}).kind,'dependency');
  });

for(const [bindingKey,cause] of [['dispatch.changeRun','server-binding-disagreement'],['dispatch.change','wrong-operation'],['dispatcher.changeRun','wrong-name']])
test(`3135: server refusal retains ${cause}, saved plan and zero check dispatch`,async t=>{
  const f=setup(t,{outside:false}),doc=JSON.parse(read(f,TEST));doc.simulation={[bindingKey]:fixture};save(f,TEST,doc);
  const fake=await fakeRuntime(t,(entry,engine)=>{
    const answer=engine.normal(entry);
    if(entry.command==='lint') {
      const reports=new Set([...answer.json.result.capabilities.map(item=>item.report),...answer.json.result.report.lint.tests.map(item=>item.capabilities)]);
      for(const report of reports) {mutate(report,'missing-binding');report.edges[0].selection.edge.resource_operation='dispatch.changeRun';}
    }
    return answer;
  });
  const {ports}=portsFor({HOME:f.home,XDG_CONFIG_HOME:join(f.home,'config'),PDD_STATE_DIR:f.state,PDD_RUNTIME_URL:fake.origin});
  assert.equal(await runCheck({cwd:f.repo,words:['place-order'],options:{'--json':true}},ports),4,ports.stderr.text+' '+ports.stdout.text);
  const output=JSON.parse(ports.stdout.text),row=output.rows[0];
  assert.ok(row.binding_plan,'3135_REFUSAL_PLAN');
  assert.equal(row.binding_diagnostics[0].cause,cause);
  assert.equal(row.binding_diagnostics[0].key,'dispatch.changeRun');
  assert.equal(fake.posts.filter(post=>post.command==='check').length,0);
  const saved=JSON.parse(readFileSync(join(f.state,'batches',output.batch,'batch.json'),'utf8'));
  assert.equal(saved.rows[0].binding_plan.edges[0].state,bindingKey==='dispatch.changeRun'?'bound':'missing');
  const later=portsFor(ports.env).ports;
  assert.equal(await runCheck({cwd:f.repo,words:[output.batch],options:{'--read':true,'--json':true}},later),4);
  assert.equal(JSON.parse(later.stdout.text).rows[0].binding_diagnostics[0].cause,cause);
});


test('3135: incomplete lookup and missing binding each retain a concrete repair in text',async t=>{
  const f=setup(t,{outside:false}),doc=JSON.parse(read(f,TEST));doc.simulation={'dispatch.changeRun':{action:'fixture.lookup',cases:[]}};save(f,TEST,doc);
  const plan=getPlan(f);assert.ok(plan,'3135_INVALID_FIXTURE');
  assert.equal(plan.edges[0].state,'missing');assert.equal(plan.edges[0].candidates[0].cause,'invalid-fixture');
  doc.simulation={};save(f,TEST,doc);
  const ports=localPorts(f);assert.equal(await explain(f,ports,false),4);
  assert.match(ports.stdout.text,/action-1.*dispatch\.changeRun.*missing/);
  assert.match(ports.stdout.text,/repair:.*dispatch\.changeRun/);
});

test('3135: an unscoped Story retains its required edges beside a scoped Story',t=>{
  const f=setup(t,{boundary:true}),doc=JSON.parse(read(f,'tests/unknown-item.json'));
  doc.steps[0].entry_path=OTHER;save(f,'tests/unknown-item.json',doc);
  let capture;
  assert.doesNotThrow(()=>{capture=captureSource(f.repo,{tests:[TEST,'tests/unknown-item.json']});},'3135_BOUNDARY_UNION');
  assert.equal(interfaceBlocks(capture.sources.find(row=>row.path===OTHER).bytes.toString()).length,1,'3135_BOUNDARY_UNION');
  assert.deepEqual(capture.bindingPlans[0].boundary,[PLACE]);
  assert.equal(capture.bindingPlans[1].boundary,null);
  assert.equal(capture.bindingPlans[1].edges.find(edge=>edge.key==='files.read').state,'missing');
});

test('3135: boundary check sends the projected closure to the repo fake and passes',async t=>{
  const f=setup(t,{boundary:true});let outsideInterface;
  const fake=await fakeRuntime(t,(entry,engine)=>{
    if(entry.command==='lint') {
      const content=spawnSync('tar',['-xOf','-',OTHER],{input:entry.tar,encoding:'utf8'});assert.equal(content.status,0);
      outsideInterface=interfaceBlocks(content.stdout).length;
    }
    return engine.normal(entry);
  });
  const {ports}=portsFor({HOME:f.home,XDG_CONFIG_HOME:join(f.home,'config'),PDD_STATE_DIR:f.state,PDD_RUNTIME_URL:fake.origin});
  assert.equal(await runCheck({cwd:f.repo,words:['place-order'],options:{'--json':true}},ports),0);
  assert.equal(outsideInterface,0,'3135_UPLOADED_BOUNDARY');
  assert.equal(JSON.parse(ports.stdout.text).rows[0].binding_plan.edges.length,1);
  assert.equal(fake.posts.filter(row=>row.command==='check').length,1);
});


test('3135: explanation refuses a malformed selected scenario without auth or state writes',async t=>{
  const f=setup(t,{outside:false});save(f,TEST,'{malformed');
  const ports=localPorts(f);assert.equal(await explain(f,ports),4,'3135_INVALID_SCENARIO');
  assert.match(ports.stderr.text,/tests\/place-order\.json/);assert.equal(existsSync(f.state),false);
});
