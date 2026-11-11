import './helpers/test-home.mjs';
import test from 'node:test';
import {randomUUID} from 'node:crypto';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,readdirSync} from 'node:fs';
import {join} from 'node:path';
import {runCheck} from '../src/runtime/runtime-client.mjs';
import {checkCause,readRunResults,savedCheckCause} from '../src/workflow-results.mjs';
import {interfaceBlocks,proseSha256} from '../src/runtime/runtime-preflight.mjs';
import {harbor,fakeRuntime,portsFor,PLACE} from './runtime-fake.mjs';

const kinds = {
  'missing-interface': {code:'interface-missing',field:'/interface'},
  'missing-bound': {code:'undefined-call-bound',field:'/limits/max_model_calls'},
  'missing-call-bound': {code:'undefined-call-bound',field:'/calls/0/max_calls'},
  'recursive-call': {code:'recursive-call-bound',field:'/calls'},
};
async function blocked(t,kind) {
  const setup=harbor(t),path='prompts/broken.prompt.md',original=readFileSync(join(setup.repo,PLACE),'utf8');
  writeFileSync(join(setup.repo,path),original);
  const testPath=join(setup.repo,'tests/place-order.json'),scenario=JSON.parse(readFileSync(testPath,'utf8'));
  scenario.steps[0].entry_path=path;writeFileSync(testPath,JSON.stringify(scenario));
  if(kind==='missing-interface')writeFileSync(join(setup.repo,path),'# Missing interface\n');
  else {
    const block=interfaceBlocks(original)[0],iface=JSON.parse(block[1]);
    if(kind==='missing-bound')delete iface.limits.max_model_calls;
    else iface.calls=[{operation:'nested',target:kind==='recursive-call'?path:PLACE,target_operation:'place_order',...(kind==='recursive-call'?{max_calls:1}:{})}];
    iface.status='draft';iface.prose_sha256=proseSha256(original);
    writeFileSync(join(setup.repo,path),original.replace(block[1],JSON.stringify(iface)));
  }
  const fake=await fakeRuntime(t,(entry,f)=>{
    if(entry.command==='lint')return {status:200,json:f.lint(entry.request.requestId,[PLACE,path].map(path=>({path,state:'draft',admission_state:'draft',interface:{calls:[]}})))};
    return f.normal(entry);
  });
  const env={HOME:setup.home,XDG_CONFIG_HOME:join(setup.home,'config'),PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin};
  const ports=portsFor(env).ports;
  assert.equal(await runCheck({cwd:setup.repo,options:{'--json':true}},ports),4);
  const result=JSON.parse(ports.stdout.text),folder=join(setup.state,'batches',result.batch);
  return {setup,path,original,fake,env,result,folder};
}
function guidance(value,kind,path) {
  for(const token of [kinds[kind].code,kinds[kind].field,path])assert.ok(value.includes(token),`3114_LOCAL_REPAIR_MISSING: ${token}`);
  assert.match(value,/repair/i);assert.match(value,/fresh.*pdd test/i);
}
for(const kind of Object.keys(kinds)) {
  test(`3114 repair: ${kind} stays local through saved classification and recovers with a fresh check`,async t=>{
    const {setup,path,original,fake,env,result,folder}=await blocked(t,kind);
    const batch=JSON.parse(readFileSync(join(folder,'batch.json'),'utf8'));
    assert.equal(checkCause(result.rows),'issue','3114_LOCAL_CAUSE_LOST');
    assert.equal(checkCause(batch.rows),'issue','3114_BATCH_LOCAL_CAUSE_LOST');
    assert.equal(savedCheckCause(result.batch,{env}),'issue','3114_SAVED_LOCAL_CAUSE_LOST');
    assert.ok(batch.rows.some(row=>row.reason?.code==='check-plan-prerequisite'));
    guidance(result.check_scope.guidance,kind,path);
    for(const row of result.rows)guidance(row.reason.message,kind,path);
    const workflow=readRunResults({root:setup.repo},{env})[0];
    assert.equal(checkCause(workflow.states),'issue');guidance(workflow.summary,kind,path);
    for(const json of [true,false]) {
      const read=portsFor(env).ports;
      assert.equal(await runCheck({cwd:setup.repo,words:[result.batch],options:{'--read':true,...(json?{'--json':true}:{})}},read),4);
      guidance(read.stdout.text,kind,path);
      if(json)assert.equal(checkCause(JSON.parse(read.stdout.text).rows),'issue');
    }
    assert.equal(fake.posts.length,0);assert.equal(fake.gets.length,0);
    writeFileSync(join(setup.repo,path),original);
    const fresh=portsFor(env,{randomUUID:randomUUID}).ports;
    assert.equal(await runCheck({cwd:setup.repo,options:{'--json':true}},fresh),0);
    assert.notEqual(JSON.parse(fresh.stdout.text).batch,result.batch);
    assert.equal(fake.posts.filter(row=>row.command==='check').length,2);
    assert.deepEqual(JSON.parse(readFileSync(join(folder,'batch.json'),'utf8')),batch);
  });
  test(`3114 repair: supported retry of ${kind} keeps history and returns a local repair without dispatch`,async t=>{
    const {setup,path,fake,env,result,folder}=await blocked(t,kind);
    const history=readFileSync(join(folder,'batch.json'),'utf8'),names=readdirSync(join(setup.state,'batches'));
    // Even after edits, retry must use the historical plan and require a fresh check.
    writeFileSync(join(setup.repo,path),'# Still needs repair\n');
    for(const json of [true,false]) {
      const {ports:retry,clock}=portsFor(env);
      let code;
      await assert.doesNotReject(async()=>{code=await runCheck({cwd:setup.repo,options:{'--retry':result.batch,...(json?{'--json':true}:{})}},retry);},'3114_LOCAL_RETRY_THREW');
      assert.equal(code,4,'3114_LOCAL_RETRY_UNCONTROLLED');
      guidance(retry.stdout.text,kind,path);
      if(json) {
        const saved=JSON.parse(retry.stdout.text);
        assert.equal(saved.batch,result.batch);assert.deepEqual(saved.check_plan,result.check_plan);
        assert.deepEqual(saved.rows,result.rows);assert.equal(saved.exit_code,4);
      }
      assert.equal(clock.gh.length,0);
    }
    assert.equal(fake.posts.length,0);assert.equal(fake.gets.length,0);
    assert.equal(readFileSync(join(folder,'batch.json'),'utf8'),history);
    assert.deepEqual(readdirSync(join(setup.state,'batches')),names);
  });
}
