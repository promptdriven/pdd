import test from 'node:test';
import assert from 'node:assert/strict';
import {runTry,runCheck} from '../src/runtime-client.mjs';
import {parseArgv} from '../src/argument-parser.mjs';
import {defaultMaxCalls} from '../src/runtime-preflight.mjs';
import {harbor,fakeRuntime,portsFor} from './runtime-fake.mjs';

async function invoke(setup,fake,options={},extra={}){
 const {ports,clock}=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin},extra);
 const code=await runTry({cwd:setup.repo,words:['place-order'],options:options['--stop']?options:{'--no-open':true,'--no-wait':true,...options}},ports);
 return{code,out:ports.stdout.text,err:ports.stderr.text,clock};
}
async function service(t,confirmed=cap=>cap){
 const caps=new Map();
 const fake=await fakeRuntime(t,(e,f)=>{
  if(e.command==='lint')return{status:200,json:f.lint(e.request.requestId)};
  if(e.command==='try'){caps.set(e.request.requestId,e.request.max_calls);return{status:202,json:f.job(e.request.requestId,'try','queued')}};
  if(e.url.endsWith('/tests')||e.url.endsWith('/approvals'))return{status:404,json:{}};
  if(f.mode==='missing')return{status:404,json:{error:{code:'not-found'}}};
  const id=e.url.split('/').at(-1),answer=f.tryJob(id,undefined,f.mode==='paused'?'paused':'running');if(f.mode==='unknown'){answer.state='unknown';answer.result.session.state='unknown'};answer.result.session.max_calls=confirmed(caps.get(id));answer.result.session.remaining_calls=confirmed(caps.get(id))-(f.spent??0);
  return{status:200,json:answer};
 });return fake;
}
test('BUDGET1: Simulator budget parses in browser, CLI and serve forms; malformed values reject',()=>{
 for(const mode of [[],['--cli'],['--serve','8080']])for(const value of ['1','400','1000'])assert.equal(parseArgv(['simulate','story',...mode,'--max-calls',value]).options['--max-calls'],value);
 for(const value of ['1','101','1000'])assert.equal(parseArgv(['test','story','--max-calls',value]).options['--max-calls'],value);
 for(const command of ['check','try'])for(const value of ['0','-1','1.5','NaN','1e3','1001','999999','9007199254740992'])assert.throws(()=>parseArgv([command,'story','--max-calls',value]));
});
test('BUDGET2: Check default ceiling is tripled and actual submitted default/override stay distinct',async t=>{
 const steps=n=>({steps:Array.from({length:n},()=>({}))});assert.deepEqual([0,1,2,3,8,9,30,83,84,100].map(n=>defaultMaxCalls(steps(n))),[18,18,24,36,96,108,360,996,1000,1000]);
 for(const requested of [undefined,7,1000]){
  const setup=harbor(t),fake=await fakeRuntime(t,(e,f)=>f.normal(e));
  const {ports}=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin});
  assert.equal(await runCheck({cwd:setup.repo,words:['place-order'],options:{'--json':true,...(requested?{'--max-calls':requested}:{})}},ports),0);
  assert.equal(fake.posts.find(p=>p.command==='check').request.max_calls,requested??18);
 }
});
test('BUDGET3: a new Try requests400 or its explicit ceiling and reports confirmed metadata',async t=>{
 for(const cap of [400,1000]){
  const setup=harbor(t),fake=await service(t),result=await invoke(setup,fake,cap===400?{}:{'--max-calls':cap});
  assert.equal(result.code,0,result.err);assert.equal(fake.posts.find(p=>p.command==='try').request.max_calls,cap);
  assert.match(result.out,new RegExp(`Simulator budget ${cap} calls; ${cap} remaining`));assert.match(result.out,/charged only for calls that run/);
  const again=await invoke(setup,fake);assert.equal(again.code,0,again.err);assert.equal(fake.posts.filter(p=>p.command==='try').length,1);assert.equal(fake.jsonPosts.length,0);
  assert.match(again.out,new RegExp(`Simulator budget ${cap} calls`));
 }
});
test('BUDGET4: direct API callers cannot bypass budget validation before any effect',async t=>{
 for(const cap of [0,-1,1.5,NaN,Infinity,true,'1e3',1001,999999,9007199254740992]){
  const setup=harbor(t),fake=await service(t),result=await invoke(setup,fake,{'--max-calls':cap});
  assert.equal(result.code,2,String(cap));assert.equal(fake.posts.length,0);assert.equal(result.clock.gh.length,0);
 }
});
test('BUDGET5: --stop cannot carry a budget',async t=>{
 const setup=harbor(t),fake=await service(t);assert.equal((await invoke(setup,fake)).code,0);const r=await invoke(setup,fake,{'--stop':true,'--max-calls':240});assert.equal(r.code,2);assert.equal(fake.posts.length,2);assert.equal(fake.deletes.length,0);assert.equal(r.clock.gh.length,0);
});

test('BUDGET6: creation must not present a different or unconfirmed explicit ceiling as success',async t=>{
 for(const [actual,code] of [[40,5],[300,5],[undefined,3]]){
  const setup=harbor(t),fake=await service(t,()=>actual),result=await invoke(setup,fake,{'--max-calls':240});
  assert.equal(result.code,code);assert.doesNotMatch(result.out,/Simulator link/);assert.match(result.err,/budget|ceiling/i);
  const read=await invoke(setup,fake);assert.equal(read.code,0,read.err);assert.equal(fake.posts.filter(p=>p.command==='try').length,1);assert.equal(fake.deletes.length,0);
 }
});

test('BUDGET7: equal or lower existing ceiling is read-only, keeps total and spent allowance',async t=>{
 const setup=harbor(t),fake=await service(t);
 assert.equal((await invoke(setup,fake)).code,0);fake.spent=40;
 for(const requested of [400,80]){
  const before=fake.posts.length,r=await invoke(setup,fake,{'--max-calls':requested});assert.equal(r.code,0,r.err);
  assert.equal(fake.posts.length,before);assert.equal(fake.jsonPosts.length,0);assert.equal(fake.deletes.length,0);assert.match(r.out,/Simulator budget 400 calls; 360 remaining/);
 }
});
test('BUDGET8: explicit budget on unknown/missing existing Try preserves it without replacement',async t=>{
 for(const mode of ['unknown','missing']){
  const setup=harbor(t),fake=await service(t);assert.equal((await invoke(setup,fake)).code,0);fake.mode=mode;
  const r=await invoke(setup,fake,{'--max-calls':240});assert.equal(r.code,3,r.err);assert.equal(fake.posts.length,2);assert.equal(fake.jsonPosts.length,0);assert.equal(fake.deletes.length,0);
  fake.mode=null;assert.equal((await invoke(setup,fake)).code,0);assert.equal(fake.posts.length,2,'receipt retained');
 }
});
test('BUDGET9: budget reuse enforces recorded owner and origin before effects',async t=>{
 const setup=harbor(t),fake=await service(t);assert.equal((await invoke(setup,fake)).code,0);const reads=fake.gets.length;
 const wrong=await invoke(setup,fake,{'--max-calls':240},{gh:args=>args[0]==='auth'?{status:0,stdout:'different-token'}:{status:0,stdout:'other 4343'}});
 assert.equal(wrong.code,5);assert.equal(fake.gets.length,reads);assert.equal(fake.jsonPosts.length,0);
 const other=await service(t),elsewhere=await invoke(setup,other,{'--max-calls':240});assert.equal(elsewhere.code,2);assert.equal(other.gets.length+other.posts.length+other.jsonPosts.length,0);
});
test('BUDGET10: missing existing budget confirmation fails before mutation or reopening',async t=>{
 let missing=false;const setup=harbor(t),fake=await service(t,cap=>missing?undefined:cap);assert.equal((await invoke(setup,fake)).code,0);missing=true;fake.mode='paused';
 const r=await invoke(setup,fake,{'--max-calls':240});assert.equal(r.code,3,r.err);assert.equal(fake.jsonPosts.length,0);assert.equal(fake.posts.length,2);assert.equal(fake.deletes.length,0);
});

test('BUDGET11: an unsupported higher budget refuses before reopening a paused Try',async t=>{
 const setup=harbor(t),fake=await service(t);assert.equal((await invoke(setup,fake)).code,0);fake.mode='paused';
 const r=await invoke(setup,fake,{'--max-calls':1000});assert.equal(r.code,5,r.err);assert.equal(fake.jsonPosts.length,0);assert.equal(fake.posts.length,2);assert.equal(fake.deletes.length,0);
});

test('BUDGET12: Check direct callers reject out-of-range budgets before any effect',async t=>{
 for(const cap of [0,-1,1.5,NaN,Infinity,true,'1e3',1001,999999,9007199254740992]){
  const setup=harbor(t),fake=await service(t),{ports,clock}=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin});
  assert.equal(await runCheck({cwd:setup.repo,words:['place-order'],options:{'--max-calls':cap}},ports),2,String(cap));assert.equal(fake.posts.length+fake.gets.length,0);assert.equal(clock.gh.length,0);
 }
});
test('BUDGET13: changing the default preserves an older existing160-call Try and its spent allowance',async t=>{
 const setup=harbor(t),fake=await service(t);assert.equal((await invoke(setup,fake,{'--max-calls':160})).code,0);fake.spent=40;
 const result=await invoke(setup,fake);assert.equal(result.code,0,result.err);assert.match(result.out,/Simulator budget 160 calls; 120 remaining/);assert.equal(fake.posts.length,2);assert.equal(fake.jsonPosts.length+fake.deletes.length,0);
});
