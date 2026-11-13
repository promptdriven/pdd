import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,readdirSync} from 'node:fs';
import {join} from 'node:path';
import {runTry} from '../../src/runtime-seam.mjs';
import {fakeRuntime,harbor,portsFor} from './runtime-fake.mjs';

const invoke=async(setup,fake,options={})=>{
 const {ports,clock}=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin});
 const code=await runTry({cwd:setup.repo,words:['place-order'],options:{'--no-open':true,'--no-wait':true,...options}},ports);
 return{code,clock,out:ports.stdout.text,err:ports.stderr.text};
};
const record=setup=>{
 const path=join(setup.state,'repos',readdirSync(join(setup.state,'repos'))[0]);
 const bytes=readFileSync(path,'utf8');return{bytes,try:JSON.parse(bytes).tries['tests/place-order.json']};
};
const server=(t,initial='running',direct=false)=>fakeRuntime(t,(e,f)=>{
 if(e.command==='lint')return{status:200,json:f.lint(e.request.requestId)};
 if(e.command==='try')return direct
  ?{status:200,json:f.tryJob(e.request.requestId,undefined,(f.mode??initial)==='unknown-session'?'unknown':f.mode??initial)}
  :{status:202,json:f.job(e.request.requestId,'try','queued')};
 if(e.method==='DELETE')return{status:404,json:{error:{code:'not-found'}}};
 if(!e.url.startsWith('/v1/runs/'))return{status:404,json:{}};
 const mode=f.mode??initial,id=e.url.split('/').at(-1);
 if(typeof mode==='number')return{status:mode,json:{error:{code:mode===404?'not-found':'result-expired'}}};
 if(mode==='unknown')return{status:200,json:f.job(id,'try','unknown',{exitCode:3,refusals:[]})};
 return{status:200,json:f.tryJob(id,undefined,mode==='unknown-session'?'unknown':mode)};
});

for(const mode of ['unknown',404,410])test(`RECOVERY721: ${mode} keeps the original intent until deliberate replacement`,async t=>{
 const setup=harbor(t),fake=await server(t);
 assert.equal((await invoke(setup,fake)).code,0);
 const saved=record(setup),posts=fake.posts.length;fake.mode=mode;
 for(let n=0;n<2;n++){
  const result=await invoke(setup,fake);
  assert.equal(result.code,3,result.err);assert.equal(fake.posts.length,posts,'status recovery must not submit even free lint');
  assert.equal(fake.deletes.length+fake.jsonPosts.length,0);assert.equal(result.clock.uuids,0);
  assert.equal(record(setup).bytes,saved.bytes);assert.match(result.err,new RegExp(saved.try.id));
  assert.ok(result.err.includes(`/v1/runs/${saved.try.id}`));assert.doesNotMatch(result.err,/used no AI calls/);
 }
 fake.mode='running';assert.equal((await invoke(setup,fake)).code,0);
 assert.equal(record(setup).try.id,saved.try.id);assert.equal(fake.posts.length,posts);
 fake.mode=mode;await invoke(setup,fake,{'--new':true});
 // The explicit replacement is submitted even if this fake also marks that new setup uncertain.
 assert.equal(fake.posts.filter(p=>p.command==='try').length,2);assert.notEqual(record(setup).try?.id,saved.try.id);
});

test('RECOVERY721: an initially unknown setup remains recorded and repeated reads send nothing new',async t=>{
 const setup=harbor(t),fake=await server(t,'unknown');
 const first=await invoke(setup,fake);assert.equal(first.code,3,first.err);
 const saved=record(setup);assert.ok(saved.try?.id,'the original setup receipt must survive');
 assert.ok(first.err.includes(saved.try.id));assert.doesNotMatch(first.err,/used no AI calls/);
 const again=await invoke(setup,fake);assert.equal(again.code,3);
 assert.equal(record(setup).bytes,saved.bytes);assert.equal(fake.posts.filter(p=>p.command==='try').length,1);
 fake.mode='running';assert.equal((await invoke(setup,fake)).code,0);
 assert.equal(record(setup).try.id,saved.try.id);
});

test('RECOVERY721: a passed setup with an unknown session cannot be replaced implicitly',async t=>{
 const setup=harbor(t),fake=await server(t);
 assert.equal((await invoke(setup,fake)).code,0);const saved=record(setup);fake.mode='unknown-session';
 // Preserve a verified passed envelope while exposing only uncertain session state.
 const result=await invoke(setup,fake);
 assert.equal(result.code,3,result.err);assert.equal(record(setup).bytes,saved.bytes);
 assert.equal(fake.posts.filter(p=>p.command==='try').length,1);
});

test('RECOVERY721: a confirmed stopped setup still requires deliberate replacement',async t=>{
 const setup=harbor(t),fake=await server(t);
 assert.equal((await invoke(setup,fake)).code,0);const saved=record(setup);fake.mode='stopped';
 const result=await invoke(setup,fake);
 assert.equal(result.code,3,result.err);assert.equal(record(setup).bytes,saved.bytes);
 assert.equal(fake.posts.filter(p=>p.command==='try').length,1);
});


for(const mode of ['unknown-session','stopped','stopping'])for(const direct of [false,true])test(`RECOVERY721: initial ${mode} session via ${direct?'setup reply':'status read'} retains its receipt`,async t=>{
 const setup=harbor(t),fake=await server(t,mode,direct);
 const first=await invoke(setup,fake);
 assert.equal(first.code,3,first.err);
 const saved=record(setup),id=fake.posts.find(p=>p.command==='try').request.requestId;
 assert.equal(saved.try.id,id);
 assert.ok(first.err.includes(id));assert.ok(first.err.includes(`/v1/runs/${id}`));
 assert.equal(fake.posts.filter(p=>p.command==='lint').length,1);
 assert.equal(fake.posts.filter(p=>p.command==='try').length,1);
 for(let n=0;n<2;n++){
  const reads=fake.gets.length,result=await invoke(setup,fake);
  assert.equal(result.code,3,result.err);assert.equal(result.clock.uuids,0);
  assert.equal(record(setup).bytes,saved.bytes);
  assert.equal(fake.posts.length,2,'a plain repeat cannot submit lint or setup');
  assert.equal(fake.deletes.length,0);assert.equal(fake.jsonPosts.length,0);
  assert.deepEqual(fake.gets.slice(reads).map(e=>e.url),[`/v1/runs/${id}`]);
  assert.ok(result.err.includes(id));assert.ok(result.err.includes(`/v1/runs/${id}`));
 }
 fake.mode='running';
 assert.equal((await invoke(setup,fake)).code,0);
 assert.equal(record(setup).try.id,id);assert.equal(fake.posts.length,2);
});
