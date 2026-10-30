import test from 'node:test';
import assert from 'node:assert/strict';
import fs, { existsSync, mkdirSync, readFileSync, symlinkSync, writeFileSync } from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
import { join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { runContracts } from '../src/contracts.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { gitFiles, interfaceBlocks } from '../src/runtime-preflight.mjs';
import { harbor, fakeRuntime, portsFor, PLACE, sink } from './runtime-fake.mjs';

const ORDER='tests/place-order.json', STORY='user_stories/place-order.md', OTHER='tests/unknown-item.json', OTHER_STORY='user_stories/unknown-item.md';
const write=(repo,path,content)=>{mkdirSync(join(repo,path,'..'),{recursive:true});writeFileSync(join(repo,path),content);};
const json=(repo,path,value)=>write(repo,path,JSON.stringify(value));
const load=(repo,path)=>JSON.parse(readFileSync(join(repo,path),'utf8'));
const body=text=>JSON.parse(interfaceBlocks(text)[0][1]);
function updatePrompt(repo,path,edit) {
  const original=readFileSync(join(repo,path),'utf8'), block=interfaceBlocks(original)[0], value=JSON.parse(block[1]);
  edit(value);
  write(repo,path,original.slice(0,block.indices[1][0])+JSON.stringify(value)+original.slice(block.indices[1][1]));
}
function shared(t) {
  const setup=harbor(t), {repo}=setup;
  const original=body(readFileSync(join(repo,PLACE),'utf8'));
  write(repo,'prompts/other.prompt.md',readFileSync(join(repo,PLACE)));
  const second=load(repo,OTHER); for(const step of second.steps)step.entry_path='prompts/other.prompt.md'; json(repo,OTHER,second);
  const records={order:original.entries[0].input_schema,ticket:structuredClone(original.entries[0].input_schema)};
  const save=()=>write(repo,'contracts/shop.md',`# Shared\n### About\nPlain description.\n${Object.entries(records).map(([name,value])=>`### ${name}\n\x60\x60\x60json\n${JSON.stringify(value)}\n\x60\x60\x60`).join('\n')}\n`);
  save();
  updatePrompt(repo,PLACE,value=>value.entries[0].input_schema={$contract:'contracts/shop.md#order'});
  updatePrompt(repo,'prompts/other.prompt.md',value=>value.entries[0].input_schema={$contract:'contracts/shop.md#ticket'});
  return {...setup,records,save};
}
async function runtime(t,setup,answer) {
  const fake=await fakeRuntime(t,(entry,f)=>{
    const special=answer?.(entry,f); if(special)return special;
    if(entry.command==='lint')return{status:200,json:f.lint(entry.request.requestId,gitFiles(setup.repo).filter(path=>path.endsWith('.prompt.md')).map(path=>({path,state:'approved',admission_state:'approved',interface:{calls:[]}})))};
    if(entry.command==='try')return{status:200,json:f.tryJob(entry.request.requestId)};
    if(entry.url.endsWith('/model'))return{status:200,json:{entries:[],calls:{cap:400,remaining:400}}};
    if(entry.url.endsWith('/state'))return{status:200,json:{actions:[],world:{persisted:true}}};
    if(entry.url.endsWith('/tests'))return{status:200,json:{tests:[]}};
    if(entry.url.endsWith('/approvals'))return{status:200,json:{approvals:[]}};
    if(entry.command==='check')return{status:200,json:f.check(entry.request.requestId)};
    return{status:200,json:f.tryJob(entry.url.split('/').at(-1))};
  });
  const env={HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin};
  return{fake,env,...portsFor(env)};
}
const list=(setup,env)=>{const stdout=sink(),stderr=sink();const code=runContracts({cwd:setup.repo},{env,stdout,stderr});return{code,stdout:stdout.text,stderr:stderr.text};};


test('catalog: seeded test and transitive users; common changes stale both actual checked Stories; listing has no writes',async t=>{
  const setup=shared(t);
  setup.records.ticket={$contract:'contracts/shop.md#order'};setup.save();
  json(setup.repo,'contracts/world.json',{stock:0});
  const authored=load(setup.repo,ORDER);authored.initial_world={$seed:'contracts/world.json'};json(setup.repo,ORDER,authored);
  const ready=await runtime(t,setup);
  assert.equal(await runCheck({cwd:setup.repo},ready.ports),0,ready.ports.stderr.text);
  const first=list(setup,ready.env);assert.equal(first.code,0,first.stderr);
  const common=first.stdout.split('\n').find(s=>s.startsWith('contracts/shop.md#order '));
  assert.ok(common.includes(PLACE)&&common.includes('prompts/other.prompt.md'),common);
  assert.ok(common.includes(STORY)&&common.includes(OTHER_STORY),common);
  const seed=first.stdout.split('\n').find(s=>s.startsWith('contracts/world.json# '));
  assert.ok(seed.includes(ORDER)&&seed.includes(STORY),seed);
  setup.records.order.description='Independently selected common record change';setup.save();
  const methods=['mkdirSync','chmodSync','writeFileSync','writeSync','renameSync','ftruncateSync'];
  const originals=Object.fromEntries(methods.map(name=>[name,fs[name]]));
  let writes=0;
  for(const name of methods)fs[name]=(...args)=>{writes++;throw Error('Listing attempted '+name);};
  syncBuiltinESMExports();
  let after;
  const gets=ready.fake.gets.length,posts=ready.fake.posts.length,gh=ready.clock.gh.length;
  try{after=list(setup,ready.env);}finally{for(const name of methods)fs[name]=originals[name];syncBuiltinESMExports();}
  assert.equal(after.code,0,after.stderr);assert.equal(writes,0);
  assert.match(after.stdout,/place-order.md: stale: needs a new check/);
  assert.match(after.stdout,/unknown-item.md: stale: needs a new check/);
  assert.equal(ready.fake.gets.length,gets);assert.equal(ready.fake.posts.length,posts);assert.equal(ready.clock.gh.length,gh);
});

test('CLI sync: unsafe symlink ancestor leaves destination, original test and unmatched prompt exact',async t=>{
  const setup=harbor(t),repo=setup.repo;
  const original=readFileSync(join(repo,PLACE),'utf8'),input=body(original).entries[0].input_schema;
  json(repo,'contracts/order.json',input);
  write(repo,'prompts/unmatched.prompt.md','# unrelated exact bytes\r\n');
  const testBytes=readFileSync(join(repo,ORDER));
  const outside=join(setup.sandbox,'outside');fs.renameSync(join(repo,'prompts'),outside);symlinkSync(outside,join(repo,'prompts'));
  const stdout=sink(),stderr=sink();
  assert.equal(await runPdd(['contracts','sync','--write'],{cwd:repo,env:{HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:'not-an-origin'},stdout,stderr}),4,stderr.text);
  assert.match(stderr.text,/symbolic link ancestor/);
  assert.equal(readFileSync(join(outside,'place_order.prompt.md'),'utf8'),original);
  assert.equal(readFileSync(join(outside,'unmatched.prompt.md'),'utf8'),'# unrelated exact bytes\r\n');
  assert.deepEqual(readFileSync(join(repo,ORDER)),testBytes);assert.equal(existsSync(setup.state),false);
});
