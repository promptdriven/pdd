import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs, { existsSync, mkdirSync, readFileSync, readdirSync, rmSync, statSync, symlinkSync, writeFileSync } from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { runPdd } from '../src/pdd-cli.mjs';
import { runContracts } from '../src/contracts.mjs';
import { runCheck, runTry, readContractHistory, readTryOwner } from '../src/runtime-client.mjs';
import { captureSource, findTests, fillHashes, gitFiles, interfaceBlocks, preflight, readPrompt, sourceFilePort } from '../src/runtime-preflight.mjs';
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
const repoState=setup=>{const dir=join(setup.state,'repos'),path=join(dir,readdirSync(dir)[0]);return{path,value:JSON.parse(readFileSync(path,'utf8'))};};

test('NATIVE references reach public preflight and capture; raw contract-only files remain private',t=>{
  const setup=shared(t),found=findTests({root:setup.repo}), selected=found.tests;
  const prompt=readPrompt(setup.repo,found.visible,PLACE);
  assert.deepEqual(prompt.interface.entries[0].input_schema,setup.records.order);
  assert.equal(preflight({root:setup.repo,found,selected}).rows.every(row=>row.refusals.length===0),true);
  const capture=captureSource(setup.repo,{tests:selected.map(test=>test.path)});
  assert.equal(capture.files.some(file=>file.path==='contracts/shop.md'),false);
  assert.equal(capture.references.length,2);
  assert.deepEqual(capture.stories.find(story=>story.story_path===STORY).references.map(ref=>ref.target),['contracts/shop.md#order']);
  assert.deepEqual(capture.stories.find(story=>story.story_path===OTHER_STORY).references.map(ref=>ref.target),['contracts/shop.md#ticket']);
  const before=capture.stories.find(story=>story.story_path===OTHER_STORY);
  setup.records.order.description='Changed shared record';setup.save();
  const after=captureSource(setup.repo).stories.find(story=>story.story_path===OTHER_STORY);
  assert.deepEqual(after,before);
  const raw=readFileSync(join(setup.repo,PLACE),'utf8');
  const fill=fillHashes({root:setup.repo});assert.equal(fill.refused.length,0);
  assert.equal(readFileSync(join(setup.repo,PLACE),'utf8'),raw);
});

test('NATIVE sourceFilePort reports missing/unsafe reads without an archive or authored effects',t=>{
  const setup=harbor(t),port=sourceFilePort(setup.repo);
  assert.deepEqual(port.stat({path:'absent.json'}),{exists:false,is_symlink:false,size:0});
  assert.throws(()=>port.read({path:'absent.json'}),error=>error.exitCode===4);
  assert.throws(()=>port.stat({path:'../outside.json'}),error=>error.exitCode===4);
  assert.equal(port.read({path:PLACE}).content,readFileSync(join(setup.repo,PLACE),'utf8'));
  assert.equal(existsSync(setup.state),false);
});

test('NATIVE generated references and virtual targets use the same effective overlay and provenance',t=>{
  const {repo}=harbor(t),scenario=load(repo,ORDER),raw=readFileSync(join(repo,PLACE),'utf8'), block=interfaceBlocks(raw)[0], iface=JSON.parse(block[1]);
  const input=iface.entries[0].input_schema;iface.entries[0].input_schema={$contract:'contracts/virtual.json#/input'};
  scenario.initial_world={$seed:'contracts/world.json'};
  const capture=captureSource(repo,{tests:['virtual/test.json'],prepareSource:()=>[
    {path:PLACE,bytes:raw.slice(0,block.indices[1][0])+JSON.stringify(iface)+raw.slice(block.indices[1][1])},
    {path:'contracts/virtual.json',bytes:JSON.stringify({input})},{path:'contracts/world.json',bytes:'{"stock":0}'},
    {path:'virtual/test.json',bytes:JSON.stringify(scenario)},
  ]});
  assert.equal(body(capture.sources.find(file=>file.path===PLACE).bytes.toString()).entries[0].input_schema.type,'object');
  assert.deepEqual(JSON.parse(capture.sources.find(file=>file.path==='virtual/test.json').bytes.toString()).initial_world,{stock:0});
  assert.deepEqual(capture.references.map(ref=>ref.kind).sort(),['contract','seed']);
});

test('NATIVE reference-only races retry the whole capture and never upload raw contract files',t=>{
  const setup=shared(t);setup.records.order.description='source-race-marker';setup.save();
  const original=fs.readFileSync;let changed=false,calls=0;
  t.after(()=>{fs.readFileSync=original;syncBuiltinESMExports();});
  fs.readFileSync=(...args)=>{
    const bytes=original(...args);
    if(typeof args[0]==='number' && bytes.includes('source-race-marker') && !changed){changed=true;setup.records.order.description='source-race-new';setup.save();}
    return bytes;
  };syncBuiltinESMExports();
  const capture=captureSource(setup.repo,{tests:[ORDER],prepareSource(){calls++;return[];}});
  assert.equal(calls,2);assert.equal(capture.files.some(file=>file.path==='contracts/shop.md'),false);
  assert.match(capture.references[0].value_json,/source-race-new/);
  let churn=0;
  fs.readFileSync=(...args)=>{
    const bytes=original(...args);
    if(typeof args[0]==='number' && bytes.includes('source-race-new')){setup.records.order.description=`source-race-new-${++churn}`;setup.save();}
    return bytes;
  };syncBuiltinESMExports();
  assert.throws(()=>captureSource(setup.repo,{tests:[ORDER],attempts:2}),error=>error.exitCode===5);
  assert.equal(churn,2);
});

test('NATIVE upload limits count expanded effective bytes rather than larger authored reference syntax',t=>{
  const setup=shared(t),path=join(setup.repo,PLACE),text=readFileSync(path,'utf8'),block=interfaceBlocks(text)[0];
  const padding=Array(170_000).fill('null'+ ' '.repeat(64)).join(',');
  writeFileSync(path,text.slice(0,block.indices[1][0])+'{"padding":['+padding+'],'+block[1].slice(1)+text.slice(block.indices[1][1]));
  const capture=captureSource(setup.repo,{tests:[ORDER]});
  assert.ok(capture.bytes<10_485_760);
  assert.match(capture.sources.find(file=>file.path===PLACE).bytes.toString(),/"input_schema":\{"additionalProperties"/);
});

test('NATIVE missing and unsafe references stop Check, explicit lint and Try before sign-in/upload',async t=>{
  const setup=shared(t);
  for(const target of ['contracts/missing.json#','../outside.json#','contracts/link.json#']) {
    if(target.includes('link'))symlinkSync(join(setup.repo,'contracts/shop.md'),join(setup.repo,'contracts/link.json'));
    updatePrompt(setup.repo,PLACE,value=>value.entries[0].input_schema={$contract:target});
    for(const [run,options]of[[runCheck,{}],[runCheck,{'--lint':true}],[runTry,{'--no-open':true,'--no-wait':true}]]) {
      const ports=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state},{gh:()=>assert.fail('must not sign in'),fetch:()=>assert.fail('must not upload')}).ports;
      assert.equal(await run({cwd:setup.repo,words:['place-order'],options},ports),4,ports.stderr.text);
      assert.match(ports.stderr.text,/contract-(?:missing|unsafe)/);
    }
  }
});

test('NATIVE catalog lists current users and unused records without creating local state',t=>{
  const setup=shared(t),env={HOME:setup.home,PDD_STATE_DIR:setup.state};
  write(setup.repo,'contracts/unused.json','{"type":"string"}');
  const output=list(setup,env);assert.equal(output.code,0,output.stderr);
  assert.match(output.stdout,/contracts\/shop.md#order.*prompts\/place_order.prompt.md.*user_stories\/place-order.md/);
  assert.match(output.stdout,/contracts\/unused.json#.*users: none/);
  assert.doesNotMatch(output.stdout,/shop.md#About/);
  assert.match(output.stdout,/place-order.md: not checked/);
  assert.equal(existsSync(setup.state),false);
  assert.equal(readContractHistory({root:setup.repo,env}).stories.every(story=>story.baseline==='not-checked'),true);
  assert.equal(existsSync(setup.state),false);
});

test('NATIVE actual batch snapshots isolate same-file Stories and survive later source edits and receipt reads',async t=>{
  const setup=shared(t),ready=await runtime(t,setup);
  assert.equal(await runCheck({cwd:setup.repo},ready.ports),0,ready.ports.stderr.text);
  const oldState=repoState(setup),oldBatch=oldState.value.last_batch;
  const initial=readContractHistory({root:setup.repo,env:ready.env});assert.equal(initial.stories.every(story=>story.baseline==='checked'),true);
  setup.records.order.description='New record';setup.save();
  const output=list(setup,ready.env);assert.equal(output.code,0,output.stderr);
  assert.match(output.stdout,/shop.md#order: changed since the last check/);
  assert.match(output.stdout,/place-order.md: stale: needs a new check/);
  assert.match(output.stdout,/unknown-item.md: current/);
  ready.clock.now+=10_000;
  assert.equal(await runCheck({cwd:setup.repo,words:['place-order']},ready.ports),0);
  const newer=readContractHistory({root:setup.repo,env:ready.env}).stories.find(story=>story.story_path===STORY);
  assert.equal(await runCheck({cwd:setup.repo,words:[oldBatch],options:{'--read':true}},ready.ports),0);
  assert.deepEqual(readContractHistory({root:setup.repo,env:ready.env}).stories.find(story=>story.story_path===STORY),newer);
  assert.notDeepEqual(newer.references,initial.stories.find(story=>story.story_path===STORY).references);
});

test('NATIVE evaluated failures remain failures; lint and Try do not advance the Check baseline',async t=>{
  const setup=shared(t),ready=await runtime(t,setup,(entry,f)=>entry.command==='check'?{status:200,json:f.check(entry.request.requestId,'failed',[{criterion_id:'AC1',target:'result',path:'/totalCents',op:'equals',expected:900,actual:0,passed:false}])}:null);
  assert.equal(await runCheck({cwd:setup.repo,words:['place-order']},ready.ports),1);
  const before=readContractHistory({root:setup.repo,env:ready.env}).stories.find(story=>story.story_path===STORY);assert.equal(before.result_state,'failed');
  setup.records.order.description='Changed';setup.save();ready.clock.now+=1000;
  assert.equal(await runCheck({cwd:setup.repo,words:['place-order'],options:{'--lint':true}},ready.ports),0);
  assert.equal(await runTry({cwd:setup.repo,words:['place-order'],options:{'--no-open':true,'--no-wait':true}},ready.ports),0);
  assert.deepEqual(readContractHistory({root:setup.repo,env:ready.env}).stories.find(story=>story.story_path===STORY),before);
  assert.match(list(setup,ready.env).stdout,/last check failed/);
});

test('NATIVE identical original Check times select a real failed result; strictly later passing Check wins',async t=>{
  const setup=shared(t);rmSync(join(setup.repo,OTHER));
  const second=load(setup.repo,ORDER);second.steps[0].step_id='second-world';json(setup.repo,'tests/second-world.json',second);
  let originalTime='2026-10-27T16:27:47.000Z';
  const ready=await runtime(t,setup,(entry,f)=>{
    if(entry.command!=='check')return null;
    const failed=entry.request.scenario==='tests/second-world.json';
    const receipt=f.check(entry.request.requestId,failed?'failed':'passed',[{criterion_id:'AC1',target:'result',path:'/totalCents',op:'equals',expected:900,actual:failed?0:900,passed:!failed}]);
    receipt.created_at=originalTime;
    return{status:200,json:receipt};
  });
  assert.equal(await runCheck({cwd:setup.repo,words:['place-order']},ready.ports),1);
  const tied=readContractHistory({root:setup.repo,env:ready.env}).stories.find(story=>story.story_path===STORY);
  assert.equal(tied.result_state,'failed');assert.equal(tied.checked_at,originalTime);
  originalTime='2026-10-27T16:28:47.000Z';ready.clock.now+=60_000;
  assert.equal(await runCheck({cwd:setup.repo,words:[ORDER]},ready.ports),0);
  const later=readContractHistory({root:setup.repo,env:ready.env}).stories.find(story=>story.story_path===STORY);
  assert.equal(later.result_state,'passed');assert.equal(later.checked_at,originalTime);
});

test('NATIVE a Check baseline uses bytes submitted before an edit during the receipt',async t=>{
  const setup=shared(t);let edited=false;
  const ready=await runtime(t,setup,(entry)=>{
    if(entry.command==='check'&&!edited){edited=true;setup.records.order.description='Edited after submission';setup.save();}
  });
  assert.equal(await runCheck({cwd:setup.repo,words:['place-order']},ready.ports),0);
  const baseline=readContractHistory({root:setup.repo,env:ready.env}).stories.find(story=>story.story_path===STORY);
  assert.doesNotMatch(baseline.references[0].value_json,/Edited after submission/);
  assert.match(list(setup,ready.env).stdout,/place-order.md: stale: needs a new check/);
});

test('NATIVE legacy receipts are unavailable; pre-execution or unknown receipts are never baselines',async t=>{
  const setup=shared(t),ready=await runtime(t,setup);
  assert.equal(await runCheck({cwd:setup.repo,words:['place-order']},ready.ports),0);
  const state=repoState(setup),folder=join(setup.state,'batches',state.value.last_batch),batch=JSON.parse(readFileSync(join(folder,'batch.json')));
  delete batch.contract_snapshots;writeFileSync(join(folder,'batch.json'),JSON.stringify(batch));
  assert.equal(readContractHistory({root:setup.repo,env:ready.env}).stories.find(story=>story.story_path===STORY).baseline,'unavailable');
  const receipt=join(folder,`${batch.rows[0].request_ids[0]}.json`),value=JSON.parse(readFileSync(receipt));
  value.state='refused';value.result.report.samples=[];writeFileSync(receipt,JSON.stringify(value));
  assert.equal(readContractHistory({root:setup.repo,env:ready.env}).stories.find(story=>story.story_path===STORY).baseline,'not-checked');
  value.state='unknown';writeFileSync(receipt,JSON.stringify(value));
  assert.equal(readContractHistory({root:setup.repo,env:ready.env}).stories.find(story=>story.story_path===STORY).baseline,'not-checked');
});

function copies(t) {
  const setup=harbor(t), canonical=body(readFileSync(join(setup.repo,PLACE),'utf8')).entries[0].input_schema;
  const original=readFileSync(join(setup.repo,PLACE),'utf8');
  const inline=structuredClone(canonical);inline.title='CLI request';inline.description='local';
  canonical.properties.run_id={type:'string'};canonical.required.push('run_id');
  json(setup.repo,'contracts/order.json',canonical);
  updatePrompt(setup.repo,PLACE,value=>value.entries[0].input_schema=inline);
  return{...setup,canonical,original};
}

test('NATIVE real CLI sync preview/write adopts shared shape, preserves hash/prose and is idempotent',async t=>{
  const setup=copies(t),env={HOME:setup.home,PDD_STATE_DIR:setup.state};
  const before=readFileSync(join(setup.repo,PLACE),'utf8'),beforeBody=body(before),stdout=sink(),stderr=sink();
  assert.equal(await runPdd(['contracts','sync'],{cwd:setup.repo,env,stdout,stderr}),0,stderr.text);
  assert.match(stdout.text,/run_id/);assert.equal(readFileSync(join(setup.repo,PLACE),'utf8'),before);
  assert.equal(existsSync(setup.state),false);
  const code=await runPdd(['contracts','sync','--write'],{cwd:setup.repo,env,stdout,stderr});assert.equal(code,0,stderr.text);
  const after=readFileSync(join(setup.repo,PLACE),'utf8'),afterBody=body(after);
  assert.equal(afterBody.status,'draft');assert.equal(afterBody.prose_sha256,beforeBody.prose_sha256);
  assert.deepEqual(afterBody.entries[0].input_schema,{$contract:'contracts/order.json#',description:'local',title:'CLI request'});
  assert.equal(after.slice(0,interfaceBlocks(after)[0].index),before.slice(0,interfaceBlocks(before)[0].index));
  const expanded=readPrompt(setup.repo,new Set(gitFiles(setup.repo)),PLACE).interface.entries[0].input_schema;
  assert.ok(expanded.required.includes('run_id'));assert.equal(expanded.title,'CLI request');
  const mtime=statSync(join(setup.repo,PLACE)).mtimeMs;
  assert.equal(await runPdd(['contracts','sync','--write'],{cwd:setup.repo,env,stdout,stderr}),0);
  assert.equal(statSync(join(setup.repo,PLACE)).mtimeMs,mtime);
});

test('NATIVE sync ambiguity skips a copy while independent exact copies migrate',t=>{
  const setup=copies(t);json(setup.repo,'contracts/duplicate.json',setup.canonical);
  const unique={type:'object',properties:{unique:{type:'boolean'}},required:['unique'],additionalProperties:false};
  json(setup.repo,'contracts/unique.json',unique);
  write(setup.repo,'prompts/unique.prompt.md',readFileSync(join(setup.repo,PLACE)));
  updatePrompt(setup.repo,'prompts/unique.prompt.md',value=>value.entries[0].input_schema=unique);
  const before=readFileSync(join(setup.repo,PLACE),'utf8'),stdout=sink(),stderr=sink();
  assert.equal(runContracts({cwd:setup.repo,words:['sync'],options:{'--write':true}},{env:{HOME:setup.home},stdout,stderr}),0);
  assert.match(stderr.text,/ambiguous/);assert.equal(readFileSync(join(setup.repo,PLACE),'utf8'),before);
  assert.equal(body(readFileSync(join(setup.repo,'prompts/unique.prompt.md'),'utf8')).entries[0].input_schema.$contract,'contracts/unique.json#');
});

test('NATIVE sync refuses concurrent destination edits and unsafe originals without overwriting',t=>{
  const setup=copies(t),original=fs.openSync;let edited=false;
  t.after(()=>{fs.openSync=original;syncBuiltinESMExports();});
  fs.openSync=(path,flags,...args)=>{
    if(path===join(setup.repo,PLACE)&&typeof flags==='number'&&(flags&fs.constants.O_RDWR)&&!edited){edited=true;writeFileSync(path,'# Concurrent edit\n');}
    return original(path,flags,...args);
  };syncBuiltinESMExports();
  const stdout=sink(),stderr=sink();
  assert.equal(runContracts({cwd:setup.repo,words:['sync'],options:{'--write':true}},{env:{HOME:setup.home},stdout,stderr}),4);
  assert.equal(readFileSync(join(setup.repo,PLACE),'utf8'),'# Concurrent edit\n');assert.match(stderr.text,/changed since preview/);
  fs.openSync=original;syncBuiltinESMExports();
  rmSync(join(setup.repo,PLACE));symlinkSync(join(setup.repo,'contracts/order.json'),join(setup.repo,PLACE));
  const unsafe=runContracts({cwd:setup.repo,words:['sync'],options:{'--write':true}},{env:{HOME:setup.home},stdout,stderr});
  assert.equal(unsafe,4);assert.equal(load(setup.repo,'contracts/order.json').type,'object');
  const secret=copies(t),originalSource=readFileSync(join(secret.repo,PLACE),'utf8');
  write(secret.repo,'secrets/consumer.prompt.md',originalSource);
  assert.equal(runContracts({cwd:secret.repo,words:['sync'],options:{'--write':true}},{env:{HOME:secret.home},stdout,stderr}),4);
  assert.equal(readFileSync(join(secret.repo,PLACE),'utf8'),originalSource);
});

test('NATIVE drift advice appears only for explicit remote lint and preserves its server outcome',async t=>{
  for(const refuse of [false,true]){
    const setup=copies(t),ready=await runtime(t,setup,(entry,f)=>entry.command==='lint'&&refuse?{status:200,json:f.lint(entry.request.requestId,[],[{path:PLACE,code:'example-refusal',message:'Synthetic server refusal'}])}:null);
    const code=await runCheck({cwd:setup.repo,words:['place-order'],options:{'--lint':true}},ready.ports);
    assert.equal(code,refuse?4:0);assert.match(ready.ports.stderr.text,/copy of contracts\/order.json# differs/);assert.match(ready.ports.stderr.text,/run_id/);
    assert.equal(ready.fake.posts.filter(post=>post.command==='check').length,0);
    assert.equal(ready.fake.posts[0].tar.equals(captureSource(setup.repo,{tests:[ORDER]}).tar),true);
    const stdout=sink(),stderr=sink();
    assert.equal(await runCheck({cwd:setup.repo,words:['place-order'],options:{'--lint':true,'--local':true}},{...ready.ports,stdout,stderr}),0);
    assert.doesNotMatch(stdout.text+stderr.text,/copy of contracts/);
  }
});

test('NATIVE Try pins expanded prompts while preserving its original world and authored append path',async t=>{
  const setup=shared(t);json(setup.repo,'contracts/world.json',{stock:0});
  const scenario=load(setup.repo,ORDER);scenario.initial_world={$seed:'contracts/world.json'};json(setup.repo,ORDER,scenario);
  const ready=await runtime(t,setup);
  assert.equal(await runTry({cwd:setup.repo,words:['place-order'],options:{'--no-open':true,'--no-wait':true}},ready.ports),0);
  const state=repoState(setup),record=state.value.tries[ORDER];
  assert.deepEqual(record.seed_scenario.initial_world,{stock:0});assert.equal(record.storyPath,STORY);assert.equal(record.contract_references.length,2);
  json(setup.repo,'contracts/world.json',{stock:9});
  const owner=await readTryOwner({cwd:setup.repo,story:'place-order'},ready.ports);assert.deepEqual(owner.test.doc.initial_world,{stock:0});
  setup.records.order.description='Prompt contract changed';setup.save();
  const before=ready.fake.gets.length;
  await assert.rejects(readTryOwner({cwd:setup.repo,story:'place-order'},ready.ports),/shared contract changed.*--new/);
  assert.equal(ready.fake.gets.length,before);
  setup.records.order.description=undefined;delete setup.records.order.description;setup.save();
  const legacy=repoState(setup);delete legacy.value.tries[ORDER].effective_prompt_hashes;writeFileSync(legacy.path,JSON.stringify(legacy.value));
  await assert.rejects(readTryOwner({cwd:setup.repo,story:'place-order'},ready.ports),/reference baseline is unavailable.*--new/);
});

test('NATIVE command parser dispatch and subprocess listing stay local without agent/PATH/auth effects',async t=>{
  let seen;
  const stdout=sink(),stderr=sink();
  assert.equal(await runPdd(['contracts','sync','--write'],{stdout,stderr,contracts:{runContracts(input,ports){seen={input,ports};return 0;}},env:{HOME:'/not-read',PATH:'/not-read'}}),0);
  assert.deepEqual(seen.input.words,['sync']);assert.equal(seen.input.options['--write'],true);
  for(const args of [['contracts','--write'],['contracts','sync','bad'],['contracts','sync','--write','--write']])assert.equal(await runPdd(args,{stdout,stderr}),2);
  const setup=shared(t),entry=fileURLToPath(new URL('../bin/pdd.mjs',import.meta.url));
  const result=spawnSync(process.execPath,[entry,'contracts'],{cwd:setup.repo,encoding:'utf8',env:{...process.env,HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:'not-an-origin'}});
  assert.equal(result.status,0,result.stderr);assert.match(result.stdout,/contracts\/shop.md#order/);assert.equal(existsSync(setup.state),false);
});
