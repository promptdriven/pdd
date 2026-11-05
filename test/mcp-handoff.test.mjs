import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {join} from 'node:path';
import {createHash} from 'node:crypto';
import {PassThrough} from 'node:stream';
import {setTimeout as delay} from 'node:timers/promises';
import {spawn} from 'node:child_process';
import {harbor,fakeRuntime,portsFor,PLACE} from './runtime-fake.mjs';
import {runMcp} from '../src/try-mcp.mjs';
import * as client from '../src/runtime-client.mjs';
import {interfaceBlocks,proseSha256} from '../src/runtime-preflight.mjs';

const read=path=>fs.readFileSync(path,'utf8');
const json=path=>JSON.parse(read(path));
const write=(path,value)=>fs.writeFileSync(path,JSON.stringify(value));
const variantFiles=f=>fs.readdirSync(join(f.repo,'tests')).filter(name=>name.includes('.try-'));
const nativePorts=f=>({env:f.env,gh:()=>assert.fail('local apply must not authenticate'),fetch:()=>assert.fail('local apply must not use HTTP')});
const apply=(f,extra={})=>client.applyPendingCaseWithHandoff({cwd:f.repo,pendingId:f.receipt.pendingId,handoff:{kind:'closed-editor',testPath:f.originalPath},...extra},nativePorts(f));

async function protocol(cwd,env,ports={}){
  const stdin=new PassThrough(),stdout=new PassThrough(),stderr=new PassThrough();let output='',errors='',nextId=0,closed=false;
  stdout.on('data',x=>output+=x);stderr.on('data',x=>errors+=x);
  const done=runMcp({cwd,env},{...ports,stdin,stdout,stderr});
  return{
    async call(method,params,id=++nextId){const count=()=>output.split('\n').filter(Boolean).map(x=>JSON.parse(x)).filter(x=>x.id===id),before=count().length;stdin.write(JSON.stringify({jsonrpc:'2.0',id,method,...(params?{params}:{})})+'\n');const end=Date.now()+15000;for(;;){const found=count();if(found.length>before)return found.at(-1);assert.ok(Date.now()<end,'stdio response timeout: '+errors);await delay(2);}},
    async close(){if(!closed){closed=true;stdin.end();assert.equal(await done,0,errors);}},
    get output(){return output;},get errors(){return errors;}
  };
}

// Default MCP, owner, saver and files. Only the initial hosted transport and gh
// identity/clock are controlled. Local application uses no injected owner/lease.
async function staged(t,{savedCase,references=false,sourceSetup}={}){
  const before={kv:{exact:['before']}},after={kv:{exact:['after']}},observed={stdout:'exact output\n',stderr:'exact stderr\n',exit_code:0};
  const f=harbor(t,root=>{
    fs.rmSync(join(root,'tests/unknown-item.json'));
    if(savedCase){const path=join(root,'tests/place-order.json'),doc=json(path);doc.steps.at(-1).checks.push({criterion_id:doc.criteria[0].id,target:'world',path:'',op:'equals',value:before});write(path,doc);}
    if(references){const path=join(root,PLACE),text=read(path),block=interfaceBlocks(text)[0],iface=JSON.parse(block[1]);fs.mkdirSync(join(root,'contracts'));write(join(root,'contracts/request.json'),iface.entries[0].input_schema);iface.entries[0].input_schema={$contract:'contracts/request.json#'};fs.writeFileSync(path,text.slice(0,block.indices[1][0])+JSON.stringify(iface)+text.slice(block.indices[1][1]));}
    sourceSetup?.(root);
  });
  const originalPath='tests/place-order.json',original=read(join(f.repo,originalPath)),doc=JSON.parse(original);
  write(join(f.repo,'pdd-workspace.json'),{allowed_paths:['prompts/','user_stories/','tests/',...(references?['contracts/']:[])]});
  const calls=new Map();let callPosts=0;
  const http=await fakeRuntime(t,(entry,h)=>{
    if(entry.url.endsWith('/model'))return{status:200,json:{entries:[{entry_path:PLACE,operation:'place_order',input_schema:{type:'object'}}],calls:{cap:400,remaining:399}}};
    if(entry.url.endsWith('/state'))return{status:200,json:{world:before,actions:[]}};
    if(entry.command==='lint')return{status:200,json:h.lint(entry.request.requestId)};
    if(entry.command==='try')return{status:200,json:h.tryJob(entry.request.requestId)};
    if(entry.method==='POST'&&entry.url.endsWith('/call')){callPosts++;const q=entry.json;const value={id:q.requestId,requestId:q.requestId,command:'call',state:'passed',session_id:entry.url.split('/')[3],result:{program_result:observed,report:{input_world:before,world:after}}};calls.set(q.requestId,value);return{status:200,json:value};}
    const id=entry.url.split('/').at(-1);return{status:200,json:calls.get(id)??h.tryJob(id)};
  });
  const state=join(f.sandbox,'requested-state'),env={...process.env,HOME:f.home,PDD_STATE_DIR:state,PDD_RUNTIME_URL:http.origin};
  const {ports}=portsFor(env);const external={blocked:false,gh:0,http:0};const gh=ports.gh;
  ports.gh=args=>{external.gh++;assert.equal(external.blocked,false,'local pending apply attempted gh');return gh(args);};
  ports.fetch=(...args)=>{external.http++;assert.equal(external.blocked,false,'local pending apply attempted HTTP');return fetch(...args);};
  const server=await protocol(f.repo,env,ports);t.after(()=>server.close());
  const run=await server.call('tools/call',{name:'try_run',arguments:{story:originalPath,entry:PLACE+'#place_order',input:{sku:'exact-input',quantity:2}}});
  assert.equal(run.result.isError,undefined,JSON.stringify(run));const runId=run.result.structuredContent.run_id;
  if(savedCase){
    const payload={id:runId,name:'Generic observed case',story_path:doc.story_path,original_path:originalPath,test:{...doc,initial_world:before,steps:[{step_id:'observed',entry_path:PLACE,operation:'place_order',input:{sku:'exact-input',quantity:2},checks:[{criterion_id:doc.criteria[0].id,target:'result',path:'',op:'equals',value:observed}]}]}};
    savedCase(payload,doc);assert.match(client.saveDoorCase(f.repo,payload,{env,seedTest:{path:originalPath,storyPath:doc.story_path}}),/not added:.*pending/);
  }else{
    const saved=await server.call('tools/call',{name:'try_save_case',arguments:{story:originalPath,run_id:runId,criterion_id:doc.criteria[0].id,name:'Recorded MCP custody'}});
    assert.equal(saved.result.isError,true);assert.match(saved.result.content[0].text,/not added:.*pending/);
  }
  const folder=join(state,'case-import',fs.readdirSync(join(state,'case-import')).find(name=>/^[a-f0-9]{64}$/.test(name)));
  const receiptPath=join(folder,fs.readdirSync(folder).find(name=>name.endsWith('.received.json'))),receiptBytes=read(receiptPath),receipt=JSON.parse(receiptBytes);
  assert.equal(receipt.isolated,!savedCase);assert.equal(receipt.identity.session,null);assert.deepEqual(receipt.saved.test.initial_world,before);
  const repoPath=join(state,'repos',createHash('sha256').update(f.repo).digest('hex').slice(0,16)+'.json'),metaPath=join(state,'calls',runId+'.meta.json');
  external.blocked=true;const externalBefore={gh:external.gh,http:external.http};
  return{...f,state,env,doc,server,originalPath,original,receiptPath,receiptBytes,receipt,repoPath,metaPath,external,externalBefore,get callPosts(){return callPosts;}};
}

test('local native handoff applies immutable default-MCP receipt and preserves duplicate history after drift',async t=>{
  const f=await staged(t);assert.equal(typeof client.applyPendingCaseWithHandoff,'function');
  const result=await apply(f);assert.equal(result.kind,'case');assert.equal(result.result.state,'committed',result.message);
  assert.equal(read(join(f.repo,f.originalPath)),f.original);assert.equal(variantFiles(f).length,1);assert.equal(read(f.receiptPath),f.receiptBytes);
  const path=join(f.repo,result.result.path);assert.deepEqual(json(path),f.receipt.saved.test);
  fs.unlinkSync(path);fs.appendFileSync(join(f.repo,PLACE),'\nChanged after application.\n');fs.unlinkSync(f.metaPath);
  const duplicate=await apply(f);assert.equal(duplicate.result.state,'committed');assert.equal(duplicate.result.duplicate,true);
  assert.equal(fs.existsSync(path),false,'a later removal must not be restored');assert.equal(variantFiles(f).length,0);
  assert.equal(read(f.receiptPath),f.receiptBytes);assert.equal(f.callPosts,1);
});

test('local authority refuses missing, changed, foreign and ambiguous original bindings and incomplete pins',async t=>{
  const f=await staged(t);assert.equal(typeof client.applyPendingCaseWithHandoff,'function');
  const metaBytes=read(f.metaPath),repoBytes=read(f.repoPath),repo=json(f.repoPath),entry=repo.tries[f.originalPath];
  const variants={
    'wrong-call-id':()=>write(f.metaPath,{...JSON.parse(metaBytes),id:'11111111-1111-4111-8111-111111111111'}),
    'wrong-root':()=>write(f.metaPath,{...JSON.parse(metaBytes),root:f.sandbox}),
    'missing-call':()=>fs.unlinkSync(f.metaPath),
    'unknown-session':()=>write(f.metaPath,{...JSON.parse(metaBytes),session_id:'11111111-1111-4111-8111-111111111111'}),
    'ambiguous-session':()=>write(f.repoPath,{...repo,tries:{...repo.tries,'tests/other.json':entry}}),
    'wrong-original-test':()=>write(f.repoPath,{...repo,tries:{'tests/other.json':entry}}),
    'wrong-story':()=>write(f.repoPath,{...repo,tries:{[f.originalPath]:{...entry,storyPath:'user_stories/other.md'}}}),
    'missing-story-pin':()=>{const changed=structuredClone(repo);delete changed.tries[f.originalPath].story_sha256;write(f.repoPath,changed);},
    'missing-raw-pins':()=>{const changed=structuredClone(repo);delete changed.tries[f.originalPath].prompt_hashes;write(f.repoPath,changed);},
    'missing-effective-pins':()=>{const changed=structuredClone(repo);delete changed.tries[f.originalPath].effective_prompt_hashes;write(f.repoPath,changed);},
    'stale-effective-pin':()=>write(f.repoPath,{...repo,tries:{[f.originalPath]:{...entry,effective_prompt_hashes:{...entry.effective_prompt_hashes,[PLACE]:'0'.repeat(64)}}}})
  };
  for(const [name,change] of Object.entries(variants)){
    fs.writeFileSync(f.metaPath,metaBytes);fs.writeFileSync(f.repoPath,repoBytes);change();
    const result=await apply(f);assert.equal(result.kind,'case',name);assert.equal(result.result.state,'pending',name);assert.equal(result.result.pendingId,f.receipt.pendingId);
    assert.ok(result.message.includes(f.receiptPath),name);assert.equal(variantFiles(f).length,0,name);assert.equal(read(f.receiptPath),f.receiptBytes,name);
    const reply=await applyCall(f.server,argumentsFor(f));assert.equal(reply.result.isError,true,name);assert.ok(reply.result.content[0].text.includes(f.receiptPath),name);
  }
  fs.writeFileSync(f.metaPath,metaBytes);fs.writeFileSync(f.repoPath,repoBytes);
  const wrong=await apply(f,{handoff:{kind:'closed-editor',testPath:'tests/another.json'}});assert.equal(wrong.result.state,'pending');
  assert.equal(read(join(f.repo,f.originalPath)),f.original);assert.equal(f.callPosts,1);
});

test('local owner distinguishes unreadable/foreign receipts from genuinely retained refusal',async t=>{
  const f=await staged(t);assert.equal(typeof client.applyPendingCaseWithHandoff,'function');
  for(const value of ['{',JSON.stringify({...f.receipt,identity:{...f.receipt.identity,root:f.sandbox}})]){
    fs.writeFileSync(f.receiptPath,value);const result=await apply(f);assert.equal(result.kind,'failure');assert.equal(Object.hasOwn(result,'result'),false);assert.doesNotMatch(result.message,/Case retained|pending [a-f0-9]{64}\./);
    const reply=await applyCall(f.server,argumentsFor(f));assert.equal(reply.result.isError,true);assert.doesNotMatch(reply.result.content[0].text,/Case retained|pending [a-f0-9]{64}\./);
  }
  fs.writeFileSync(f.receiptPath,f.receiptBytes);const moved=f.receiptPath+'.moved';fs.renameSync(f.receiptPath,moved);fs.symlinkSync(moved,f.receiptPath);
  const unsafe=await apply(f);assert.equal(unsafe.kind,'failure');assert.equal((await applyCall(f.server,argumentsFor(f))).result.isError,true);fs.unlinkSync(f.receiptPath);fs.renameSync(moved,f.receiptPath);
  assert.equal(variantFiles(f).length,0);assert.equal(read(join(f.repo,f.originalPath)),f.original);
});

test('source is revalidated after real contention and an interrupted wait cannot publish later',async t=>{
  const f=await staged(t);assert.equal(typeof client.applyPendingCaseWithHandoff,'function');
  for(const cancel of [false,true]){
    const peer=await client.acquireCaseWriteOwnership({root:f.repo,testPath:f.originalPath,handoff:{kind:'closed-editor',testPath:f.originalPath}},{env:f.env});
    let waiting;const started=new Promise(resolve=>waiting=resolve),controller=new AbortController();
    const ports={...nativePorts(f),sleep:async(ms,signal)=>{waiting();if(!signal.aborted)await new Promise(resolve=>{const timer=setTimeout(resolve,ms);signal.addEventListener('abort',()=>{clearTimeout(timer);resolve();},{once:true});});}};
    const pending=client.applyPendingCaseWithHandoff({cwd:f.repo,pendingId:f.receipt.pendingId,handoff:{kind:'closed-editor',testPath:f.originalPath},signal:controller.signal},ports);
    await Promise.race([started,pending.then(value=>{throw Error('owner did not reach real contention: '+value.message);})]);const prompt=read(join(f.repo,PLACE));if(cancel)controller.abort();else fs.appendFileSync(join(f.repo,PLACE),'\nSource changed while waiting.\n');
    peer.release();const result=await pending;assert.equal(result.result.state,'pending',result.message);if(cancel)assert.match(result.message,/cancelled/);
    assert.equal(variantFiles(f).length,0);assert.equal(read(f.receiptPath),f.receiptBytes);fs.writeFileSync(join(f.repo,PLACE),prompt);
  }
});

const argumentsFor=f=>({pending_id:f.receipt.pendingId,closed_editor_for:f.originalPath});
const applyCall=(server,args,id)=>server.call('tools/call',{name:'try_save_case',arguments:args},id);
const until=async predicate=>{const end=Date.now()+10000;while(!predicate()){assert.ok(Date.now()<end,'native process/progress timeout');await delay(5);}};

test('default stdio apply validates paired inputs, publishes once and restarts without run memory or external access',async t=>{
  const f=await staged(t),args=argumentsFor(f),listed=await f.server.call('tools/list');
  const schema=listed.result.tools.find(tool=>tool.name==='try_save_case').inputSchema;
  assert.ok(schema.properties.pending_id,'NEW_ROUTE_GAP: default MCP must advertise pending identity application');assert.ok(schema.properties.closed_editor_for);assert.equal(schema.properties.pending_id.type,'string');assert.equal(schema.properties.closed_editor_for.type,'string');
  for(const bad of [{pending_id:args.pending_id},{closed_editor_for:args.closed_editor_for},{...args,pending_id:'bad'},{...args,closed_editor_for:true},...['story','run_id','name','criterion_id'].map(key=>({...args,[key]:'unexpected'}))]){
    const refusal=await applyCall(f.server,bad);assert.equal(refusal.result.isError,true);assert.equal(variantFiles(f).length,0);
  }
  const wrong=await applyCall(f.server,{...args,closed_editor_for:'tests/other.json'});assert.equal(wrong.result.isError,true);assert.ok(wrong.result.content[0].text.includes(f.receiptPath));
  const missing=await applyCall(f.server,{...args,pending_id:'0'.repeat(64)+'.'+'0'.repeat(64)});assert.equal(missing.result.isError,true);assert.doesNotMatch(missing.result.content[0].text,/Case retained/);
  const success=await applyCall(f.server,args,90);assert.equal(success.result.isError,undefined,JSON.stringify(success));
  assert.match(success.result.structuredContent.note,/references 1 of 3 retained scenario criteria/);assert.match(success.result.structuredContent.note,/Whole-Story coverage is unavailable/);
  assert.equal(variantFiles(f).length,1);const published=join(f.repo,'tests',variantFiles(f)[0]),publishedBytes=read(published);
  const replay=await applyCall(f.server,args,90);assert.deepEqual(replay,success);assert.equal(read(published),publishedBytes);
  const conflict=await applyCall(f.server,{...args,closed_editor_for:'tests/other.json'},90);assert.equal(conflict.error.code,-32600);
  await f.server.close();
  const restarted=await protocol(join(f.repo,'prompts'),f.env,nativePorts(f));t.after(()=>restarted.close());
  const duplicate=await applyCall(restarted,args);assert.equal(duplicate.result.isError,undefined,JSON.stringify(duplicate));assert.match(duplicate.result.structuredContent.result,/already saved/);
  assert.equal(read(published),publishedBytes);assert.equal(read(join(f.repo,f.originalPath)),f.original);assert.equal(read(f.receiptPath),f.receiptBytes);
  fs.unlinkSync(published);fs.appendFileSync(join(f.repo,'user_stories/place-order.md'),'\n4. A later criterion.\n');fs.unlinkSync(f.metaPath);
  const historical=await applyCall(restarted,args);assert.equal(historical.result.isError,undefined);assert.equal(historical.result.structuredContent.note,duplicate.result.structuredContent.note);
  assert.equal(variantFiles(f).length,0,'a historical duplicate must not restore a removed variant');
  assert.deepEqual({gh:f.external.gh,http:f.external.http},f.externalBefore);assert.equal(f.callPosts,1);
});

test('public retained identity application after restart has a real old-schema refusal control',async t=>{
  const f=await staged(t);await f.server.close();const restarted=await protocol(f.repo,f.env,nativePorts(f));t.after(()=>restarted.close());
  const reply=await applyCall(restarted,argumentsFor(f));
  assert.equal(reply.result.isError,undefined,'NEW_ROUTE_GAP: actual default stdio pending application was refused: '+JSON.stringify(reply));
  assert.equal(variantFiles(f).length,1);assert.equal(read(join(f.repo,f.originalPath)),f.original);assert.equal(read(f.receiptPath),f.receiptBytes);assert.equal(f.callPosts,1);
});

test('default stdio retains source drift after actual wait, times out safely and cleans subscriptions',async t=>{
  const f=await staged(t);await f.server.close();const server=await protocol(f.repo,f.env,{...nativePorts(f),progressMs:10});t.after(()=>server.close());
  const listeners=process.listenerCount('SIGINT'),promptPath=join(f.repo,PLACE),prompt=read(promptPath),repoBytes=read(f.repoPath),metaBytes=read(f.metaPath);
  for(const drift of ['source','pins','association','timeout']){
    const peer=await client.acquireCaseWriteOwnership({root:f.repo,testPath:f.originalPath,handoff:{kind:'closed-editor',testPath:f.originalPath}},{env:f.env});
    const prior=server.errors.length,started=Date.now(),pending=applyCall(server,argumentsFor(f));
    await until(()=>server.errors.slice(prior).includes('still working'));
    if(drift!=='timeout'){
      if(drift==='association')write(f.metaPath,{...JSON.parse(metaBytes),session_id:'11111111-1111-4111-8111-111111111111'});
      else{fs.appendFileSync(promptPath,'\nChanged during custody wait.\n');if(drift==='pins'){const repo=JSON.parse(repoBytes),hash=createHash('sha256').update(read(promptPath)).digest('hex');repo.tries[f.originalPath].prompt_hashes[PLACE]=hash;repo.tries[f.originalPath].effective_prompt_hashes[PLACE]=hash;write(f.repoPath,repo);}}
      peer.release();
    }
    const reply=await pending;peer.release();assert.equal(reply.result.isError,true);assert.ok(reply.result.content[0].text.includes(f.receiptPath));
    if(drift==='timeout'){assert.match(reply.result.content[0].text,/another saver or editor/);assert.ok(Date.now()-started<5000,'ownership wait must remain bounded');}
    assert.equal(variantFiles(f).length,0);assert.equal(read(f.receiptPath),f.receiptBytes);fs.writeFileSync(promptPath,prompt);fs.writeFileSync(f.repoPath,repoBytes);fs.writeFileSync(f.metaPath,metaBytes);
    assert.equal(process.listenerCount('SIGINT'),listeners,'local operation must remove only its own signal subscription');
  }
  await delay(40);assert.equal(variantFiles(f).length,0);assert.equal(read(join(f.repo,f.originalPath)),f.original);
});

function childMcp(f,{crash=false}={}){
  const code=`const {runMcp}=await import(process.argv[1]);let gh=0,http=0;const before=process.listenerCount('SIGINT');const ports={progressMs:10,gh(){gh++;throw Error('AUTH_FORBIDDEN');},fetch(){http++;throw Error('HTTP_FORBIDDEN');},${crash?"fault(stage){if(stage==='published'){process.stderr.write('CRASH_PUBLISHED\\n');Atomics.wait(new Int32Array(new SharedArrayBuffer(4)),0,0);}},":''}};const exit=await runMcp({cwd:process.argv[2],env:process.env},ports);process.stderr.write('LOCAL_DIAGNOSTIC '+JSON.stringify({gh,http,before,after:process.listenerCount('SIGINT')})+'\\n');process.exitCode=exit;`;
  const child=spawn(process.execPath,['--input-type=module','-e',code,new URL('../src/try-mcp.mjs',import.meta.url).href,f.repo],{env:f.env,stdio:['pipe','pipe','pipe']});let output='',errors='';child.stdout.on('data',data=>output+=data);child.stderr.on('data',data=>errors+=data);
  const done=new Promise((resolve,reject)=>{child.once('error',reject);child.once('exit',(code,signal)=>resolve({code,signal}));});
  return{child,done,send(){child.stdin.write(JSON.stringify({jsonrpc:'2.0',id:1,method:'tools/call',params:{name:'try_save_case',arguments:argumentsFor(f)}})+'\n');},get output(){return output;},get errors(){return errors;}};
}

test('actual SIGINT interrupts default child MCP apply without later publication, auth or HTTP',async t=>{
  const f=await staged(t);await f.server.close();
  const peer=await client.acquireCaseWriteOwnership({root:f.repo,testPath:f.originalPath,handoff:{kind:'closed-editor',testPath:f.originalPath}},{env:f.env});
  const worker=childMcp(f);t.after(()=>{worker.child.kill('SIGKILL');peer.release();});worker.send();
  await until(()=>worker.errors.includes('still working'));worker.child.kill('SIGINT');
  await until(()=>worker.output.includes('"id":1'));worker.child.stdin.end();assert.deepEqual(await worker.done,{code:0,signal:null});peer.release();
  const reply=JSON.parse(worker.output.trim());assert.equal(reply.result.isError,true);assert.match(reply.result.content[0].text,/cancelled/);assert.ok(reply.result.content[0].text.includes(f.receiptPath));
  const diagnostic=JSON.parse(worker.errors.split('\n').find(line=>line.startsWith('LOCAL_DIAGNOSTIC ')).slice(17));
  assert.equal(diagnostic.gh,0);assert.equal(diagnostic.http,0);assert.equal(diagnostic.after,diagnostic.before);
  await delay(40);assert.equal(variantFiles(f).length,0);assert.equal(read(f.receiptPath),f.receiptBytes);assert.equal(read(join(f.repo,f.originalPath)),f.original);
});

test('retained coverage counts unique members, scopes generic append and never gates its historical result',async t=>{
  for(const duplicateIds of [false,true]){
    const f=await staged(t,{savedCase(payload,doc){
      payload.test.criteria=duplicateIds?[{id:'same',text:doc.criteria[0].text},{id:'same',text:doc.criteria[0].text}]:[{id:'left',text:doc.criteria[0].text},{id:'right',text:doc.criteria[0].text}];
      const first=payload.test.steps[0].checks[0];payload.test.steps[0].checks=[{...first,criterion_id:duplicateIds?'same':'left'},{...first,criterion_id:duplicateIds?'same':'right'},{...first,criterion_id:duplicateIds?'same':'left'}];
    }});
    const reply=await applyCall(f.server,argumentsFor(f));assert.equal(reply.result.isError,undefined,JSON.stringify(reply));
    const native=await apply(f);assert.equal(native.result.state,'committed');assert.equal(native.result.duplicate,true);
    assert.deepEqual(native.coverage,duplicateIds?{scope:'unavailable',covered:null,total:null}:{scope:'retained-scenario',covered:2,total:2});
    assert.match(reply.result.structuredContent.note,duplicateIds?/criterion coverage is unavailable/:/references 2 of 2 retained scenario criteria/);
    const actual=json(join(f.repo,f.originalPath));assert.ok(actual.steps.at(-1).checks.every(check=>check.criterion_id===f.doc.criteria[0].id),'append maps by text; retained IDs must not be claimed as two original criteria');
    const bytes=read(join(f.repo,f.originalPath));fs.unlinkSync(f.metaPath);const historical=await applyCall(f.server,argumentsFor(f));assert.equal(historical.result.isError,undefined);assert.equal(historical.result.structuredContent.note,reply.result.structuredContent.note);assert.equal(read(join(f.repo,f.originalPath)),bytes);
  }
});

test('unknown/missing retained mapping has null coverage, and payload conflict takes precedence over a prior commit',async t=>{
  for(const missing of [false,true]){
    const f=await staged(t,{savedCase(payload){if(missing)delete payload.test.steps[0].checks;else payload.test.steps[0].checks[0].criterion_id='not-a-member';}});
    const result=await apply(f);assert.equal(result.result.state,'pending');assert.deepEqual(result.coverage,{scope:'unavailable',covered:null,total:null});
    const reply=await applyCall(f.server,argumentsFor(f));assert.equal(reply.result.isError,true);assert.equal(read(join(f.repo,f.originalPath)),f.original);
  }
  const f=await staged(t),committed=await applyCall(f.server,argumentsFor(f));assert.equal(committed.result.isError,undefined);const paths=variantFiles(f),bytes=read(join(f.repo,'tests',paths[0]));
  const different=structuredClone(f.receipt.saved);different.name='Different payload, same action';assert.match(client.saveDoorCase(f.repo,different,{env:f.env,isolated:true}),/not added:/);
  fs.unlinkSync(f.metaPath);const conflict=await applyCall(f.server,argumentsFor(f));assert.equal(conflict.result.isError,true);assert.match(conflict.result.content[0].text,/different received payloads/);
  assert.equal(read(join(f.repo,'tests',paths[0])),bytes);assert.equal(read(f.receiptPath),f.receiptBytes);
});

test('retained native original association authorizes the exact target without a payload-supplied path',async t=>{
  const f=await staged(t,{savedCase(payload){delete payload.original_path;}});
  const reply=await applyCall(f.server,argumentsFor(f));assert.equal(reply.result.isError,undefined,JSON.stringify(reply));
  assert.equal(f.receipt.saved.original_path,undefined);assert.equal(f.receipt.identity.original.path,f.originalPath);
  assert.equal(json(join(f.repo,f.originalPath)).steps.at(-1).step_id,'observed');assert.equal(read(f.receiptPath),f.receiptBytes);
});

test('actual referenced prompt requires the complete original reference baseline without fallback',async t=>{
  const f=await staged(t,{references:true}),repoBytes=read(f.repoPath),original=JSON.parse(repoBytes).tries[f.originalPath].contract_references;
  assert.ok(original.length>0,'fixture must really capture contract references');
  for(const baseline of [undefined,[],original.slice(1),original.map(ref=>({...ref,target:'contracts/other.json#'}))]){
    const repo=JSON.parse(repoBytes);if(baseline===undefined)delete repo.tries[f.originalPath].contract_references;else repo.tries[f.originalPath].contract_references=baseline;write(f.repoPath,repo);
    const refusal=await applyCall(f.server,argumentsFor(f));assert.equal(refusal.result.isError,true);assert.match(refusal.result.content[0].text,/reference baseline/);assert.equal(variantFiles(f).length,0);assert.equal(read(f.receiptPath),f.receiptBytes);
  }
  fs.writeFileSync(f.repoPath,repoBytes);const applied=await applyCall(f.server,argumentsFor(f));assert.equal(applied.result.isError,undefined,JSON.stringify(applied));assert.equal(variantFiles(f).length,1);
  assert.deepEqual({gh:f.external.gh,http:f.external.http},f.externalBefore);
});

test('actual crash after publication reconciles ledger only or holds a removed variant without restoration',async t=>{
  for(const removed of [false,true]){
    const f=await staged(t);await f.server.close();const worker=childMcp(f,{crash:true});t.after(()=>worker.child.kill('SIGKILL'));worker.send();
    await until(()=>worker.errors.includes('CRASH_PUBLISHED'));worker.child.kill('SIGKILL');assert.equal((await worker.done).signal,'SIGKILL');
    const journal=f.receiptPath.replace('.received.json','.transaction.json');assert.equal(json(journal).state,'publishing');
    const path=join(f.repo,'tests',variantFiles(f)[0]),bytes=read(path),stat=fs.statSync(path),prompt=read(join(f.repo,PLACE));
    if(removed)fs.unlinkSync(path);fs.appendFileSync(join(f.repo,PLACE),'\nLater source change.\n');
    const server=await protocol(f.repo,f.env,nativePorts(f));t.after(()=>server.close());const reply=await applyCall(server,argumentsFor(f));
    if(removed){assert.equal(reply.result.isError,true);assert.equal(fs.existsSync(path),false);fs.writeFileSync(join(f.repo,PLACE),prompt);const again=await applyCall(server,argumentsFor(f));assert.equal(again.result.isError,true);assert.equal(fs.existsSync(path),false,'uncertain publication may not restore a deliberately removed variant');}
    else{assert.equal(reply.result.isError,undefined,JSON.stringify(reply));assert.equal(json(journal).state,'committed');assert.equal(read(path),bytes);assert.equal(fs.statSync(path).ino,stat.ino);assert.equal(fs.statSync(path).mtimeMs,stat.mtimeMs);}
    assert.equal(read(f.receiptPath),f.receiptBytes);assert.equal(read(join(f.repo,f.originalPath)),f.original);assert.equal(f.callPosts,1);
  }
});

test('repair: interrupted publication conflict survives removal and MCP restart without restoration',async t=>{
  const f=await staged(t);await f.server.close();const worker=childMcp(f,{crash:true});t.after(()=>worker.child.kill('SIGKILL'));worker.send();
  await until(()=>worker.errors.includes('CRASH_PUBLISHED'));worker.child.kill('SIGKILL');assert.equal((await worker.done).signal,'SIGKILL');
  const journal=f.receiptPath.replace('.received.json','.transaction.json');assert.equal(json(journal).state,'publishing');
  const path=join(f.repo,'tests',variantFiles(f)[0]),published=read(path),edited={...JSON.parse(published),personEdit:'retain this authored revision'};write(path,edited);const editedBytes=read(path);
  const first=await protocol(f.repo,f.env,nativePorts(f));const conflict=await applyCall(first,argumentsFor(f));await first.close();
  assert.equal(conflict.result.isError,true);assert.match(conflict.result.content[0].text,/authored revision changed/);
  assert.equal(json(journal).state,'conflict');assert.ok(json(journal).observed.includes(editedBytes));assert.equal(read(path),editedBytes);const conflictBytes=read(journal);
  fs.unlinkSync(path);
  const restarted=await protocol(f.repo,f.env,nativePorts(f));t.after(()=>restarted.close());
  for(let attempt=0;attempt<2;attempt++){
    const reply=await applyCall(restarted,argumentsFor(f));assert.equal(reply.result.isError,true,'UNCERTAIN_CONFLICT_MUST_NOT_RESTORE: retry must retain the conflict');
    assert.equal(fs.existsSync(path),false,'UNCERTAIN_CONFLICT_MUST_NOT_RESTORE: removed variant must stay absent');assert.equal(read(journal),conflictBytes);
    const local=await apply(f);assert.equal(local.result.state,'conflict');assert.equal(local.result.pendingId,f.receipt.pendingId);
    if(attempt===0){fs.unlinkSync(f.metaPath);fs.appendFileSync(join(f.repo,PLACE),'\nSource changed after interrupted publication.\n');}
  }
  assert.equal(read(f.receiptPath),f.receiptBytes);assert.equal(read(join(f.repo,f.originalPath)),f.original);assert.equal(f.callPosts,1);
  assert.deepEqual({gh:f.external.gh,http:f.external.http},f.externalBefore);
});

test('repair: genuinely prepublication conflict can recover after the conflicting variant is removed',async t=>{
  const f=await staged(t);await f.server.close();const path=join(f.repo,'tests',`place-order.try-${f.receipt.saved.id}.json`),foreign='{"person":"prepublication revision"}\n';
  const first=await protocol(f.repo,f.env,{...nativePorts(f),fault(stage){if(stage==='before-publication')fs.writeFileSync(path,foreign);}});
  const conflict=await applyCall(first,argumentsFor(f));await first.close();assert.equal(conflict.result.isError,true);assert.equal(read(path),foreign);
  const journal=f.receiptPath.replace('.received.json','.transaction.json');assert.equal(json(journal).state,'conflict');assert.ok(json(journal).observed.includes(foreign));
  fs.unlinkSync(path);const restarted=await protocol(f.repo,f.env,nativePorts(f));t.after(()=>restarted.close());
  const recovered=await applyCall(restarted,argumentsFor(f));assert.equal(recovered.result.isError,undefined,JSON.stringify(recovered));assert.equal(json(journal).state,'committed');
  assert.deepEqual(json(path),f.receipt.saved.test);assert.equal(read(join(f.repo,f.originalPath)),f.original);assert.equal(read(f.receiptPath),f.receiptBytes);
  const duplicate=await apply(f);assert.equal(duplicate.result.duplicate,true);assert.equal(f.callPosts,1);assert.deepEqual({gh:f.external.gh,http:f.external.http},f.externalBefore);
});

test('repair: complete original capture pins include transitive, root and original test context prompts',async t=>{
  for(const selection of ['transitive','root-include','context-prompt','context-path','original-context']){
    const required='prompts/required-context.prompt.md',bridge='prompts/bridge.prompt.md';
    const f=await staged(t,{savedCase:selection==='original-context'?()=>{}:undefined,sourceSetup(root){
      fs.writeFileSync(join(root,required),'# Required context\n\nOriginal required rule.\n\n## Dependencies\n\nNone.\n');
      if(['transitive','root-include'].includes(selection)){
        fs.writeFileSync(join(root,bridge),'# Bridge\n\n## Dependencies\n\n[Required context](required-context.prompt.md)\n');
        if(selection==='root-include')write(join(root,'pdd-source.json'),{include:[bridge]});
        else{const path=join(root,PLACE);let text=read(path).replace('## Dependencies\n\nNone.','## Dependencies\n\n[Bridge](bridge.prompt.md)');text=text.replace(/("prose_sha256":\s*")[a-f0-9]+(")/,'$1'+proseSha256(text)+'$2');fs.writeFileSync(path,text);}
      }else{const path=join(root,'tests/place-order.json'),doc=json(path);doc.context=selection==='context-prompt'?[{prompt_path:required,paths:[]}]:[{prompt_path:PLACE,paths:[required]}];write(path,doc);}
    }});
    const repoBytes=read(f.repoPath),repo=JSON.parse(repoBytes),entry=repo.tries[f.originalPath],requiredPath=join(f.repo,required),requiredBytes=read(requiredPath);
    assert.ok(entry.prompt_hashes[required]&&entry.effective_prompt_hashes[required],selection+' must start with an actual complete capture');
    if(selection==='original-context'){const doc=json(join(f.repo,f.originalPath));doc.context=[];write(join(f.repo,f.originalPath),doc);}
    const authoredBefore=read(join(f.repo,f.originalPath));
    delete entry.prompt_hashes[required];delete entry.effective_prompt_hashes[required];write(f.repoPath,repo);fs.appendFileSync(requiredPath,'\nRequired context changed after capture.\n');
    const native=await apply(f);assert.equal(native.result.state,'pending','COMPLETE_ORIGINAL_PIN_SET_REQUIRED: '+selection);assert.equal(native.result.pendingId,f.receipt.pendingId);
    const refusal=await applyCall(f.server,argumentsFor(f));assert.equal(refusal.result.isError,true,selection);assert.ok(refusal.result.content[0].text.includes(f.receiptPath));
    assert.equal(variantFiles(f).length,0);assert.equal(read(join(f.repo,f.originalPath)),authoredBefore);assert.equal(read(f.receiptPath),f.receiptBytes);
    fs.writeFileSync(f.repoPath,repoBytes);fs.writeFileSync(requiredPath,requiredBytes);fs.writeFileSync(join(f.repo,f.originalPath),f.original);
    const missingSeed=JSON.parse(repoBytes);delete missingSeed.tries[f.originalPath].seed_scenario;write(f.repoPath,missingSeed);
    assert.equal((await apply(f)).result.state,'pending','missing original selection context must stay held');assert.equal(variantFiles(f).length,0);fs.writeFileSync(f.repoPath,repoBytes);
    const valid=await applyCall(f.server,argumentsFor(f));assert.equal(valid.result.isError,undefined,'complete original pins must still apply: '+JSON.stringify(valid));
    if(selection==='original-context')assert.equal(json(join(f.repo,f.originalPath)).steps.at(-1).step_id,'observed');else assert.equal(variantFiles(f).length,1);
    assert.equal(read(f.receiptPath),f.receiptBytes);assert.equal(f.callPosts,1);assert.deepEqual({gh:f.external.gh,http:f.external.http},f.externalBefore);await f.server.close();
  }
});
