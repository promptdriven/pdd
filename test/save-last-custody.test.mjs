import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {join,relative} from 'node:path';
import {createHash} from 'node:crypto';
import {Readable} from 'node:stream';
import {spawnSync} from 'node:child_process';
import {fixture,closed,json,read,get,stream} from './helpers/runtime-workspace-fixture.mjs';
import {proseSha256} from '../src/runtime-preflight.mjs';
import {runShim} from '../src/try-doors.mjs';
import * as client from '../src/runtime-client.mjs';

const hash=text=>createHash('sha256').update(text).digest('hex');
const receipts=f=>{
  const area=join(f.state,'case-import');if(!fs.existsSync(area))return [];
  return fs.readdirSync(area,{withFileTypes:true}).filter(e=>e.isDirectory()).flatMap(e=>fs.readdirSync(join(area,e.name)).filter(name=>name.endsWith('.received.json')).map(name=>{
    const path=join(area,e.name,name),text=fs.readFileSync(path,'utf8');return{path,text,record:JSON.parse(text)};
  }));
};

// Native saved-session files and the production runShim/runTry boundaries, with
// controlled owner HTTP replies. This proves local custody, not a hosted call.
async function recorded(t){
  const f=fixture(t),inputSchema={type:'object',properties:{argv:{type:'array',items:{type:'string'}},stdin:{type:'string'}},required:['argv'],additionalProperties:false};
  const resultSchema={type:'object',properties:{stdout:{type:'string'},stderr:{type:'string'},exit_code:{type:'integer'}},required:['stdout','stderr','exit_code'],additionalProperties:false};
  const iface={status:'draft',prose_sha256:'',entries:[{operation:'main',input_schema:inputSchema,result_schema:resultSchema,errors:[]}],calls:[],resources:[],limits:{max_steps:1,max_model_calls:1},conventions:['input_schema','result_schema'].map(key=>({path:'/entries/0/'+key,convention:'cli'}))};
  const content=()=>`# custodycmd\n\nEcho arguments and stdin.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\x60\x60\x60json\n${JSON.stringify(iface)}\n\x60\x60\x60\n</details>\n`;
  iface.prose_sha256=proseSha256(content());fs.writeFileSync(join(f.root,f.prompt),content());
  const beforeWorld={count:7,nested:{tag:'A-original-world',items:[1,2]}},afterWorld={count:8,nested:{tag:'A-after-world',items:[1,2,3]}};
  const doc={...f.doc,initial_world:beforeWorld,steps:[{...f.doc.steps[0],operation:'main',input:{argv:['initial']},checks:[{criterion_id:'AC1',target:'result',path:'',op:'equals',value:{stdout:'initial\n',stderr:'',exit_code:0}},{criterion_id:'AC1',target:'world',path:'',op:'equals',value:beforeWorld}]}]};
  json(f.root,f.second,doc);json(f.root,f.test,doc);
  const session='11111111-1111-4111-8111-111111111111',ids=['aaaaaaaa-aaaa-4aaa-8aaa-aaaaaaaaaaaa','bbbbbbbb-bbbb-4bbb-8bbb-bbbbbbbbbbbb'];
  const descriptor=join(f.state,'tries',session+'.door.json'),last=join(f.state,'tries',session+'.last.json'),repoState=join(f.state,'repos',hash(f.root).slice(0,16)+'.json');
  const d={version:1,root:f.root,sessionId:session,origin:'https://synthetic.example.invalid',login:'owner',prompt:f.prompt,operation:'main',originalPath:f.second,storyPath:f.story,criteria:doc.criteria,criterion:'AC1',promptHash:hash(read(f.root,f.prompt)),promptHashes:{[f.prompt]:hash(read(f.root,f.prompt))},effectivePromptHashes:{[f.prompt]:hash(read(f.root,f.prompt))},storyHash:hash(read(f.root,f.story)),stateDir:f.state,repoState,name:'custodycmd',inputSchema};
  json(f.state,relative(f.state,descriptor),d);json(f.state,relative(f.state,repoState),{root:f.root,last_batch:null,tries:{}});
  const input={argv:['A-unique-input','two words'],stdin:'A-private-stdin\n'},result={stdout:'A unique observed output\n',stderr:'A stderr\n',exit_code:0};
  let seq=0;const replies=new Map(),requests=[];
  const ports=()=>({env:f.env,gh:args=>({status:0,stdout:args[0]==='auth'?'SYNTHETIC-NOT-A-CREDENTIAL':'owner 1'}),stdout:stream(),stderr:stream(),interactive:false,agentBridge:false,stdin:Readable.from([]),randomUUID:()=>ids[seq++],fetch:async(url,init)=>{
    const path=new URL(url).pathname;requests.push({path,method:init.method});
    if(init.method==='POST'){
      const request=JSON.parse(init.body),a=request.requestId===ids[0];
      assert.deepEqual(request.input,a?input:{argv:['B-later-independent'],stdin:'B-stdin\n'});
      const answer={requestId:request.requestId,id:request.requestId,command:'call',state:'passed',session_id:session,result:{program_result:a?result:{stdout:'B later output\n',stderr:'',exit_code:0},report:{input_world:a?beforeWorld:{count:20},world:a?afterWorld:{count:21}}}};
      replies.set(request.requestId,answer);return new Response(JSON.stringify(answer),{status:200});
    }
    const answer=replies.get(path.split('/').at(-1));assert.ok(answer,'only the controlled owner GET is allowed');return new Response(JSON.stringify(answer),{status:200});
  }});
  const io=ports();io.stdin=Readable.from([input.stdin]);assert.equal(await runShim(descriptor,input.argv,io),0,io.stderr.text);
  assert.equal(io.stdout.text,result.stdout);assert.ok(io.stderr.text.startsWith(result.stderr));
  assert.deepEqual(JSON.parse(fs.readFileSync(last)),{state:'confirmed',id:ids[0],input,result,inputWorld:beforeWorld,world:afterWorld});
  const saved={id:ids[0],name:'Recorded terminal command',story_path:f.story,original_path:f.second,test:{schema_version:'prompt-runtime.program-scenario.v1',story_path:f.story,criteria:doc.criteria,initial_world:beforeWorld,steps:[{step_id:'try-'+ids[0],entry_path:f.prompt,operation:'main',input,checks:[{criterion_id:'AC1',target:'result',path:'',op:'equals',value:result}]}]}};
  return{...f,doc,descriptor,last,ids,ports,requests,saved,beforeWorld,afterWorld,result};
}

for(const mode of ['timeout','cancel']){
  test(`save-last ${mode} retains A before waiting, survives B and recovers A independently`,{timeout:15000},async t=>{
    const f=await recorded(t),original=read(f.root,f.second),sibling=read(f.root,f.test);
    const answerPath=join(f.state,'tries',f.ids[0]+'.json'),answerBytes=fs.readFileSync(answerPath,'utf8');
    const peer=await client.acquireCaseWriteOwnership({root:f.root,testPath:f.second,handoff:closed(f.second)},{env:f.env});
    const controller=new AbortController(),save=f.ports();let stagedBeforeHandoff=[];
    save.signal=controller.signal;save.caseHandoff=async({testPath})=>{stagedBeforeHandoff=receipts(f);if(mode==='cancel')setTimeout(()=>controller.abort(),60);return closed(testPath);};
    try{assert.equal(await client.runTry({cwd:f.root,options:{'--save-last':true}},save),125,save.stderr.text);}finally{peer.release();}
    assert.match(save.stderr.text,mode==='cancel'?/cancelled/:/another saver or editor/);
    assert.doesNotMatch(save.stdout.text,/added to|already saved/);
    assert.equal(JSON.parse(fs.readFileSync(f.last)).saved,undefined);
    const later=f.ports();later.stdin=Readable.from(['B-stdin\n']);assert.equal(await runShim(f.descriptor,['B-later-independent'],later),0,later.stderr.text);
    const lastB=fs.readFileSync(f.last,'utf8');assert.equal(JSON.parse(lastB).id,f.ids[1]);
    const retained=receipts(f);assert.equal(retained.length,1,'MISSING_DURABLE_CUSTODY: A must survive replacement of last.json by B');
    assert.equal(stagedBeforeHandoff.length,1,'A must be durably retained before even the editor handoff can wait');
    const receipt=retained[0];assert.deepEqual(receipt.record.saved,f.saved,'the existing recorded-case payload must not drift');
    assert.equal(receipt.record.raw,JSON.stringify(f.saved));assert.equal(receipt.record.identity.action,f.ids[0]);
    assert.deepEqual(receipt.record.identity.original,{path:f.second,storyPath:f.story});assert.equal(receipt.record.identity.root,f.root);
    assert.ok(save.stderr.text.includes(receipt.path),'timeout/cancel must identify the actual retained recovery location');
    assert.equal(read(f.root,f.second),original);assert.equal(read(f.root,f.test),sibling);
    assert.equal(fs.readFileSync(answerPath,'utf8'),answerBytes,'the stable A receipt must retain its observed worlds/output');
    const answer=JSON.parse(answerBytes);assert.deepEqual(answer.result.report,{input_world:f.beforeWorld,world:f.afterWorld});assert.deepEqual(answer.result.program_result,f.result);
    // Recover by pending identity in fresh processes. The current last command is B.
    const code=`const c=await import(process.argv[1]),f=JSON.parse(process.argv[2]);const lease=await c.acquireCaseWriteOwnership({root:f.root,testPath:f.path,handoff:{kind:'closed-editor',testPath:f.path}},{env:process.env});try{console.log(JSON.stringify(await c.applyPendingCase({root:f.root,pendingId:f.id,writeOwnership:lease},{env:process.env})));}finally{lease.release();}`;
    for(const duplicate of [false,true]){
      const recovery=spawnSync(process.execPath,['--input-type=module','-e',code,new URL('../src/runtime-client.mjs',import.meta.url).href,JSON.stringify({root:f.root,path:f.second,id:receipt.record.pendingId})],{env:f.env,encoding:'utf8'});
      assert.equal(recovery.status,0,recovery.stderr);const applied=JSON.parse(recovery.stdout);assert.equal(applied.state,'committed');assert.equal(applied.duplicate===true,duplicate);
    }
    const actual=get(f.root,f.second);assert.equal(actual.steps.length,2);assert.deepEqual(actual.steps[0],f.doc.steps[0]);assert.deepEqual(actual.steps[1],f.saved.test.steps[0]);
    assert.equal(read(f.root,f.test),sibling);assert.equal(fs.readFileSync(f.last,'utf8'),lastB);
    assert.equal(fs.readFileSync(receipt.path,'utf8'),receipt.text);assert.equal(fs.readFileSync(answerPath,'utf8'),answerBytes);
    assert.equal(f.requests.filter(r=>r.method==='POST').length,2,'saving/recovering must not redispatch either command');
  });
}

test('receipt failure returns a synchronous typed failure and save-last never waits or claims pending',async t=>{
  const f=await recorded(t),original=read(f.root,f.second),outside=join(f.parent,'unsafe-state');fs.mkdirSync(outside);
  fs.symlinkSync(outside,join(f.state,'case-import'));
  assert.equal(typeof client.saveDoorCaseResult,'function');
  const failure=client.saveDoorCaseResult(f.root,f.saved,{env:f.env});
  assert.equal(failure.kind,'failure');assert.deepEqual(Object.keys(failure).sort(),['kind','message']);
  assert.equal(client.saveDoorCase(f.root,f.saved,{env:f.env}),failure.message);
  const save=f.ports();let handoffs=0;save.caseHandoff=async()=>{handoffs++;return closed(f.second);};
  assert.equal(await client.runTry({cwd:f.root,options:{'--save-last':true}},save),125);
  assert.equal(handoffs,0,'failed durable receipt must stop before editor handoff or ownership waiting');
  assert.doesNotMatch(save.stdout.text,/added to|already saved/);assert.doesNotMatch(save.stderr.text,/keep pending|Case retained|pending [a-f0-9]/);
  assert.equal(JSON.parse(fs.readFileSync(f.last)).saved,undefined);assert.equal(read(f.root,f.second),original);assert.deepEqual(fs.readdirSync(outside),[]);
});

test('typed case outcomes preserve the existing printable pending, committed, duplicate and conflict results',async t=>{
  const f=fixture(t),saved=f.saved();assert.equal(typeof client.saveDoorCaseResult,'function');
  const pending=client.saveDoorCaseResult(f.root,saved,{env:f.env});assert.equal(pending.kind,'case');assert.equal(pending.result.state,'pending');
  assert.equal(client.saveDoorCase(f.root,saved,{env:f.env}),pending.message);
  const lease=await client.acquireCaseWriteOwnership({root:f.root,testPath:f.second,handoff:closed(f.second)},{env:f.env});
  try{const applied=client.saveDoorCaseResult(f.root,saved,{env:f.env,writeOwnership:lease});assert.equal(applied.result.state,'committed');assert.equal(applied.kind,'case');assert.equal(applied.result.duplicate,undefined);}finally{lease.release();}
  const duplicate=client.saveDoorCaseResult(f.root,saved,{env:f.env});assert.equal(duplicate.result.state,'committed');assert.equal(duplicate.result.duplicate,true);
  assert.equal(client.saveDoorCase(f.root,saved,{env:f.env}),duplicate.message);
  const changed=structuredClone(saved);changed.test.steps[0].checks[0].value=99;
  const conflict=client.saveDoorCaseResult(f.root,changed,{env:f.env});assert.equal(conflict.kind,'case');assert.equal(conflict.result.state,'conflict');
  assert.equal(client.saveDoorCase(f.root,changed,{env:f.env}),conflict.message);
});
