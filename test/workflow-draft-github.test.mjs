import test from 'node:test';
import assert from 'node:assert/strict';
import {prepareWorkflowPr,publishWorkflowPr,reconcileWorkflowPr} from '../src/workflow-github.mjs';

const cwd='/synthetic/project',sha='a'.repeat(40);
function world() {
  const f={calls:[],rows:[],remote:null,createCode:0,readback:true};
  f.row=extra=>({number:42,url:'https://github.com/example/project/pull/42',state:'OPEN',headRefName:'topic/draft',baseRefName:'main',headRefOid:sha,mergeCommit:null,
    body:'Original\n<!-- pdd-workflow:draft-run:prompt-pr -->\n',isCrossRepository:false,headRepository:{name:'project'},headRepositoryOwner:{login:'example'},isDraft:true,...extra});
  f.input={cwd,runId:'draft-run',stageId:'prompt-pr',repository:'example/project',baseBranch:'main'};
  f.ports={async execFile(file,args,options){
    f.calls.push({file,args:[...args],input:options.input});
    if(f.intercept){const value=await f.intercept(file,args,options);if(value!==undefined)return value;}
    const key=[file,...args].join(' ');let stdout='';
    if(key==='git remote get-url origin'||key==='git remote get-url --push --all origin')stdout='https://github.com/example/project.git';
    else if(file==='gh'&&args[0]==='repo')stdout=JSON.stringify({nameWithOwner:'example/project',defaultBranchRef:{name:'main'},url:'https://github.com/example/project'});
    else if(file==='git'&&args[0]==='check-ref-format')stdout='';
    else if(key==='git rev-parse --show-toplevel')stdout=cwd;
    else if(file==='git'&&args[0]==='status')stdout='';
    else if(file==='git'&&args[0]==='symbolic-ref')stdout='topic/draft';
    else if(file==='git'&&args[0]==='rev-parse')stdout=sha;
    else if(file==='git'&&args[0]==='rev-list')stdout='1';
    else if(file==='git'&&args[0]==='log')stdout='Synthetic draft';
    else if(file==='gh'&&args[1]==='list')stdout=JSON.stringify(f.rows);
    else if(file==='git'&&args[0]==='ls-remote')return f.remote===null?{stdout:'',code:2}:{stdout:`${f.remote}\trefs/heads/topic/draft\n`};
    else if(file==='git'&&args[0]==='push'){f.remote=sha;stdout='';}
    else if(file==='gh'&&args[1]==='create'){
      if(f.readback!=='absent')f.rows=[f.row({body:options.input,isDraft:f.readback})];
      return {stdout:'https://github.com/example/project/pull/42',code:f.createCode,stderr:f.createError??''};
    }else assert.fail(`Unexpected port ${key}`);
    return {stdout};
  }};
  f.effects=()=>f.calls.filter(c=>c.file==='git'&&c.args[0]==='push'||c.file==='gh'&&['create','edit','ready'].includes(c.args[1]));
  f.prepare=()=>prepareWorkflowPr(f.input,f.ports);
  f.publish=(intent,extra={})=>publishWorkflowPr({cwd,intent,body:`Synthetic\n<!-- ${intent.marker} -->\n`,draft:true,...extra},f.ports);
  f.reconcile=(intent,extra={})=>reconcileWorkflowPr({cwd,intent,draft:true,...extra},f.ports);
  return f;
}
for(const value of [null,0,1,'','true',{}])test(`L1: helper nonboolean draft ${JSON.stringify(value)} refuses before commands`,async()=>{
  const f=world(),intent=await f.prepare();f.calls=[];
  assert.equal((await f.publish(intent,{draft:value})).state,'failed');assert.deepEqual(f.calls,[]);
  assert.equal((await f.reconcile(intent,{draft:value})).state,'recovery_required');assert.deepEqual(f.calls,[]);
});
for(const observation of [true,false,undefined,null,'true',1])test(`L3/N8: exact existing PR draft observation ${String(observation)}`,async()=>{
  const f=world(),intent=await f.prepare();f.calls=[];
  f.rows=[f.row({isDraft:observation})];
  for(const action of [f.publish,f.reconcile]){
    const out=await action(intent);assert.equal(out.state,observation===true?'open':'recovery_required');
    assert.equal(out.pr?.number??null,observation===true?42:null);assert.deepEqual(f.effects(),[]);
  }
  assert.ok(f.calls.filter(c=>c.file==='gh'&&c.args[1]==='list').every(c=>c.args[c.args.indexOf('--json')+1].split(',').includes('isDraft')));
});
for(const code of [0,1])for(const observation of [true,false,undefined,null,'true',1,'absent'])test(`E1/L3: create ${code}, readback ${String(observation)} cannot infer draft from URL`,async()=>{
  const f=world(),intent=await f.prepare();f.calls=[];f.createCode=code;f.readback=observation;
  const out=await f.publish(intent);
  assert.equal(out.state,observation===true?'open':'recovery_required');assert.equal(out.pr?.number??null,observation===true?42:null);
  assert.equal(f.calls.filter(c=>c.file==='gh'&&c.args[1]==='create').length,1);assert.equal(f.calls.filter(c=>c.file==='git'&&c.args[0]==='push').length,1);
  assert.equal(f.calls.find(c=>c.file==='gh'&&c.args[1]==='create').args.filter(a=>a==='--draft').length,1);
  const before=f.effects().length;await f.reconcile(intent);assert.equal(f.effects().length,before);
});

test('N7/L9: exact eight intent keys unchanged; draft inside intent fails; false/omitted retain ready behavior with missing isDraft',async()=>{
  for(const mode of ['omitted',false]){
    const f=world(),intent=await f.prepare();assert.deepEqual(Object.keys(intent).sort(),['baseBranch','headBranch','headSha','marker','repository','runId','stageId','title']);
    f.calls=[];assert.equal((await f.publish({...intent,draft:true})).state,'failed');assert.deepEqual(f.calls,[]);
    f.readback=undefined;
    const input={cwd,intent,body:`Default\n<!-- ${intent.marker} -->\n`,...(mode==='omitted'?{}:{draft:false})};
    assert.equal((await publishWorkflowPr(input,f.ports)).state,'open');
    assert.equal(f.calls.find(c=>c.file==='gh'&&c.args[1]==='create').args.includes('--draft'),false);
  }
});

test('E3: caller mutation while first port awaits cannot change captured mode or intent',async()=>{
  for(const original of [false,true]){
    const f=world(),intent=await f.prepare();f.calls=[];f.readback=original;
    const input={cwd,intent,body:`Capture\n<!-- ${intent.marker} -->\n`,draft:original};let changed=false;
    f.intercept=async()=>{if(!changed){changed=true;await Promise.resolve();input.draft=!original;input.intent.headBranch='attacker';}};
    const out=await publishWorkflowPr(input,f.ports);assert.equal(out.state,'open');assert.equal(out.pr.headBranch,'topic/draft');
    const args=f.calls.find(c=>c.file==='gh'&&c.args[1]==='create').args;assert.equal(args.includes('--draft'),original);
  }
  const f=world(),intent=await f.prepare();f.rows=[f.row({isDraft:false})];const input={cwd,intent,draft:true};
  f.intercept=async()=>{input.draft=false;input.intent.headBranch='attacker';};
  assert.equal((await reconcileWorkflowPr(input,f.ports)).state,'recovery_required');assert.deepEqual(f.effects(),[]);
});

for(const existing of [false,true])test(`L10: unpublishedOnly refuses every existing PR, draft=${existing}`,async()=>{
  const f=world(),intent=await f.prepare();f.rows=[f.row({isDraft:existing})];f.calls=[];
  assert.equal((await f.publish(intent,{unpublishedOnly:true})).state,'recovery_required');assert.deepEqual(f.effects(),[]);
});
for(const remote of [sha,'b'.repeat(40),'unknown'])test(`L10: unpublishedOnly refuses present/unknown remote ${remote.slice(0,6)}`,async()=>{
  const f=world(),intent=await f.prepare();f.calls=[];
  f.remote=remote;
  if(remote==='unknown')f.intercept=(file,args)=>file==='git'&&args[0]==='ls-remote'?{stdout:'',code:1}:undefined;
  assert.equal((await f.publish(intent,{unpublishedOnly:true})).state,'recovery_required');assert.deepEqual(f.effects(),[]);
});

test('L9/E2: draft preserves ordinary exact identity, source, marker and body limits',async()=>{
  for(const extra of [{headRefName:'different'},{baseRefName:'other'},{headRefOid:'b'.repeat(40)},{body:'<!-- pdd-workflow:foreign:prompt-pr -->'},
    {url:'https://github.com/foreign/project/pull/42'},{isCrossRepository:true}]){
    const f=world(),intent=await f.prepare();f.rows=[f.row(extra)];f.calls=[];
    assert.equal((await f.publish(intent)).state,'recovery_required');assert.deepEqual(f.effects(),[]);
  }
  for(const body of ['missing marker','x'.repeat(65_537)+'\n<!-- pdd-workflow:draft-run:prompt-pr -->\n']){
    const f=world(),intent=await f.prepare();f.calls=[];assert.equal((await f.publish(intent,{body})).state,'failed');assert.deepEqual(f.effects(),[]);
  }
  for(const count of [2,100]){
    const f=world(),intent=await f.prepare();f.rows=Array.from({length:count},(_,i)=>f.row({number:42+i,url:`https://github.com/example/project/pull/${42+i}`}));f.calls=[];
    assert.equal((await f.publish(intent)).state,'recovery_required');assert.deepEqual(f.effects(),[]);
  }
  for(const local of ['dirty','branch','sha']){
    const f=world(),intent=await f.prepare();f.calls=[];
    f.intercept=(file,args)=>file==='git'&&(local==='dirty'&&args[0]==='status'||local==='branch'&&args[0]==='symbolic-ref'||local==='sha'&&args.join(' ')==='rev-parse --verify HEAD')?{stdout:local==='dirty'?' M value\0':local==='branch'?'other':'b'.repeat(40)}:undefined;
    assert.equal((await f.publish(intent)).state,'failed');assert.deepEqual(f.effects(),[]);
  }
});

test('E1/E4: unavailable readback and uncertain push never create again; known GraphQL rejection preserved',async()=>{
  const f=world(),intent=await f.prepare();f.calls=[];
  f.intercept=(file,args)=>file==='git'&&args[0]==='push'?{stdout:'',code:1}:undefined;
  assert.equal((await f.publish(intent)).state,'recovery_required');assert.equal(f.calls.filter(c=>c.file==='gh'&&c.args[1]==='create').length,0);
  const g=world(),saved=await g.prepare();g.createCode=1;g.readback='absent';g.createError='GraphQL: Body is too long (createPullRequest)';
  assert.equal((await g.publish(saved)).state,'rejected');
  const h=world(),prepared=await h.prepare();let created=false;
  h.intercept=(file,args)=>{if(file==='gh'&&args[1]==='create')created=true;if(created&&file==='gh'&&args[1]==='list')return {stdout:'',code:1};};
  assert.equal((await h.publish(prepared)).state,'recovery_required');assert.equal(h.calls.filter(c=>c.file==='gh'&&c.args[1]==='create').length,1);
});
