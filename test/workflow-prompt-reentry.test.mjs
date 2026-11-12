// Real temporary Git. The repo fixture fakes GitHub, Herdr and native launches.
import test from 'node:test';
import assert from 'node:assert/strict';
import {existsSync,mkdirSync,readFileSync,unlinkSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {openRun,stepDone,approveRun,runStatus} from '../src/workflow-runner.mjs';
import {legacyManualGates} from './helpers/legacy-manual-gates.mjs';
import {fixture,packageRoot} from './helpers/workflow-runner-fixture.mjs';

import {prepared,vector,save,reopen} from './helpers/workflow-prompt-reentry-fixture.mjs';

for(const [area,newSession] of [['prompt-pr',false],['prompt-pr',true],['story',false]])
 test(`2897: ${area} reopens on PR 1 with newSession=${newSession}`,async t=>{
  const f=await prepared(t),before=f.record(),pr1=before.pr[0];
  let resumedPane;
  if(area==='prompt-pr' && !newSession) {
    const saved=f.record(),chat=saved.chats.find(chat=>chat.area===area);
    resumedPane=f.herdr.paneOf(chat);
    chat.session={agent:'codex',id:resumedPane.agent.agent_session.value};chat.state='ended';
    save(f,saved);resumedPane.agent=null;
  }
  for(const file of ['replay-evidence.json','old-code-proof.json','verify.md'])writeFileSync(join(before.runDir,file),'old evidence');
  f.tick();const out=await reopen(f,area,{newSession});assert.equal(out.exitCode,0,out.message);
  const run=f.record();assert.equal(run.area,area==='story'?0:1);
  assert.equal(run.branch,pr1.branch);assert.equal(f.git(run.root,'branch','--show-current'),pr1.branch);
  assert.deepEqual(run.pr,before.pr);assert.deepEqual(run.decisions,before.decisions);assert.deepEqual(run.changes,before.changes);
  assert.equal(run.done.build,undefined);assert.equal(run.done.verify,undefined);assert.equal(run.replayEvidence,undefined);
  assert.equal(run.testInventory,undefined);assert.equal(run.gate,null);
  for(const file of ['replay-evidence.json','old-code-proof.json','verify.md'])assert.equal(existsSync(join(run.runDir,file)),false);
  const status=await runStatus({ref:'17',cwd:f.source},f.ports);
  assert.ok(status.message.includes(run.promptReturn.reason));
  if(resumedPane)assert.ok(resumedPane.agent.prompts.some(text=>text.includes(run.promptReturn.reason)));
 });

test('2897: prompt correction updates PR 1 then rebuilds the same PR 2 without prompt changes',async t=>{
  const f=await prepared(t),before=f.record(),pr1=before.pr[0],pr2=before.pr[1];
  assert.equal((await reopen(f)).exitCode,0);
  assert.equal(f.record().area,1);
  writeFileSync(join(before.root,'value.prompt.md'),'# Value\nReturn the value selected by the caller.\n');
  await f.done('check');
  assert.equal(f.record().gate.kind,'ask-code');assert.equal(f.prs.length,2);
  assert.ok(f.pushes.at(-1)[2].endsWith(`:refs/heads/${pr1.branch}`));
  const promptHead=f.git(before.root,'rev-parse','HEAD');
  assert.equal(f.git(before.root,'show',`${pr1.branch}:value.mjs`),'export const value = 1;');
  assert.ok(f.prs[0].body.includes(f.record().promptReturn.reason));
  await f.approve();assert.equal(f.record().branch,pr2.branch);assert.equal(f.record().area,2);
  assert.equal(f.git(before.root,'merge-base',promptHead,'HEAD'),promptHead);
  assert.equal(f.git(before.root,'diff',pr1.branch,'--','value.prompt.md'),'');
  assert.equal(f.record().done.verify,undefined);
  writeFileSync(join(before.root,'value.mjs'),'export const value = 3;\n');
  await f.done('build');await f.done('verify');
  assert.equal(f.prs.length,2);assert.equal(f.record().pr[1].url,pr2.url);
  assert.ok(f.prs[1].body.includes(f.record().promptReturn.reason));
  assert.ok(f.pushes.every(args=>!args.some(arg=>arg.startsWith('--force'))));
});

for(const kind of ['story','expected'])test(`2897: a changed ${kind} reopens the existing Story gate`,async t=>{
  const f=await prepared(t),before=f.record();await reopen(f);
  if(kind==='story')writeFileSync(join(before.root,'user_stories/value.md'),'I can select another value.\n');
  else writeFileSync(join(before.root,'tests/value.json'),JSON.stringify(vector(3)));
  const count=f.pushes.length;await f.done('check');
  assert.equal(f.record().area,0);assert.equal(f.record().gate,null);assert.equal(f.pushes.length,count);
  await f.done('prompt-story');assert.equal(f.record().gate.kind,'approve');
  assert.notEqual(f.record().gate.id,before.decisions[0].gateId);
  await f.approve();await f.done('check');
  assert.equal(f.record().gate.kind,'ask-code');assert.equal(f.record().area,1);
  assert.deepEqual(f.record().replayBaseline.vectors.map(v=>v.path),['tests/value.json']);
  if(kind==='expected')assert.equal(f.record().replayBaseline.vectors[0].snapshot.steps[0].checks[0].value,3);
});

test('2897: code publication refuses prompt edits before commit or push',async t=>{
  const f=await prepared(t),run=f.record(),head=f.git(run.root,'rev-parse','HEAD'),pushes=f.pushes.length;
  writeFileSync(join(run.root,'value.prompt.md'),'# Changed specification\n');
  const out=await stepDone({step:'verify',summary:'reviewed',cwd:run.root},f.agentPorts());
  assert.notEqual(out.exitCode,0);assert.equal(f.git(run.root,'rev-parse','HEAD'),head);
  assert.equal(f.pushes.length,pushes);
});

test('2894: replay anchor excludes unrelated scenarios merged from the original base',async t=>{
  const f=await prepared(t,{code:false}),run=f.record();
  // Upstream advances independently. Only this run changed tests/value.json.
  writeFileSync(join(f.source,'unrelated.json'),JSON.stringify(vector(99)));
  f.git(f.source,'add','unrelated.json');f.git(f.source,'commit','-qm','Unrelated upstream scenario');
  f.git(f.source,'update-ref','refs/remotes/origin/main',f.git(f.source,'rev-parse','HEAD'));
  f.git(run.root,'merge','--no-edit','main');
  await f.approve();
  assert.deepEqual(f.record().replayBaseline.vectors.map(v=>v.path),['tests/value.json']);
  assert.equal(f.record().baseSha,run.baseSha);
});

test('2897: returned Story approval covers revisions made in the Story area',async t=>{
  const f=await prepared(t),root=f.record().root;
  await reopen(f,'story');
  writeFileSync(join(root,'tests/value.json'),JSON.stringify(vector(5)));
  await f.done('prompt-story');await f.approve();legacyManualGates(f);await f.done('check');
  assert.equal(f.record().area,1);assert.equal(f.record().gate.kind,'ask-code');
  assert.equal(f.record().replayBaseline.vectors[0].snapshot.steps[0].checks[0].value,5);
});

test('2897: return refuses dirty code and merged PR 1 before branch or progress effects',async t=>{
  const f=await prepared(t),run=f.record(),recordPath=join(run.runDir,'status.json');
  for(const dirty of [true,false]) {
    if(dirty)writeFileSync(join(run.root,'value.mjs'),'export const value = 10;\n');
    else {f.git(run.root,'restore','value.mjs');f.merged=true;}
    const before=readFileSync(recordPath),branch=f.git(run.root,'branch','--show-current'),pushes=f.pushes.length;
    const out=await reopen(f);assert.notEqual(out.exitCode,0);
    assert.deepEqual(readFileSync(recordPath),before);assert.equal(f.git(run.root,'branch','--show-current'),branch);
    assert.equal(f.pushes.length,pushes);
  }
});

test('2897: an automatic code worker uses the same prompt return with current claim ownership',async t=>{
  const f=await prepared(t),run=f.record();
  const origin={repository:run.repo,coordinatorId:'synthetic-owner',machine:'synthetic-machine',claim:{commentId:'11',labelEventId:'12'}};
  run.automaticOrigin=origin;save(f,run);
  const {createHash}=await import('node:crypto');
  const autopilotStateRoot=join(f.state,'autopilot');mkdirSync(autopilotStateRoot);
  writeFileSync(join(autopilotStateRoot,`${createHash('sha256').update(f.source).digest('hex').slice(0,20)}.json`),JSON.stringify({repo:run.repo,cwd:f.source,coordinatorId:origin.coordinatorId}));
  const execute=f.ports.execFile;
  const rows={
    'repos/example/project':{owner:{login:'example'}},
    'repos/example/project/collaborators?per_page=100':[],
    'repos/example/project/issues/17':{labels:['pdd:working']},
    'repos/example/project/issues/17/timeline?per_page=100':[{id:12,event:'labeled',label:{name:'pdd:working'},actor:{login:'example'}}],
    'repos/example/project/issues/17/comments?per_page=100':[{id:11,user:{login:'example'},body:JSON.stringify({...origin,labelEventId:'12'})}]
  };
  const ports={...f.agentPorts(),autopilotStateRoot,execFile:async(file,args,options)=>{
    if(file==='gh' && args[0]==='api' && args[1]==='--include') {
      assert.ok(Object.hasOwn(rows,args[4]),args[4]);return {stdout:`HTTP/1.1 200 OK\n\n${JSON.stringify(rows[args[4]])}`};
    }
    return execute(file,args,options);
  }};
  const out=await openRun({ref:'17',area:'prompt-pr',cwd:run.root,packageRoot},ports);
  assert.equal(out.exitCode,0,out.message);assert.equal(f.record().area,1);
  assert.equal(f.record().branch,run.pr[0].branch);assert.deepEqual(f.record().automaticOrigin,origin);
});

// Repair 1: approvals cover the displayed contract, including edits fetched on return.
for (const kind of ['expected','story','unknown']) test(`2897 repair: ${kind} contract on PR 1 before return needs a Story decision`,async t=>{
  const f=await prepared(t),run=f.record(),pr1=run.pr[0];
  if(kind==='unknown') {
    for(const decision of run.decisions)delete decision.storyContract;
    save(f,run);
  } else {
    f.git(run.root,'switch','-q',pr1.branch);
    if(kind==='expected')writeFileSync(join(run.root,'tests/value.json'),JSON.stringify(vector(9)));
    else writeFileSync(join(run.root,'user_stories/value.md'),'I can select a different value.\n');
    f.git(run.root,'commit','-qam','Contract corrected on PR 1');
    f.git(run.root,'update-ref',`refs/remotes/origin/${pr1.branch}`,f.git(run.root,'rev-parse','HEAD'));
    f.prs[0].headRefOid=f.git(run.root,'rev-parse','HEAD');
    f.git(run.root,'switch','-q',run.branch);
  }
  assert.equal((await reopen(f)).exitCode,0);
  const pushes=f.pushes.length,decisions=f.record().decisions.length;
  await f.done('check');
  assert.equal(f.record().area,0);
  assert.equal(f.record().gate,null);assert.equal(f.pushes.length,pushes);
  assert.equal(f.record().decisions.length,decisions);
  assert.equal(f.record().replayBaseline.vectors[0].snapshot.steps[0].checks[0].value,2);
  await f.done('prompt-story');await f.approve();legacyManualGates(f);await f.done('check');
  assert.equal(f.record().gate.kind,'ask-code');
  assert.equal(f.record().replayBaseline.vectors[0].snapshot.steps[0].checks[0].value,kind==='expected'?9:2);
});

for(const kind of ['expected','story','added','removed']) test(`2897 repair: unseen ${kind} contract refuses a reply to the returned Story gate`,async t=>{
  const f=await prepared(t),root=f.record().root;
  assert.equal((await reopen(f,'story')).exitCode,0);await f.done('prompt-story');
  const before=f.record(),pushes=f.pushes.length;
  if(kind==='expected')writeFileSync(join(root,'tests/value.json'),JSON.stringify(vector(8)));
  if(kind==='story')writeFileSync(join(root,'user_stories/value.md'),'I can choose eight.\n');
  if(kind==='added')writeFileSync(join(root,'tests/extra.json'),JSON.stringify(vector(8)));
  if(kind==='removed') {
    const {unlinkSync}=await import('node:fs');unlinkSync(join(root,'tests/value.json'));
  }
  const out=await approveRun({ref:'17',cwd:f.source,packageRoot,said:'I approve the Story and expected value 2 shown to me.'},f.ports);
  assert.notEqual(out.exitCode,0);
  assert.equal(f.record().area,0);assert.equal(f.record().gate.id,before.gate.id);
  assert.deepEqual(f.record().decisions,before.decisions);assert.equal(f.pushes.length,pushes);
  // Only a newly displayed gate and a later decision can cover the revision.
  await f.done('prompt-story');
  const approved=await approveRun({ref:'17',cwd:f.source,packageRoot,said:'I approve the revised Story and cases now shown.'},f.ports);
  assert.equal(approved.exitCode,0,approved.message);assert.equal(f.record().area,1);
});

test('2897 repair: a contract edit during terminal confirmation refuses approval',async t=>{
  const f=await prepared(t);await reopen(f,'story');await f.done('prompt-story');
  const before=f.record();
  f.ports.confirm=async()=>{writeFileSync(join(before.root,'tests/value.json'),JSON.stringify(vector(8)));return true;};
  const out=await approveRun({ref:'17',cwd:f.source,packageRoot},f.ports);
  assert.notEqual(out.exitCode,0);assert.equal(f.record().area,0);
  assert.deepEqual(f.record().decisions,before.decisions);
});

for(const base of ['main','topic/selected']) test(`2897 repair: code publication uses fetched ${base} after PR 1 merges`,async t=>{
  const f=await prepared(t,{code:false});
  const published=await approveRun({ref:'17',cwd:f.source,packageRoot,said:'I approve the prompt PR.'},f.ports);
  assert.equal(published.exitCode,0,published.message);
  if(base!=='main') {
    f.git(f.source,'branch',base,'main');
    f.git(f.source,'update-ref',`refs/remotes/origin/${base}`,f.git(f.source,'rev-parse',base));
    const saved=f.record();saved.baseBranch=base;saved.pr[0].base=base;save(f,saved);
    f.prs[0].baseRefName=base;
  }
  f.mergedNumbers.push(f.prs[0].number);
  await f.approve();
  const run=f.record(),localBase=f.git(run.root,'rev-parse',base);
  assert.notEqual(localBase,f.git(run.root,'rev-parse',`refs/remotes/origin/${base}`));
  writeFileSync(join(run.root,'value.mjs'),'export const value = 3;\n');
  await f.done('build');await f.done('verify');
  assert.equal(f.prs[1].baseRefName,base);
  assert.equal(f.git(run.root,'rev-parse',base),localBase);
  // The published comparison still refuses a real prompt edit before commit or push.
  const head=f.git(run.root,'rev-parse','HEAD'),pushes=f.pushes.length;
  writeFileSync(join(run.root,'value.prompt.md'),'# Changed contract\n');
  const refused=await stepDone({step:'verify',summary:'retry',cwd:run.root},f.agentPorts());
  assert.notEqual(refused.exitCode,0);assert.equal(f.git(run.root,'rev-parse','HEAD'),head);assert.equal(f.pushes.length,pushes);
});

test('2897 repair: returned automatic code resume arms completion for its new attempt',async t=>{
  const f=await prepared(t),run=f.record();
  const origin={repository:run.repo,coordinatorId:'synthetic-owner',machine:'synthetic-machine',claim:{commentId:'11',labelEventId:'12'}};
  run.automaticOrigin=origin;
  const chat=run.chats.find(x=>x.area==='code'),pane=f.herdr.paneOf(chat);
  chat.session={agent:'codex',id:pane.agent.agent_session.value};chat.state='ended';pane.agent=null;
  save(f,run);
  const {createHash}=await import('node:crypto');
  const autopilotStateRoot=join(f.state,'autopilot');mkdirSync(autopilotStateRoot);
  writeFileSync(join(autopilotStateRoot,`${createHash('sha256').update(f.source).digest('hex').slice(0,20)}.json`),JSON.stringify({repo:run.repo,cwd:f.source,coordinatorId:origin.coordinatorId,enabled:true,paneId:'fake-coordinator'}));
  const execute=f.ports.execFile,arms=[];
  const rows={
    'repos/example/project':{owner:{login:'example'}},
    'repos/example/project/collaborators?per_page=100':[],
    'repos/example/project/issues/17':{labels:['pdd:working']},
    'repos/example/project/issues/17/timeline?per_page=100':[{id:12,event:'labeled',label:{name:'pdd:working'},actor:{login:'example'}}],
    'repos/example/project/issues/17/comments?per_page=100':[{id:11,user:{login:'example'},body:JSON.stringify({...origin,labelEventId:'12'})}]
  };
  Object.assign(f.ports,{autopilotStateRoot,armWorkerCompletion:identity=>arms.push(identity),execFile:async(file,args,options)=>{
    if(file==='gh' && args[0]==='api' && args[1]==='--include') {
      assert.ok(Object.hasOwn(rows,args[4]),args[4]);return {stdout:`HTTP/1.1 200 OK\n\n${JSON.stringify(rows[args[4]])}`};
    }
    return execute(file,args,options);
  }});
  assert.equal((await reopen(f)).exitCode,0);
  writeFileSync(join(run.root,'value.prompt.md'),'# Value\nReturn the corrected value.\n');
  await f.done('check');arms.length=0;await f.approve();
  const current=f.record(),code=current.chats.find(x=>x.area==='code');
  assert.equal(current.area,2);assert.ok(code.resumedAt>chat.startedAt);
  assert.equal(arms.length,1);assert.equal(arms[0].startAnchor,code.resumedAt);
  assert.equal(arms[0].requireActivity,true);assert.equal(arms[0].paneId,code.paneId);
  assert.equal(arms[0].coordinatorPaneId,'fake-coordinator');
});

test('2897 repair: owning prompt passes local interpreter freshness admission',async()=>{
  const {interfaceBlocks,proseSha256,promptRefusal}=await import('../src/runtime-seam.mjs');
  const path='prompts/cli/workflow-runner.prompt.md',text=readFileSync(join(packageRoot,path),'utf8');
  const iface=JSON.parse(interfaceBlocks(text)[0][1]);
  assert.ok(['draft','approved'].includes(iface.status));
  assert.equal(promptRefusal({path,interface:iface,prose:proseSha256(text)},'Runtime interface'),null);
});

// Repair 2: the review requires immutable publication and fresh code-entry coverage.
for(const published of [false,true])for(const boundary of (published?['status','staging','commit','preparation']:['status','staging','commit']))
 test(`2897 repair 2: real remote refuses a prompt race during ${boundary}, existing PR 2=${published}`,async t=>{
  const f=await prepared(t,{realRemote:true,publishCode:published}),run=f.record(),pr1=run.pr[0];
  const head=f.git(run.root,'rev-parse','HEAD'),remote=published?f.git(f.remote,'rev-parse',run.branch):'',pushes=f.pushes.length;
  writeFileSync(join(run.root,'value.mjs'),'export const value = 4;\n');
  const execute=f.ports.execFile;let compared=false,changed=false;
  f.ports.execFile=async(file,args,options)=>{
    if(file==='git' && args[0]==='diff' && args[1]==='--quiet' && args.at(-1)==='*.prompt.md')compared=true;
    const target=boundary==='status'?file==='git' && args[0]==='status'
      :boundary==='staging'?file==='git' && args[0]==='add'
      :boundary==='commit'?file==='git' && args[0]==='commit'
      :file==='gh' && args[0]==='pr' && args[1]==='edit';
    if(compared && !changed && target) {
      changed=true;writeFileSync(join(run.root,'value.prompt.md'),'# Concurrent prompt correction\n');
      // Simulate another writer staging and committing while publication prepares.
      if(['commit','preparation'].includes(boundary)) {
        f.git(run.root,'add','value.prompt.md');
        if(boundary==='preparation')f.git(run.root,'commit','-qm','Concurrent prompt edit');
      }
    }
    return execute(file,args,options);
  };
  const out=await stepDone({step:'verify',summary:'reviewed',cwd:run.root},f.agentPorts());
  assert.equal(changed,true,'the race must run after the first prompt comparison');
  if(published) {
    assert.equal(f.git(f.remote,'rev-parse',run.branch),remote,'unsafe source must never reach the remote');
    assert.equal(f.git(run.root,'diff',`origin/${pr1.branch}`,`origin/${run.branch}`,'--','*.prompt.md'),'');
  } else {
    assert.equal(f.git(f.remote,'for-each-ref',`refs/heads/${run.branch}`),'','the unsafe code branch must not be pushed');
    assert.equal(f.prs.length,1);
  }
  assert.notEqual(out.exitCode,0);assert.match(out.message,/prompt-pr/);
  assert.equal(f.pushes.length,pushes);
  assert.equal(readFileSync(join(run.root,'value.prompt.md'),'utf8'),'# Concurrent prompt correction\n');
  if(['status','staging'].includes(boundary))assert.equal(f.git(run.root,'rev-parse','HEAD'),head);
 });

for(const route of ['terminal','reply','sync','fetch','first-publication'])for(const kind of ['contract','bytes'])
 test(`2897 repair 2: ${kind} edit during ${route} code entry stays in prompt space`,async t=>{
  const f=await prepared(t,{code:route!=='first-publication'}),run=f.record(),root=run.root;
  if(route!=='first-publication') {
    assert.equal((await reopen(f)).exitCode,0);
    writeFileSync(join(root,'value.prompt.md'),'# Value\nA corrected prompt.\n');await f.done('check');
  }
  const before=f.record(),branch=f.git(root,'branch','--show-current');let changed=false;
  const change=()=>{changed=true;writeFileSync(join(root,'tests/value.json'),kind==='contract'?JSON.stringify(vector(8)):JSON.stringify(vector(2),null,2)+'\n');};
  if(route==='terminal' || route==='first-publication')f.ports.confirm=async()=>{if(route==='terminal' || f.prs.length===1)change();return true;};
  if(route==='reply') {
    let replied=false;
    f.ports.stdin=(async function*(){replied=true;yield 'Start code from the approved contract.';})();
    const execute=f.ports.execFile;
    f.ports.execFile=async(file,args,options)=>{
      if(replied && !changed && file==='git' && args[0]==='diff' && args.some(arg=>arg.includes('...')))change();
      return execute(file,args,options);
    };
  }
  if(['sync','fetch'].includes(route)) {
    const execute=f.ports.execFile;let statusReads=0;
    f.ports.execFile=async(file,args,options)=>{
      // Explicit-reply synchronization follows the prompt snapshot checks.
      if(route==='sync' && file==='gh' && args[0]==='pr' && args[1]==='view' && args.at(-1)?.includes('state'))statusReads++;
      if(!changed && (route==='sync'?statusReads===2:file==='git' && args[0]==='fetch' && args[2]?.startsWith('refs/heads/')))change();
      return execute(file,args,options);
    };
  }
  const out=await approveRun({ref:'17',cwd:f.source,packageRoot,...(['reply','sync','fetch'].includes(route)?{said:route==='reply'?'-':'Start code from the approved contract.'}:{})},f.ports);
  if(out.exitCode!==0)t.diagnostic(JSON.stringify({route,kind,message:out.message,area:f.record().area}));
  assert.equal(changed,true,'the edit must occur at the selected boundary');
  assert.notEqual(out.exitCode,0);assert.equal(f.record().area,kind==='contract'?0:1);
  assert.equal(f.git(root,'branch','--show-current'),branch);
  const decisions=f.record().decisions;
  assert.deepEqual(decisions.slice(0,before.decisions.length),before.decisions);
  if(route==='first-publication') {
    assert.equal(decisions.length,before.decisions.length+1,'only the separate PR 1 approval may be recorded');
    assert.notEqual(decisions.at(-1).gateId,f.record().gate?.id);
  } else assert.deepEqual(decisions,before.decisions,'a changed code contract cannot record code approval');
  assert.equal(f.record().replayBaseline.vectors[0].snapshot.steps[0].checks[0].value,2);
 });

for(const boundary of ['return','gate'])for(const edit of ['add','edit','delete'])
 test(`2897 repair 2: nested Story ${edit} at ${boundary} needs fresh coverage`,async t=>{
  const f=await prepared(t,{nested:edit!=='add'}),root=f.record().root;
  assert.equal((await reopen(f,boundary==='gate'?'story':'prompt-pr')).exitCode,0);
  if(boundary==='gate')await f.done('prompt-story');
  const before=f.record(),pushes=f.pushes.length,path=join(root,'packages/widget/user_stories/value.md');
  if(edit==='delete')unlinkSync(path);
  else {mkdirSync(join(root,'packages/widget/user_stories'),{recursive:true});writeFileSync(path,'I can select a different nested value.\n');}
  if(boundary==='return')await f.done('check');
  else {
    const out=await approveRun({ref:'17',cwd:f.source,packageRoot,said:'I approve the displayed Story.'},f.ports);
    assert.notEqual(out.exitCode,0);
  }
  assert.equal(f.record().area,0);assert.equal(f.pushes.length,pushes);
  assert.deepEqual(f.record().decisions,before.decisions);
 });
