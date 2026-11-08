// Public workflow calls with real fetch/merge/push to a local bare remote.
import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync,readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {approveRun,stepDone} from '../src/workflow-runner.mjs';
import {prepared,vector,reopen} from './helpers/workflow-prompt-reentry-fixture.mjs';

function peer(f) {
  const root=join(f.base,'peer');
  f.git(f.base,'clone','-q',f.remote,root);
  f.git(root,'config','user.name','Peer');f.git(root,'config','user.email','peer@example.invalid');
  return root;
}
function pushPeer(f,root,branch,path,text) {
  f.git(root,'switch','-q',branch);
  writeFileSync(join(root,path),text);f.git(root,'add','.');f.git(root,'commit','-qm','Peer correction');
  f.git(root,'push','-q','origin',`HEAD:refs/heads/${branch}`);
  return f.git(root,'rev-parse','HEAD');
}

for (const route of ['reply','terminal']) for (const kind of ['expected','story','bytes']) {
  test(`2897 fetched source: ${kind} at final fetch refuses ${route} before a code decision`,async t=>{
    const f=await prepared(t,{realRemote:true}),old=f.record(),pr1=old.pr[0],pr2=old.pr[1],other=peer(f);
    assert.equal((await reopen(f)).exitCode,0);
    writeFileSync(join(old.root,'value.prompt.md'),'# Value\nReturn the corrected value.\n');
    await f.done('check');
    f.git(other,'fetch','-q','origin');
    const execute=f.ports.execFile,decisions=f.record().decisions.length,anchor=f.record().replayBaseline,code=f.git(old.root,'rev-parse',pr2.branch);
    let injected=false,peerHead;
    f.ports.execFile=async(file,args,options)=>{
      if(!injected&&file==='git'&&args[0]==='fetch'&&args[2]===`refs/heads/${pr1.branch}:refs/remotes/origin/${pr1.branch}`) {
        injected=true;
        const path=kind==='story'?'user_stories/value.md':'tests/value.json';
        const text=kind==='expected'?JSON.stringify(vector(8)):kind==='story'?'I can select a revised value.\n':JSON.stringify(vector(2),null,2)+'\n';
        peerHead=pushPeer(f,other,pr1.branch,path,text);
      }
      return execute(file,args,options);
    };
    f.tick();
    const out=await approveRun({ref:'17',cwd:f.source,...(route==='reply'?{said:'Continue the code PR.'}:{})},f.ports);
    assert.equal(injected,true);assert.notEqual(out.exitCode,0,out.message);
    const run=f.record();assert.equal(run.area,kind==='bytes'?1:0);
    assert.equal(run.branch,pr1.branch);assert.equal(f.git(old.root,'branch','--show-current'),pr1.branch);
    assert.equal(run.decisions.length,decisions);assert.deepEqual(run.replayBaseline,anchor);
    assert.equal(f.git(old.root,'merge-base',peerHead,pr1.branch),peerHead);
    assert.equal(run.pr[0].url,pr1.url);assert.equal(run.pr[1].url,pr2.url);
    assert.equal(f.git(old.root,'rev-parse',pr2.branch),code);
  });
}

test('2897 current main: return integrates main into PR 1 and reanchors without unrelated scenarios',async t=>{
  const f=await prepared(t,{realRemote:true}),old=f.record(),pr1=old.pr[0],pr2=old.pr[1],other=peer(f);
  const head=pushPeer(f,other,'main','upstream.json',JSON.stringify(vector(99)));
  assert.equal((await reopen(f)).exitCode,0);
  assert.equal(f.record().branch,pr1.branch);
  assert.equal(f.git(old.root,'merge-base',head,pr1.branch),head);
  assert.equal(f.record().done.check,undefined);assert.equal(f.record().done.verify,undefined);
  const decisions=f.record().decisions.length;
  await f.done('check');assert.equal(f.record().area,1);assert.equal(f.record().decisions.length,decisions);
  assert.deepEqual(f.record().replayBaseline.vectors.filter(v=>v.source!=='base').map(v=>v.path),['tests/value.json']);
  await f.approve();assert.equal(f.record().area,2);
  assert.equal(f.git(old.root,'merge-base',head,pr2.branch),head);
  assert.equal(f.record().baseSha,old.baseSha);assert.equal(f.prs.length,2);
});

test('2897 pinned source: a remote ref that moves after capture cannot change the code merge',async t=>{
  const f=await prepared(t,{realRemote:true}),old=f.record(),pr1=old.pr[0],other=peer(f);
  await reopen(f);writeFileSync(join(old.root,'value.prompt.md'),'# Value\nCorrected prompt.\n');await f.done('check');
  f.git(other,'fetch','-q','origin');
  const execute=f.ports.execFile;let moved=false;
  f.ports.execFile=async(file,args,options)=>{
    if(!moved&&file==='git'&&args[0]==='switch'&&args.at(-1)===old.branch) {
      moved=true;const changed=pushPeer(f,other,pr1.branch,'tests/value.json',JSON.stringify(vector(8)));
      // Model another fetch changing the tracking ref after the pinned read.
      f.git(old.root,'fetch','-q',f.remote,changed);
      f.git(old.root,'update-ref',`refs/remotes/origin/${pr1.branch}`,changed);
    }
    return execute(file,args,options);
  };
  await f.approve();assert.equal(moved,true);assert.equal(f.record().area,2);
  assert.equal(JSON.parse(readFileSync(join(old.root,'tests/value.json'))).steps[0].checks[0].value,2);
});

test('2897 merged source: a code-side expected change refuses entry and keeps the code commit',async t=>{
  const f=await prepared(t,{realRemote:true}),old=f.record();
  // A saved code correction can exist locally, but cannot become the contract.
  writeFileSync(join(old.root,'tests/value.json'),JSON.stringify(vector(8)));
  f.git(old.root,'commit','-qam','Unsafe code-side expected value');const code=f.git(old.root,'rev-parse','HEAD');
  await reopen(f);writeFileSync(join(old.root,'value.prompt.md'),'# Value\nCorrected prompt.\n');await f.done('check');
  const decisions=f.record().decisions.length;
  const out=await approveRun({ref:'17',cwd:f.source},f.ports);
  assert.notEqual(out.exitCode,0,out.message);assert.equal(f.record().area,1);
  assert.equal(f.record().decisions.length,decisions);assert.equal(f.git(old.root,'branch','--show-current'),old.pr[0].branch);
  assert.equal(f.git(old.root,'merge-base',code,old.branch),code);
});

test('2897 current main: reopening returned prompt space integrates a newer base and clears checks',async t=>{
  const f=await prepared(t,{realRemote:true}),old=f.record(),other=peer(f);
  await reopen(f);assert.equal(f.record().area,1);await f.done('check');assert.equal(f.record().gate?.kind,'ask-code');
  const upstream=pushPeer(f,other,'main','upstream.md','Current base context.\n');
  const out=await reopen(f);assert.equal(out.exitCode,0,out.message);
  assert.equal(f.record().done.check,undefined);assert.equal(f.record().gate,null);
  assert.equal(f.git(old.root,'merge-base','HEAD',upstream),upstream);
  assert.equal(f.record().baseSha,old.baseSha);
});

test('2897 current main: a base merge conflict retains prompt progress and both branches',async t=>{
  const f=await prepared(t,{realRemote:true}),old=f.record(),other=peer(f),code=f.git(old.root,'rev-parse',old.branch);
  pushPeer(f,other,'main','value.prompt.md','# Different upstream specification\n');
  const out=await reopen(f);assert.notEqual(out.exitCode,0);
  assert.equal(f.record().area,1);assert.equal(f.record().branch,old.pr[0].branch);
  assert.equal(f.git(old.root,'branch','--show-current'),old.pr[0].branch);
  assert.notEqual(f.git(old.root,'diff','--name-only','--diff-filter=U'),'');
  assert.equal(f.git(old.root,'rev-parse',old.branch),code);
  assert.equal(f.record().done.verify,undefined);assert.equal(f.prs.length,2);
});

test('2897 current main: an explicit Story return keeps its selected area after base integration',async t=>{
  const f=await prepared(t,{realRemote:true}),old=f.record(),other=peer(f);
  const head=pushPeer(f,other,'main','upstream.md','Base context.\n');
  const out=await reopen(f,'story');assert.equal(out.exitCode,0,out.message);
  assert.equal(f.record().area,0);assert.equal(f.record().branch,old.pr[0].branch);
  assert.equal(f.git(old.root,'merge-base','HEAD',head),head);
  assert.equal(f.record().done['prompt-story'],undefined);
  await f.done('prompt-story');assert.equal(f.record().gate.kind,'approve');
});
