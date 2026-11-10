import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {approveRun} from '../src/workflow-runner.mjs';
import {prepared,vector} from './helpers/workflow-prompt-reentry-fixture.mjs';

for (const kind of ['prompt','scenario']) test(`2897 publication merge: retains owned anchor with upstream ${kind}`,async t=>{
  const f=await prepared(t,{code:false,realRemote:true});
  assert.equal((await approveRun({ref:'17',cwd:f.source,said:'Publish PR 1 and stop.'},f.ports)).exitCode,0);
  const before=f.record(),pr1=before.pr[0],peer=join(f.base,'main-peer');
  f.git(f.base,'clone','-q',f.remote,peer);
  f.git(peer,'config','user.name','Peer'); f.git(peer,'config','user.email','peer@example.invalid');
  f.git(peer,'switch','-q','main');
  const path=kind==='prompt'?'upstream.prompt.md':'upstream.json';
  const content=n=>kind==='prompt'?`# Upstream ${n}\n`:JSON.stringify({...vector(n),steps:[{...vector(n).steps[0],entry_path:'upstream.prompt.md'}]});
  writeFileSync(join(peer,path),content(1)); f.git(peer,'add',path); f.git(peer,'commit','-qm','Upstream addition'); f.git(peer,'push','-q','origin','main');
  f.git(before.root,'fetch','-q',f.remote,'main:refs/remotes/origin/main'); f.git(before.root,'merge','--no-edit','refs/remotes/origin/main');
  const execute=f.ports.execFile; let injected=false;
  f.ports.execFile=async(file,args,options)=>{
    if (!injected && file==='gh' && args[0]==='pr' && args[1]==='view' && args[2]===pr1.url && args.at(-1)?.includes('state') && f.record().gate?.kind==='ask-code') {
      injected=true; f.git(peer,'fetch','-q','origin');
      writeFileSync(join(peer,path),content(2)); f.git(peer,'commit','-qam','Upstream edit');
      f.git(peer,'merge','--no-ff','--no-edit',`origin/${pr1.branch}`); f.git(peer,'push','-q','origin','main');
      f.mergedNumbers.push(pr1.number);
    }
    return execute(file,args,options);
  };
  await f.done('check');
  const out=await approveRun({ref:'17',cwd:f.source,said:'Continue code.'},f.ports);
  assert.equal(injected,true); assert.equal(out.exitCode,0,out.message); assert.equal(f.record().area,2);
  assert.equal(readFileSync(join(before.root,path),'utf8'),content(2));
  assert.deepEqual(f.record().replayBaseline.vectors,before.replayBaseline.vectors,'publication-anchor-preserved');
  assert.equal(f.record().baseSha,before.baseSha);
});
