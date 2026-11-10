import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {approveRun,openRun} from '../src/workflow-runner.mjs';
import {prepared,vector} from './helpers/workflow-prompt-reentry-fixture.mjs';
import {preparedCard,PROMPT,TEST,STORY} from './helpers/workflow-prompt-reentry-card-fixture.mjs';

for (const returned of [false,true]) for (const gate of ['legacy','card']) for (const kind of ['prompt','scenario']) {
  if (!returned && gate==='card') continue;
  test(`2897 fix 2: integrated upstream ${kind} changes during ${returned?'returned':'initial'} ${gate} entry`,async t=>{
    const f=gate==='card'?await preparedCard(t,{through:returned?'code':'prompt-pr'}):await prepared(t,{code:returned,realRemote:true});
    if (!returned && gate==='legacy') assert.equal((await approveRun({ref:'17',cwd:f.source,said:'Publish PR 1 and stop.'},f.ports)).exitCode,0);
    const before=f.record(),pr1=before.pr[0],peer=join(f.base,'main-peer');
    f.git(f.base,'clone','-q',f.remote,peer);
    f.git(peer,'config','user.name','Peer'); f.git(peer,'config','user.email','peer@example.invalid');
    f.git(peer,'switch','-q','main');
    const path=kind==='prompt'?'upstream.prompt.md':'upstream.json';
    const content=n=>kind==='prompt'?`# Upstream ${n}\n`:JSON.stringify({...vector(n),steps:[{...vector(n).steps[0],entry_path:'upstream.prompt.md'}]});
    writeFileSync(join(peer,path),content(1)); f.git(peer,'add',path); f.git(peer,'commit','-qm','Upstream addition'); f.git(peer,'push','-q','origin','main');
    if (returned) assert.equal((await openRun({ref:'17',area:'prompt-pr',cwd:f.source},f.ports)).exitCode,0);
    else { f.git(before.root,'fetch','-q',f.remote,'main:refs/remotes/origin/main'); f.git(before.root,'merge','--no-edit','refs/remotes/origin/main'); }
    const owned=gate==='card'?[PROMPT,TEST,STORY]:['value.prompt.md','tests/value.json','user_stories/value.md'];
    const bytes=owned.map(p=>readFileSync(join(before.root,p),'utf8'));
    const execute=f.ports.execFile; let injected=false,pinned,armed=returned;
    f.ports.execFile=async(file,args,options)=>{
      if (armed && !injected && file==='gh' && args[0]==='pr' && args[1]==='view' && args[2]===pr1.url && args.at(-1)?.includes('state') && f.record().gate?.kind==='ask-code') {
        injected=true; f.git(peer,'fetch','-q','origin');
        writeFileSync(join(peer,path),content(2)); f.git(peer,'commit','-qam','Upstream edit');
        f.git(peer,'merge','--no-ff','--no-edit',`origin/${pr1.branch}`); f.git(peer,'push','-q','origin','main');
        pinned=f.git(peer,'rev-parse','HEAD'); f.mergedNumbers.push(pr1.number);
      }
      return execute(file,args,options);
    };
    if (gate==='card') await f.check();
    const published=await f.done('check'); armed=true;
    const out=gate==='card' && returned?published:await approveRun({ref:'17',cwd:f.source,said:'Continue code.'},f.ports);
    assert.equal(injected,true,'peer-merge-reached');
    const after=f.record();
    assert.equal(out.exitCode,0,`owned-source-scope: ${out.message}`);
    assert.equal(after.area,2,'owned-source-area'); assert.equal(after.gate,null);
    assert.equal(f.git(before.root,'merge-base','HEAD',pinned),pinned);
    assert.equal(readFileSync(join(before.root,path),'utf8'),content(2));
    assert.deepEqual(owned.map(p=>readFileSync(join(before.root,p),'utf8')),bytes);
    assert.deepEqual(after.storyApproval,before.storyApproval);
    assert.equal(after.baseSha,before.baseSha); assert.equal(after.pr[0].url,pr1.url);
    assert.deepEqual(after.replayBaseline.vectors.map(v=>v.path),before.replayBaseline.vectors.map(v=>v.path));
    if (returned) assert.equal(after.pr[1].url,before.pr[1].url);
  });
}
