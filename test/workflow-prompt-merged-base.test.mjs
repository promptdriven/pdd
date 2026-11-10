// Public code entry after PR 1 merges into a concurrently changed saved base.
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {approveRun,runStatus} from '../src/workflow-runner.mjs';
import {prepared,vector} from './helpers/workflow-prompt-reentry-fixture.mjs';
import {preparedCard,PROMPT,TEST,STORY} from './helpers/workflow-prompt-reentry-card-fixture.mjs';

for(const gate of ['legacy','card']) for(const kind of ['prompt','scenario']) for(const route of ['reply','terminal']) {
  test(`2897 merged base: unrelated ${kind} preserves ${gate} code entry through ${route}`,async t=>{
    const f=gate==='card'?await preparedCard(t,{through:'prompt-pr'}):await prepared(t,{code:false,realRemote:true});
    if(gate==='legacy') {
      const published=await approveRun({ref:'17',cwd:f.source,said:'Publish the prompt PR and stop.'},f.ports);
      assert.equal(published.exitCode,0,published.message);
    }
    const before=f.record(),pr1=before.pr[0];
    assert.equal(before.area,1);assert.equal(before.gate.kind,'ask-code');assert.equal(before.pr.length,1);
    const paths=gate==='card'?[PROMPT,TEST,STORY]:['value.prompt.md','tests/value.json','user_stories/value.md'];
    const bytes=paths.map(path=>readFileSync(join(before.root,path),'utf8'));
    const peer=join(f.base,'merged-peer');
    f.git(f.base,'clone','-q',f.remote,peer);
    f.git(peer,'config','user.name','Peer');f.git(peer,'config','user.email','peer@example.invalid');
    f.git(peer,'switch','-q','main');
    const path=kind==='prompt'?'upstream.prompt.md':'upstream.json';
    const unrelated=vector(99);unrelated.steps[0].entry_path='upstream.prompt.md';
    const text=kind==='prompt'?'# Upstream\nReturn a separate value.\n':JSON.stringify(unrelated);
    writeFileSync(join(peer,path),text);f.git(peer,'add',path);f.git(peer,'commit','-qm','Independent base work');
    f.git(peer,'merge','--no-ff','--no-edit',`origin/${pr1.branch}`);
    f.git(peer,'push','-q','origin','main');
    const merged=f.git(peer,'rev-parse','HEAD');
    f.mergedNumbers.push(pr1.number);
    assert.equal((await runStatus({ref:'17',cwd:f.source},f.ports)).exitCode,0);
    assert.equal(f.record().state,'completed');
    f.tick();
    const out=await approveRun({ref:'17',cwd:f.source,...(route==='reply'?{said:'Make the code PR now.'}:{})},f.ports);
    assert.equal(out.exitCode,0,out.message);
    const run=f.record();
    assert.equal(run.area,2);assert.equal(run.state,'running');assert.equal(run.gate,null);
    assert.equal(run.branch,`${pr1.branch}-code`);assert.equal(run.prBase,'main');
    assert.equal(f.git(run.root,'rev-parse','HEAD'),merged);
    assert.equal(readFileSync(join(run.root,path),'utf8'),text);
    assert.deepEqual(paths.map(path=>readFileSync(join(run.root,path),'utf8')),bytes);
    assert.deepEqual(run.storyApproval,before.storyApproval);assert.deepEqual(run.replayBaseline,before.replayBaseline);
    assert.equal(run.baseSha,before.baseSha);assert.equal(run.pr[0].url,pr1.url);assert.equal(f.prs.length,1);
    assert.deepEqual(run.decisions.slice(0,before.decisions.length),before.decisions);
    assert.equal(run.decisions.length,before.decisions.length+1);
  });
}
