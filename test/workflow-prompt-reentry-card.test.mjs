import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {mkdirSync,readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {openRun,approveRun} from '../src/workflow-runner.mjs';
import {fillHashes} from '../src/runtime-seam.mjs';
import {writeRun} from '../src/workflow-runs.mjs';
import {preparedCard,PROMPT,TEST,STORY} from './helpers/workflow-prompt-reentry-card-fixture.mjs';

const open=f=>openRun({ref:'17',area:'prompt-pr',cwd:f.source},f.ports);
function correctPrompt(f) {
  const path=join(f.record().root,PROMPT);
  writeFileSync(path,readFileSync(path,'utf8').replace('Return the order:','Return the priced order:').replace('\"status\":\"approved\"','\"status\":\"draft\"').replace('\"status\": \"approved\"','\"status\": \"draft\"'));
  fillHashes({root:f.record().root,files:[PROMPT]});
}
function delegate(f,{action=true,strict=false}={}) {
  const run=f.record(),origin={repository:run.repo,coordinatorId:'synthetic-owner',machine:'synthetic-machine',claim:{commentId:'11',labelEventId:'12'}};
  run.automaticOrigin=origin;writeRun(run,f.ports);
  writeFileSync(join(f.source,'pdd.json'),JSON.stringify({strict_approvals:strict,autopilot:{mode:'auto'}}));
  const folder=join(f.state,'autopilot');mkdirSync(folder);
  writeFileSync(join(folder,`${createHash('sha256').update(f.source).digest('hex').slice(0,20)}.json`),JSON.stringify({repo:run.repo,cwd:f.source,coordinatorId:origin.coordinatorId,machine:origin.machine,enabled:true,
    ...(action?{startAction:{command:'pdd autopilot start',repository:run.repo,mode:'auto'}}:{})}));
  const rows={
    'repos/example/project':{owner:{login:'example'}},
    'repos/example/project/collaborators?per_page=100':[],
    'repos/example/project/issues/17':{labels:['pdd:working']},
    'repos/example/project/issues/17/timeline?per_page=100':[{id:12,event:'labeled',label:{name:'pdd:working'},actor:{login:'example'}}],
    'repos/example/project/issues/17/comments?per_page=100':[{id:11,user:{login:'example'},body:JSON.stringify({...origin,labelEventId:'12'})}]
  },execute=f.ports.execFile;
  Object.assign(f.ports,{autopilotStateRoot:folder,execFile:async(file,args,options)=>{
    if(file==='gh'&&args[0]==='api'&&args[1]==='--include') {
      assert.ok(Object.hasOwn(rows,args[4]),args[4]);return {stdout:`HTTP/1.1 200 OK\n\n${JSON.stringify(rows[args[4]])}`};
    }
    return execute(file,args,options);
  }});
  return origin;
}

test('2897 card: prompt-only reentry preserves the Story choice and requires a new full saved check',async t=>{
  const f=await preparedCard(t),old=f.record(),approval=old.storyApproval;
  assert.equal((await open(f)).exitCode,0);correctPrompt(f);f.prompts.length=0;
  await f.done('check');assert.equal(f.record().area,1);assert.equal(f.prs.length,2);assert.equal(f.prompts.length,0);
  await f.check();const published=await f.done('check');
  const run=f.record();assert.equal(run.area,2,published.message);assert.equal(run.branch,old.branch);assert.equal(f.prompts.length,0);
  assert.deepEqual(run.storyApproval,approval);assert.equal(run.through,'code');assert.equal(run.pr[1].url,old.pr[1].url);
  assert.equal(run.done.verify,undefined);assert.notEqual(run.replayBaseline,undefined);
});

for(const kind of ['expected','story'])test(`2897 card: changed ${kind} reopens the existing Story card`,async t=>{
  const f=await preparedCard(t),old=f.record();await open(f);
  const path=join(old.root,kind==='expected'?TEST:STORY);
  if(kind==='expected') {
    const doc=JSON.parse(readFileSync(path));doc.steps[0].checks[0].value=950;writeFileSync(path,JSON.stringify(doc));
  } else writeFileSync(path,readFileSync(path,'utf8')+'\n## What must not change\n\nThe order stays visible.\n');
  const pushes=f.pushes.length;await f.done('check');
  assert.equal(f.record().area,0);assert.equal(f.pushes.length,pushes);
  const shown=await f.done('prompt-story');
  assert.equal(f.record().gate.kind,'approve');assert.ok(shown.message.includes(join(old.root,STORY)));
  assert.ok(shown.message.includes(join(old.root,TEST)));assert.deepEqual(f.record().storyApproval,old.storyApproval);
});

test('2897 card: automatic code choice validates the final fetched contract',async t=>{
  const f=await preparedCard(t),old=f.record();await open(f);correctPrompt(f);await f.check();
  const peer=join(f.base,'peer');f.git(f.base,'clone','-q',f.remote,peer);f.git(peer,'config','user.name','Peer');f.git(peer,'config','user.email','peer@example.invalid');
  const pr1=old.pr[0],execute=f.ports.execFile,decisions=f.record().decisions.length;let changed=false;
  f.ports.execFile=async(file,args,options)=>{
    if(!changed&&file==='git'&&args[0]==='fetch'&&args[2]===`refs/heads/${pr1.branch}:refs/remotes/origin/${pr1.branch}`&&f.record().gate?.kind==='ask-code') {
      changed=true;f.git(peer,'fetch','-q','origin');f.git(peer,'switch','-q',pr1.branch);
      const path=join(peer,TEST),doc=JSON.parse(readFileSync(path));doc.steps[0].checks[0].value=950;writeFileSync(path,JSON.stringify(doc));
      f.git(peer,'commit','-qam','Peer expected correction');f.git(peer,'push','-q','origin',pr1.branch);
    }
    return execute(file,args,options);
  };
  const result=await f.done('check');
  assert.equal(changed,true,result.message);assert.equal(f.record().area,0);
  // The current full prompt pass can approve PR 1; it cannot approve entry with the later fetched contract.
  assert.equal(f.record().decisions.slice(decisions).filter(d=>d.via==='card-choice').length,0);
  assert.equal(f.record().branch,pr1.branch);assert.equal(f.prs.length,2);
});

test('2897 automatic: full current checks republish PR 1 and resume PR 2 under the same claim',async t=>{
  const f=await preparedCard(t),old=f.record();
  const peer=join(f.base,'main-peer');f.git(f.base,'clone','-q',f.remote,peer);
  f.git(peer,'config','user.name','Peer');f.git(peer,'config','user.email','peer@example.invalid');
  writeFileSync(join(peer,'upstream.md'),'Current main context.\n');
  f.git(peer,'add','.');f.git(peer,'commit','-qm','Current main');f.git(peer,'push','-q','origin','main');
  const upstream=f.git(peer,'rev-parse','HEAD'),origin=delegate(f);
  assert.equal((await open(f)).exitCode,0);
  assert.equal(f.record().branch,old.pr[0].branch);
  assert.equal(f.git(old.root,'merge-base','HEAD',upstream),upstream);correctPrompt(f);f.prompts.length=0;
  await f.done('check');assert.equal(f.record().area,1);
  await f.check();const published=await f.done('check');
  const run=f.record();assert.equal(run.area,2,published.message);assert.deepEqual(run.automaticOrigin,origin);
  assert.equal(run.pr[0].url,old.pr[0].url);assert.equal(run.pr[1].url,old.pr[1].url);
  assert.equal(f.prompts.length,0);assert.equal(run.done.verify,undefined);
  assert.ok(run.decisions.some(d=>d.via==='prompt-reentry'&&d.evidence.basis.priorCodeApprovalId));
  writeFileSync(join(old.root,'value.mjs'),'export const value=3;\n');
  await f.done('build');await f.done('verify');
  assert.equal(f.prs.length,2);assert.equal(f.record().pr[1].url,old.pr[1].url);
  assert.equal(f.git(old.root,'merge-base','HEAD',upstream),upstream);
  assert.ok(f.prs[1].body.includes('prompt-reentry'));
  assert.equal(f.git(old.root,'diff',old.pr[0].branch,'--','*.prompt.md'),'');
});

for(const limitation of ['missing-action','strict'])test(`2897 automatic: ${limitation} cannot authorize automatic code reentry`,async t=>{
  const f=await preparedCard(t);delegate(f,{action:limitation!=='missing-action',strict:limitation==='strict'});
  await open(f);correctPrompt(f);await f.check();await f.done('check');
  if(f.record().done.try===undefined)await f.done('try');
  assert.equal(f.record().area,1);assert.equal(f.record().decisions.some(d=>d.via==='prompt-reentry'),false);
});

test('2897 automatic: a changed expected contract still needs its Story gate',async t=>{
  const f=await preparedCard(t),old=f.record();delegate(f);await open(f);
  const path=join(old.root,TEST),doc=JSON.parse(readFileSync(path));doc.steps[0].checks[0].value=950;
  writeFileSync(path,JSON.stringify(doc));const count=f.pushes.length;
  await f.done('check');assert.equal(f.record().area,0);assert.equal(f.pushes.length,count);
  await f.done('prompt-story');assert.equal(f.record().gate.kind,'approve');
});

test('2897 automatic: a later Story decision replaces old coverage before checked code continuation',async t=>{
  const f=await preparedCard(t),old=f.record();delegate(f);await open(f);
  const path=join(old.root,STORY);writeFileSync(path,readFileSync(path,'utf8')+'\n## What must not change\n\nThe order stays visible.\n');
  await f.done('check');assert.equal(f.record().area,0);await f.done('prompt-story');
  f.tick();const approval=await approveRun({ref:'17',cwd:f.source,said:'The revised Story is right.'},f.agentPorts());
  assert.equal(approval.exitCode,0,approval.message);assert.equal(f.record().area,1);
  await f.check();const out=await f.done('check');assert.equal(f.record().area,2,out.message);
  assert.equal(f.record().pr[1].url,old.pr[1].url);
});
