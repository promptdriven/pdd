// Generated from prompts/test/autopilot-factory.prompt.md.
import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {proseSha256} from '../src/runtime-preflight.mjs';
import {scriptedAgent} from './helpers/factory/agent.mjs';
import {existsSync,readdirSync,readFileSync} from 'node:fs';
import {join} from 'node:path';
import {factoryWorld,put,readJson,valuePrompt} from './helpers/factory/world.mjs';

for(const workflow of ['small-change','bug','feature'])test(`factory 1: ${workflow} reaches merge without lead action`,async t=>{
  const w=await factoryWorld(t,{workflow});await w.begin();
  const a=scriptedAgent(w);await a.finish();
  assert.equal(w.github.prs.length,workflow==='small-change'?1:2);
  if(workflow!=='small-change')assert.equal(w.github.prs[1].baseRefName,w.github.prs[0].headRefName,'PR 2 starts stacked on open PR 1');
  await a.merge();assert.equal(w.record().state,'completed');assert.deepEqual(w.leadActions,[]);
});

test('factory 2: machine restart retains claim, work and chat identity to merge',async t=>{
  const w=await factoryWorld(t,{workflow:'bug'});await w.begin();const a=scriptedAgent(w);
  await a.until(r=>Boolean(r.done.reproduce));await w.command(['workflow','status','17']);
  const before=w.record();assert.ok(before.chats.at(-1).session?.id,'register native session before restart');
  const allocations=readdirSync(join(w.commonDir,'pdd/worktree-assignments/runs')).length,publications=w.github.prs.length;
  const claim=w.github.issues.get(17).comments.find(c=>c.body.includes('coordinatorId'));
  w.herdr.workspaces=[];w.herdr.tabs=[];w.herdr.panes=[];w.time+=120000;
  await w.tick();await w.tick();
  const after=w.record();
  assert.equal(readdirSync(join(w.commonDir,'pdd/worktree-assignments/runs')).length,allocations);assert.equal(w.github.prs.length,publications);
  assert.equal(after.runId,before.runId);assert.equal(after.root,before.root);assert.deepEqual(after.done,before.done);
  assert.equal(after.chats.at(-1).session.id,before.chats.at(-1).session.id,'GAP restart lost the native session');
  assert.equal(w.github.issues.get(17).comments.filter(c=>c.body.includes('coordinatorId')).length,1);
  assert.equal(w.github.issues.get(17).comments.find(c=>c.id===claim.id).id,claim.id);
  assert.ok(w.herdr.panes.some(p=>p.cwd===after.root && p.agent),'GAP restart did not resume the worker');
  await a.finish();await a.merge();assert.deepEqual(w.leadActions,[]);
});

test('factory 3: lost verdict holds through ticks; one person-approved resend reaches merge',async t=>{
  const w=await factoryWorld(t,{workflow:'bug'});await w.begin();const a=scriptedAgent(w);
  await a.until(r=>r.area===1);w.interpreter.mode='no-verdict';
  const lost=await a.step();assert.notEqual(lost.check.code,0);
  const batch=JSON.parse(lost.check.stdout).batch;
  await w.command(['workflow','status','17']);
  await w.command(['workflow','park','--interpreter','--reason',`Interpreter batch ${batch}: runner-stopped; no verdict.`],{cwd:w.record().root});
  const sent=w.interpreter.posts.filter(p=>p.command==='check').length;
  await w.tick();await w.tick();assert.equal(w.interpreter.posts.filter(p=>p.command==='check').length,sent);
  assert.equal(w.record().parking?.blocker?.kind,'interpreter',JSON.stringify({warnings:w.warnings,run:{state:w.record().state,origin:w.record().automaticOrigin,source:w.record().sourceRoot,chats:w.record().chats.map(c=>({area:c.area,session:c.session,state:c.state,closed:c.closed})),runtime:w.record().runtimeWait},state:{parking:w.state().parking,cwd:w.state().cwd,coordinatorId:w.state().coordinatorId,machine:w.state().machine}}));
  assert.ok(w.alerts.some(a=>a.kind==='decision'),'GAP lost verdict needs a person decision, without a lead prompt');
  w.interpreter.mode='verdict';
  const decision=await w.command(['workflow','resend','17','--said','-'],{actor:'person',stdin:'Resend the lost factory check once with its saved call cap.'});
  assert.equal(w.record().checkResends.at(-1).state,'verdict');assert.equal(w.interpreter.posts.filter(p=>p.command==='check').length,sent+1);
  a.checks.push(decision);await w.tick();
  await w.command(['workflow','done','check','--summary','Prompt tests: 1 of 1 pass; person-approved resend receipt retained'],{cwd:w.record().root});
  await a.finish();assert.equal(w.interpreter.posts.filter(p=>p.command==='check').length,sent+1);await a.merge();assert.equal(w.commands.filter(c=>c.actor==='person').length,1);assert.deepEqual(w.leadActions,[]);
});

test('factory 4: stuck run parks and its merged dependency wakes it to merge',async t=>{
  const w=await factoryWorld(t);await w.begin();const a=scriptedAgent(w);await a.until(r=>r.area===1);
  w.github.add(18,{title:'Dependency',body:'Provide the prerequisite.',created:w.time-1000,updated:w.time});
  await w.command(['workflow','status','17']);
  await w.command(['workflow','park','--reason','Waiting for issue #18 to merge','--blocker','dependency','--until','18'],{cwd:w.record().root});
  const before=w.record();await w.tick();
  assert.equal(w.record().parking?.phase,'parked',JSON.stringify({warnings:w.warnings,run:{state:w.record().state,origin:w.record().automaticOrigin,source:w.record().sourceRoot,chats:w.record().chats.map(c=>({area:c.area,session:c.session,state:c.state,closed:c.closed})),runtime:w.record().runtimeWait},state:{parking:w.state().parking,cwd:w.state().cwd,coordinatorId:w.state().coordinatorId,machine:w.state().machine}}));assert.equal(w.record().parking.blocker.kind,'dependency');
  assert.ok(!w.herdr.panes.some(p=>p.cwd===before.root),'GAP parking must give worker panes back');
  w.github.close(18);
  const commit=w.git(w.remote,'rev-parse','main');
  w.github.prs.push({number:118,url:'https://github.com/example/project/pull/118',state:'MERGED',body:'Fixes #18',headRefName:'main',headRefOid:commit,baseRefName:'main',mergeCommit:{oid:commit}});
  w.github.issues.get(18).timeline.push({id:String(w.github.nextEvent++),event:'cross-referenced',actor:'example',created:w.time,source:{issue:{pull_request:{url:'https://api.github.com/repos/example/project/pulls/118'}}}});
  await w.tick();await w.tick();
  assert.ok(!w.record().parking || w.record().parking.phase!=='parked','GAP dependency merge did not wake the run');
  assert.deepEqual(w.record().done,before.done);await a.finish();await a.merge();assert.deepEqual(w.leadActions,[]);
});

test('factory 5a: a full Herdr pane budget defers admission, then released room reaches merge',async t=>{
  const w=await factoryWorld(t);
  await w.begin({beforeRun:async()=>{
    const workspace=w.herdr.workspaces[0].workspace_id;
    for(let n=w.herdr.panes.length;n<56;n++) {
      w.herdr.tabs.push({tab_id:`occupied-t${n}`,workspace_id:workspace});
      w.herdr.panes.push({pane_id:`occupied-p${n}`,tab_id:`occupied-t${n}`,workspace_id:workspace,terminal_id:`occupied-term${n}`,cwd:w.cwd,agent:null});
    }
    w.herdr.paneLimit=56;
    const refused=await w.command(w.runArgs,{actor:'coordinator',env:w.context(),allowFailure:true});
    assert.notEqual(refused.code,0);assert.equal(w.github.prs.length,0);assert.ok(!existsSync(join(w.commonDir,'pdd/runs/17/status.json')));
    w.herdr.panes=w.herdr.panes.filter(p=>!p.pane_id.startsWith('occupied-'));w.herdr.tabs=w.herdr.tabs.filter(p=>!p.tab_id.startsWith('occupied-'));delete w.herdr.paneLimit;
  }});
  const a=scriptedAgent(w);await a.finish();await a.merge();assert.deepEqual(w.leadActions,[]);
});

test('factory 5b: full check slots queue the second suite and release admits it to merge',async t=>{
  const w=await factoryWorld(t);await w.begin();const a=scriptedAgent(w);await a.until(r=>Boolean(r.done.change));
  const release=join(w.base,'release'),started=join(w.base,'started');
  put(w.base,'hold.mjs',`import fs from 'node:fs';fs.writeFileSync(${JSON.stringify(started)},'started');const timer=setInterval(()=>{if(fs.existsSync(${JSON.stringify(release)}))clearInterval(timer);},10);`);
  t.after(()=>put(w.base,'release','release'));
  const holder=w.command(['workflow','suite','--command',`${JSON.stringify(process.execPath)} ${JSON.stringify(join(w.base,'hold.mjs'))}`],{actor:'other-worker',cwd:w.record().root});
  await eventually(()=>existsSync(started),'holder must start');
  const waiter=w.command(['workflow','suite','--command',`${JSON.stringify(process.execPath)} --test test/value.test.mjs`],{actor:'worker',cwd:w.record().root});
  await eventually(()=>queueRows(w.env.PDD_SUITE_QUEUE).some(r=>r.state==='waiting'),'second suite must wait');
  assert.equal(queueRows(w.env.PDD_SUITE_QUEUE).filter(r=>r.state==='running').length,1);
  put(w.base,'release','release');await holder;await waiter;
  assert.ok(queueRows(w.env.PDD_SUITE_QUEUE).every(r=>r.state==='finished'));
  await a.finish();await a.merge();assert.deepEqual(w.leadActions,[]);
});

test('factory 5c: a dead interpreter queue holder is reclaimed before checking and merging',async t=>{
  const w=await factoryWorld(t,{workflow:'feature'});await w.begin();const a=scriptedAgent(w);await a.until(r=>r.area===1);
  await w.command(undefined,{operation:'hold-interpreter',actor:'other-worker'});
  const holder=queueRows(w.env.PDD_INTERPRETER_QUEUE).find(r=>r.requestId==='dead-holder');assert.equal(holder.state,'running');
  await a.finish();
  const recovered=queueRows(w.env.PDD_INTERPRETER_QUEUE).find(r=>r.requestId==='dead-holder');
  assert.equal(recovered.state,'finished');assert.equal(recovered.releaseReason,'owner-dead');assert.equal(recovered.outcome,'not_sent');
  await a.merge();assert.deepEqual(w.leadActions,[]);
});

test('factory 5d: a dead dispatched holder records uncertainty without resending it',async t=>{
  const w=await factoryWorld(t,{workflow:'bug'});await w.begin();const a=scriptedAgent(w);await a.until(r=>r.area===1);
  await w.command(undefined,{operation:'hold-interpreter-dispatched',actor:'other-worker'});
  await a.finish();
  const recovered=queueRows(w.env.PDD_INTERPRETER_QUEUE).find(r=>r.requestId==='dead-holder');
  assert.equal(recovered.dispatched,true);assert.equal(recovered.state,'finished');assert.equal(recovered.outcome,'unknown');
  assert.ok(w.interpreter.posts.every(p=>p.request.requestId!=='dead-holder'),'queue recovery cannot resend the uncertain request');
  await a.merge();assert.deepEqual(w.leadActions,[]);
});

test('factory 6: another machine takes the claim; the old worker cannot publish',async t=>{
  const w=await factoryWorld(t);await w.begin();const a=scriptedAgent(w);await a.until(r=>r.area===1);
  const before=w.record();w.github.unlabel(17,'pdd:working');w.github.claim(17,{coordinatorId:'another-coordinator',machine:'another-machine'});
  const out=await w.command(['workflow','open','17'],{actor:'old-coordinator',allowFailure:true});
  const replacement=await w.command(['workflow','open','17','--new'],{actor:'old-coordinator',allowFailure:true});
  assert.notEqual(replacement.code,0,'replacement launch must reject the changed claim');
  assert.match(replacement.stderr+replacement.stdout,/ownership|claim/i);
  let publication;
  for(let n=0;n<4;n++){const result=await a.step({allowFailure:true});if(result?.refused){publication=result.refused;break;}}
  assert.ok(publication,'publication must reject the changed claim');assert.match(publication.stderr+publication.stdout,/ownership|claim/i);
  await w.tick();assert.equal(w.github.prs.length,0);assert.equal(w.record().runId,before.runId);
  assert.equal(w.github.issues.get(17).comments.filter(c=>c.body.includes('another-coordinator')).length,1);assert.deepEqual(w.leadActions,[]);
  // Keep this candidate finding red even though publication has its own guard.
  assert.notEqual(out.code,0,'GAP claim-transfer-open: the old coordinator can still open its current chat after another machine takes the claim');
});

async function eventually(check,message) {
  for(let n=0;n<500;n++){if(check())return;await new Promise(r=>setTimeout(r,10));}
  assert.fail(message);
}
function queueRows(root) {return existsSync(root)?readdirSync(root).filter(p=>/^ticket-\d+\.json$/.test(p)).map(p=>readJson(join(root,p))):[];}

test('factory 7: PR 1 changes after code starts; supported re-entry rebuilds and merges (#2897)',async t=>{
  const w=await factoryWorld(t,{workflow:'bug'});await w.begin();const a=scriptedAgent(w);
  await a.until(r=>Boolean(r.done.build));
  const before=w.record(),pr1=w.github.prs[0],oldHead=pr1.headRefOid;
  w.git(before.root,'add','.');w.git(before.root,'commit','-qm','Retain implementation before prompt review');
  await w.command(['workflow','open','17','prompt-pr'],{actor:'worker'});
  assert.equal(w.record().branch,before.pr[0].branch);assert.equal(w.record().done.build,undefined);
  const returnedPrompt=valuePrompt(2).replace('Return the value 2.','Return the value 2. Keep the result stable on repeated calls.');
  const expectedProse=proseSha256(returnedPrompt);put(before.root,'value.prompt.md',returnedPrompt);
  await w.command(['test','--fill-hash'],{cwd:before.root});
  await a.until(r=>r.area===2);
  assert.notEqual(w.github.prs[0].headRefOid,oldHead);assert.equal(w.github.prs[0].url,pr1.url);
  assert.equal(w.git(before.root,'diff',before.pr[0].branch,'--','value.prompt.md'),'');
  await a.finish();assert.equal(w.github.prs.length,2);assert.equal(proseSha256(readFileSync(join(before.root,'value.prompt.md'),'utf8')),expectedProse);
  await a.merge();assert.equal(proseSha256(w.git(w.remote,'show','main:value.prompt.md')+'\n'),expectedProse);assert.deepEqual(w.leadActions,[]);
});

test('factory 8: a pre-card persisted run continues after upgrade without lead action',async t=>{
  const w=await factoryWorld(t,{workflow:'feature'});await w.begin();const a=scriptedAgent(w);
  await a.until(r=>r.area===1);
  // Serialize the additive-field omissions of the repository's legacy fixture.
  // Retain actual decisions; this does not create or grant any approval.
  const old=w.record();delete old.storyApproval;
  for(const decision of old.decisions)delete decision.storyCoverage;
  old.metricsOrigin.cliVersion='0.1.20';old.metricsOrigin.skillVersion='0.1.20';
  put(old.runDir,'status.json',old);
  const prior=old.decisions.map(d=>({gateId:d.gateId,evidence:d.evidence}));
  await a.until(r=>r.gate?.kind==='approve-pr');
  await w.tick();assert.equal(w.github.prs.length,0,'legacy coverage alone must not open PR 1');assert.equal(w.record().gate?.kind,'approve-pr');
  await a.finish();
  assert.deepEqual(w.record().decisions.slice(0,prior.length).map(d=>({gateId:d.gateId,evidence:d.evidence})),prior);
  await a.merge();assert.deepEqual(w.leadActions,[]);
});

test('factory interpreter: slow verdict completes the feature to merge',async t=>{
  const w=await factoryWorld(t,{workflow:'feature'});w.interpreter.mode='slow';await w.begin();const a=scriptedAgent(w);
  await a.finish();assert.ok(w.interpreter.gets.length>=3);await a.merge();assert.deepEqual(w.leadActions,[]);
});

test('factory interpreter: a refused check remains a refusal and sends nothing on timer ticks',async t=>{
  const w=await factoryWorld(t,{workflow:'bug'});await w.begin();const a=scriptedAgent(w);await a.until(r=>r.area===1);
  w.interpreter.mode='refused';const refused=await a.step();assert.notEqual(refused.check.code,0);
  const report=JSON.parse(refused.check.stdout);assert.equal(report.rows[0].state,'refused');
  await w.command(['workflow','park','--interpreter','--reason','Interpreter refused the request; no verdict.'],{cwd:w.record().root});
  const posts=w.interpreter.posts.length;await w.tick();await w.tick();
  assert.equal(w.interpreter.posts.length,posts);assert.equal(w.github.prs.length,0);assert.equal(w.record().parking?.blocker?.kind,'interpreter');assert.deepEqual(w.leadActions,[]);
});
