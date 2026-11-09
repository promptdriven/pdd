// Generated from prompts/test/autopilot-factory.prompt.md.
import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {proseSha256} from '../src/runtime-preflight.mjs';
import {scriptedAgent} from './helpers/factory/agent.mjs';
import {existsSync,readdirSync,readFileSync,writeFileSync,rmSync} from 'node:fs';
import {join} from 'node:path';
import {spawnSync} from 'node:child_process';
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
  w.herdr.workspaces=[];w.herdr.tabs=[];w.herdr.panes=[];
  w.coordinatorHerdr.workspaces=[];w.coordinatorHerdr.tabs=[];w.coordinatorHerdr.panes=[];w.time+=120000;
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
    if(!w.herdr.workspaces.length)await w.herdr.herdr(['workspace','create','--cwd',w.cwd,'--label','personal','--no-focus']);
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
  assert.notEqual(out.code,0,'claim-transfer-open: the old coordinator can still open its current chat after another machine takes the claim');
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
  // No approved contract or path inventory is available to reconstruct coverage.
  for(const decision of old.decisions){delete decision.storyCoverage;delete decision.storyContract;delete decision.storyPaths;}
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

test('factory 9: base refresh retains failed evidence and reaches merge without a defect repair (#3116)',async t=>{
  const w=await factoryWorld(t);
  put(w.cwd,'base-ready.mjs','export const ready = false;\n');
  put(w.cwd,'test/base.test.mjs',"import {ready} from '../base-ready.mjs';import assert from 'node:assert/strict';assert.equal(ready,true,'FACTORY_BASE_READY');\n");
  w.git(w.cwd,'add','.');w.git(w.cwd,'commit','-qm','Synthetic base validation defect');w.git(w.cwd,'push','-q',w.remote,'main');
  w.git(w.cwd,'fetch','-q',w.remote,'main:refs/remotes/origin/main');
  await w.begin();const a=scriptedAgent(w);
  await a.until(r=>r.area===1);
  put(w.record().root,'value.mjs','export const value = 2;\n');
  w.git(w.record().root,'add','.');w.git(w.record().root,'commit','-qm','Retain issue patch before validation');
  await a.until(r=>Boolean(r.done.verify));
  const baseCheck=['workflow','suite','--command','node --test test/base.test.mjs'];
  const nativeFailure=spawnSync(process.execPath,['--test','test/base.test.mjs'],{cwd:w.record().root,env:w.env,encoding:'utf8'});
  assert.equal(nativeFailure.status,1);assert.match(nativeFailure.stdout+nativeFailure.stderr,/FACTORY_BASE_READY/);
  const failed=await w.command(baseCheck,{cwd:w.record().root,allowFailure:true});
  assert.equal(failed.code,1);
  const failedTicket=queueRows(w.env.PDD_SUITE_QUEUE).at(-1);
  assert.equal(failedTicket.state,'finished');assert.match(failedTicket.reason,/status 1\b/);
  await w.command(['workflow','done','verify','--summary','Failed base validation; retain this evidence'],{cwd:w.record().root});
  await w.command(['workflow','done','formal','--summary','Formal validation needs the current base'],{cwd:w.record().root});
  const before=w.record(),issue=w.git(before.root,'show','HEAD:value.mjs');
  put(w.cwd,'base-only.txt','Unrelated base integration\n');w.git(w.cwd,'add','.');w.git(w.cwd,'commit','-qm','Advance synthetic base');
  put(w.cwd,'base-ready.mjs','export const ready = true;\n');w.git(w.cwd,'add','.');w.git(w.cwd,'commit','-qm','Correct the synthetic base validation');
  w.git(w.cwd,'push','-q',w.remote,'main');w.git(w.cwd,'fetch','-q',w.remote,'main:refs/remotes/origin/main');
  w.git(before.root,'merge','--no-edit','refs/remotes/origin/main');
  await w.command(['workflow','done','change','--summary','Integrate the saved base'],{cwd:before.root});
  const refreshed=w.record();
  assert.equal(w.git(before.root,'show','HEAD:value.mjs'),issue);
  assert.equal(refreshed.repairRounds,undefined,'G24 base-only refresh consumed a defect repair');
  assert.deepEqual(refreshed.integrationRounds,{build:1});
  assert.equal(refreshed.done.verify,undefined);assert.equal(refreshed.done.formal,undefined);
  assert.ok(refreshed.stepHistory.some(row=>row.step==='verify'&&row.record.summary===before.done.verify.summary));
  assert.equal((await w.command(baseCheck,{cwd:before.root})).code,0);
  assert.deepEqual(readJson(join(w.env.PDD_SUITE_QUEUE,`ticket-${failedTicket.ticket}.json`)),failedTicket,
    'the persisted failed result survives a succeeding command');
  await a.finish();assert.equal(w.record().repairRounds,undefined);
  assert.notEqual(w.record().done.verify.worktreeSha256,before.done.verify.worktreeSha256);
  await a.merge();assert.deepEqual(w.leadActions,[]);
});

test('factory interpreter: a refused check remains a refusal and sends nothing on timer ticks',async t=>{
  const w=await factoryWorld(t,{workflow:'bug'});await w.begin();const a=scriptedAgent(w);await a.until(r=>r.area===1);
  w.interpreter.mode='refused';const refused=await a.step();assert.notEqual(refused.check.code,0);
  const report=JSON.parse(refused.check.stdout);assert.equal(report.rows[0].state,'refused');
  await w.command(['workflow','park','--interpreter','--reason','Interpreter refused the request; no verdict.'],{cwd:w.record().root});
  const posts=w.interpreter.posts.length;await w.tick();await w.tick();
  assert.equal(w.interpreter.posts.length,posts);assert.equal(w.github.prs.length,0);assert.equal(w.record().parking?.blocker?.kind,'interpreter');assert.deepEqual(w.leadActions,[]);
});


test('factory 9: automatic merge starts a fresh audit and saves its verdict once',async t=>{
  const w=await factoryWorld(t);await w.begin();const a=scriptedAgent(w);await a.finish();await a.merge();
  const pr=w.github.prs[0];
  await w.tick();w.messages();
  assert.ok(w.packets.some(p=>p.timeRules?.some(r=>r.kind==='post-merge-audit' && r.number===17 && r.pr===pr.number)),'closed issue merge must remain offered for audit');
  await w.command(['autopilot','audit','17',String(pr.number)],{actor:'coordinator'});
  const saved=readJson(join(w.record().runDir,'audits',`${pr.number}.json`));
  assert.equal(saved.result.verdict,'OK');assert.equal(saved.merge,pr.mergeCommit.oid);assert.equal(saved.comment.state,'sent');
  assert.equal(w.auditCalls.length,1);assert.equal(w.auditCalls[0].observations[0].code,1);assert.equal(w.auditCalls[0].observations[1].code,0);
  assert.ok(!w.record().chats.some(c=>c.session?.id===saved.chat.session.id));
  const before=w.github.issues.get(17).comments.length;
  await w.command(['autopilot','audit','17',String(pr.number)],{actor:'coordinator'});
  assert.equal(w.auditCalls.length,1);assert.equal(w.github.issues.get(17).comments.length,before);assert.deepEqual(w.leadActions,[]);
});


test('factory 10: BAD audit creates a real revert PR and never changes the base',async t=>{
  const w=await factoryWorld(t);await w.begin();const a=scriptedAgent(w);await a.finish();await a.merge();
  const merged=w.git(w.remote,'rev-parse','main');w.auditVerdict='BAD';
  await w.command(['autopilot','audit','17',String(w.github.prs[0].number)],{actor:'coordinator'});
  const saved=readJson(join(w.record().runDir,'audits',`${w.github.prs[0].number}.json`)),revert=w.github.prs[1];
  assert.equal(saved.result.verdict,'BAD');assert.equal(saved.revert.state,'sent');assert.equal(revert.state,'OPEN');assert.equal(revert.baseRefName,'main');
  assert.match(revert.headRefName,/^pdd\/revert-/);assert.equal(w.git(w.remote,'rev-parse','main'),merged);
  assert.equal(w.git(w.remote,'show',`${revert.headRefName}:value.mjs`),'export const value = 1;');assert.equal(w.alerts.filter(a=>a.kind==='decision').length,1);
  await w.command(['autopilot','audit','17',String(w.github.prs[0].number)],{actor:'coordinator'});
  assert.equal(w.github.prs.length,2);assert.equal(w.auditCalls.length,1);assert.equal(w.alerts.filter(a=>a.kind==='decision').length,1);assert.deepEqual(w.leadActions,[]);
});


test('factory 11: damaged audit evidence holds while new work is delivered',async t=>{
  const w=await factoryWorld(t);await w.begin();const a=scriptedAgent(w);await a.finish();await a.merge();
  const pr=w.github.prs[0];
  await w.command(['autopilot','audit','17',String(pr.number)],{actor:'coordinator'});
  const comments=w.github.issues.get(17).comments.length;
  writeFileSync(join(w.record().runDir,'audits',`${pr.number}.json`),'{');
  const held=await w.command(['autopilot','audit','17',String(pr.number)],{actor:'coordinator',allowFailure:true});
  assert.equal(held.code,1);assert.equal(w.auditCalls.length,1);
  w.messages();const before=w.packets.length;
  w.github.add(18,{title:'Next value task',body:'Inspect the value.',created:w.time,updated:w.time});
  for(let attempt=0;attempt<2;attempt++) {
    const tick=await w.command(undefined,{operation:'tick',actor:'timer',allowFailure:true})
      .catch(error=>({code:1,stderr:error.message}));
    assert.equal(tick.code,0,'AUDIT_SCAN_INTAKE: damaged audit must allow the tick to complete');
    await w.reviewDependencies();
  }
  w.messages();const packets=w.packets.slice(before);
  assert.ok(packets.some(p=>p.issues.some(i=>i.number===18 && i.eligible)),
    'AUDIT_SCAN_INTAKE: damaged audit must allow selection and coordinator delivery');
  assert.ok(packets.every(p=>!p.timeRules?.some(r=>r.kind==='post-merge-audit' && r.number===17 && r.pr===pr.number)));
  assert.deepEqual(w.state().auditHolds,[{number:17,pr:pr.number,cause:'audit-evidence-invalid'}]);
  const status=await w.command(['autopilot','status'],{actor:'operator'});
  assert.match(status.stdout,/audit-evidence-invalid/);
  assert.equal(w.auditCalls.length,1);assert.equal(w.github.issues.get(17).comments.length,comments);
  assert.deepEqual(w.leadActions,[]);
});

test('factory 12: stopped legacy runs free a full shared budget for a second repository and resume their sessions',async t=>{
  const w=await factoryWorld(t,{workflow:'bug'});await w.begin();
  const readRecord=w.record,held=[];
  for(const number of [17,18]) {
    if(number===18) {
      w.github.add(18,{title:'Use value two in another run',body:'The value must be 2.',created:w.time-1000,updated:w.time});
      await w.begin({number});
    }
    w.record=()=>readRecord(number);
    await scriptedAgent(w).until(r=>r.area===2);
    const r=w.record();assert.equal(r.chats.length,3);
    const sessions=r.chats.map(c=>w.herdr.sessions.find(s=>s.root===r.root&&s.at>=c.startedAt)?.id);
    assert.ok(sessions.every(Boolean));
    held.push({number,run:r,sessions});
  }
  w.record=readRecord;
  for(const {number} of held) {
    const r=readRecord(number);
    await w.command(['workflow','ask','Choose the next factory action'],{cwd:r.root});
    await w.command(['workflow','park','--reason','Wait for the factory reply','--blocker','person'],{cwd:r.root});
    const stopped=readRecord(number);
    for(const c of stopped.chats) {c.session=null;w.herdr.paneOf(c).agent=null;}
    delete stopped.layout.createdWorkspaceId;put(stopped.runDir,'status.json',stopped);
  }
  // Restarted local coordinator: claims still name this machine's previous owner.
  const state=w.state(),oldOwner=state.coordinatorId;state.coordinatorId='factory-restarted-coordinator';
  state.ownerLaunch.coordinator.coordinatorId=state.coordinatorId;put(w.stateRoot,state.stateFile.split('/').at(-1),state);
  const second=await factoryWorld(t,{repository:'example/second',shared:w});
  assert.equal(second.sessionName,w.sessionName);assert.match(w.sessionName,/^pdd-factory-/);
  second.time=w.time+120000;w.time=second.time;
  const foreign=await w.herdr.herdr(['workspace','create','--cwd',w.cwd,'--label','personal','--no-focus']);
  const busy=w.herdr.panes.find(p=>p.pane_id===foreign.result.root_pane.pane_id);
  busy.agent={agent:'codex',agent_status:'working',agent_session:{kind:'id',value:'aaaaaaaa-aaaa-4aaa-8aaa-aaaaaaaaaaaa'}};
  const budget=w.herdr.panes.length;
  w.env.PDD_HERDR_PANE_BUDGET=String(budget);second.env.PDD_HERDR_PANE_BUDGET=String(budget);
  w.herdr.paneLimit=budget;
  await second.start();
  assert.ok(second.state().paneId,'second-repository-coordinator-starts');
  for(const {number,run,sessions} of held) {
    const parked=readRecord(number);assert.equal(parked.parking?.phase,'parked',JSON.stringify({gap:'legacy-run-yields-shared-panes',number,state:parked.state,closed:parked.chats.map(c=>c.closed),origin:parked.automaticOrigin,secondWarnings:second.warnings,owner:w.state().coordinatorId}));
    assert.notEqual(parked.automaticOrigin.coordinatorId,oldOwner);
    assert.deepEqual(parked.automaticOrigin.claim,run.automaticOrigin.claim);
    assert.deepEqual(parked.chats.map(c=>c.session.id),sessions,'each-area-native-session-is-retained');
    assert.ok(parked.chats.every(c=>existsSync(c.closed.screen)));
  }
  assert.ok(w.herdr.panes.includes(busy),'foreign-busy-pane-survives');
  await second.begin();
  const first=second.record(),firstChat=first.chats.at(-1);
  assert.equal(first.state,'running','second-repository-first-workflow-starts');
  assert.ok(firstChat?.paneId);
  assert.equal(second.herdr.paneOf(firstChat)?.agent?.agent,'codex','second-repository-first-chat-is-live');
  for(const {number,run,sessions} of held) {
    await w.command(['workflow','changes',String(number),'Continue this factory run with its saved session.']);
    await w.tick();
    const resumed=readRecord(number);assert.notEqual(resumed.parking?.phase,'parked');
    assert.equal(resumed.chats.at(-1).session.id,sessions.at(-1),'right-session-resumes');
    assert.ok(w.herdr.panes.some(p=>p.cwd===run.root&&p.agent?.agent_session?.value===sessions.at(-1)),'native-resume-observed');
  }
  assert.ok(w.herdr.panes.includes(busy),'foreign-busy-pane-survives-resume');
  assert.deepEqual(w.leadActions,[]);assert.deepEqual(second.leadActions,[]);
});


test('factory 3125: fresh repo with stale PATH and no agent sign-in refuses start without effects',async t=>{
  const w=await factoryWorld(t);
  rmSync(join(w.base,'bin/pdd'));
  put(w.base,'bin/pdd','#!/bin/sh\nif [ "$1" = --version ]; then echo 0.1.15; else echo "pdd setup"; fi\n');
  const {chmodSync}=await import('node:fs');chmodSync(join(w.base,'bin/pdd'),0o700);
  const commands=w.github.commands.length,issues=JSON.stringify([...w.github.issues]),panes=w.herdr.panes.length;
  const opts={env:{PDD_FACTORY_DOCTOR:'1'},allowFailure:true};
  const doctor=await w.command(['autopilot','doctor'],opts);
  const start=await w.command(['autopilot','start'],opts);
  assert.equal(doctor.code,1,'doctor must diagnose stale PATH and missing agent sign-in');
  assert.match(doctor.stderr,/FAIL path:.*0\.1\.15.*; fix: .*autopilot doctor/);
  assert.match(doctor.stderr,/FAIL agent:.*; fix: .*codex.*login/);
  assert.equal(start.code,1,'preflight must refuse a first start');
  assert.equal(start.stderr,doctor.stderr,'start must use the same doctor report');
  assert.equal(existsSync(w.stateFile),false);assert.equal(existsSync(w.stateRoot),false);
  assert.equal(w.herdr.panes.length,panes);assert.equal(w.github.prs.length,0);
  assert.equal(JSON.stringify([...w.github.issues]),issues);assert.equal(w.interpreter.posts.length,0);
  const reads=w.github.commands.slice(commands);
  assert.ok(reads.every(({args})=>args[0]==='repo'||args[0]==='auth'||args[0]==='api'&&!args.includes('POST')));
  assert.ok(!existsSync(join(w.home,'.config/systemd')));
});


test('factory 3125: restart and doctor use the healthy saved profile with a signed-out caller',async t=>{
  const w=await factoryWorld(t);
  w.agentProfile=join(w.home,'original-profile');
  const env={CODEX_HOME:w.agentProfile};
  await w.command(['autopilot','start'],{env});
  const prior=w.state(),caller={CODEX_HOME:join(w.home,'signed-out-caller')};
  await w.command(['autopilot','doctor'],{env:caller});
  await w.command(['autopilot','start'],{env:caller});
  assert.equal(w.state().coordinatorId,prior.coordinatorId);
  assert.equal(w.state().environment.CODEX_HOME,w.agentProfile);
  assert.ok(w.doctorAccounts.length>=3);assert.ok(w.doctorAccounts.every(profile=>profile===w.agentProfile));
});

test('factory 3125: a full workflow session admits healthy coordinator reuse in its own session',async t=>{
  const w=await factoryWorld(t);await w.start();
  const prior=w.state();
  const personal=await w.herdr.herdr(['workspace','create','--cwd',w.cwd,'--label','personal','--no-focus']);
  const workflowPanes=structuredClone(w.herdr.panes),coordinatorPanes=structuredClone(w.coordinatorHerdr.panes);
  assert.ok(!w.herdr.panes.some(p=>p.pane_id===prior.paneId));
  assert.ok(w.coordinatorHerdr.panes.some(p=>p.pane_id===prior.paneId));
  const offset=w.herdrTransportCalls.length;
  await w.command(['autopilot','doctor'],{env:{PDD_HERDR_PANE_BUDGET:'1'}});
  assert.ok(!w.herdrTransportCalls.slice(offset).some(a=>a[1]==='pdd'&&a[2]==='pane'&&a[3]==='list'));
  await w.command(['autopilot','start'],{env:{PDD_HERDR_PANE_BUDGET:'1'}});
  assert.equal(w.state().paneId,prior.paneId);assert.equal(w.state().coordinatorId,prior.coordinatorId);
  assert.deepEqual(w.herdr.panes,workflowPanes);assert.deepEqual(w.coordinatorHerdr.panes,coordinatorPanes);
  assert.ok(w.herdr.panes.some(p=>p.pane_id===personal.result.root_pane.pane_id));
  assert.ok(w.herdrTransportCalls.slice(offset).some(a=>a[1]==='pdd-autopilot'&&a[2]==='agent'&&a[3]==='get'&&a[4]===prior.paneId));
});
