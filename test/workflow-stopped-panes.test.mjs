import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {existsSync, mkdirSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture} from './helpers/workflow-runner-fixture.mjs';
import {ownSession, ensurePaneBudget} from '../src/workflow-chat.mjs';
import {parkBlockedRun, sweepIdleRuns, tidyRuns, runStatus, resumeStoppedRun} from '../src/workflow-runner.mjs';
const ids=['11111111-1111-4111-8111-111111111111','22222222-2222-4222-8222-222222222222','33333333-3333-4333-8333-333333333333'];
const save=(f,r)=>writeFileSync(join(r.runDir,'status.json'),JSON.stringify(r));
async function stopped(t) {
  const f=await fixture(t,{agent:'codex',name:'bug'});await f.run();
  const r=f.record(), first=r.chats[0];f.herdr.sessions=[];
  first.session=null;first.state='ended';f.herdr.paneOf(first).agent=null;
  f.herdr.sessions.push({agent:'codex',root:r.root,at:first.startedAt,id:ids[0]});
  for(let i=1;i<3;i++) {
    f.tick(1000);
    const reply=await f.herdr.herdr(['tab','create','--workspace',r.layout.workspaceId,'--cwd',r.root,'--label',r.areas[i].name,'--no-focus']);
    const p=reply.result.root_pane;
    r.chats.push({...first,area:r.areas[i].name,startedAt:f.clock,tabId:reply.result.tab.tab_id,paneId:p.pane_id,terminalId:p.terminal_id});
    f.herdr.sessions.push({agent:'codex',root:r.root,at:f.clock,id:ids[i]});
  }
  r.area=2;r.state='paused';r.blockedOn={kind:'pdd',until:'capability:fixture-fix'};
  r.automaticOrigin={repository:r.repo,coordinatorId:'current',machine:'fixture',claim:{commentId:'11',labelEventId:'12'}};
  delete r.layout.createdWorkspaceId;save(f,r);f.tick(120000);
  f.ports.autopilotStateFile=join(f.state,'owner.json');
  writeFileSync(f.ports.autopilotStateFile,JSON.stringify({enabled:true,cwd:r.sourceRoot,repo:r.repo,coordinatorId:'current',machine:'fixture'}));
  return {f,r};
}
test('3123 bounded discovery proves every area in one worktree',async t=>{
  const {f,r}=await stopped(t);
  for(const [i,chat] of r.chats.entries())assert.deepEqual(await ownSession({run:r,chat,since:chat.startedAt,ports:f.ports}),{kind:'match',id:ids[i]},'older-area-session-window');
});
test('3123 session discovery respects its own end and next resume',async t=>{
  const {f,r}=await stopped(t),chat=r.chats[0];
  r.chats[1].resumedAt=chat.startedAt+500;r.chats[1].startedAt=chat.startedAt-500;
  f.herdr.sessions.push({agent:'codex',root:r.root,at:chat.startedAt+500,id:ids[1]});
  assert.deepEqual(await ownSession({run:r,chat,since:chat.startedAt,ports:f.ports}),{kind:'match',id:ids[0]});
  chat.endedAt=chat.startedAt-1;
  assert.notEqual((await ownSession({run:r,chat,since:chat.startedAt,ports:f.ports})).kind,'match');
});
test('3123 park discovers all IDs, adopts old layout and captures before close',async t=>{
  const {f,r}=await stopped(t),herdr=f.ports.herdr;
  f.ports.herdr=async args=>{
    if(args[0]==='tab'&&args[1]==='close') {
      const chat=f.record().chats.find(c=>c.tabId===args[2]);
      assert.ok(existsSync(chat.closed.screen),'screen-before-close');assert.ok(chat.session?.id);
      assert.equal(f.record().layout.createdWorkspaceId,r.layout.workspaceId);
    }
    return herdr(args);
  };
  const result=await parkBlockedRun({ref:'17',cwd:f.source,coordinatorId:'current',machine:'fixture',blocker:r.blockedOn},f.ports);
  assert.equal(result.recovery,'parked','stopped-run-reclaims-panes');
  assert.deepEqual(f.record().chats.map(c=>c.session.id),ids);
  assert.ok(!f.herdr.panes.some(p=>p.workspace_id===r.layout.workspaceId));
});
for(const guard of ['current-session','busy','foreign-label','foreign-path','explicit-foreign-owner','screen','screen-write'])test(`3123 partial park keeps unsafe custody: ${guard}`,async t=>{
  const {f,r}=await stopped(t),current=r.chats.at(-1),pane=f.herdr.paneOf(current);
  if(guard==='current-session')f.herdr.sessions=f.herdr.sessions.filter(s=>s.id!==ids[2]);
  if(guard==='busy')pane.agent={agent:'codex',agent_status:'working',agent_session:{kind:'id',value:ids[2]}};
  const w=f.herdr.workspaces.find(w=>w.workspace_id===r.layout.workspaceId);
  if(guard==='foreign-label')w.label='personal';
  if(guard==='foreign-path')w.worktree.checkout_path=f.source;
  if(guard==='explicit-foreign-owner'){r.layout.createdWorkspaceId='other';save(f,r);}
  if(guard==='screen-write') {mkdirSync(join(r.runDir,'chats'),{recursive:true});mkdirSync(join(r.runDir,'chats',`${current.area}-${current.startedAt}.txt`));}
  if(guard==='screen') {const h=f.ports.herdr;f.ports.herdr=async a=>{if(a[0]==='pane'&&a[1]==='read')throw Error('screen unavailable');return h(a);};}
  const result=await parkBlockedRun({ref:'17',cwd:f.source,coordinatorId:'current',machine:'fixture',blocker:r.blockedOn},f.ports);
  assert.equal(result.recovery,'skipped');assert.ok(f.herdr.paneOf(current),'unsafe-pane-survives');
  assert.ok(Object.keys(result.reasonCounts??{}).length,'retained-reason-counts');
  if(guard==='current-session'||guard==='busy')assert.equal(f.record().chats.filter(c=>c.closed?.confirmedAt).length,2,'safe-finished-chats-close-independently');
});
test('3123 finished area can close with screen when no session can be proved',async t=>{
  const {f,r}=await stopped(t);f.herdr.sessions=f.herdr.sessions.filter(s=>s.id!==ids[0]);
  const result=await parkBlockedRun({ref:'17',cwd:f.source,coordinatorId:'current',machine:'fixture',blocker:r.blockedOn},f.ports);
  assert.equal(result.recovery,'parked');assert.ok(existsSync(f.record().chats[0].closed.screen));assert.equal(f.record().chats[0].session,null);
});
test('3123 tidy persists discovered IDs and reports retained counts',async t=>{
  const {f,r}=await stopped(t);r.state='completed';save(f,r);f.tick(16*60000);
  f.herdr.sessions=f.herdr.sessions.filter(s=>s.id!==ids[1]);
  const result=await tidyRuns({},f.ports);
  assert.equal(result.closed,3,'finished-sessionless-chat-screen-close');assert.equal(result.kept,0);
  assert.equal(f.record().chats[0].session.id,ids[0]);
});
test('3123 pane budget reports retained reasons from the latest sweeps',async()=>{
  const panes=[{pane_id:'p',workspace_id:'w',tab_id:'t',terminal_id:'term'}];
  await assert.rejects(ensurePaneBudget(1,{env:{PDD_HERDR_PANE_BUDGET:'1'},herdr:async()=>({result:{type:'pane_list',panes}}),
    sweepFinished:async()=>({closed:0,reasonCounts:{'no-saved-session':2}}),sweepIdle:async()=>({closed:0,reasonCounts:{'not-pdd-created':1}})}),e=>e.code==='herdr_pane_budget'&&/no-saved-session 2/.test(e.message)&&/not-pdd-created 1/.test(e.message));
});
test('3123 admission sweep adopts the older coordinator only after claim recovery',async t=>{
  const {f,r}=await stopped(t);r.automaticOrigin.coordinatorId='old';save(f,r);
  let recoveries=0;f.ports.recoverCoordinatorClaim=async input=>{recoveries++;assert.equal(input.claim.coordinatorId,'old');return {state:'recovered'};};
  const result=await sweepIdleRuns({graceMs:0},f.ports);
  assert.equal(recoveries,1,'older-owner-enters-recovery');assert.equal(f.record().automaticOrigin.coordinatorId,'current');
  assert.equal(f.record().parking.phase,'parked');assert.equal(result.closed,3);
});
test('3123 unknown old claim stays visible and retries without adoption',async t=>{
  const {f,r}=await stopped(t);r.automaticOrigin.coordinatorId='old';save(f,r);
  f.ports.recoverCoordinatorClaim=async()=>({state:'skipped'});f.ports.owners={read:async()=>{throw Error('offline');}};
  const result=await sweepIdleRuns({graceMs:0},f.ports);
  assert.equal(f.record().automaticOrigin.coordinatorId,'old');assert.equal(result.reasonCounts?.['claim-unavailable'],1);
  assert.ok(f.herdr.paneOf(r.chats.at(-1)));
});

test('3123 status saves positive native evidence for older and already ended chats',async t=>{
  const {f,r}=await stopped(t);
  assert.equal((await runStatus({ref:'17',cwd:f.source},f.ports)).exitCode,0);
  assert.deepEqual(f.record().chats.map(c=>c.session?.id),ids,'observed-ids-are-durable');
});
test('3123 old coordinator with a transferred claim uses normal handover cleanup',async t=>{
  const {f,r}=await stopped(t);r.automaticOrigin.coordinatorId='old';save(f,r);
  f.ports.recoverCoordinatorClaim=async()=>({state:'skipped'});
  f.ports.owners={read:async()=>({json:JSON.stringify({localOwner:'current',claims:[{issue:r.issue.url,active:true,owner:'remote',coordinatorId:'remote',machine:'another-machine',commentId:'13',labelEventId:'14'}]})})};
  await sweepIdleRuns({graceMs:0},f.ports);
  assert.equal(f.record().state,'cancelled','transferred-old-run-is-not-orphaned');
  assert.equal(f.record().cancelled.state,'handed-over');assert.equal(f.record().automaticOrigin.coordinatorId,'old');
});
test('3123 parking rechecks busy status after the screen checkpoint',async t=>{
  const {f,r}=await stopped(t),herdr=f.ports.herdr,current=r.chats.at(-1);
  f.ports.herdr=async args=>{
    if(args[0]==='agent'&&args[1]==='get'&&args[2]===current.paneId&&f.record().chats.at(-1).closed)
      f.herdr.paneOf(current).agent={agent:'codex',agent_status:'working',agent_session:{kind:'id',value:ids[2]}};
    return herdr(args);
  };
  const result=await parkBlockedRun({ref:'17',cwd:f.source,coordinatorId:'current',machine:'fixture',blocker:r.blockedOn},f.ports);
  assert.equal(result.reasonCounts?.['agent-busy'],1,'late-busy-agent-survives');assert.ok(f.herdr.paneOf(current));
});
test('3123 finished cleanup preserves legacy idle grace for the following parking sweep',async t=>{
  const {f,r}=await stopped(t);assert.equal(r.progressAt,undefined);
  assert.equal((await tidyRuns({graceMs:0},f.ports)).closed,2);
  assert.equal(f.record().progressAt,r.updatedAt,'maintenance-is-not-worker-progress');
  await sweepIdleRuns({graceMs:60000},f.ports);
  assert.equal(f.record().parking?.phase,'parked','cleanup-does-not-restart-idle-grace');
});
for(const claim of ['absent','superseded'])test(`3123 older owner releases a proven ${claim} claim and keeps busy work`,async t=>{
  const {f,r}=await stopped(t);r.automaticOrigin.coordinatorId='old';save(f,r);
  const current=r.chats.at(-1),pane=f.herdr.paneOf(current);
  pane.agent={agent:'codex',agent_status:'working',agent_session:{kind:'id',value:ids[2]}};
  f.ports.recoverCoordinatorClaim=async()=>({state:'skipped'});
  f.ports.owners={read:async()=>({json:JSON.stringify({localOwner:'current',claims:claim==='absent'?[]:[{issue:r.issue.url,active:true,owner:'replacement',coordinatorId:'replacement',machine:'fixture',commentId:'13',labelEventId:'14'}]})})};
  await sweepIdleRuns({graceMs:0},f.ports);
  assert.equal(f.record().state,'cancelled','unowned-run-enters-normal-release');
  assert.equal(f.record().cancelled.state,'handed-over');assert.ok(f.herdr.paneOf(current),'release-keeps-busy-agent');
});
test('3123 older-owner handover waits for check custody before closing its parent chat',async t=>{
  const {f,r}=await stopped(t);r.automaticOrigin.coordinatorId='old';save(f,r);
  f.ports.recoverCoordinatorClaim=async()=>({state:'skipped'});
  f.ports.owners={read:async()=>({json:JSON.stringify({localOwner:'current',claims:[]})})};
  f.ports.readSuiteProgress=()=>({state:'running',pausedMs:0});
  await sweepIdleRuns({graceMs:0},f.ports);
  assert.equal(f.record().state,'paused');assert.ok(f.herdr.paneOf(r.chats.at(-1)));
  f.ports.readSuiteProgress=()=>({state:'finished',pausedMs:0});
  await sweepIdleRuns({graceMs:0},f.ports);
  assert.equal(f.record().state,'cancelled','idle-check-custody-allows-normal-release');
});
test('3123 tick recovery saves all found IDs even when the current agent still runs',async t=>{
  const {f,r}=await stopped(t);r.state='running';delete r.blockedOn;save(f,r);
  f.ports.owners={read:async()=>({json:JSON.stringify({localOwner:'current',claims:[{issue:r.issue.url,active:true,owner:'current',coordinatorId:'current',machine:'fixture',commentId:'11',labelEventId:'12'}]})})};
  f.herdr.paneOf(r.chats.at(-1)).agent={agent:'codex',agent_status:'idle',agent_session:{kind:'id',value:ids[2]}};
  f.herdr.calls.length=0;
  await resumeStoppedRun({ref:'17',cwd:f.source,coordinatorId:'current',machine:'fixture'},f.ports);
  assert.deepEqual(f.record().chats.map(c=>c.session?.id),ids,'tick-evidence-is-durable-without-parking');
  assert.equal(f.herdr.calls.filter(a=>a[0]==='pane'&&a[1]==='run').length,0,'observation-does-not-relaunch-a-live-chat');
});
