import './test-home.mjs';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {factoryWorld} from './factory/world.mjs';
import {scriptedAgent} from './factory/agent.mjs';
import {launcher} from './environment-launcher-fixture.mjs';

const manualIssue = number => ({number,state:'open',title:'Held issue',body:'Keep for a person',user:{login:'owner'},author_association:'OWNER',created_at:'2026-11-06T00:00:00Z',updated_at:'2026-11-06T00:00:00Z',comments:0,labels:['pdd:manual'],html_url:`https://github.com/owner/repo/issues/${number}`});

import {readDependencySnapshot} from '../../src/issue-dependencies-github.mjs';
import {reconcileDependencyIntake} from '../../src/issue-dependencies-intake.mjs';
import {fixture,repository} from './issue-sort-fixture.mjs';
const tick=w=>reconcileDependencyIntake({repository,mode:'auto'},w.ports);
const seed=(w,ns)=>{for(const n of ns){w.save(w.record(n));w.review(n);}};

export const manualEffectCases = [
 ['review2: manual hold suppresses environment exhaustion alert', async t=>{
 const f=await launcher(t); await f.start(); f.prompts.length=0;
 f.issues=[manualIssue(12)]; f.ports.readManualHold=async()=>({known:true,held:true});
 f.environmentWaits=[{number:12,at:f.time,step:'verify',area:0,reason:'Native full suite filesystem journal I/O stall',attempts:3,nextAt:null}];
 f.time+=60000; await f.tick();
 assert.deepEqual(JSON.parse(readFileSync(f.stateFile())).manualIssues,[12]);
 const sent=f.sent.filter(text=>!/digest/i.test(text));
 return sent.length;
 }],
 ['review2: manual hold suppresses resource alert', async t=>{
 const f=await launcher(t); await f.start(); f.prompts.length=0;
 f.issues=[manualIssue(12)]; f.ports.readManualHold=async()=>({known:true,held:true});
 f.ports.machineHealth=async()=>({healthy:false,causes:['disk full'],resources:null});
 f.time+=60000; await f.tick();
 assert.deepEqual(JSON.parse(readFileSync(f.stateFile())).manualIssues,[12]);
 const sent=f.sent.filter(text=>!/digest/i.test(text));
 return sent.length;
 }],
 ['review2: closed manually held issue cannot be offered for automatic audit', async t=>{
 const w=await factoryWorld(t); await w.begin(); const a=scriptedAgent(w); await a.finish(); await a.merge();
 assert.equal(w.record().state,'completed');
 await w.github.gh(['issue','edit','17','--add-label','pdd:manual']);
 const start=w.herdr.calls.length; await w.tick(); w.seenCalls=start; w.messages();
 const rules=w.packets.flatMap(p=>p.timeRules??[]).filter(r=>r.number===17&&r.kind==='post-merge-audit');
 const commentsBefore=w.github.issues.get(17).comments.length;
 await w.command(['autopilot','audit','17','100'],{actor:'coordinator',env:w.context(),allowFailure:true});
 return rules.length+w.auditCalls.length+w.github.issues.get(17).comments.length-commentsBefore;
 }],
 ['review2: busy manual run from older coordinator avoids ordinary adoption sweep', async t=>{
 const w=await factoryWorld(t,{workflow:'bug'});await w.begin();
 await scriptedAgent(w).until(run=>Boolean(run.done.reproduce)); await w.command(['workflow','status','17']);
 const before=w.record(),state=w.state(); state.coordinatorId='review-replacement';state.ownerLaunch.coordinator.coordinatorId=state.coordinatorId;
 writeFileSync(w.stateFile,JSON.stringify(state));
 const run=w.record();run.state='stuck';run.stuckCause='Synthetic stop';
 writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run));
 for(const p of w.herdr.panes)if(p.cwd===run.root&&p.agent)p.agent.agent_status='busy';
 w.time+=120000; await w.github.gh(['issue','edit','17','--add-label','pdd:manual']);
 await w.tick();
 return Number(w.record().parking !== undefined);
 }],
 ['review2: unknown manual authority blocks ordinary adoption sweep', async t=>{
 const w=await factoryWorld(t,{workflow:'bug'});await w.begin();
 await scriptedAgent(w).until(run=>Boolean(run.done.reproduce)); await w.command(['workflow','status','17']);
 const before=w.record(),state=w.state(); state.coordinatorId='review-replacement';state.ownerLaunch.coordinator.coordinatorId=state.coordinatorId;
 writeFileSync(w.stateFile,JSON.stringify(state));
 const run=w.record();run.state='stuck';run.stuckCause='Synthetic stop';
 writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run));
 for(const p of w.herdr.panes)if(p.cwd===run.root&&p.agent)p.agent.agent_status='busy';
 w.time+=120000; await w.github.gh(['issue','edit','17','--add-label','pdd:manual']);
 w.github.issues.get(17).timeline.at(-1).actor='manual-writer';
 const execute=w.execute;w.execute=async(file,args,options)=>file==='gh'&&args.some(arg=>String(arg).includes('/collaborators/manual-writer/permission'))
  ?{code:1,stdout:'HTTP/2 503 Service Unavailable\r\n\r\n{}',stderr:'permission service unavailable'}:execute(file,args,options);
 await w.tick();
 return Number(w.record().automaticOrigin.coordinatorId !== before.automaticOrigin.coordinatorId);
 }],
 ['review2: group membership comment cannot mutate a held running umbrella', async t=>{
 const w=fixture([1,2,3,4]);seed(w,[1,2,3]);await tick(w);
 const [group]=(await w.ports.sortGroups.read()).groups;
 const umbrella=w.issues.find(x=>x.html_url===group.umbrella);
 umbrella.labels=['pdd:working','pdd:manual'];
 w.claims.push({issue:group.umbrella,active:true,owner:'worker'});
 w.ports.manualAuthority={read:async()=>({known:true,allowed:true})};
 const page=w.ports.github.page;
 w.ports.github.page=async args=>args.kind==='timeline'&&args.issue===umbrella.number
  ?{json:JSON.stringify({items:[{event:'labeled',label:{name:'pdd:manual'},actor:{login:'writer'}}],next:''})}:page(args);
 w.ports.manualHold={read:async({issue})=>({known:true,held:issue===umbrella.number})};
 seed(w,[4]);const snapshot=(await readDependencySnapshot({repository},w.ports)).snapshot;
 assert.ok(snapshot.issues.find(i=>i.key===group.umbrella).holds.includes('pdd:manual'));
 const start=w.writes.length;await tick(w);
 const writes=w.writes.slice(start).filter(x=>x.issue===umbrella.number);
 return writes.length;
 }],
 ['PR publication is held at the final workflow step', async t => {
   const w = await factoryWorld(t); await w.begin(); const a = scriptedAgent(w);
   await a.until(run => run.areas[run.area].steps.slice(0,-1).every(step => Boolean(run.done[step])));
   assert.equal(w.github.prs.length,0);
   await w.github.gh(['issue','edit','17','--add-label','pdd:manual']);
   await a.step({allowFailure:true});
   if (w.record().gate) await w.command(['workflow','approve','17','--said','-'],{cwd:w.record().root,actor:'coordinator',stdin:'The synthetic factory operator auto start covers this ordinary publication gate.',allowFailure:true});
   return w.github.prs.length;
 }],
];
