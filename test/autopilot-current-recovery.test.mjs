import { readAutopilotState, saveAutopilotState } from '../src/autopilot-store.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { tickAutopilot } from '../src/autopilot-launcher.mjs';

test('fresh dependency request recovers version 2 custody on an idle coordinator', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-recovery-')); t.after(() => rmSync(dir, {recursive:true,force:true}));
  const cwd=join(dir,'repo'), home=join(dir,'home'), stateFile=join(dir,'state.json'); mkdirSync(cwd); mkdirSync(home);
  writeFileSync(join(cwd,'pdd.json'), JSON.stringify({autopilot:{mode:'auto',trust:[]}}));
  const agent={id:'codex',kind:'codex',command:'codex'}, coordinator={version:'pdd.autopilot-coordinator.v1',repository:'example/repo',coordinatorId:'c',machine:'m',activation:1};
  const previous={version:2,paneId:'p1',workspaceId:'w1',at:2,fingerprint:'old',payloadDigest:'old-payload'};
  const history={kind:'legacy-uncertain',paneId:'p1',workspaceId:'w1',at:1};
  const state={enabled:true,cwd,repo:'example/repo',stateFile,coordinatorId:'c',machine:'m',activatedAt:1,agent,environment:{HOME:home},paneId:'p1',workspaceId:'w1',recipeDelivered:false,ownerLaunch:{paneId:'p1',startedAt:1,coordinator,profile:{agent:{id:'codex',kind:'codex'},home,definitionHome:home,configHome:null}},reconciliationIntent:previous,uncertainDeliveryHistory:[history]};
  saveAutopilotState(stateFile, state);
  const request={id:'new-request',repository:'example/repo',issues:['example/repo#42'],snapshotJson:JSON.stringify({repository:'example/repo'}),contextJson:JSON.stringify({source:[],requirements:[]})};
  let sent=[], delivered, savedAtSend;
  const live={pane_id:'p1',workspace_id:'w1',cwd,foreground_cwd:cwd,tab_id:'t1',terminal_id:'term1',agent:'codex',agent_status:'done',agent_session:'session'};
  const ports={now:()=>100,run:async cmd=>cmd==='git'?{code:0,stdout:cwd+'\n'}:{code:0,stdout:JSON.stringify({nameWithOwner:'example/repo',url:'https://github.com/example/repo'})},queryIssues:async()=>({status:304}),warn:()=>{},
    herdr:async args=>{ if(args[0]==='agent'&&args[1]==='get')return {result:{type:'agent_info',agent:live}}; if(args[0]==='workspace')return {result:{type:'workspace_info',workspace:{workspace_id:'w1'}}}; if(args[0]==='pane'&&args[1]==='get')return {result:{type:'pane_info',pane:live}}; if(args[0]==='pane'&&args[1]==='read')return ''; if(args[0]==='agent'&&args[1]==='prompt'){savedAtSend=readAutopilotState(stateFile); sent.push(args.at(-1)); return {result:{}};} throw Error(args.join(' '));},
    reconcileDependencyIntake:async (_input,{pending})=>{await pending.save({json:JSON.stringify({requested:['example/repo#42']})}); delivered=await pending.deliver({requestJson:JSON.stringify(request)});return {queued:[],eligible:[],skipped:[],pending:true};}};
  await tickAutopilot(stateFile,ports);
  assert.equal(delivered.state,'delivered'); assert.equal(sent.length,1); assert.match(sent[0], /recipeFirst\":true/); assert.match(sent[0], /bounded startup readiness/); assert.equal(readAutopilotState(stateFile).recipeDelivered,true); assert.match(sent[0],/new-request/); assert.doesNotMatch(sent[0],/old-payload/);
  assert.deepEqual(savedAtSend.uncertainDeliveryHistory[0],history); assert.equal(savedAtSend.uncertainDeliveryHistory[1].payloadDigest,'old-payload'); assert.notEqual(savedAtSend.reconciliationIntent.payloadDigest,'old-payload');
  const final=readAutopilotState(stateFile); assert.equal(final.coordinatorId,'c'); assert.deepEqual(final.uncertainDeliveryHistory,savedAtSend.uncertainDeliveryHistory);
});
