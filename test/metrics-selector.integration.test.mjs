import { isolatedCheckCapacity } from './helpers/check-machine.mjs';
import { healthyMachine } from './helpers/healthy-machine.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, readdirSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { readEvents } from '../src/metrics-store.mjs';
import { tickAutopilot, autopilotLaunchFingerprint } from '../src/autopilot-launcher.mjs';
const issue = (number, extra = {}) => ({number,state:'open',title:`Issue ${number}`,body:'body',user:{login:'owner'},author_association:'OWNER',created_at:'2026-11-04T00:01:00Z',updated_at:'2026-11-04T00:01:00Z',comments:0,labels:[],html_url:`https://example.test/${number}`,...extra});
function fixture(t) {
  const root=mkdtempSync(join(tmpdir(),'pdd-selector-')); t.after(()=>rmSync(root,{recursive:true,force:true})); execFileSync('git',['init','-q',root]);
  writeFileSync(join(root,'pdd.json'),JSON.stringify({autopilot:{mode:'auto',trust:['helper']}})); const stateFile=join(root,'state.json');
  const activatedAt='2026-11-04T00:00:00Z', home=process.env.HOME, coordinator={version:'pdd.autopilot-coordinator.v1',repository:'Owner/Repo',coordinatorId:'c',machine:'m',activation:activatedAt};
  writeFileSync(stateFile,JSON.stringify({enabled:true,cwd:root,repo:'Owner/Repo',activatedAt,coordinatorId:'c',machine:'m',agent:{id:'codex',kind:'codex',command:'codex',env:{}},environment:{HOME:home},stateFile,workspaceId:'w',paneId:'p',recipeDelivered:true,ownerLaunch:{paneId:'p',startedAt:1,coordinator,profile:{agent:{id:'codex',kind:'codex'},home,definitionHome:home,configHome:null},fingerprint:autopilotLaunchFingerprint({cwd:root,agent:{kind:"codex"}})}}));
  const f={root,stateFile,issues:[],warnings:[],packets:[]};
  f.ports={...healthyMachine, checkCapacityPorts:isolatedCheckCapacity(root),now:()=>Date.parse('2026-11-05T00:00:00Z'),allocationCheck:async()=>({state:'ready',message:''}),warn:s=>f.warnings.push(s),queryIssues:async()=>({status:200,issues:structuredClone(f.issues)}),comments:async()=>{throw Error('comments unavailable');},run:async (command,args)=>({code:0,stdout:command==='git'?execFileSync('git',args,{cwd:root,encoding:'utf8'}):JSON.stringify({nameWithOwner:'Owner/Repo',url:'https://github.com/Owner/Repo'}),stderr:''}),reconcileDependencyIntake:async()=>({eligible:f.issues.map(x=>x.html_url),queued:[],skipped:[]}),herdr:async args=>{const live={pane_id:'p',workspace_id:'w',cwd:root,foreground_cwd:root,tab_id:'t',terminal_id:'term',agent:'codex',agent_status:'idle',agent_session:'session'}; if(args[0]==='agent'&&args[1]==='get') return {result:{type:'agent_info',agent:live}}; if(args[0]==='pane'&&args[1]==='get') return {result:{type:'pane_info',pane:live}}; if(args[0]==='workspace'&&args[1]==='get') return {result:{type:'workspace_info',workspace:{workspace_id:'w'}}}; if(args[0]==='pane'&&args[1]==='read') return '';  if(args[0]==='agent'&&args[1]==='prompt') { const instruction=args.at(-1), match=/Artifact path: (.+)/.exec(instruction); f.packets.push(match ? readFileSync(JSON.parse(match[1]),'utf8') : instruction); } return {result:{}};}};
  f.tick=()=>tickAutopilot(stateFile,f.ports); f.decisions=()=>{const dir=join(root,'.git','pdd','metrics','decisions');try{return readdirSync(dir).map(x=>JSON.parse(readFileSync(join(dir,x),'utf8')));}catch(e){if(e.code==='ENOENT')return [];throw e;}}; return f;
}
test('selector captures observed open issues with scope, reasons, unknown and a shared snapshot',async t=>{
  const f=fixture(t); f.issues=[issue(1),issue(2,{labels:['pdd:working']}),issue(3,{created_at:'2026-11-03T00:00:00Z'}),issue(4,{comments:1}),issue(5,{state:'closed'}),issue(6,{pull_request:{}})];
  await f.tick(); const rows=f.decisions(); assert.deepEqual(rows.map(r=>r.issue).sort(),[1,2,3,4]); assert.equal(new Set(rows.map(r=>r.snapshotId)).size,1);
  const byIssue=Object.fromEntries(rows.map(r=>[r.issue,r.events.find(e=>e.type==='selection').data]));
  assert.deepEqual([byIssue[2].state,byIssue[2].reasons],['waiting',['pdd:working']]); assert.equal(byIssue[3].inScope,true); assert.equal(byIssue[3].state,'ready'); assert.deepEqual(byIssue[3].reasons,[]); assert.equal(byIssue[4].state,'unknown'); assert.ok(byIssue[4].reasons.length);
  assert.equal(rows.find(r=>r.issue===1).offered,true); assert.ok(rows.find(r=>r.issue===1).events.some(e=>e.type==='launch'));
  assert.equal(byIssue[1].state,'ready'); assert.match(f.packets[0],new RegExp(rows.find(r=>r.issue===1).id));
});
test('decisions survive delivery failure and retry creates a fresh linked decision',async t=>{
  const f=fixture(t); f.issues=[issue(1)]; let fail=true; const herdr=f.ports.herdr; f.ports.herdr=async args=>{if(args[0]==='agent'&&args[1]==='prompt'&&fail) throw Error('offline');return herdr(args);};
  await assert.rejects(f.tick(),/offline/); const first=f.decisions(); assert.equal(first.length,1); fail=false; await f.tick(); const all=f.decisions(); assert.equal(all.length,2); assert.notEqual(all[0].id,all[1].id);
  assert.ok(all.some(row=>f.packets[0].includes(row.id))); assert.ok(all.every(row=>row.offered && row.events.some(e=>e.type==='selection')));
});
test('decision capture failure does not gate delivery',async t=>{
  const f=fixture(t); f.issues=[issue(1)]; const dir=join(f.root,'.git','pdd','metrics'); mkdirSync(dir,{recursive:true}); writeFileSync(join(dir,'decisions'),'unavailable');
  const result=await f.tick(); assert.equal(result.exitCode,0); assert.equal(f.packets.length,1); assert.ok(f.warnings.some(w=>/capture incomplete/i.test(w)));
});
test('capture failure gap survives and is exported by the real CLI',async t=>{
  const f=fixture(t); f.issues=[issue(1)];
  execFileSync('git',['remote','add','origin','https://github.com/Owner/Repo.git'],{cwd:f.root});
  const dir=join(f.root,'.git','pdd','metrics'); mkdirSync(dir,{recursive:true}); writeFileSync(join(dir,'decisions'),'unavailable');
  await f.tick();
  const file=join(f.root,'export.json');
  execFileSync(process.execPath,[join(import.meta.dirname,'..','bin','pdd.mjs'),'metrics','export',file],{cwd:f.root,encoding:'utf8'});
  const bundle=JSON.parse(readFileSync(file,'utf8'));
  assert.ok(bundle.events.some(e=>e.issue===1 && e.type==='coverage' && e.data.complete===false));
});
test('real CLI export backfills a saved skipped step as skipped', t=>{
  const f=fixture(t); execFileSync('git',['remote','add','origin','https://github.com/Owner/Repo.git'],{cwd:f.root});
  const runDir=join(f.root,'.git','pdd','runs','8'); mkdirSync(runDir,{recursive:true});
  writeFileSync(join(runDir,'status.json'),JSON.stringify({v:1,runId:'legacy8',number:8,repo:'owner/repo',done:{verify:{at:1700000000000,skipped:{reason:'optional'}}}}));
  const file=join(f.root,'skipped.json'); execFileSync(process.execPath,[join(import.meta.dirname,'..','bin','pdd.mjs'),'metrics','export',file],{cwd:f.root,encoding:'utf8'});
  const rows=JSON.parse(readFileSync(file,'utf8')).events.filter(e=>e.issue===8 && e.type==='step');
  assert.equal(rows.length,1); assert.equal(rows[0].data.status,'skipped');
});
test('an uncommitted partial snapshot cannot enter an exported issue group', t=>{
  const f=fixture(t); execFileSync('git',['remote','add','origin','https://github.com/Owner/Repo.git'],{cwd:f.root});
  const dir=join(f.root,'.git','pdd','metrics','decisions'); mkdirSync(dir,{recursive:true});
  const id='11234567-89ab-4cde-8fab-123456789abc',at='2026-11-05T00:00:00.000Z',snapshotId='snapshot:21234567-89ab-4cde-8fab-123456789abc';
  const event={schema:'pdd.metrics.event.v1',id:`${id}:selection`,repo:'owner/repo',issue:1,type:'selection',at,observedAt:at,source:'test',data:{snapshotId,inScope:true,state:'unknown',reasons:[]}};
  writeFileSync(join(dir,`${id}.json`),JSON.stringify({id,repo:'owner/repo',issue:1,snapshotId,pendingSnapshot:true,offered:true,events:[event]}));
  const file=join(f.root,'partial.json'); execFileSync(process.execPath,[join(import.meta.dirname,'..','bin','pdd.mjs'),'metrics','export',file],{cwd:f.root,encoding:'utf8'});
  assert.equal(JSON.parse(readFileSync(file,'utf8')).events.some(e=>e.id===event.id),false);
});

test('empty selector saves a timestamped empty snapshot', async t=>{ const f=fixture(t); await f.tick(); const dir=join(f.root,'.git','pdd','metrics','snapshots'); const snapshot=JSON.parse(readFileSync(join(dir,readdirSync(dir)[0]),'utf8')); assert.deepEqual(snapshot.events,[]); assert.equal(snapshot.observedAt,'2026-11-05T00:00:00.000Z'); });

test('actual wake records attempted and delivered facts linked to decision',async t=>{
 const f=fixture(t); f.issues=[issue(1)]; await f.tick(); const id=f.decisions()[0].id;
 const events=(await readEvents({root:f.root})).events.filter(e=>e.type==='launch');
 assert.deepEqual(events.map(e=>e.data.status).sort(),['attempted','confirmed']); assert.ok(events.every(e=>e.data.decisionId===id));
});
test('uncertain and certain wake errors retain attempt without claiming start',async t=>{
 for(const certain of [false,true]) { const f=fixture(t); f.issues=[issue(1)]; const herdr=f.ports.herdr;
 f.ports.herdr=async args=>{if(args[0]==='agent'&&args[1]==='prompt') throw Object.assign(Error('delivery error'),{code:certain?'agent_blocked':'server_unavailable'});return herdr(args);};
 await assert.rejects(f.tick(),/delivery error/); const id=f.decisions()[0].id; const events=(await readEvents({root:f.root})).events.filter(e=>e.type==='launch');
 assert.deepEqual(events.map(e=>e.data.status).sort(),['attempted',certain?'failed':'uncertain'].sort()); assert.ok(events.every(e=>e.data.decisionId===id));
 }
});

test('unchanged trusted ready work remains ready in the next snapshot',async t=>{
 const f=fixture(t); f.issues=[issue(1)]; await f.tick(); await f.tick();
 assert.deepEqual(f.decisions().map(r=>r.events.find(e=>e.type==='selection').data.state),['ready','ready']);
 assert.equal(f.packets.length,2); assert.ok(f.packets.every(packet=>packet.includes('\"number\":1,')));
});

test('launch outbox survives ledger failure and export retries without duplication',async t=>{
 const f=fixture(t); f.issues=[issue(1)]; execFileSync('git',['remote','add','origin','https://github.com/Owner/Repo.git'],{cwd:f.root});
 const transactions=join(f.root,'.git','pdd','metrics','transactions'); mkdirSync(join(f.root,'.git','pdd','metrics'),{recursive:true}); writeFileSync(transactions,'unavailable');
 await f.tick(); const decision=f.decisions()[0]; assert.deepEqual(decision.events.filter(e=>e.type==='launch').map(e=>e.data.status),['attempted','confirmed']);
 rmSync(transactions); const file=join(f.root,'export.json');
 for(let i=0;i<2;i++) execFileSync(process.execPath,[join(import.meta.dirname,'..','bin','pdd.mjs'),'metrics','export',file],{cwd:f.root,encoding:'utf8'});
 const events=JSON.parse(readFileSync(file,'utf8')).events.filter(e=>e.type==='launch'); assert.equal(events.length,2); assert.ok(events.every(e=>e.data.decisionId===decision.id));
});
