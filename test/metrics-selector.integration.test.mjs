import './helpers/test-home.mjs';
import { isolatedCheckCapacity } from './helpers/check-machine.mjs';
import { healthyMachine } from './helpers/healthy-machine.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, readdirSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { readEvents } from '../src/metrics-store.mjs';
import { tickAutopilot } from '../src/autopilot-launcher.mjs';
const autopilotLaunchFingerprint = () => 'full-engine-launch';
const issue = (number, extra = {}) => ({number,state:'open',title:`Issue ${number}`,body:'body',user:{login:'owner'},author_association:'OWNER',created_at:'2026-11-04T00:01:00Z',updated_at:'2026-11-04T00:01:00Z',comments:0,labels:[],html_url:`https://example.test/${number}`,...extra});
function fixture(t) {
  const root=mkdtempSync(join(tmpdir(),'pdd-selector-')); t.after(()=>rmSync(root,{recursive:true,force:true})); execFileSync('git',['init','-q',root]);
  writeFileSync(join(root,'pdd.json'),JSON.stringify({autopilot:{mode:'auto',trust:['helper']}})); const stateFile=join(root,'state.json');
  const activatedAt='2026-11-04T00:00:00Z', home=join(root,'home'), coordinator={version:'pdd.autopilot-coordinator.v1',repository:'Owner/Repo',coordinatorId:'c',machine:'m',activation:activatedAt};
  mkdirSync(home);
  writeFileSync(stateFile,JSON.stringify({enabled:true,defaultBranch:'main',baseBranch:'main',cwd:root,repo:'Owner/Repo',activatedAt,coordinatorId:'c',machine:'m',agent:{id:'codex',kind:'codex',command:'codex',env:{}},environment:{HOME:home},stateFile,workspaceId:'w',paneId:'p',recipeDelivered:true,ownerLaunch:{paneId:'p',startedAt:1,coordinator,profile:{agent:{id:'codex',kind:'codex'},home,definitionHome:home,configHome:null},fingerprint:autopilotLaunchFingerprint({cwd:root,agent:{kind:"codex"}})}}));
  const f={root,stateFile,issues:[],warnings:[],packets:[]};
  f.ports={...healthyMachine, checkCapacityPorts:isolatedCheckCapacity(root),now:()=>Date.parse('2026-11-05T00:00:00Z'),allocationCheck:async()=>({state:'ready',message:''}),warn:s=>f.warnings.push(s),queryIssues:async()=>({status:200,issues:structuredClone(f.issues)}),comments:async()=>{throw Error('comments unavailable');},run:async (command,args)=>{const endpoint=args.find(word=>/^repos\//.test(word)),subject=/^repos\/Owner\/Repo\/issues\/(\d+)$/i.exec(endpoint??'');if(command==='gh'&&subject){const row=f.issues.find(row=>row.number===Number(subject[1]));return {code:row?0:1,stdout:JSON.stringify(row??{})};}return {code:0,stdout:command==='git'?execFileSync('git',args,{cwd:root,encoding:'utf8'}):JSON.stringify({nameWithOwner:'Owner/Repo',url:'https://github.com/Owner/Repo'}),stderr:''};},reconcileDependencyIntake:async()=>({eligible:f.issues.map(x=>x.html_url),queued:[],skipped:[]}),herdr:async args=>{const live={pane_id:'p',workspace_id:'w',cwd:root,foreground_cwd:root,tab_id:'t',terminal_id:'term',agent:'codex',agent_status:'idle',agent_session:'session'}; if(args[0]==='agent'&&args[1]==='get') return {result:{type:'agent_info',agent:live}}; if(args[0]==='pane'&&args[1]==='get') return {result:{type:'pane_info',pane:live}}; if(args[0]==='workspace'&&args[1]==='get') return {result:{type:'workspace_info',workspace:{workspace_id:'w'}}}; if(args[0]==='pane'&&args[1]==='read') return '';  if(args[0]==='agent'&&args[1]==='prompt') { const instruction=args.at(-1), match=/Artifact path: (.+)/.exec(instruction); f.packets.push(match ? readFileSync(JSON.parse(match[1]),'utf8') : instruction); } return {result:{}};}};
  f.tick=()=>tickAutopilot(stateFile,f.ports); f.decisions=()=>{const dir=join(root,'.git','pdd','metrics','decisions');try{return readdirSync(dir).map(x=>JSON.parse(readFileSync(join(dir,x),'utf8')));}catch(e){if(e.code==='ENOENT')return [];throw e;}}; return f;
}
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

