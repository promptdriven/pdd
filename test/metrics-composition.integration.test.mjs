import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {join} from 'node:path';
import {tmpdir} from 'node:os';
import {execFileSync,spawnSync} from 'node:child_process';
import {tickAutopilot,autopilotLaunchFingerprint} from '../src/autopilot-launcher.mjs';
import {writeRun,updateRun} from '../src/workflow-runs.mjs';
import {runPdd} from '../src/pdd-cli.mjs';
const at=Date.parse('2026-11-05T00:00:00Z');
function selector(t,{issues=true}={}) {
 const root=fs.mkdtempSync(join(tmpdir(),'pdd-composed-selector-'));t.after(()=>fs.rmSync(root,{recursive:true,force:true}));execFileSync('git',['init','-q',root]);
 fs.writeFileSync(join(root,'pdd.json'),JSON.stringify({autopilot:{mode:'auto'}}));const stateFile=join(root,'state.json');
 const home=process.env.HOME, activatedAt='2026-11-04T00:00:00Z', coordinator={version:'pdd.autopilot-coordinator.v1',repository:'Owner/Repo',coordinatorId:'c',machine:'m',activation:activatedAt};
 fs.writeFileSync(stateFile,JSON.stringify({enabled:true,defaultBranch:'main',baseBranch:'main',cwd:root,repo:'Owner/Repo',activatedAt,coordinatorId:'c',machine:'m',environment:{HOME:home},agent:{id:'codex',kind:'codex',command:'codex',env:{}},stateFile,workspaceId:'w',paneId:'p',recipeDelivered:true,ownerLaunch:{paneId:'p',startedAt:1,coordinator,profile:{agent:{id:'codex',kind:'codex'},home,definitionHome:home,configHome:null},fingerprint:autopilotLaunchFingerprint({cwd:root,agent:{kind:"codex"}})}}));
 const rows=issues?[{number:1,state:'open',title:'One',body:'body',user:{login:'owner'},author_association:'OWNER',created_at:'2026-11-04T00:01:00Z',updated_at:'2026-11-04T00:01:00Z',comments:0,labels:[],html_url:'https://example.test/1'}]:[];
 const f={root,stateFile,sent:[],ports:{now:()=>at,warn:()=>{},allocationCheck:async()=>({state:'ready',message:''}),queryIssues:async()=>({status:200,issues:rows}),run:async (command,args)=>({code:0,stdout:command==='git'?execFileSync('git',args,{cwd:root,encoding:'utf8'}):'{}',stderr:''})}};
 f.ports.reconcileDependencyIntake=async()=>({eligible:rows.map(row=>row.html_url),queued:[],skipped:[]});
 f.ports.herdr=async args=>{if(args[0]==='agent'&&args[1]==='get')return {result:{agent:{agent_status:'idle',agent_session:'session'}}};if(args[0]==='pane'&&args[1]==='read')return '';if(args[0]==='agent'&&args[1]==='prompt'){const text=args.at(-1),match=/Artifact path: (.+)/.exec(text);f.sent.push(match?fs.readFileSync(JSON.parse(match[1]),'utf8'):text);}return {};};
 f.tick=()=>tickAutopilot(stateFile,f.ports);return f;
}
function storage(t) {
 const root=fs.mkdtempSync(join(tmpdir(),'pdd-composed-run-'));t.after(()=>fs.rmSync(root,{recursive:true,force:true}));const commonDir=join(root,'.git'),runDir=join(commonDir,'pdd','runs','1');fs.mkdirSync(commonDir);
 return {root,runDir,run:{v:1,runId:'one',repo:'example/repo',number:1,root,sourceRoot:root,commonDir,runDir,state:'running',workflow:'small-change',areas:[{name:'code',steps:['build'],optional:[]}],area:0,chats:[],done:{},pr:[]},ports:{stateDir:join(root,'state'),now:()=>at,skipMetricsDelivery:true,metricsWarning:()=>{}}};
}
test('composed launcher sends successfully despite capture, gap and warning failures',async t=>{
 const f=selector(t);const dir=join(f.root,'.git','pdd','metrics');fs.mkdirSync(dir,{recursive:true});fs.writeFileSync(join(dir,'transactions'),'unavailable');
 f.ports.warn=()=>{throw Error('warning unavailable');};f.ports.metricsGap=()=>{throw Error('gap unavailable');};
 const result=await f.tick();assert.equal(result.exitCode,0);assert.equal(f.sent.length,1);
 const saved=JSON.parse(fs.readFileSync(f.stateFile,'utf8'));assert.ok(saved.seen['1']);
 const decisions=fs.readdirSync(join(dir,'decisions')).filter(n=>n.endsWith('.json')).map(n=>JSON.parse(fs.readFileSync(join(dir,'decisions',n),'utf8')));
 assert.deepEqual(decisions[0].events.filter(e=>e.type==='launch').map(e=>e.data.status),['attempted','confirmed']);
});
test('composed launcher preserves original delivery error under failed telemetry',async t=>{
 const f=selector(t),error=Object.assign(Error('native send failed'),{code:'agent_blocked'}),herdr=f.ports.herdr;
 f.ports.herdr=async args=>{if(args[1]==='prompt')throw error;return herdr(args);};f.ports.metricsAppendEvents=async()=>{throw Error('metrics unavailable');};f.ports.warn=()=>{throw Error('warning unavailable');};
 await assert.rejects(f.tick(),e=>e===error);assert.equal(f.sent.length,0);assert.equal(JSON.parse(fs.readFileSync(f.stateFile,'utf8')).seen['1'],undefined);
});
test('composed launcher does not record busy pane as delivery attempt',async t=>{
 const f=selector(t);f.ports.herdr=async()=>({result:{agent:{agent_status:'working'}}});await f.tick();
 const dir=join(f.root,'.git','pdd','metrics','decisions'),rows=fs.readdirSync(dir).map(n=>JSON.parse(fs.readFileSync(join(dir,n),'utf8')));assert.equal(rows.flatMap(r=>r.events).some(e=>e.type==='launch'),false);assert.equal(f.sent.length,0);
});
test('composed launcher preserves a time-only wake and its successful acknowledgement',async t=>{
 const f=selector(t,{issues:false});f.ports.readRunProgress=async()=>[{number:9,changedAt:at-3600001}];await f.tick();
 assert.equal(f.sent.length,1);const packet=JSON.parse(f.sent[0].trim().split('\n').at(-1));assert.deepEqual(packet.issues,[]);assert.equal(packet.timeRules[0].kind,'stuck-run');
 assert.equal(JSON.parse(fs.readFileSync(f.stateFile,'utf8')).timeSeen['run:9'],at-3600001);await f.tick();assert.equal(f.sent.length,1);
});
test('composed storage retains pending capture and ordinary success under throwing warning',t=>{
 const f=storage(t);f.run.metricsObservations=[{type:'coverage',at:new Date(at).toISOString(),data:{complete:false}}];
 const originalWrite=fs.writeFileSync;const ports={...f.ports,metricsWarning:()=>{throw Error('warn failed');},runFiles:{writeFileSync:(path,...args)=>{if(String(path).includes('.identity-'))throw Error('metrics identity failed');return originalWrite(path,...args);}}};
 assert.equal(writeRun(f.run,ports),f.run);let saved=JSON.parse(fs.readFileSync(join(f.runDir,'status.json'),'utf8'));assert.equal(saved.metrics.coverageGap,true);assert.equal(saved.metricsObservations.length,1);
 saved=updateRun(f.runDir,r=>r,f.ports);assert.equal(saved.metricsObservations,undefined);assert.equal(saved.metrics.events.filter(e=>e.type==='coverage').length,1);
});
test('composed storage preserves pathname write port and native rename failure',t=>{
 const f=storage(t);let statusWrites=0;const files={writeFileSync:(path,...args)=>{assert.equal(typeof path,'string');if(path.includes('.status.json.'))statusWrites++;return fs.writeFileSync(path,...args);}};
 writeRun(f.run,{...f.ports,runFiles:files});assert.equal(statusWrites,1);const before=fs.readFileSync(join(f.runDir,'status.json'),'utf8');
 assert.throws(()=>updateRun(f.runDir,r=>{r.message='must not commit';return r;},{...f.ports,runFiles:{renameSync:(from,to)=>{if(to===join(f.runDir,'status.json'))throw Error('native rename failed');return fs.renameSync(from,to);}}}),/native rename failed/);
 assert.equal(fs.readFileSync(join(f.runDir,'status.json'),'utf8'),before);
});
test('composed storage contains post-commit drain and warning rejection',async t=>{
 const f=storage(t);f.run.done.build={at};const ports={...f.ports,skipMetricsDelivery:false,metricsAppendEvents:async()=>{throw Error('append failed');},metricsWarning:()=>{throw Error('warning failed');},metricsGap:()=>{throw Error('gap failed');}};
 writeRun(f.run,ports);assert.equal(JSON.parse(fs.readFileSync(join(f.runDir,'status.json'),'utf8')).done.build.at,at);
 await new Promise(resolve=>setImmediate(resolve));await new Promise(resolve=>setImmediate(resolve));
 const saved=JSON.parse(fs.readFileSync(join(f.runDir,'status.json'),'utf8'));assert.equal(saved.done.build.at,at);assert.equal(saved.metrics.coverageGap,true);assert.equal(saved.metrics.events.filter(e=>e.type==='step').length,1);
});
test('composed workflow dispatch forwards metadata together with draft/base/adoption',async()=>{
 let actual;const stream={write(){}};const result=await runPdd(['workflow','run','feature','17','--draft','--base','topic','--adopt-corpus','corpus.json','--origin','autopilot','--decision-id','token','--outcome','code'],{stdout:stream,stderr:stream,workflowAgents:{checkWorkflowAgents:async()=>({ok:true})},workflowRunner:{startRun:async input=>{actual=input;return {exitCode:0,message:'ok'};}},pathDiagnostic:()=>[]});
 assert.equal(result,0);assert.deepEqual([actual.draft,actual.base,actual.adoptCorpus,actual.origin,actual.decisionId,actual.outcome],[true,'topic','corpus.json','autopilot','token','code']);
});
test('real CLI recovers retained journal after process exit and discovers over 200 runs',t=>{
 const f=storage(t);execFileSync('git',['init','-q',f.root]);execFileSync('git',['remote','add','origin','https://github.com/example/repo.git'],{cwd:f.root});
 const code=`import {writeRun} from ${JSON.stringify(new URL('../src/workflow-runs.mjs',import.meta.url).href)};const run=${JSON.stringify({...f.run,done:{build:{at}}})};writeRun(run,{stateDir:${JSON.stringify(join(f.root,'state'))},metricsAppendEvents:()=>new Promise(()=>{}),metricsWarning:()=>{}});process.exit(0);`;
 const child=spawnSync(process.execPath,['--input-type=module','-e',code],{encoding:'utf8'});assert.equal(child.status,0,child.stderr);
 const journal=JSON.parse(fs.readFileSync(join(f.runDir,'status.json'),'utf8')).metrics.events;assert.equal(journal.length,1);
 for(let n=2;n<=202;n++) {const dir=join(f.run.commonDir,'pdd','runs',n===202?'202-cancelled-a1':String(n));fs.mkdirSync(dir,{recursive:true});fs.writeFileSync(join(dir,'status.json'),JSON.stringify({v:1,runId:`legacy${n}`,repo:'example/repo',number:n,state:n===202?'cancelled':'completed',done:{build:{at}}}));}
 const output=join(f.root,'export.json'),bin=new URL('../bin/pdd.mjs',import.meta.url).pathname;
 const offline=join(f.root,'offline-bin');fs.mkdirSync(offline);fs.writeFileSync(join(offline,'gh'),'#!/bin/sh\nexit 1\n',{mode:0o755});
 const exported=()=>{const result=spawnSync(process.execPath,[bin,'metrics','export',output],{cwd:f.root,encoding:'utf8',env:{...process.env,HOME:f.root,GH_CONFIG_DIR:f.root,GH_TOKEN:'',GITHUB_TOKEN:'',PATH:offline+':'+process.env.PATH}});assert.equal(result.status,0,result.stderr);return JSON.parse(fs.readFileSync(output,'utf8'));};
 const first=exported();assert.ok(first.events.some(e=>e.id===journal[0].id));assert.equal(new Set(first.events.filter(e=>e.type==='step').map(e=>e.issue)).size,202);assert.ok(first.events.some(e=>e.issue===202));
 const second=exported();assert.deepEqual(second.events.map(e=>[e.source,e.id]).sort(),first.events.map(e=>[e.source,e.id]).sort());
});
