import { isolatedCheckCapacity } from './helpers/check-machine.mjs';
import { healthyMachine } from './helpers/healthy-machine.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture,packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {startRun} from '../src/workflow-runner.mjs';
import {appendEvents,exportMetrics} from '../src/metrics-store.mjs';
const token='a1111111-b222-c333-d444-e55555555555',snapshotId='snapshot:f1111111-b222-c333-d444-e55555555555';
const cases=[
 ['canonical complete positive','autopilot',()=>{},false],
 ['both selections lack event time','unknown',({d,s})=>{delete d.events[0].at;delete s.events[0].at;},true],
 ['both selections have invalid event time','unknown',({d,s})=>{d.events[0].at=s.events[0].at='not-a-time';},true],
 ['both selections lack observation time','unknown',({d,s})=>{delete d.events[0].observedAt;delete s.events[0].observedAt;},true],
 ['both selections lack source identity','unknown',({d,s})=>{delete d.events[0].source;delete s.events[0].source;},true],
 ['both selections carry unsupported envelope field','unknown',({d,s})=>{d.events[0].unexpected=s.events[0].unexpected=true;},true],
 ['snapshot lacks source identity','unknown',({s})=>delete s.source,false],
 ['snapshot observation time differs from member','unknown',({s})=>s.observedAt='2026-10-27T16:59:59.000Z',false],
 ['snapshot has duplicate issue membership','unknown',({s})=>s.events.push(structuredClone(s.events[0])),false],
];
for(const [label,expected,alter,eventInvalid] of cases)test(label,async t=>{
 const f=await fixture(t);f.ports.skipMetricsDelivery=true;
 const at='2026-10-27T17:00:00.000Z',source='install:independent-review';
 const event={schema:'pdd.metrics.event.v1',id:token+':selection',repo:'example/project',issue:17,type:'selection',at,observedAt:at,source,data:{snapshotId,inScope:true,state:'ready',reasons:[]}};
 const x={d:{id:token,repo:'example/project',issue:17,offered:true,snapshotId,pendingSnapshot:true,events:[structuredClone(event)]},s:{snapshotId,repo:'example/project',source,observedAt:at,events:[structuredClone(event)]}};alter(x);
 const dir=join(f.source,'.git','pdd','metrics');mkdirSync(join(dir,'decisions'),{recursive:true});mkdirSync(join(dir,'snapshots'),{recursive:true});writeFileSync(join(dir,'decisions',token+'.json'),JSON.stringify(x.d));writeFileSync(join(dir,'snapshots',snapshotId.slice(9)+'.json'),JSON.stringify(x.s));
 const nativeStore={ledger:{read:async()=>({events:[]}),write:async()=>{}}};
 if(eventInvalid)await assert.rejects(appendEvents({root:f.source,events:x.d.events},nativeStore),/Invalid metrics|Unsupported metrics/);
 else await appendEvents({root:f.source,events:x.d.events},nativeStore);
 const exported=()=>exportMetrics({root:f.source,metadata:{repo:'example/project',timezone:'UTC',exportedAt:at}});
 if(expected==='unknown')await assert.rejects(exported(),/Invalid metrics|Unsupported metrics/);else assert.equal((await exported()).snapshots.length,1);
 const response=await startRun({name:'small-change',issue:'17',agent:'claude',cwd:f.source,packageRoot,origin:'autopilot',decisionId:token},f.ports);
 assert.equal(response.exitCode,0,response.message);const actual=f.record().metricsOrigin.origin;
 console.log(JSON.stringify({label,expected,actual,nativeExit:response.exitCode,nativeCanonicalSnapshotAccepted:expected==='autopilot'}));
 assert.equal(actual,expected,'Malformed/incomplete evidence must leave origin unknown while startup succeeds');
});

import {readFileSync} from 'node:fs';
import {execFileSync} from 'node:child_process';
import {validateSnapshot} from '../src/metrics-store.mjs';
import {tickAutopilot,autopilotLaunchFingerprint} from '../src/autopilot-launcher.mjs';

for(const label of ['missing snapshot time','invalid snapshot time','unsupported snapshot field','snapshot source mismatch','unsupported selection data','invalid selection boolean','invalid selection reasons','member source mismatch','member time mismatch','duplicate issue with distinct id','contradictory duplicate member','additional distinct valid issue'])test('canonical snapshot counterexample: '+label,async t=>{
 const f=await fixture(t);f.ports.skipMetricsDelivery=true;const at='2026-10-27T17:00:00.000Z',source='install:canonical';
 const event={schema:'pdd.metrics.event.v1',id:token+':selection',repo:'example/project',issue:17,type:'selection',at,observedAt:at,source,data:{snapshotId,inScope:true,state:'ready',reasons:[]}};
 const decision={id:token,repo:'example/project',issue:17,offered:true,snapshotId,events:[structuredClone(event)]};const snapshot={snapshotId,repo:'example/project',source,observedAt:at,events:[structuredClone(event)]};
 if(label==='missing snapshot time')delete snapshot.observedAt;
 if(label==='invalid snapshot time')snapshot.observedAt='not-a-time';
 if(label==='unsupported snapshot field')snapshot.extra=true;
 if(label==='snapshot source mismatch')snapshot.source='install:other';
 for(const e of [decision.events[0],snapshot.events[0]]) {
  if(label==='unsupported selection data')e.data.unsupported=true;
  if(label==='invalid selection boolean')e.data.inScope='yes';
  if(label==='invalid selection reasons')e.data.reasons='ready';
  if(label==='member source mismatch')e.source='install:different';
  if(label==='member time mismatch')e.at='2026-10-27T17:00:01.000Z';
 }
 if(['duplicate issue with distinct id','contradictory duplicate member','additional distinct valid issue'].includes(label)) {
  const extra=structuredClone(event);
  if(label==='duplicate issue with distinct id')extra.id='different:selection';
  if(label==='contradictory duplicate member')extra.data.state='waiting';
  if(label==='additional distinct valid issue'){extra.id='different:selection';extra.issue=18;}
  snapshot.events.push(extra);
 }
 const dir=join(f.source,'.git','pdd','metrics');mkdirSync(join(dir,'decisions'),{recursive:true});mkdirSync(join(dir,'snapshots'),{recursive:true});writeFileSync(join(dir,'decisions',token+'.json'),JSON.stringify(decision));writeFileSync(join(dir,'snapshots',snapshotId.slice(9)+'.json'),JSON.stringify(snapshot));
 const valid=label==='additional distinct valid issue';if(valid)assert.equal(validateSnapshot(snapshot,'example/project'),undefined);else assert.throws(()=>validateSnapshot(snapshot,'example/project'),/Invalid metrics|Unsupported metrics/);
 const response=await startRun({name:'small-change',issue:'17',agent:'claude',cwd:f.source,packageRoot,origin:'autopilot',decisionId:token},f.ports);assert.equal(response.exitCode,0,response.message);assert.equal(f.record().metricsOrigin.origin,valid?'autopilot':'unknown');
});

test('real native selector capture produces committed evidence accepted by workflow origin',async t=>{
 const f=await fixture(t);f.ports.skipMetricsDelivery=true;const now=f.clock;writeFileSync(join(f.source,'pdd.json'),JSON.stringify({autopilot:{mode:'auto'}}));
 const stateFile=join(f.base,'selector.json'),activatedAt=new Date(now-1000).toISOString(),home=f.ports.env.HOME,coordinator={version:'pdd.autopilot-coordinator.v1',repository:'example/project',coordinatorId:'c',machine:'m',activation:activatedAt};writeFileSync(stateFile,JSON.stringify({enabled:true,defaultBranch:'main',baseBranch:'main',cwd:f.source,repo:'example/project',activatedAt,coordinatorId:'c',machine:'m',environment:{HOME:home},agent:{id:'claude',kind:'claude',command:'claude',env:{}},stateFile,workspaceId:'fixture-workspace',paneId:'fixture-pane',recipeDelivered:true,ownerLaunch:{paneId:'fixture-pane',startedAt:1,coordinator,profile:{agent:{id:'claude',kind:'claude'},home,definitionHome:home,configHome:null},fingerprint:autopilotLaunchFingerprint({cwd:f.source,agent:{kind:"claude"}})}}));
 const offered=[];const result=await tickAutopilot(stateFile,{...healthyMachine, checkCapacityPorts:isolatedCheckCapacity(f.base),env:f.ports.env,now:()=>now,readRunProgress:async()=>[],warn:text=>assert.fail(text),reconcileDependencyIntake:async()=>({eligible:['https://example.test/17'],queued:[],skipped:[]}),queryIssues:async()=>({status:200,issues:[{number:17,state:'open',title:'Controlled issue',body:'Controlled work',user:{login:'example'},created_at:new Date(now).toISOString(),updated_at:new Date(now).toISOString(),comments:0,labels:[],html_url:'https://example.test/17'}]}),run:async(command,args)=>{assert.equal(command,'git');return {code:0,stdout:execFileSync('git',args,{cwd:f.source,encoding:'utf8'}),stderr:''};},herdr:async args=>{if(args[1]==='get')return {result:{agent:{agent_status:'idle',agent_session:'session'}}};if(args[0]==='pane'&&args[1]==='read')return '';assert.equal(args[1],'prompt');const text=args.at(-1),match=/Artifact path: (.+)/.exec(text);offered.push(match?readFileSync(JSON.parse(match[1]),'utf8'):text);return {};}});
 assert.equal(result.exitCode,0);assert.equal(offered.length,1);const packet=JSON.parse(offered[0].trim().split('\n').at(-1));const decisionId=packet.issues[0].decisionId;assert.ok(decisionId);
 const folder=join(f.source,'.git','pdd','metrics'),decision=JSON.parse(readFileSync(join(folder,'decisions',decisionId+'.json'),'utf8')),snapshot=JSON.parse(readFileSync(join(folder,'snapshots',decision.snapshotId.slice(9)+'.json'),'utf8'));assert.equal(validateSnapshot(snapshot,'example/project'),undefined);
 const response=await startRun({name:'small-change',issue:'17',agent:'claude',cwd:f.source,packageRoot,origin:'autopilot',decisionId},f.ports);assert.equal(response.exitCode,0,response.message);assert.equal(f.record().metricsOrigin.origin,'autopilot');assert.equal(f.record().metricsOrigin.decisionId,decisionId);
});

test('canonical snapshot validation is pure and accepts deeply frozen records',()=>{
 const at='2026-10-27T17:00:00.000Z';const event={schema:'pdd.metrics.event.v1',id:token+':selection',repo:'example/project',issue:17,type:'selection',at,observedAt:at,source:'install:pure',data:{snapshotId,inScope:true,state:'ready',reasons:[]}};const snapshot={snapshotId,repo:'example/project',source:'install:pure',observedAt:at,events:[event]};const before=JSON.stringify(snapshot);
 const freeze=value=>{if(value&&typeof value==='object'){Object.values(value).forEach(freeze);Object.freeze(value);}};freeze(snapshot);assert.equal(validateSnapshot(snapshot,'example/project'),undefined);assert.equal(JSON.stringify(snapshot),before);assert.throws(()=>validateSnapshot(snapshot,'other/repo'),/Invalid metrics/);
});
