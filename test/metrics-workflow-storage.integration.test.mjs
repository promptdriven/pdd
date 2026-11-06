import { test } from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { writeRun, updateRun } from '../src/workflow-runs.mjs';

test('workflow storage journals a completion before a later update clears it', () => {
  const root = mkdtempSync(join(tmpdir(),'pdd-metrics-run-'));
  const commonDir = join(root,'.git'), runDir = join(commonDir,'pdd','runs','1');
  mkdirSync(commonDir,{recursive:true});
  const run = {v:1,runId:'attempt',repo:'example/repo',number:1,root,sourceRoot:root,commonDir,runDir,state:'running',workflow:'feature',areas:[{name:'code',steps:['build'],optional:[]}],area:0,chats:[],done:{build:{at:1700000000000}},pr:[]};
  const ports = {stateDir:join(root,'state'),metricsWarning:()=>{}};
  writeRun(run,ports);
  updateRun(runDir, current => { current.done = {}; return current; },ports);
  const saved = JSON.parse(readFileSync(join(runDir,'status.json'),'utf8'));
  assert.equal(saved.metrics.events.filter(e => e.type === 'step' && e.data.step === 'build').length,1);
  assert.equal(saved.metrics.events[0].at,'2023-11-14T22:13:20.000Z');
  assert.equal(JSON.parse(readFileSync(join(commonDir,'pdd','metrics','installation.json'),'utf8')).source,saved.metrics.events[0].source);
});

test('the retained journal survives more than 200 overwritten completions', () => {
  const root = mkdtempSync(join(tmpdir(),'pdd-metrics-many-'));
  const commonDir = join(root,'.git'), runDir = join(commonDir,'pdd','runs','2');
  mkdirSync(commonDir,{recursive:true});
  const run = {v:1,runId:'many',repo:'example/repo',number:2,root,sourceRoot:root,commonDir,runDir,state:'running',workflow:'feature',areas:[{name:'code',steps:['build'],optional:[]}],area:0,chats:[],done:{},pr:[]};
  const ports = {stateDir:join(root,'state'),metricsWarning:()=>{}};
  writeRun(run,ports);
  for (let i=0;i<205;i++) updateRun(runDir, current => { current.done.build={at:1700000000000+i}; return current; },ports);
  const saved=JSON.parse(readFileSync(join(runDir,'status.json'),'utf8'));
  assert.equal(saved.metrics.events.filter(event=>event.type==='step').length,205);
  assert.equal(new Set(saved.metrics.events.map(event=>event.id)).size,205);
});

test('identity creation failure records a coverage gap without blocking workflow', () => {
  const root = mkdtempSync(join(tmpdir(),'pdd-metrics-gap-'));
  const commonDir=join(root,'.git'), runDir=join(commonDir,'pdd','runs','3');
  mkdirSync(commonDir,{recursive:true});
  const run={v:1,runId:'gap',repo:'example/repo',number:3,root,sourceRoot:root,commonDir,runDir,state:'running',workflow:'feature',areas:[],area:0,chats:[],done:{},pr:[]};
  const ports={stateDir:join(root,'state'),metricsWarning:()=>{},runFiles:{linkSync(){throw Error('unavailable');}}};
  writeRun(run,ports);
  assert.equal(JSON.parse(readFileSync(join(runDir,'status.json'),'utf8')).metrics.coverageGap,true);
});


test('delivery failure retains the outbox and exposes a coverage gap without blocking progress', async () => {
  const root = mkdtempSync(join(tmpdir(),'pdd-metrics-drain-'));
  const commonDir=join(root,'.git'), runDir=join(commonDir,'pdd','runs','4');
  mkdirSync(commonDir,{recursive:true});
  const run={v:1,runId:'drain',repo:'example/repo',number:4,root,sourceRoot:root,commonDir,runDir,state:'running',workflow:'feature',areas:[{name:'code',steps:['build'],optional:[]}],area:0,chats:[],done:{build:{at:1700000000000}},pr:[]};
  const ports={stateDir:join(root,'state'),metricsWarning:()=>{},metricsAppendEvents:async()=>{throw Error('offline');}};
  writeRun(run,ports);
  for (let i=0;i<100;i++) {
    const saved=JSON.parse(readFileSync(join(runDir,'status.json'),'utf8'));
    if (saved.metrics.coverageGap) { assert.equal(saved.metrics.events.length,1); return; }
    await new Promise(resolve=>setTimeout(resolve,5));
  }
  assert.fail('delivery gap was not persisted');
});

test('structured outcome changes and wait/resume survive later run updates', () => {
  const root=mkdtempSync(join(tmpdir(),'pdd-metrics-transitions-'));
  const commonDir=join(root,'.git'),runDir=join(commonDir,'pdd','runs','5'); mkdirSync(commonDir,{recursive:true});
  const run={v:1,runId:'transitions',repo:'example/repo',number:5,root,sourceRoot:root,commonDir,runDir,state:'running',workflow:'feature',areas:[],area:0,chats:[],done:{},pr:[],metricsOrigin:{requiredOutcome:'prompt-only'}};
  const ports={stateDir:join(root,'state'),metricsWarning:()=>{},skipMetricsDelivery:true}; writeRun(run,ports);
  updateRun(runDir,current=>{current.state='waiting';current.gate={kind:'ask-code'};return current;},ports);
  updateRun(runDir,current=>{current.state='running';current.gate=null;current.metricsOrigin.requiredOutcome='code';return current;},ports);
  const saved=JSON.parse(readFileSync(join(runDir,'status.json'),'utf8'));
  assert.deepEqual(saved.metrics.events.map(e=>[e.type,e.data.requiredOutcome??e.data.stage,e.data.reason]),[['outcome','prompt-only',undefined],['milestone','wait','ask-code'],['outcome','code',undefined],['milestone','resume',undefined]]);
});

test('failed capture retains observations for a later successful save', () => {
  const root=mkdtempSync(join(tmpdir(),'pdd-pending-')), commonDir=join(root,'.git'), runDir=join(commonDir,'pdd','runs','6'); mkdirSync(commonDir,{recursive:true});
  const run={v:1,runId:'pending',repo:'example/repo',number:6,root,sourceRoot:root,commonDir,runDir,state:'cancelled',workflow:'feature',areas:[],area:0,chats:[],done:{},pr:[],metricsObservations:[{type:'coverage',at:'2026-11-05T00:00:00.000Z',data:{complete:false}}]};
  const ports={stateDir:join(root,'state'),metricsWarning:()=>{},skipMetricsDelivery:true};
  writeRun(run,{...ports,runFiles:{linkSync(){throw Error('unavailable');}}});
  let saved=JSON.parse(readFileSync(join(runDir,'status.json'),'utf8')); assert.equal(saved.metricsObservations.length,1); assert.equal(saved.metrics.coverageGap,true);
  updateRun(runDir,current=>current,ports); saved=JSON.parse(readFileSync(join(runDir,'status.json'),'utf8'));
  assert.equal(saved.metricsObservations,undefined); assert.ok(saved.metrics.events.some(e=>e.type==='coverage')); assert.equal(saved.metrics.coverageGap,true);
});

test('optional sync failure does not reject a valid status save', () => {
  const root=mkdtempSync(join(tmpdir(),'pdd-sync-')), commonDir=join(root,'.git'), runDir=join(commonDir,'pdd','runs','7'); mkdirSync(commonDir,{recursive:true});
  const run={v:1,runId:'sync',repo:'example/repo',number:7,root,sourceRoot:root,commonDir,runDir,state:'running',workflow:'feature',areas:[],area:0,chats:[],done:{},pr:[]};
  writeRun(run,{stateDir:join(root,'state'),metricsWarning:()=>{},skipMetricsDelivery:true,runFiles:{fsyncSync(){throw Error('sync unavailable');}}});
  assert.equal(JSON.parse(readFileSync(join(runDir,'status.json'),'utf8')).state,'running');
});

test('only a native cancellation transition records the terminal attempt', () => {
  const root=mkdtempSync(join(tmpdir(),'pdd-cancel-')),commonDir=join(root,'.git'),runDir=join(commonDir,'pdd','runs','8'); mkdirSync(commonDir,{recursive:true});
  const run={v:1,runId:'attempt-cancel',repo:'example/repo',number:8,root,sourceRoot:root,commonDir,runDir,state:'running',workflow:'feature',areas:[],area:0,chats:[],done:{},pr:[]};
  const ports={stateDir:join(root,'state'),metricsWarning:()=>{},skipMetricsDelivery:true}; writeRun(run,ports);
  updateRun(runDir,r=>{r.cancelled={state:'cancelled',at:1700000000000};return r;},ports);
  let saved=JSON.parse(readFileSync(join(runDir,'status.json'),'utf8')); assert.equal(saved.metrics.events.filter(e=>e.data.step==='cancel').length,0);
  updateRun(runDir,r=>{r.state='cancelled';return r;},ports); updateRun(runDir,r=>r,ports);
  saved=JSON.parse(readFileSync(join(runDir,'status.json'),'utf8')); const events=saved.metrics.events.filter(e=>e.data.step==='cancel');
  assert.equal(events.length,1); assert.equal(events[0].attempt,'attempt-cancel'); assert.equal(events[0].at,'2023-11-14T22:13:20.000Z'); assert.equal(events[0].data.status,'done');
});
