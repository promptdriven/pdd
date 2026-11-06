import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { startRun, openRun, runStatus, cancelRun } from '../src/workflow-runner.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const starts = run => (run.metrics?.events ?? []).filter(e => e.type === 'start');
const closed = () => Object.assign(Error('closed channel'), {code:'server_unavailable'});
const status = f => runStatus({ref:'17',json:true,cwd:f.source}, f.ports);
const launch = (f, extra={}) => startRun({name:'small-change',issue:'17',agent:'claude',cwd:f.source,packageRoot,...extra},f.ports);

for (const scenario of ['manual','unknown','autopilot','unlinked autopilot']) {
  test(`confirmed lifecycle start records ${scenario} origin once across repeated status`, async t => {
    const f=await fixture(t); f.ports.skipMetricsDelivery=true;
    const id='11234567-89ab-4cde-8fab-123456789abc';
    if (scenario==='autopilot') {
      const dir=join(f.source,'.git','pdd','metrics','decisions'); mkdirSync(dir,{recursive:true});
      writeFileSync(join(dir,`${id}.json`),JSON.stringify({id,repo:'example/project',issue:17,offered:true,events:[{type:'selection',repo:'example/project',issue:17}]}));
    }
    const options=scenario==='manual'?{origin:'manual',outcome:'code'}:scenario.includes('autopilot')?{origin:'autopilot',decisionId:id}:{};
    assert.equal((await launch(f,options)).exitCode,0);
    assert.equal(starts(f.record()).length,0,'launch alone does not establish an exact running observation');
    assert.ok(f.record().metrics.events.some(e=>e.type==='coverage' && e.data.complete===false),'an unobserved or fast-ended worker remains an explicit coverage gap');
    await status(f); await status(f);
    const events=starts(f.record()); assert.equal(events.length,1);
    assert.equal(events[0].attempt,f.record().runId);
    assert.equal(events[0].data.origin,scenario==='autopilot'?'autopilot':scenario==='manual'?'manual':'unknown');
    assert.equal(events[0].data.decisionId,scenario==='autopilot'?id:undefined);
    if(scenario==='manual') { assert.equal(events[0].data.requiredOutcome,'code'); assert.match(events[0].data.candidateVersion,/^sha256:[a-f0-9]{64}$/); assert.ok((f.record().metrics.events).some(e=>e.type==='coverage' && e.data.complete===false)); }
  });
}

test('failed startup and uncertain delivery do not create a start until exact live observation', async t => {
  const f=await fixture(t), healthy=f.ports.herdr; f.ports.skipMetricsDelivery=true;
  f.ports.herdr=async args=>{const result=await healthy(args); if(args[0]==='pane'&&args[1]==='run') throw closed(); return result;};
  assert.equal((await launch(f,{origin:'manual'})).exitCode,1);
  assert.equal(starts(f.record()).length,0);
  const pane=f.herdr.paneOf(f.record().chats[0]);
  f.ports.herdr=async args=>{if(args[0]==='agent') throw closed(); return healthy(args);};
  await status(f); assert.equal(starts(f.record()).length,0); assert.equal(pane.commands.length,1);
  f.ports.herdr=healthy;
  assert.equal((await openRun({ref:'17',cwd:f.source},f.ports)).exitCode,0);
  await status(f); await status(f);
  assert.equal(starts(f.record()).length,1); assert.equal(pane.commands.length,1);
});

test('cancel and restart creates a distinct attempt with its own exact start', async t => {
  const f=await fixture(t); f.ports.skipMetricsDelivery=true;
  assert.equal((await launch(f,{origin:'manual'})).exitCode,0);
  await status(f); const first=f.record(); assert.equal(starts(first).length,1);
  assert.equal((await cancelRun({ref:'17',cwd:f.source},f.ports)).exitCode,0);
  assert.equal((await launch(f,{origin:'manual'})).exitCode,0);
  await status(f); const second=f.record();
  assert.notEqual(second.runId,first.runId); assert.equal(starts(second).length,1);
  assert.equal(starts(second)[0].attempt,second.runId);
  assert.notEqual(starts(first)[0].id,starts(second)[0].id);
});

test('a running agent with a different session is not a confirmed start', async t => {
  const f=await fixture(t); f.ports.skipMetricsDelivery=true;
  assert.equal((await launch(f,{origin:'manual'})).exitCode,0);
  const pane=f.herdr.paneOf(f.record().chats[0]);
  pane.agent.agent_session.value='11111111-1111-4111-8111-111111111111';
  await status(f); assert.equal(starts(f.record()).length,0);
});

test('delayed status uses native start time across midnight',async t=>{
 const f=await fixture(t); f.ports.skipMetricsDelivery=true; f.clock=Date.parse('2026-11-05T23:59:00Z');
 assert.equal((await launch(f,{origin:'manual'})).exitCode,0); f.clock=Date.parse('2026-11-06T00:05:00Z'); await status(f);
 assert.equal(starts(f.record()).length,1); assert.equal(starts(f.record())[0].at,'2026-11-05T23:59:00.000Z');
});
test('missing live session or native timestamp cannot assert a start',async t=>{
 for (const missing of ['live','time']) { const f=await fixture(t); f.ports.skipMetricsDelivery=true; assert.equal((await launch(f,{origin:'manual'})).exitCode,0);
  if(missing==='live') f.herdr.paneOf(f.record().chats[0]).agent.agent_session.value=null;
  else f.ports.findNativeSessions=async()=>[{id:f.record().chats[0].session.id}];
  await status(f); assert.equal(starts(f.record()).length,0);
 }
});

test('a fast-ended worker without native session metadata remains unknown',async t=>{
 const f=await fixture(t); f.ports.skipMetricsDelivery=true; assert.equal((await launch(f,{origin:'manual'})).exitCode,0);
 f.herdr.paneOf(f.record().chats[0]).agent=null; f.ports.findNativeSessions=async()=>[]; f.tick(120000);
 await status(f); assert.equal(starts(f.record()).length,0); assert.ok(f.record().metrics.events.some(e=>e.type==='coverage' && !e.data.complete));
});
