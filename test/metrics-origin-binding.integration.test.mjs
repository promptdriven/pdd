import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture,packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {startRun} from '../src/workflow-runner.mjs';

const id='11234567-89ab-4cde-8fab-123456789abc';
const snapshotId='snapshot:21234567-89ab-4cde-8fab-123456789abc';
for (const scenario of ['committed matching','missing snapshot flagged','missing snapshot false','missing snapshot flag absent','wrong snapshot issue','wrong snapshot member repo','wrong snapshot member type']) {
  test(`origin requires committed matching membership: ${scenario}`,async t=>{
    const f=await fixture(t); f.ports.skipMetricsDelivery=true;
    const dir=join(f.source,'.git','pdd','metrics');mkdirSync(join(dir,'decisions'),{recursive:true});
    const selection={schema:'pdd.metrics.event.v1',id:`${id}:selection`,repo:'example/project',issue:17,type:'selection',at:'2026-10-27T17:00:00.000Z',observedAt:'2026-10-27T17:00:00.000Z',source:'install:fixture',data:{snapshotId,inScope:true,state:'ready',reasons:[]}};
    const decision={id,repo:'example/project',issue:17,offered:true,snapshotId,pendingSnapshot:true,events:[selection]};
    if(scenario==='missing snapshot false')decision.pendingSnapshot=false;
    if(scenario==='missing snapshot flag absent')delete decision.pendingSnapshot;
    writeFileSync(join(dir,'decisions',`${id}.json`),JSON.stringify(decision));
    if(!scenario.startsWith('missing')) {
      mkdirSync(join(dir,'snapshots'));
      const member=structuredClone(selection);
      if(scenario==='wrong snapshot issue')member.issue=18;
      if(scenario==='wrong snapshot member repo')member.repo='elsewhere/repo';
      if(scenario==='wrong snapshot member type')member.type='launch';
      writeFileSync(join(dir,'snapshots',`${snapshotId.slice(9)}.json`),JSON.stringify({snapshotId,repo:'example/project',source:'install:fixture',observedAt:selection.observedAt,events:[member]}));
    }
    const response=await startRun({name:'small-change',issue:'17',agent:'claude',cwd:f.source,packageRoot,origin:'autopilot',decisionId:id},f.ports);
    assert.equal(response.exitCode,0,response.message);
    const actual=f.record().metricsOrigin.origin;
    console.log(JSON.stringify({scenario,expected:scenario==='committed matching'?'autopilot':'unknown',actual,nativeWorkflowExit:response.exitCode}));
    assert.equal(actual,scenario==='committed matching'?'autopilot':'unknown','unverifiable metadata must remain unknown without blocking workflow');
  });
}

for (const scenario of ['committed false flag','committed absent flag','malformed snapshot JSON','snapshot has no events','wrong snapshot token','wrong snapshot identifier','wrong decision token','wrong decision issue','wrong decision repo','not offered','wrong retained selection type','wrong retained selection snapshot','wrong retained selection schema','wrong member schema','wrong member snapshot','contradictory selection observation']) {
 test(`origin binding counterexample: ${scenario}`,async t=>{
  const f=await fixture(t);f.ports.skipMetricsDelivery=true;const dir=join(f.source,'.git','pdd','metrics');mkdirSync(join(dir,'decisions'),{recursive:true});mkdirSync(join(dir,'snapshots'),{recursive:true});
  const selection={schema:'pdd.metrics.event.v1',id:`${id}:selection`,repo:'example/project',issue:17,type:'selection',at:'2026-10-27T17:00:00.000Z',observedAt:'2026-10-27T17:00:00.000Z',source:'install:fixture',data:{snapshotId,inScope:true,state:'ready',reasons:[]}};
  const decision={id,repo:'example/project',issue:17,offered:true,snapshotId,pendingSnapshot:true,events:[structuredClone(selection)]};
  const snapshot={snapshotId,repo:'example/project',source:'install:fixture',observedAt:selection.observedAt,events:[structuredClone(selection)]};
  if(scenario==='committed false flag')decision.pendingSnapshot=false;
  if(scenario==='committed absent flag')delete decision.pendingSnapshot;
  if(scenario==='snapshot has no events')delete snapshot.events;
  if(scenario==='wrong snapshot token')snapshot.events[0].id='31234567-89ab-4cde-8fab-123456789abc:selection';
  if(scenario==='wrong snapshot identifier')snapshot.snapshotId='snapshot:31234567-89ab-4cde-8fab-123456789abc';
  if(scenario==='wrong decision token')decision.id='31234567-89ab-4cde-8fab-123456789abc';
  if(scenario==='wrong decision issue')decision.issue=18;
  if(scenario==='wrong decision repo')decision.repo='other/repo';
  if(scenario==='not offered')decision.offered=false;
  if(scenario==='wrong retained selection type')decision.events[0].type='launch';
  if(scenario==='wrong retained selection snapshot')decision.events[0].data.snapshotId='snapshot:31234567-89ab-4cde-8fab-123456789abc';
  if(scenario==='wrong retained selection schema')decision.events[0].schema='invalid';
  if(scenario==='wrong member schema')snapshot.events[0].schema='invalid';
  if(scenario==='wrong member snapshot')snapshot.events[0].data.snapshotId='snapshot:31234567-89ab-4cde-8fab-123456789abc';
  if(scenario==='contradictory selection observation')snapshot.events[0].data.state='waiting';
  writeFileSync(join(dir,'decisions',`${id}.json`),JSON.stringify(decision));writeFileSync(join(dir,'snapshots',`${snapshotId.slice(9)}.json`),scenario==='malformed snapshot JSON'?'{invalid':JSON.stringify(snapshot));
  const response=await startRun({name:'small-change',issue:'17',agent:'claude',cwd:f.source,packageRoot,origin:'autopilot',decisionId:id},f.ports);assert.equal(response.exitCode,0,response.message);
  const valid=scenario==='committed false flag'||scenario==='committed absent flag';assert.equal(f.record().metricsOrigin.origin,valid?'autopilot':'unknown');
 });
}
