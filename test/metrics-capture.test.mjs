import { test } from 'node:test';
import { strict as assert } from 'node:assert';
import { captureObservation, backfillRun, recordObservation } from '../src/metrics-capture.mjs';
const base = {id:'e1',repo:'Owner/Repo',issue:3,source:'machine',at:'2026-11-05T12:00:00Z',observedAt:'2026-11-05T12:00:00Z',attempt:'run-1'};
test('keeps explicit start and strips private fields', () => {
  const e = captureObservation({...base,type:'start',data:{origin:'autopilot',decisionId:'launch-1',cliVersion:'1',requiredOutcome:'code',chat:'private text'}});
  assert.deepEqual(e.data,{origin:'autopilot',decisionId:'launch-1',cliVersion:'1',requiredOutcome:'code'});
  assert.equal(e.repo,'owner/repo');
  assert.throws(()=>captureObservation({...base,type:'start',data:{origin:'claimed'}}));
});
test('backfill preserves only dated saved steps, never infers a start or copies summaries', () => {
  const result = backfillRun({run:{repo:'o/r',number:1,runId:'r',startedAt:100,done:{review:{at:1000,summary:'secret'},build:{summary:'secret'}}},source:'s',observedAt:base.observedAt,idPrefix:'old'});
  assert.equal(result.length,1); assert.equal(result[0].type,'step'); assert.deepEqual(result[0].data,{step:'review',status:'done'});
});
test('recording failures are reported and do not throw', async () => {
  const result = await recordObservation({root:'/repo',observation:{...base,type:'launch',data:{origin:'autopilot',status:'attempted'}},store:{appendEvents(){throw Error('unavailable');}}});
  assert.deepEqual(result,{ok:false,error:'unavailable'});
});
