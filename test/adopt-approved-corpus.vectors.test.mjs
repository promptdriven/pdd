import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
const {adoptReplayCorpus}=await import(process.env.PDD_ADOPTION_MODULE || '../src/workflow-replay.mjs');
const doc=JSON.parse(readFileSync(new URL('./runtime/adopt-approved-corpus.json',import.meta.url)));
const world=structuredClone(doc.initial_world);
const pointer=(value,path)=>path===''?value:path.split('/').slice(1).reduce((v,k)=>v?.[k.replace(/~1/g,'/').replace(/~0/g,'~')],value);
// Replay the approved JSON unchanged. The snapshot port models local I/O only;
// every decision and original result assertion runs through the public module.
for(const step of doc.steps) test(`2640 vector ${step.step_id}`,async()=>{
  assert.equal(step.operation,'adoptReplayCorpus');let calls=0;
  const result=await adoptReplayCorpus(step.input.root,step.input.declarationPath,{readAdoptionSnapshot:async args=>{
    calls++;assert.deepEqual(args,step.input);
    return {snapshot:structuredClone(world.snapshots.find(row=>row.path===args.declarationPath)?.snapshot)};
  }});
  assert.equal(calls,1);
  for(const [index,check] of step.checks.entries()) {
    assert.equal(check.target,'result',`Unmapped target: ${check.target}`);
    assert.equal(check.op,'equals',`Unmapped assertion: ${check.op}`);
    assert.deepEqual(pointer(result,check.path),check.value,`${step.step_id} check ${index} ${check.criterion_id} ${check.path}`);
  }
});
