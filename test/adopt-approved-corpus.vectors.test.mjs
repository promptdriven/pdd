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
    const actual=pointer(result,check.path), label=`${step.step_id} check ${index} ${check.criterion_id} ${check.path}`;
    if(check.op==='equals')assert.deepEqual(actual,check.value,label);
    else if(check.op==='contains') {
      assert.ok(typeof actual==='string' || Array.isArray(actual),`${label}: contains requires a string or array`);
      assert.ok(actual.includes(check.value),`${label}: missing ${JSON.stringify(check.value)} in ${JSON.stringify(actual)}`);
    } else assert.fail(`Unmapped assertion: ${check.op}`);
  }
});
