import {test} from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assessNativeEvidence} from '../src/workflow-results.mjs';
const pointer=(value,path)=>path.split('/').slice(1).reduce((row,key)=>row?.[key.replaceAll('~1','/').replaceAll('~0','~')],value);
export function replayNativeVectors(name) {
  const scenario=JSON.parse(readFileSync(new URL(`./runtime/${name}.json`,import.meta.url)));
  const cases=scenario.simulation['native.read_context'].cases;
  for(const step of scenario.steps)test(`${name}: ${step.step_id}`,async()=>{
    let calls=0;
    const result=await assessNativeEvidence(step.input,{readNativeContext:async input=>{calls++;const row=cases.find(row=>JSON.stringify(row.args)===JSON.stringify(input));assert.ok(row,'original supplied reader case');return row.result;}});
    for(const check of step.checks) {
      const actual=check.target==='calls'?calls:check.target==='world'?pointer(scenario.initial_world,check.path):pointer(result,check.path);
      assert.equal(['result','calls','world'].includes(check.target),true,'all original targets replayed');
      if(check.op==='equals')assert.deepEqual(actual,check.value,`${step.step_id} ${check.path}`);
      else if(check.op==='count')assert.equal(actual.length,check.value);
      else assert.fail(`unmapped original operation ${check.op}`);
    }
  });
}
