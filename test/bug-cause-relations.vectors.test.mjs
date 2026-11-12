import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { recordBugCause } from '../src/workflow-bug-cause.mjs';
const scenario=JSON.parse(readFileSync(new URL('./runtime/bug-cause-relations.json',import.meta.url),'utf8'));
const pointer=(value,path)=>path.split('/').slice(1).reduce((node,key)=>node[key.replaceAll('~1','/').replaceAll('~0','~')],value);
test('2841: replay all Story vectors on native code',async()=>{
 const world=structuredClone(scenario.initial_world);const ports={};
 for(const [name,binding] of Object.entries(scenario.simulation)){
  const [resource,operation]=name.split('.');(ports[resource]??={})[operation]=async args=>{
   if(binding.action==='port.write'){pointer(world,binding.world_pointer).push(structuredClone(args));return structuredClone(binding.result_template);}
   assert.equal(binding.action,'fixture.lookup');
   const keys=binding.world_pointer.split('/').slice(1),field=keys.pop(),parent=pointer(world,'/'+keys.join('/'));const index=++parent[field];
   const row=binding.cases.find(x=>x.call_index===index&&JSON.stringify(x.args)===JSON.stringify(args));assert.ok(row,`fixture ${name} call ${index}`);return structuredClone(row.result);
  };
 }
 for(const step of scenario.steps){
  let result,error;try{result=await recordBugCause(step.input,ports);}catch(e){error=e;}
  if(step.expected_error)assert.equal(error?.code,step.expected_error);else if(error)throw error;
  for(const check of step.checks){assert.equal(check.op,'equals');const actual=pointer({result,error,world}[check.target],check.path);assert.deepEqual(actual,check.value,`${step.step_id}: ${check.criterion_id} ${check.path}`);}
 }
});
