import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import * as workspace from '../src/runtime-workspace.mjs';
const scenario=JSON.parse(readFileSync(new URL('./runtime/bounded-workspace-policy.json',import.meta.url),'utf8'));
const counters={stat:0,read:0};
const files=Object.fromEntries(['stat','read'].map(operation=>[operation,args=>{const index=++counters[operation];const row=scenario.simulation['files.'+operation].cases.find(c=>c.call_index===index);assert.deepEqual(args,row.args);return row.result;}]));
const at=(value,path)=>path.split('/').slice(1).reduce((v,k)=>v?.[k],value);
for(const step of scenario.steps)test('workspace policy '+step.step_id,()=>{const before=counters.read;let result,error;try{result=workspace.loadRuntimeWorkspace(step.input,files);}catch(e){error=e;}
  for(const check of step.checks){const actual=check.target==='calls'?counters.read-before:at(check.target==='error'?error:result,check.path);assert.deepEqual(actual,check.value,step.step_id+' '+check.target+check.path);}
});
test('component policy is immutable and never treats a prefix as permission',()=>{const p=workspace.loadRuntimeWorkspace({root:'/repo'},{stat:()=>({exists:true,is_symlink:false,size:1}),read:()=>({content:'{"allowed_paths":["simulation/","contracts/a.md","simulation/"]}'})});assert.deepEqual(p.allowed_paths,['simulation/','contracts/a.md']);assert.equal(workspace.allowsRuntimePath(p,'simulation-private/x'),false);assert.equal(workspace.allowsRuntimePath(p,'simulation/x'),true);assert.equal(workspace.allowsRuntimePath(p,'contracts/a.md/x'),false);assert.equal(Object.isFrozen(p.allowed_paths),true);});
