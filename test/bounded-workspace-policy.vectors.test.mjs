import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,symlinkSync,unlinkSync} from 'node:fs';
import {join} from 'node:path';
import * as workspace from '../src/runtime/runtime-workspace.mjs';
import {fixture,json} from './helpers/runtime-workspace-fixture.mjs';
const scenario=JSON.parse(readFileSync(new URL('./runtime/bounded-workspace-policy.json',import.meta.url),'utf8'));
const counters={stat:0,read:0};
const files=Object.fromEntries(['stat','read'].map(operation=>[operation,args=>{const index=++counters[operation];const row=scenario.simulation['files.'+operation].cases.find(c=>c.call_index===index);assert.deepEqual(args,row.args);return row.result;}]));
const at=(value,path)=>path.split('/').slice(1).reduce((v,k)=>v?.[k],value);
for(const step of scenario.steps)test('workspace policy '+step.step_id,()=>{const before=counters.read;let result,error;try{result=workspace.loadRuntimeWorkspace(step.input,files);}catch(e){error=e;}
  for(const check of step.checks){const actual=check.target==='calls'?counters.read-before:at(check.target==='error'?error:result,check.path);assert.deepEqual(actual,check.value,step.step_id+' '+check.target+check.path);}
});
test('component policy is immutable and never treats a prefix as permission',()=>{const p=workspace.loadRuntimeWorkspace({root:'/repo'},{stat:()=>({exists:true,is_symlink:false,size:1}),read:()=>({content:'{"allowed_paths":["simulation/","contracts/a.md","simulation/"]}'})});assert.deepEqual(p.allowed_paths,['simulation/','contracts/a.md']);assert.equal(workspace.allowsRuntimePath(p,'simulation-private/x'),false);assert.equal(workspace.allowsRuntimePath(p,'simulation/x'),true);assert.equal(workspace.allowsRuntimePath(p,'contracts/a.md/x'),false);assert.equal(Object.isFrozen(p.allowed_paths),true);});

test('native policy accepts a repository ancestor alias while retaining the ceiling and refusing a linked policy',t=>{
  const f=fixture(t),alias=join(f.parent,'alias');
  symlinkSync(f.parent,alias);
  const root=join(alias,'repo');
  const policy=workspace.loadRuntimeWorkspace({root});
  assert.deepEqual(policy,workspace.loadRuntimeWorkspace({root:f.root}));
  assert.equal(policy.configured,true);
  assert.deepEqual(policy.allowed_paths,['simulation/']);
  assert.equal(workspace.allowsRuntimePath(policy,'simulation/tests/order.json'),true);
  assert.equal(workspace.allowsRuntimePath(policy,'private/ordinary.md'),false);
  unlinkSync(join(f.root,'pdd-workspace.json'));
  assert.deepEqual(workspace.loadRuntimeWorkspace({root}),{configured:false,allowed_paths:[]});
  json(f.root,'other-policy.json',{allowed_paths:['private/']});
  symlinkSync('other-policy.json',join(f.root,'pdd-workspace.json'));
  assert.throws(()=>workspace.loadRuntimeWorkspace({root}),error=>error.code==='workspace-config-unsafe');
});
