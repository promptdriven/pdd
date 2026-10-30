import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';

// Dynamic loading makes the old-code control an explicit assertion, even when
// alpha has no inventory module. No missing import can masquerade as detection.
export async function inventoryModule() {
  const module = await import('../src/workflow-inventory.mjs').catch(error => {
    if (error.code === 'ERR_MODULE_NOT_FOUND' && error.url?.endsWith('/src/workflow-inventory.mjs')) return {};
    throw error;
  });
  assert.equal(typeof module.analyzeTestChanges, 'function', 'approved inventory public boundary is implemented');
  assert.equal(typeof module.collectTestInventory, 'function', 'approved collector public boundary is implemented');
  return module;
}
const pointer = (value,path) => path.split('/').slice(1).reduce((v,k)=>v[k.replace(/~1/g,'/').replace(/~0/g,'~')],value);
export async function replay(story) {
  const module = await inventoryModule();
  const scenario = JSON.parse(readFileSync(new URL(`./runtime/${story}.json`,import.meta.url),'utf8'));
  const world = structuredClone(scenario.initial_world);let calls=0;
  for(const step of scenario.steps) {
    const result = await module[step.operation](step.input,{readSnapshot:async request=>{
      calls++;
      const binding=scenario.simulation['snapshot.read'];
      pointer(world,binding.world_pointer).push(request);
      return binding.result_template;
    }});
    for(const check of step.checks) {
      const got = check.target === 'result' ? pointer(result,check.path) : check.target === 'world' ? pointer(world,check.path) : calls;
      assert.equal(check.op,'equals',`${step.step_id}: supported check operator`);
      assert.deepEqual(got,check.value,`${story} / ${step.step_id} / ${check.criterion_id} / ${check.target}${check.path}`);
    }
    calls=0;
  }
}
