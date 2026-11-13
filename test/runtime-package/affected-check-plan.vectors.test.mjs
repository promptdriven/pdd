import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {selectCheckTests,baselineReport,checkPlanResults} from '../../src/runtime-seam.mjs';

const exact = text => JSON.parse(text,(key,value,context)=>typeof value === 'number'
  && /^-?(?:0|[1-9][0-9]*)$/.test(context.source) && !Number.isSafeInteger(value) ? BigInt(context.source) : value);
const at = (value,path) => path === '' ? value : path.slice(1).split('/').reduce((item,key)=>item[key.replace(/~1/g,'/').replace(/~0/g,'~')],value);
const operations = {
  selectCheckTests: input=>selectCheckTests(input.plan,{affected:input.affected}),
  baselineReport,
  checkPlanResults: input=>checkPlanResults(input.plan,input.rows)
};

for (const name of ['affected-story-selection','affected-baseline-report']) {
  const scenario = exact(readFileSync(new URL(`../runtime/${name}.json`,import.meta.url),'utf8'));
  test(`3146 approved pure Runtime replay: ${name}`,()=>{
    for (const step of scenario.steps) {
      assert.equal(typeof operations[step.operation],'function',`unmapped operation ${step.operation}`);
      const result = operations[step.operation](step.input);
      for (const [index,check] of step.checks.entries()) {
        assert.equal(check.target,'result',`unmapped target ${check.target}`);
        assert.equal(check.op,'equals',`unmapped operator ${check.op}`);
        assert.deepEqual(at(result,check.path),check.value,`${name}/${step.step_id}/${index}/${check.criterion_id}`);
      }
    }
  });
}
