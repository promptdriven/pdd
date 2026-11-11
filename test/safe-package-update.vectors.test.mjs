import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {packageInstallDiagnostic} from '../src/path-diagnostic.mjs';

const scenario=JSON.parse(readFileSync(new URL('./runtime/safe-package-update.json',import.meta.url),'utf8'));
let reads=0;
const files={readFileSync(path,encoding) {
  assert.equal(encoding,'utf8');
  reads++;
  const fixture=scenario.simulation['files.readFileSync'].cases.find(c=>c.call_index===reads);
  assert.deepEqual(fixture?.args,{path});
  const reply=fixture.result;
  if (!reply?.found) throw Object.assign(Error('missing'),{code:'ENOENT'});
  return reply.text;
}};
for (const step of scenario.steps) test(`package advice vector: ${step.step_id}`,()=>{
  assert.equal(step.operation,'packageInstallDiagnostic');
  const result=packageInstallDiagnostic(step.input,{files});
  for (const check of step.checks) {
    assert.equal(check.target,'result');assert.equal(check.op,'equals');
    const actual=check.path.slice(1).split('/').reduce((value,key)=>value[key],result);
    assert.deepEqual(actual,check.value,`${step.step_id}: ${check.criterion_id} ${check.path}`);
  }
});
