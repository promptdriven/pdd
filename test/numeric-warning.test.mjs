import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, symlinkSync } from 'node:fs';
import { join } from 'node:path';
import { numberWarnings, findTests, preflight, sha256, captureSource } from '../src/runtime-preflight.mjs';
import { harbor } from './runtime-fake.mjs';

const criterion = 'Enforce a cumulative usage cap of 100 across the worker and watchdog.';
const check = (path, value, extra = {}) => ({ criterion_id:'AC8', target:'result', path, op:'equals', value, ...extra });
const doc = (checks, text = criterion) => ({ story_path:'user_stories/budget.md', criteria:[{id:'AC8',text}], steps:[{step_id:'usage',checks}] });

test('NUMERIC2504: components 95 and 5 plus total100 do not warn or change expected values', () => {
  const source=doc([check('/worker_usage',95),check('/watchdog_usage',5),check('/total_usage',100)]), before=structuredClone(source);
  assert.deepEqual(numberWarnings(source),[]);
  assert.deepEqual(source,before);
  assert.deepEqual(numberWarnings(doc([check('/worker_usage',95)])),[]);
});

test('NUMERIC2504: a same-quantity limit95 versus100 remains possible typo advice with locations', () => {
  const warnings=numberWarnings(doc([check('/limit',95),check('/other',100)],'The limit is 100.'),{testPath:'tests/budget.json'});
  assert.equal(warnings.length,1);
  for(const part of ['possible numeric mismatch','tests/budget.json','steps[0].checks[0]','result /limit','user_stories/budget.md','AC8','95','100','different quantities','correct expected value','pdd-numeric-reviews.json']) assert.ok(warnings[0].includes(part),part);
});

test('NUMERIC2504: same-path or different-criterion assertions cannot hide a typo', () => {
  const source=doc([check('/limit',95),check('/limit',100),check('/total',100,{criterion_id:'OTHER'})],'The limit is 100.');
  assert.equal(numberWarnings(source).length,1);
  assert.equal(numberWarnings(doc([check('/x',95),check('/x',100)])).length,1);
});

test('NUMERIC2504: companion values and one_of suppress only distinct quantities, not total typos', () => {
  assert.deepEqual(numberWarnings(doc([check('/component',95,{op:'one_of',value:[95,5]}),check('/total_usage',100)])),[]);
  assert.equal(numberWarnings(doc([check('/total_usage',95),check('/component',100)])).length,1);
});

test('NUMERIC2504: call, world, count, far and exact values remain silent', () => {
  assert.deepEqual(numberWarnings(doc([check('/worker',95,{target:'calls'}),check('/worker',95,{target:'world'}),check('/items',95,{op:'count'}),check('/x',5),check('/limit',100)])),[]);
});

const review = { test_path:'tests/budget.json',test_sha256:'a'.repeat(64),step_id:'usage',criterion_id:'AC8',target:'result',path:'/x',value:95,reason:'This is the derived subtotal; the stated cap is a separate quantity.' };
test('NUMERIC2504: reviewed advisory is scoped to exact test bytes, step, quantity and value', () => {
  const source=doc([check('/x',95)]), context={testPath:review.test_path,testSha:review.test_sha256,reviews:[review]};
  assert.deepEqual(numberWarnings(source,context),[]);
  for(const [key,value] of Object.entries({test_path:'tests/other.json',test_sha256:'b'.repeat(64),step_id:'other',criterion_id:'OTHER',target:'error',path:'/other',value:94,reason:''})) {
    assert.equal(numberWarnings(source,{...context,reviews:[{...review,[key]:value}]}).length,1,key);
  }
});

test('NUMERIC2504: local review metadata leaves test bytes, P1-P10 and uploaded source unchanged', t => {
  const setup=harbor(t),file=join(setup.repo,'tests/place-order.json');
  const source=JSON.parse(readFileSync(file)); source.steps[0].checks[0].value=899;
  writeFileSync(file,JSON.stringify(source)+'\n');
  const before=readFileSync(file), c=source.steps[0].checks[0];
  const row={...review,test_path:'tests/place-order.json',test_sha256:sha256(before),step_id:source.steps[0].step_id,criterion_id:c.criterion_id,target:c.target,path:c.path,value:899};
  const config=join(setup.repo,'pdd-numeric-reviews.json');
  writeFileSync(config,JSON.stringify({schema_version:'pdd.numeric-reviews.v1',reviews:[row]}));
  const found=findTests({root:setup.repo}), selected=found.tests.filter(t=>t.path===row.test_path);
  const result=preflight({root:setup.repo,found,selected});
  assert.deepEqual(result.rows[0].warnings,[]);
  assert.deepEqual(result.rows[0].refusals,[]);
  assert.deepEqual(readFileSync(file),before);
  assert.ok(!captureSource(setup.repo,{tests:[row.test_path],appMap:null}).files.some(f=>f.path==='pdd-numeric-reviews.json'));
  source.criteria[0].text='A different criterion.'; writeFileSync(file,JSON.stringify(source));
  const changed=findTests({root:setup.repo});
  assert.equal(preflight({root:setup.repo,found:changed,selected:changed.tests.filter(t=>t.path===row.test_path)}).rows[0].refusals[0].code,'story-criterion-mismatch');
});

test('NUMERIC2504: malformed or symlink review files warn and suppress nothing', t => {
  for(const kind of ['malformed','symlink']) {
    const setup=harbor(t), file=join(setup.repo,'tests/place-order.json');
    const source=JSON.parse(readFileSync(file)); source.steps[0].checks[0].value=899; writeFileSync(file,JSON.stringify(source));
    const config=join(setup.repo,'pdd-numeric-reviews.json');
    if(kind==='malformed')writeFileSync(config,'{');else symlinkSync(file,config);
    const found=findTests({root:setup.repo}), result=preflight({root:setup.repo,found,selected:found.tests.filter(t=>t.path==='tests/place-order.json')});
    assert.equal(result.rows[0].warnings.length,1);
    assert.ok(result.warnings.some(text=>text.includes('pdd-numeric-reviews.json')&&text.includes('ignored')),kind);
  }
});
