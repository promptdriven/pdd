import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import * as body from '../src/workflow-pr-body.mjs';
import {interfaceBlocks,interfaceSchemaProblems,checkInput} from '../src/runtime-seam.mjs';
import {smallChange} from './helpers/readable-pr-fixtures.mjs';
const contract=()=>JSON.parse(interfaceBlocks(readFileSync(new URL('../prompts/cli/workflow-pr-body.prompt.md',import.meta.url),'utf8'))[0][1]);
test('typed field adapter preserves arbitrary note paths and case columns',()=>{
  assert.equal(typeof body.readPrFieldsJson,'function');
  const texts=['Problem: value mismatch\nCase: 7 | 8 | 9 | 9\nFile: src/custom/δ.mjs — boundary'];
  const result=JSON.parse(body.readPrFieldsJson(texts));
  assert.deepEqual(result.cases,[{input:'7',before:'8',after:'9',expected:'9'}]);
  assert.deepEqual(result.notes,{'src/custom/δ.mjs':'boundary'});
  assert.equal(result.problem,'value mismatch');
  assert.deepEqual(interfaceSchemaProblems(contract()),[]);
});
test('typed renderer adapter admits full native facts and keeps status, notes and safe paths',()=>{
  assert.equal(typeof body.readablePrTopJson,'function');
  const facts=smallChange();facts.records.ci='passing';
  facts.diff.files[0].path='src/custom/δ.mjs';facts.fields.notes={'src/custom/δ.mjs':'boundary'};
  const input={factsJson:JSON.stringify(facts),fileLimit:40};
  const entry=contract().entries.find(e=>e.operation==='readablePrTopJson');
  assert.deepEqual(checkInput(input,entry.input_schema,0).refusals,[]);
  const result=body.readablePrTopJson(input);
  assert.match(result.text,/^✅/);assert.ok(result.text.includes('src/custom/δ.mjs'));assert.ok(result.text.includes('boundary'));
  assert.ok(Array.isArray(result.notes));assert.doesNotMatch(result.text,/pdd-workflow:/);
  for(const factsJson of ['{','null','[]','4'])assert.throws(()=>body.readablePrTopJson({factsJson}),{code:'invalid-facts'});
});
