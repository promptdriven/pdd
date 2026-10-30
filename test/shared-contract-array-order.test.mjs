import test from 'node:test';
import assert from 'node:assert/strict';
import { expandSource, catalogRecords } from '../src/contract-refs.mjs';

const path = 'contracts/ordered.json';
const port = text => ({
  stat: () => ({exists:true,is_symlink:false,size:Buffer.byteLength(text)}),
  read: () => ({content:text}),
});
const catalogValue = text => {
  const catalog = catalogRecords([{path,text}]);
  assert.deepEqual(catalog.warnings,[]);
  return catalog.records.find(record => record.target === `${path}#`).value_json;
};

test('canonical seed snapshots preserve array order at lengths 0 through 16', async t => {
  for (let length=0;length<=16;length++) await t.test(`length ${length}`, () => {
    const list = JSON.stringify(Array.from({length},(_,i)=>i));
    const text = `{\n "sequence": ${list},\n "nested": [{"z": ${list}, "a": [${list}, {"z":false,"a":null}]}],\n "2": 2, "10": 10\n}`;
    const expected = `{"10":10,"2":2,"nested":[{"a":[${list},{"a":null,"z":false}],"z":${list}}],"sequence":${list}}`;
    const input = ` { "initial_world": {"$seed":"${path}"}, "literal": ${list} }\n`;
    const result = expandSource({path:'scenario.json',text:input,format:'scenario'},port(text));
    assert.equal(result.text,input.replace(`{"$seed":"${path}"}`,text));
    assert.equal(result.references.length,1);
    assert.equal(result.references[0].value_json,expected);
    assert.equal(catalogValue(text),expected);
  });
});

test('canonical schema snapshots preserve nested literal array order at lengths 0 through 16', async t => {
  for (let length=0;length<=16;length++) await t.test(`length ${length}`, () => {
    const list = JSON.stringify(Array.from({length},(_,i)=>i));
    const text = `{ "type": "array", "items": {"type":"number"}, "default": ${list}, "examples": [${list}], "enum": [${list}], "const": {"sequence":${list},"nested":[${list}]} }`;
    const expected = `{"const":{"nested":[${list}],"sequence":${list}},"default":${list},"enum":[${list}],"examples":[${list}],"items":{"type":"number"},"type":"array"}`;
    const result = expandSource({path:'consumer.prompt.md',text:`{"$contract":"${path}#"}`,format:'json-schema'},port(text));
    assert.equal(result.text,text);
    assert.equal(result.references.length,1);
    assert.equal(result.references[0].value_json,expected);
    assert.equal(catalogValue(text),expected);
  });
});
