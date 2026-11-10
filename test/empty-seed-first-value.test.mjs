import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { expandSource } from '../src/contract-refs.mjs';

const expand = (seed, overrides) => {
  const reference = JSON.stringify({$seed:'contracts/empty.json',set:overrides});
  const text = ` { "before": 1, "initial_world": ${reference}, "after": 2 }\n`;
  const result = expandSource({path:'scenario.json',text,format:'scenario'}, {
    stat: () => ({exists:true,is_symlink:false,size:Buffer.byteLength(seed)}),
    read: () => ({content:seed}),
  });
  return {text, reference, result};
};

test('first seed members remain own falsy values inside root and nested empty objects', async t => {
  for (const nested of [false,true]) for (const key of ['x','__proto__','constructor']) for (const value of [false,null,'']) {
    await t.test(`${nested ? 'nested' : 'root'} ${key} ${JSON.stringify(value)}`, () => {
      const seed = nested ? '{"nested":{}}' : '{}';
      const pointer = `${nested ? '/nested' : ''}/${key}`;
      const {result} = expand(seed,{[pointer]:value});
      const world = JSON.parse(result.text).initial_world;
      const target = nested ? world.nested : world;
      assert.equal(Object.getPrototypeOf(target),Object.prototype);
      assert.ok(Object.hasOwn(target,key));
      assert.equal(target[key],value);
      assert.equal(result.references[0].value_json,seed);
    });
  }
});

test('empty layout whitespace and surrounding source survive multiple additions', () => {
  const seed = '{ "nested": { \n }, "keep": 1 }';
  const {text,reference,result} = expand(seed,{'/nested/a':false,'/nested/b':null});
  assert.equal(result.text,text.replace(reference,'{ "nested": {"a":false,"b":null \n }, "keep": 1 }'));
  assert.deepEqual(JSON.parse(result.text).initial_world,{nested:{a:false,b:null},keep:1});
});
