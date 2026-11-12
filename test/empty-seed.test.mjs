import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { expandSource } from '../src/runtime/contract-refs.mjs';

for (const seed of ['{}', '{ \n }']) {
  for (const key of ['x', '__proto__', 'constructor']) {
    for (const value of [false, null, '']) {
      test(`empty seed ${JSON.stringify(seed)} adds ${key} = ${JSON.stringify(value)}`, () => {
        const source = ` {"initial_world":{"$seed":"contracts/empty.json","set":{${JSON.stringify('/'+key)}:${JSON.stringify(value)}}},"literal":false} \n`;
        const files = {stat: () => ({exists:true,is_symlink:false,size:Buffer.byteLength(seed)}), read: () => ({content:seed})};
        const result = expandSource({path:'test/runtime/empty-seed.json',text:source,format:'scenario'},files);
        const expectedWorld = `{${JSON.stringify(key)}:${JSON.stringify(value)}${seed.slice(1,-1)}}`;
        assert.equal(result.text, ` {"initial_world":${expectedWorld},"literal":false} \n`);
        const world = JSON.parse(result.text).initial_world;
        assert.ok(Object.hasOwn(world,key));
        assert.deepEqual(world[key],value);
        assert.equal(Object.getPrototypeOf(world),Object.prototype);
        assert.equal(result.references[0].target,'contracts/empty.json#');
        assert.equal(result.references[0].value_json,'{}');
      });
    }
  }
}
