import test from 'node:test';
import assert from 'node:assert/strict';

const { expandSource } = await import(process.env.PDD_FORMAL_MODULE || '../src/runtime/contract-refs.mjs');

test('bounded empty-object insertions preserve values, own keys and surrounding bytes', () => {
  const keys = ['x', '__proto__', 'constructor'];
  const values = [false, null, ''];
  let cases = 0;
  for (const whitespace of ['', ' \n ']) {
    for (const nested of [false, true]) {
      for (const firstKey of keys) for (const firstValue of values) {
        for (const secondKey of [null, ...keys.filter(key => key !== firstKey)]) {
          for (const secondValue of secondKey === null ? [null] : values) {
            const seed = nested ? `{"box":{${whitespace}}}` : `{${whitespace}}`;
            const entries = [[firstKey, firstValue], ...(secondKey === null ? [] : [[secondKey, secondValue]])];
            const set = Object.fromEntries(entries.map(([key, value]) => [`/${nested ? 'box/' : ''}${key}`, value]));
            const reference = JSON.stringify({$seed:'contracts/empty.json', set});
            const before = ' \n{"literal":false,"initial_world":';
            const after = ',"tail":"unchanged"} \n';
            const source = before + reference + after;
            const files = {stat: () => ({exists:true,is_symlink:false,size:Buffer.byteLength(seed)}), read: () => ({content:seed})};
            const members = entries.map(([key, value]) => `${JSON.stringify(key)}:${JSON.stringify(value)}`).join(',');
            const expected = nested ? `{"box":{${members}${whitespace}}}` : `{${members}${whitespace}}`;
            const result = expandSource({path:'test/runtime/empty-seed.json', text:source, format:'scenario'}, files);
            assert.equal(result.text, before + expected + after, `case ${cases}: ${seed} ${JSON.stringify(entries)}`);
            const world = JSON.parse(result.text).initial_world;
            const object = nested ? world.box : world;
            assert.equal(Object.getPrototypeOf(object), Object.prototype);
            for (const [key, value] of entries) {
              assert.ok(Object.hasOwn(object, key));
              assert.deepEqual(object[key], value);
            }
            assert.equal(files.read().content, seed);
            cases++;
          }
        }
      }
    }
  }
  assert.equal(cases, 252);
});
