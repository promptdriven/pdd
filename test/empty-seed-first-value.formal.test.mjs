import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { expandSource } from '../src/contract-refs.mjs';

// Exhaustive within the Story's 3 keys × 3 values × 2 depths × 3 layouts.
test('empty seed first member: bounded Story rule', () => {
  const keys = ['x', '__proto__', 'constructor'];
  const values = [false, null, ''];
  const spaces = ['', ' ', '\n  '];
  let cases = 0;
  for (const key of keys) for (const value of values) for (const nested of [false, true]) for (const space of spaces) {
    const empty = `{${space}}`;
    const seed = nested ? `{ "nested" : ${empty}, "keep" : [1, 2] }` : empty;
    const pointer = `${nested ? '/nested' : ''}/${key}`;
    const directive = `{"$seed":"contracts/seed.json","set":{${JSON.stringify(pointer)}:${JSON.stringify(value)}}}`;
    const before = '{\n  "before" : [1, 2], "initial_world" : ';
    const after = ',\n  "after" : {"sentinel":true}\n}\n';
    const source = before + directive + after;
    const files = { 'contracts/seed.json': seed };
    const port = {
      stat: ({path}) => ({exists: Object.hasOwn(files, path), is_symlink: false, size: Buffer.byteLength(files[path] ?? '')}),
      read: ({path}) => ({content: files[path]}),
    };
    const result = expandSource({path: 'test/scenario.json', text: source, format: 'scenario'}, port);
    const member = `${JSON.stringify(key)}:${JSON.stringify(value)}`;
    const inserted = `{${member}${space}}`;
    const expectedWorld = nested ? `{ "nested" : ${inserted}, "keep" : [1, 2] }` : inserted;
    const label = `${pointer}=${JSON.stringify(value)} whitespace=${JSON.stringify(space)}`;
    assert.equal(result.text, before + expectedWorld + after, label);
    const parsed = JSON.parse(result.text);
    const target = nested ? parsed.initial_world.nested : parsed.initial_world;
    assert.equal(Object.getPrototypeOf(target), Object.prototype, label);
    assert.equal(Object.getPrototypeOf(parsed.initial_world), Object.prototype, label);
    assert.ok(Object.hasOwn(target, key), label);
    assert.equal(target[key], value, label);
    assert.deepEqual(Object.keys(target), [key], label);
    assert.equal(files['contracts/seed.json'], seed, label);
    assert.deepEqual(result.references, [{consumer:'test/scenario.json', source_pointer:'/initial_world', target:'contracts/seed.json#', kind:'seed', value_json: nested ? '{"keep":[1,2],"nested":{}}' : '{}'}], label);
    cases++;
  }
  assert.equal(cases, 54);
});
