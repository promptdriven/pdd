import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { composeProductTry } from '../src/product-composition.mjs';

const cases = JSON.parse(readFileSync(new URL('./native/product-malformed-screen-values.json', import.meta.url)));
const source = JSON.parse(readFileSync(new URL('./runtime/product-compose-try.json', import.meta.url))).initial_world.files;

function compose(screenSet) {
  const files = structuredClone(source);
  const path = '/project/app/maps/phone.json';
  const map = JSON.parse(files[path].content);
  Object.assign(map.screens[0], screenSet);
  files[path].content = JSON.stringify(map);
  return composeProductTry({ root: '/project', parts: ['phone'] }, {
    statFile(path) {
      const file = files[path];
      return { exists: !!file, is_symlink: file?.is_symlink ?? false, size: file ? Buffer.byteLength(file.content) : 0 };
    },
    readFile(path) { assert.ok(Object.hasOwn(files, path), `unexpected read: ${path}`); return files[path].content; },
  });
}

for (const item of cases.invalid) test(`malformed screen value: ${item.id}`, () => {
  assert.throws(() => compose(item.screen_set), error => {
    assert.equal(error.code, item.expected_error.code);
    assert.ok(error.message.includes(item.expected_error.field), error.message);
    return true;
  });
});

for (const item of cases.valid) test(`preserved screen value: ${item.id}`, () => {
  const result = compose(item.screen_set);
  const screen = JSON.parse(result.files[0].content).screens[0];
  for (const field of item.preserve_fields) assert.deepEqual(screen[field], item.screen_set[field], field);
  assert.equal(screen.id, 'phone/menu');
  assert.deepEqual(result.parts, ['phone']);
});
