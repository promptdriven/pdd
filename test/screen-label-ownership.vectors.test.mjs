import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, join, relative } from 'node:path';
import { compareScreen } from '../src/screen-compare.mjs';
import { temp } from './runtime-fake.mjs';

// Replay the approved native vectors without deriving expectations from code.
const vectors = JSON.parse(readFileSync(new URL('./runtime/screen-label-ownership.json', import.meta.url), 'utf8'));
for (const vector of vectors.cases) test(`label ownership vector: ${vector.case_id}`, async t => {
  const root = temp(t);
  for (const [path, file] of Object.entries(vectors.files)) {
    assert.equal(file.is_symlink, false, 'this replay requires regular drawing files');
    const destination = join(root, relative('/', path));
    mkdirSync(dirname(destination), { recursive: true });
    writeFileSync(destination, file.content);
  }
  // Only relocate the declared filesystem world into this test's temporary root.
  const input = { ...vector.input, cwd: join(root, relative('/', vector.input.cwd)) };
  const result = await compareScreen(input, { browser: async () => structuredClone(vector.browser_reply) });
  for (const check of vector.checks) {
    const label = `${vector.case_id} ${check.criterion_id} ${check.path} ${check.op}`;
    assert.equal(check.target, 'result', `${label}: unsupported replay target`);
    const actual = check.path.split('/').slice(1).reduce((value, key) => value[key.replace(/~1/g, '/').replace(/~0/g, '~')], result);
    if (check.op === 'equals') assert.deepEqual(actual, check.value, label);
    else if (check.op === 'count') assert.equal(actual.length, check.value, label);
    else assert.fail(`${label}: unsupported replay operation`);
  }
});
