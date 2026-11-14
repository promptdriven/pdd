import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { findTests, preflight, interfaceBlocks, proseSha256 } from '../../src/runtime-seam.mjs';
import { harbor, PLACE } from './runtime-fake.mjs';

const TEST = 'tests/place-order.json';
const object = properties => ({ type: 'object', properties, required: [], additionalProperties: false });
const leaf = () => object({ child: { type: 'string' }, list: { type: 'array', items: { type: 'string' } } });

// Story oracle: either branch explicitly contains the named optional property,
// and only its child and array-item paths exist. All objects are closed.
test('bounded result paths are admitted iff a branch permits them', t => {
  const { repo } = harbor(t);
  const testPath = join(repo, TEST), promptPath = join(repo, PLACE);
  const doc = JSON.parse(readFileSync(testPath, 'utf8'));
  doc.steps[0].checks = [doc.steps[0].checks[0]];
  const original = readFileSync(promptPath, 'utf8');
  const block = interfaceBlocks(original)[0];
  const names = ['a', 'a/b'];
  const paths = [
    ['/a/child', 'a', true], ['/a/list/0', 'a', true],
    ['/a~1b/child', 'a/b', true], ['/a~1b/list/0', 'a/b', true],
    ['/missing/child', 'missing', true], ['/a/missing', 'a', false],
    ['/a/list/0/missing', 'a', false],
  ];
  const mismatches = [];
  let cases = 0;
  for (let left = 0; left < 4; left++) for (let right = 0; right < 4; right++) {
    const subsets = [left, right].map(mask => names.filter((_, i) => mask & (1 << i)));
    const iface = JSON.parse(block[1]);
    iface.entries[0].result_schema = { oneOf: subsets.map((subset, index) => object({ branch: { const: index, type: 'integer' }, ...Object.fromEntries(subset.map(name => [name, leaf()])) })) };
    iface.status = 'draft';
    let prompt = original.slice(0, block.indices[1][0]) + JSON.stringify(iface) + original.slice(block.indices[1][1]);
    prompt = prompt.replace(/"prose_sha256"\s*:\s*"[^"]*"/, `"prose_sha256":"${proseSha256(prompt)}"`);
    writeFileSync(promptPath, prompt);
    for (const [path, name, suffixExists] of paths) {
      doc.steps[0].checks[0].path = path;
      writeFileSync(testPath, JSON.stringify(doc));
      const found = findTests({ root: repo });
      const row = preflight({ root: repo, found, selected: found.tests.filter(item => item.path === TEST) }).rows[0];
      const refused = row.refusals.some(item => item.code === 'invalid-check');
      const permitted = suffixExists && subsets.some(subset => subset.includes(name));
      if (refused === permitted) mismatches.push({ left, right, path, permitted, refused });
      cases++;
    }
  }
  assert.equal(cases, 112);
  assert.deepEqual(mismatches, [], `${mismatches.length} admission mismatches: ${JSON.stringify(mismatches.slice(0, 4))}`);
});
