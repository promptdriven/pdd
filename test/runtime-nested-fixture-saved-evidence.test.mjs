import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createSavedStoryEvidenceReader } from '../src/runtime-client.mjs';

// Synthetic accepted saved Check records; only raw observations are injected.
const fixture = JSON.parse(readFileSync(new URL('./fixtures/product-saved-checks-owner.json', import.meta.url), 'utf8'));
const A = 'a'.repeat(64), B = 'b'.repeat(64);

function setup() {
  const records = [
    { root: '/absent', sha: A },
    { root: '/false', sha: B, policy: false },
    { root: '/true', sha: B, policy: true },
  ];
  const files = new Map(), calls = [];
  for (const [index, record] of records.entries()) {
    const name = `20261030-120000-${String(index).padStart(4, '0')}`;
    const batch = structuredClone(fixture.batch);
    Object.assign(batch, { batch: name, root: record.root, source_sha256: record.sha });
    if (index === 1) batch.rows.reverse();
    if (Object.hasOwn(record, 'policy')) batch.exclude_fixture_projects = record.policy;
    files.set(`/state/batches/${name}/batch.json`, JSON.stringify(batch));
    for (const [id, receipt] of Object.entries(fixture.receipts)) {
      files.set(`/state/batches/${name}/${id}.json`, JSON.stringify(receipt));
    }
    record.name = name;
  }
  const reader = createSavedStoryEvidenceReader({
    env: { PDD_STATE_DIR: '/state' },
    readDir: path => { assert.equal(path, '/state/batches'); return records.map(r => r.name); },
    readFile: path => { assert.ok(files.has(path), `unexpected read ${path}`); return files.get(path); },
    realpath: path => path === '/base-alias' ? '/base' : path,
    captureSource: (root, options) => {
      calls.push({ root, options: structuredClone(options) });
      return { sha256: options.excludeFixtureProjects === true ? B : A };
    },
  });
  return { reader, calls };
}

const tests = ['test/runtime/one.json', 'test/runtime/two.json'];

test('saved checks with absent and false fixture policy share the legacy capture port and judge each SHA', async () => {
  const { reader, calls } = setup();
  const absent = await reader({ root: '/absent', comparisonRoot: '/base' });
  const explicitFalse = await reader({ root: '/false', comparisonRoot: '/base-alias' });
  assert.deepEqual(absent.warnings, []);
  assert.deepEqual(explicitFalse.warnings, []);
  assert.deepEqual(absent.stories.map(row => [row.pass, row.current]), [[true, true], [true, true]]);
  assert.deepEqual(explicitFalse.stories.map(row => [row.pass, row.current]), [[true, false], [true, false]]);
  assert.deepEqual(calls, [{ root: '/base', options: { tests, appMap: null } }]);
});

test('true fixture policy is forwarded and has an independent memoized capture', async () => {
  const { reader, calls } = setup();
  const absent = await reader({ root: '/absent', comparisonRoot: '/base' });
  const excluded = await reader({ root: '/true', comparisonRoot: '/base-alias' });
  await reader({ root: '/true', comparisonRoot: '/base' });
  assert.deepEqual(absent.stories.map(row => row.current), [true, true]);
  assert.deepEqual(excluded.stories.map(row => [row.pass, row.current]), [[true, true], [true, true]]);
  assert.equal(calls.length, 2);
  assert.deepEqual(calls[1], { root: '/base', options: { tests, appMap: null, excludeFixtureProjects: true } });
});
