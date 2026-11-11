import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { interfaceBlocks, checkInput, findTests } from '../src/runtime/runtime-preflight.mjs';
import { loadRuntimeWorkspace } from '../src/runtime/runtime-workspace.mjs';
import { fileURLToPath } from 'node:url';

test('817: workspace port grammar rejects absolute paths and keeps the native relative callback', () => {
  const text = readFileSync(new URL('../prompts/cli/runtime-workspace.prompt.md', import.meta.url), 'utf8');
  const declaration = JSON.parse(interfaceBlocks(text)[0][1]);
  const operations = declaration.resources.find(resource => resource.name === 'files').operations;
  for (const name of ['stat', 'read']) {
    const operation = operations.find(operation => operation.name === name);
    assert.deepEqual(checkInput({ path: 'pdd-workspace.json' }, operation.arguments_schema, 0).refusals, []);
    for (const path of ['/synthetic/repo/pdd-workspace.json', 'other.json', './pdd-workspace.json']) {
      assert.ok(checkInput({ path }, operation.arguments_schema, 0).refusals.length,
        `${name} must retain the adapter-owned literal path: ${path}`);
    }
  }
  const calls = [];
  assert.deepEqual(loadRuntimeWorkspace({ root: '/synthetic/repo' }, {
    stat: args => { calls.push(['stat', args]); return { exists: true, is_symlink: false, size: 20 }; },
    read: args => { calls.push(['read', args]); return { content: '{"allowed_paths":[]}' }; },
  }), { configured: true, allowed_paths: [] });
  assert.deepEqual(calls, [['stat', { path: 'pdd-workspace.json' }], ['read', { path: 'pdd-workspace.json' }]]);
});

test('817: all saved-evidence native vectors remain present without claiming Runtime discovery', () => {
  const vectors = JSON.parse(readFileSync(new URL('./cases/import-authorized-workspace-evidence.scenario', import.meta.url), 'utf8'));
  assert.equal(vectors.steps.length, 19);
  assert.ok(vectors.steps.every(step => step.operation === 'recordEvidence' && step.checks.length));
  const root = fileURLToPath(new URL('../', import.meta.url));
  const found = findTests({ root });
  assert.ok(!found.tests.some(test => test.story === 'import-authorized-workspace-evidence'),
    'the unsupported Runtime operation remains native-only test data');
  assert.ok(found.tests.some(test => test.story === 'bounded-workspace-policy'),
    'the executable workspace scenario stays in Runtime discovery');
});
