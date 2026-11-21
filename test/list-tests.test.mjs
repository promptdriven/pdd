import './helpers/test-home.mjs';
import './helpers/test-net-guard.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  discoverTestFiles,
  EXCLUDED_TEST_FILES,
  isBrowserTest,
} from '../scripts/list-tests.mjs';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const listScript = join(root, 'scripts', 'list-tests.mjs');

test('list-tests matches current flat test/*.test.mjs exactly while excluding baseline fixture', () => {
  const flat = readdirSync(join(root, 'test'), { withFileTypes: true })
    .filter(entry => entry.isFile() && entry.name.endsWith('.test.mjs'))
    .map(entry => `test/${entry.name}`)
    .sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));

  const all = discoverTestFiles({ root, mode: 'all' });
  const unit = discoverTestFiles({ root, mode: 'unit' });
  const browser = discoverTestFiles({ root, mode: 'browser' });

  assert.deepEqual(all, flat);
  for (const excluded of EXCLUDED_TEST_FILES) {
    assert.equal(all.includes(excluded), false, `must exclude ${excluded}`);
  }
  assert.ok(browser.length > 0, 'expected browser screen tests');
  assert.ok(browser.every(isBrowserTest));
  assert.ok(unit.every(file => !isBrowserTest(file)));
  assert.deepEqual([...unit, ...browser].sort((a, b) => (a < b ? -1 : a > b ? 1 : 0)), all);
});

test('list-tests discovers nested unit and browser tests recursively and skips excluded fixtures', t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-list-tests-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));

  const files = [
    'test/top.test.mjs',
    'test/screen-top.test.mjs',
    'test/nested/core/unit-a.test.mjs',
    'test/nested/visual/screen-modal.test.mjs',
    'test/nested/helper.mjs',
    'test/workflow-commit-warning-paths/baseline.test.mjs',
    'test/workflow-commit-warning-paths-replay.test.mjs',
  ];
  for (const rel of files) {
    const abs = join(dir, rel);
    mkdirSync(dirname(abs), { recursive: true });
    writeFileSync(abs, '// fixture\n');
  }

  assert.deepEqual(discoverTestFiles({ root: dir, mode: 'all' }), [
    'test/nested/core/unit-a.test.mjs',
    'test/nested/visual/screen-modal.test.mjs',
    'test/screen-top.test.mjs',
    'test/top.test.mjs',
    'test/workflow-commit-warning-paths-replay.test.mjs',
  ]);
  assert.deepEqual(discoverTestFiles({ root: dir, mode: 'unit' }), [
    'test/nested/core/unit-a.test.mjs',
    'test/top.test.mjs',
    'test/workflow-commit-warning-paths-replay.test.mjs',
  ]);
  assert.deepEqual(discoverTestFiles({ root: dir, mode: 'browser' }), [
    'test/nested/visual/screen-modal.test.mjs',
    'test/screen-top.test.mjs',
  ]);

  const cliJson = spawnSync(process.execPath, [listScript, '--json', '--root', dir], { encoding: 'utf8' });
  assert.equal(cliJson.status, 0, cliJson.stderr);
  assert.deepEqual(JSON.parse(cliJson.stdout), discoverTestFiles({ root: dir, mode: 'all' }));

  const cliUnit = spawnSync(process.execPath, [listScript, '--unit'], { cwd: dir, encoding: 'utf8' });
  assert.equal(cliUnit.status, 0, cliUnit.stderr);
  assert.deepEqual(cliUnit.stdout.trim().split('\n'), discoverTestFiles({ root: dir, mode: 'unit' }));
});

test('list-tests emits 4-part agent-teaching diagnostics on invalid flags or missing test directory', t => {
  const emptyDir = mkdtempSync(join(tmpdir(), 'pdd-list-empty-'));
  t.after(() => rmSync(emptyDir, { recursive: true, force: true }));

  for (const args of [['--bogus'], ['--unit', '--browser'], ['--root', emptyDir]]) {
    const res = spawnSync(process.execPath, [listScript, ...args], { encoding: 'utf8' });
    assert.equal(res.status, 2, `expected exit 2 for ${args.join(' ')}`);
    assert.match(res.stderr, /^Location: /m);
    assert.match(res.stderr, /^Invariant: /m);
    assert.match(res.stderr, /^Fix: /m);
    assert.match(res.stderr, /^Rerun: /m);
  }
});

test('package.json and ci.yml wire recursive test manifest without stale alpha branch trigger or ci-install', () => {
  const pkg = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
  assert.match(pkg.scripts.test, /scripts\/list-tests\.mjs/);
  assert.match(pkg.scripts.test, /--import \.\/test\/helpers\/test-home\.mjs/);
  assert.match(pkg.scripts.test, /--import \.\/test\/helpers\/test-net-guard\.mjs/);
  assert.doesNotMatch(pkg.scripts.test, /test\/\*\.test\.mjs/);

  const ci = readFileSync(join(root, '.github', 'workflows', 'ci.yml'), 'utf8');
  assert.match(ci, /branches:\s*\[main\]/);
  assert.doesNotMatch(ci, /branches:\s*\[.*alpha/);
  assert.doesNotMatch(ci, /pdd-alpha-/);
  assert.match(ci, /node scripts\/list-tests\.mjs --unit/);
  assert.match(ci, /node scripts\/list-tests\.mjs --browser/);
  assert.doesNotMatch(ci, /ci-install\.mjs/);
});
