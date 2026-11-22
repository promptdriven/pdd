import '../../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import {
  extractTestCases,
  findConflictMarkers,
  findExecutableOnlyMarkers,
  runDiffSpotlight,
} from '../../../src/core/lint/test-inventory.mjs';

function initGitRepo(t, prefix) {
  const dir = mkdtempSync(join(tmpdir(), prefix));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q', '-b', 'main'], { cwd: dir });
  execFileSync('git', ['config', 'user.name', 'Test'], { cwd: dir });
  execFileSync('git', ['config', 'user.email', 'test@example.com'], { cwd: dir });
  return dir;
}

function commitAll(dir, msg) {
  execFileSync('git', ['add', '.'], { cwd: dir });
  execFileSync('git', ['commit', '-q', '-m', msg], { cwd: dir });
}

test('extractTestCases fixes Prettier semi:false, Vitest timeouts, multiline expect(), and Go/Python test + skip detection', () => {
  // JS/TS: Prettier semi: false + Vitest timeout + multiline expect().
  const jsSrc = [
    "import { test, expect } from 'vitest'",
    "test('handles semi false and multiline expect', () => {",
    '  const result = compute(42)',
    '  expect(',
    '    result.total',
    '  ).toBe(42)',
    '}, 10000)',
    "it.skip('deferred case', () => {",
    '  expect(1).toBe(1)',
    '})',
  ].join('\n');
  const jsInv = extractTestCases(jsSrc, 'js');
  assert.equal(jsInv.cases.length, 2);
  assert.equal(jsInv.cases[0].name, 'handles semi false and multiline expect');
  assert.deepEqual(jsInv.cases[0].skips, []);
  assert.ok(jsInv.cases[0].assertions.length >= 1, `multiline expect() counted: ${JSON.stringify(jsInv.cases[0])}`);
  assert.equal(jsInv.cases[1].name, 'deferred case');
  assert.ok(jsInv.cases[1].skips.length >= 1);

  // Go: func Test*, t.Run, t.Skip, t.Error/t.Fatal.
  const goSrc = [
    'package calc',
    'import "testing"',
    'func TestAdd(t *testing.T) {',
    '  if 1+1 != 2 { t.Fatalf("bad math") }',
    '  t.Run("negative", func(t *testing.T) {',
    '    if -1+1 != 0 { t.Error("bad neg") }',
    '  })',
    '}',
    'func TestSkipped(t *testing.T) {',
    '  t.Skip("pending")',
    '}',
  ].join('\n');
  const goInv = extractTestCases(goSrc, 'go');
  assert.deepEqual(goInv.cases.map(x => x.name), ['TestAdd', 'negative', 'TestSkipped']);
  assert.ok(goInv.cases[0].assertions.length >= 1);
  assert.ok(goInv.cases[1].assertions.length >= 1);
  assert.ok(goInv.cases[2].skips.length >= 1);

  // Python: def test_*, @unittest.skip, pytest.raises, @pytest.mark.parametrize.
  const pySrc = [
    'import pytest, unittest',
    '@pytest.mark.parametrize("x", [1, 2])',
    'def test_positive(x):',
    '    assert x > 0',
    '    with pytest.raises(ValueError):',
    '        int("bad")',
    '@unittest.skip("wip")',
    'def test_later():',
    '    assert True',
  ].join('\n');
  const pyInv = extractTestCases(pySrc, 'py');
  assert.deepEqual(pyInv.cases.map(x => x.name), ['test_positive', 'test_later']);
  assert.deepEqual(pyInv.cases[0].skips, []);
  assert.ok(pyInv.cases[0].assertions.length >= 2, `assert + pytest.raises counted: ${JSON.stringify(pyInv.cases[0])}`);
  assert.ok(pyInv.cases[1].skips.length >= 1);
  assert.ok(pyInv.tableCaseCount >= 2);
});

test('findExecutableOnlyMarkers catches executable .only/fit/fdescribe while ignoring comments, strings, regexes, and fixtures', () => {
  const src = [
    '// test.only("commented out")',
    'const sample = "it.only(\'in string\')";',
    'const re = /describe\\.only\\(/;',
    "test.only('real focused test', () => {});",
    "fit('focused jasmine test', () => {});",
  ].join('\n');
  const hits = findExecutableOnlyMarkers(src, 'test/focus.test.mjs');
  assert.equal(hits.length, 2, JSON.stringify(hits));
  assert.equal(hits[0].line, 4);
  assert.equal(hits[1].line, 5);

  assert.deepEqual(findExecutableOnlyMarkers(src, 'test/fixtures/sample.test.mjs'), []);

  const pyFocus = '# @pytest.mark.only\n@pytest.mark.only\ndef test_one(): pass\n';
  const pyHits = findExecutableOnlyMarkers(pyFocus, 'tests/test_focus.py');
  assert.equal(pyHits.length, 1);
  assert.equal(pyHits[0].line, 2);
});

test('runDiffSpotlight compares BASE..WORKTREE, excludes helpers/fixtures/mocks, tracks cross-file moves + snapshots + harness edits, and hard-fails .only/conflicts/misplaced prompts', t => {
  const repo = initGitRepo(t, 'pdd-diff-spotlight-');
  mkdirSync(join(repo, 'test', 'helpers'), { recursive: true });
  mkdirSync(join(repo, 'test', 'fixtures'), { recursive: true });
  mkdirSync(join(repo, 'test', '__snapshots__'), { recursive: true });
  mkdirSync(join(repo, 'src'), { recursive: true });

  writeFileSync(join(repo, 'package.json'), JSON.stringify({ name: 'demo', scripts: { test: 'node --test' } }, null, 2) + '\n');
  writeFileSync(join(repo, 'test', 'old.test.mjs'), "test('migrated case', () => { assert.equal(1, 1); });\ntest('deleted case', () => { assert.equal(2, 2); });\n");
  writeFileSync(join(repo, 'test', 'helpers', 'util.mjs'), "export function test() {}\n");
  writeFileSync(join(repo, 'test', '__snapshots__', 'app.snap'), 'snap v1\n');
  commitAll(repo, 'base');

  execFileSync('git', ['checkout', '-q', '-b', 'feature'], { cwd: repo });

  // Move 'migrated case' to new.test.mjs (untracked!) and remove 'deleted case' from old.test.mjs.
  writeFileSync(join(repo, 'test', 'old.test.mjs'), '');
  writeFileSync(join(repo, 'test', 'new.test.mjs'), "test('migrated case', () => { assert.equal(1, 1); });\n");
  // Modify helper (must be excluded from test counts), snapshot, and package.json scripts.test.
  writeFileSync(join(repo, 'test', 'helpers', 'util.mjs'), "export function test() { return 1; }\n");
  writeFileSync(join(repo, 'test', '__snapshots__', 'app.snap'), 'snap v2\n');
  writeFileSync(join(repo, 'package.json'), JSON.stringify({ name: 'demo', scripts: { test: 'node --test --concurrency=1' } }, null, 2) + '\n');

  const clean = runDiffSpotlight({ cwd: repo, baseRef: 'main' });
  assert.equal(clean.ok, true, JSON.stringify(clean.errors));
  assert.deepEqual(clean.movedTests, [{ name: 'migrated case', from: 'test/old.test.mjs', to: 'test/new.test.mjs' }]);
  assert.deepEqual(clean.removedTests, [{ name: 'deleted case', path: 'test/old.test.mjs', line: 2 }]);
  assert.deepEqual(clean.snapshotEdits, ['test/__snapshots__/app.snap']);
  assert.ok(clean.harnessEdits.some(h => h.includes('package.json')));
  assert.ok(clean.advisories.some(a => a.includes('moved across files')));
  assert.ok(clean.advisories.some(a => a.includes('test(s) removed')));

  // Now inject hard-fail violations into worktree: executable .only, conflict markers, and misplaced test prompt!
  writeFileSync(join(repo, 'test', 'new.test.mjs'), "test.only('migrated case', () => { assert.equal(1, 1); });\n");
  writeFileSync(join(repo, 'src', 'conflict.mjs'), '<<<<<<< HEAD\nconst a = 1;\n=======\nconst a = 2;\n>>>>>>> main\n');
  mkdirSync(join(repo, 'prompts', 'test'), { recursive: true });
  writeFileSync(join(repo, 'prompts', 'test', 'bad.prompt.md'), '# Bad test prompt\n');

  assert.equal(findConflictMarkers('<<<<<<< HEAD\n=======\n>>>>>>> main\n', 'src/conflict.mjs').length, 1);

  const failed = runDiffSpotlight({ cwd: repo, baseRef: 'main' });
  assert.equal(failed.ok, false);
  const codes = new Set(failed.errors.map(e => e.code));
  assert.ok(codes.has('diff-focus-only'), `missing diff-focus-only: ${JSON.stringify(failed.errors)}`);
  assert.ok(codes.has('diff-conflict-marker'), `missing diff-conflict-marker: ${JSON.stringify(failed.errors)}`);
  assert.ok(codes.has('misplaced-test-prompt'), `missing misplaced-test-prompt: ${JSON.stringify(failed.errors)}`);
  for (const err of failed.errors) {
    assert.match(err.formatted, /Fix:.*Rerun: `pdd lint --diff`/);
  }
});
