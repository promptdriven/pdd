import '../../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import {
  findConflictMarkers,
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

test('runDiffSpotlight tracks snapshots + harness edits and hard-fails conflict markers and misplaced test prompts', t => {
  const repo = initGitRepo(t, 'pdd-diff-spotlight-');
  mkdirSync(join(repo, 'test', '__snapshots__'), { recursive: true });
  mkdirSync(join(repo, 'src'), { recursive: true });

  writeFileSync(join(repo, 'package.json'), JSON.stringify({ name: 'demo', scripts: { test: 'node --test' } }, null, 2) + '\n');
  writeFileSync(join(repo, 'test', '__snapshots__', 'app.snap'), 'snap v1\n');
  commitAll(repo, 'base');

  execFileSync('git', ['checkout', '-q', '-b', 'feature'], { cwd: repo });
  writeFileSync(join(repo, 'test', '__snapshots__', 'app.snap'), 'snap v2\n');
  writeFileSync(join(repo, 'package.json'), JSON.stringify({ name: 'demo', scripts: { test: 'node --test --concurrency=1' } }, null, 2) + '\n');

  const clean = runDiffSpotlight({ cwd: repo, baseRef: 'main' });
  assert.equal(clean.ok, true, JSON.stringify(clean.errors));
  assert.deepEqual(clean.snapshotEdits, ['test/__snapshots__/app.snap']);
  assert.ok(clean.harnessEdits.some(h => h.includes('package.json')));

  writeFileSync(join(repo, 'src', 'conflict.mjs'), '<<<<<<< HEAD\nconst a = 1;\n=======\nconst a = 2;\n>>>>>>> main\n');
  mkdirSync(join(repo, 'prompts', 'test'), { recursive: true });
  writeFileSync(join(repo, 'prompts', 'test', 'bad.prompt.md'), '# Bad test prompt\n');

  assert.equal(findConflictMarkers('<<<<<<< HEAD\n=======\n>>>>>>> main\n', 'src/conflict.mjs').length, 1);

  const failed = runDiffSpotlight({ cwd: repo, baseRef: 'main' });
  assert.equal(failed.ok, false);
  const codes = new Set(failed.errors.map(e => e.code));
  assert.ok(codes.has('diff-conflict-marker'), `missing diff-conflict-marker: ${JSON.stringify(failed.errors)}`);
  assert.ok(codes.has('misplaced-test-prompt'), `missing misplaced-test-prompt: ${JSON.stringify(failed.errors)}`);
  for (const err of failed.errors) {
    assert.match(err.formatted, /Fix:.*Rerun: `pdd lint --diff`/);
  }
});

test('Astra #1 + #12: invalid base ref fails closed and orphan/diff3 conflict markers are caught', t => {
  assert.equal(findConflictMarkers('const a = 1;\n=======\nconst b = 2;\n', 'src/partial.mjs').length, 1);
  assert.equal(findConflictMarkers('<<<<<<< HEAD\nconst a = 1;\n', 'src/unclosed.mjs').length, 1);
  assert.equal(findConflictMarkers('const a = 1;\n>>>>>>> main\n', 'src/tail.mjs').length, 1);
  assert.equal(findConflictMarkers('const a = 1;\n||||||| parent of abc\nconst b = 2;\n', 'src/diff3.mjs').length, 1);

  const repo = initGitRepo(t, 'pdd-diff-astra12-');
  mkdirSync(join(repo, 'src'), { recursive: true });
  writeFileSync(join(repo, 'src', 'a.mjs'), 'export const a = 1;\n');
  commitAll(repo, 'base');

  const badBase = runDiffSpotlight({ cwd: repo, baseRef: 'refs/heads/does-not-exist' });
  assert.equal(badBase.ok, false);
  assert.equal(badBase.baseAvailable, false);
  assert.ok(badBase.errors.some(e => e.code === 'diff-base-unavailable'));
});
