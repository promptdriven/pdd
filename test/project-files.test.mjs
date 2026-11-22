import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { runProjectFiles } from '../src/project-files.mjs';

test('S1 project-files handles EPIPE stdout pipe close gracefully with exit 0 and empty stderr', t => {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-files-epipe-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q'], { cwd: root });
  mkdirSync(join(root, 'prompts'), { recursive: true });
  writeFileSync(join(root, 'prompts/app.prompt.md'), '# App\n\nOwn `src/app.mjs`.\n');

  let err = '';
  const brokenStdout = {
    write() {
      const error = new Error('write EPIPE');
      error.code = 'EPIPE';
      throw error;
    },
  };
  const stderr = { write(chunk) { err += chunk; } };

  assert.equal(runProjectFiles({ cwd: root, json: false }, { stdout: brokenStdout, stderr }), 0);
  assert.equal(err, '');
  assert.equal(runProjectFiles({ cwd: root, json: true }, { stdout: brokenStdout, stderr }), 0);
  assert.equal(err, '');
});

test('S1 project-files returns exit 2 outside a Git repository', t => {
  const outside = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-files-nogit-')));
  t.after(() => rmSync(outside, { recursive: true, force: true }));
  let out = '', err = '';
  const code = runProjectFiles(
    { cwd: outside },
    { stdout: { write(s) { out += s; } }, stderr: { write(s) { err += s; } } },
  );
  assert.equal(code, 2);
  assert.equal(out, '');
  assert.match(err, /Git repository/);
});
