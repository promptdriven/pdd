import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawn } from 'node:child_process';
import { mkdtempSync, mkdirSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { runProjectFiles } from '../src/project-files.mjs';

const BIN = resolve(fileURLToPath(new URL('../bin/pdd.mjs', import.meta.url)));

function runHeadOnePipe(args, cwd) {
  return new Promise((resolveDone, rejectDone) => {
    const child = spawn(process.execPath, [BIN, ...args], {
      cwd,
      env: { ...process.env, PDD_NO_UPDATE_CHECK: '1' },
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    let stderr = '';
    let firstLine = '';
    let closed = false;
    child.stderr.on('data', chunk => { stderr += chunk.toString('utf8'); });
    child.stdout.on('data', chunk => {
      if (closed) return;
      firstLine += chunk.toString('utf8');
      if (firstLine.includes('\n')) {
        closed = true;
        // Close the read end immediately after receiving the first line (identical to `| head -n 1`).
        child.stdout.destroy();
      }
    });
    child.on('error', rejectDone);
    child.on('close', (code, signal) => resolveDone({ code, signal, stderr, firstLine: firstLine.split('\n')[0] }));
  });
}

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

test('S1/C1 real subprocess pipe (`pdd files | head -1` and `pdd status | head -1`) exits 0 with empty stderr', async t => {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-real-epipe-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q'], { cwd: root });
  mkdirSync(join(root, 'prompts'), { recursive: true });
  // Create enough prompt files to exceed the OS pipe buffer / emit many lines so closing after line 1 triggers real kernel EPIPE.
  for (let i = 0; i < 60; i++) {
    writeFileSync(join(root, `prompts/mod-${String(i).padStart(2, '0')}.prompt.md`), `# Mod ${i}\n\nOwn \`src/mod-${i}.mjs\`.\n`);
  }

  for (const args of [['files'], ['status', '--changed']]) {
    const res = await runHeadOnePipe(args, root);
    assert.equal(res.signal, null, `${args.join(' ')} terminated by signal ${res.signal}`);
    assert.equal(res.code, 0, `${args.join(' ')} exited ${res.code}; stderr: ${res.stderr}`);
    assert.equal(res.stderr, '', `${args.join(' ')} unexpected stderr: ${res.stderr}`);
    assert.ok(res.firstLine.length > 0, `${args.join(' ')} produced first line`);
  }
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
