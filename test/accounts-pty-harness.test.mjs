import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const REPO_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const HARNESS_PATH = join(REPO_ROOT, 'scripts', 'verify-accounts-pty.mjs');

function runHarness(args, timeoutMs = 45_000) {
  return new Promise((res, rej) => {
    const child = spawn(process.execPath, [HARNESS_PATH, ...args], {
      cwd: REPO_ROOT,
      env: process.env,
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    let stdout = '';
    let stderr = '';
    const timer = setTimeout(() => {
      try { child.kill('SIGKILL'); } catch {}
      rej(new Error(`verify-accounts-pty timed out after ${timeoutMs}ms\nstdout:\n${stdout}\nstderr:\n${stderr}`));
    }, timeoutMs);
    child.stdout.on('data', d => { stdout += d.toString('utf8'); });
    child.stderr.on('data', d => { stderr += d.toString('utf8'); });
    child.on('error', err => { clearTimeout(timer); rej(err); });
    child.on('close', code => { clearTimeout(timer); res({ code, stdout, stderr }); });
  });
}

test('P1 permanent 13-check interactive PTY & forced-rotation harness passes 13/13 in --offline mode', async () => {
  const res = await runHarness(['--offline', '--json']);
  assert.equal(res.code, 0, `harness failed (exit ${res.code}):\n${res.stdout}\n${res.stderr}`);
  const report = JSON.parse(res.stdout);
  assert.equal(report.mode, 'offline');
  assert.equal(report.failed, 0, JSON.stringify(report.checks.filter(c => c.status !== 'PASS'), null, 2));
  assert.equal(report.passed, 13);
  assert.deepEqual(
    report.checks.map(c => c.id),
    ['C01', 'C02', 'C03', 'C04', 'C05', 'C06', 'C07', 'C08', 'C09', 'C10', 'C11', 'C12', 'C13'],
  );
  for (const check of report.checks) {
    assert.equal(check.status, 'PASS', `${check.id} (${check.name}) failed: ${check.detail}`);
  }
  const c12 = report.checks.find(c => c.id === 'C12');
  assert.match(c12.detail, /seam=false/, 'bin/pdd-codex, bin/pdd-claude, and src/accounts-cli must not reach runtime-seam.mjs');
});
