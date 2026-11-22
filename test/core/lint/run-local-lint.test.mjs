import '../../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { performance } from 'node:perf_hooks';
import { runLocalLint } from '../../../src/core/lint/run-local-lint.mjs';

function makeSink() {
  let text = '';
  return { write(s) { text += String(s); }, get text() { return text; } };
}

function initCleanRepo(t) {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-run-local-lint-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));
  const repo = join(scratch, 'repo');
  const stateDir = join(scratch, 'state');
  mkdirSync(join(repo, 'prompts'), { recursive: true });
  mkdirSync(join(repo, 'src'), { recursive: true });
  mkdirSync(join(repo, 'user_stories'), { recursive: true });
  mkdirSync(stateDir, { recursive: true });

  execFileSync('git', ['init', '-q', '-b', 'main'], { cwd: repo });
  execFileSync('git', ['config', 'user.name', 'Test'], { cwd: repo });
  execFileSync('git', ['config', 'user.email', 'test@example.com'], { cwd: repo });

  writeFileSync(join(repo, 'prompts', 'price.prompt.md'), '# Price\n\nOwn `src/price.mjs`. Compute price in integer cents.\n\n## Dependencies\nNone.\n');
  writeFileSync(join(repo, 'src', 'price.mjs'), '// Generated from prompts/price.prompt.md.\nexport const price = n => n * 100;\n');
  writeFileSync(
    join(repo, 'user_stories', 'price.md'),
    '# Calculate price\n\nAs a shopper, I want the price shown in cents, so that totals stay exact.\n\n## Acceptance criteria\n\n1. Passing 2 items prints 200 cents and exits with code 0.\n',
  );
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['commit', '-q', '-m', 'init'], { cwd: repo });
  return { repo, stateDir };
}

test('runLocalLint runs 100% offline in <1s, writes 0 batch-state files, and emits clean 0 warnings summary with empty stderr', t => {
  const { repo, stateDir } = initCleanRepo(t);
  const stdout = makeSink(), stderr = makeSink();

  const t0 = performance.now();
  const exitCode = runLocalLint(
    { cwd: repo },
    { stdout, stderr, env: { ...process.env, PDD_RUNTIME_URL: 'invalid', PDD_STATE_DIR: stateDir } },
  );
  const elapsedMs = performance.now() - t0;

  assert.equal(exitCode, 0);
  assert.equal(stderr.text, '', 'clean repo must leave stderr completely empty');
  assert.match(stdout.text, /^Local lint: 0 errors, 0 warnings\. \(0 AI calls, 0 network calls\)\n$/);
  assert.deepEqual(readdirSync(stateDir), [], 'local lint must write 0 batch-state files');
  assert.ok(elapsedMs < 1000, `expected <1s offline run, took ${elapsedMs.toFixed(1)}ms`);

  // JSON mode outputs structured offline receipt.
  const jOut = makeSink(), jErr = makeSink();
  const jCode = runLocalLint({ cwd: repo, json: true }, { stdout: jOut, stderr: jErr });
  assert.equal(jCode, 0);
  assert.equal(jErr.text, '');
  const parsed = JSON.parse(jOut.text);
  assert.equal(parsed.schema_version, 'pdd.local-lint.v1');
  assert.equal(parsed.ok, true);
  assert.equal(parsed.exit_code, 0);
  assert.equal(parsed.local_only, true);
  assert.deepEqual(parsed.problems, []);
  assert.deepEqual(parsed.warnings, []);
});

test('runLocalLint supports --diff hard gates (.only / conflicts) and opt-in lint.commands delegation', t => {
  const { repo } = initCleanRepo(t);
  mkdirSync(join(repo, 'test'), { recursive: true });
  writeFileSync(join(repo, 'test', 'price.test.mjs'), "test.only('focused', () => {});\n");

  const diffOut = makeSink(), diffErr = makeSink();
  const diffCode = runLocalLint({ cwd: repo, diff: true, baseRef: 'main' }, { stdout: diffOut, stderr: diffErr });
  assert.equal(diffCode, 1);
  assert.match(diffErr.text, /\[diff-focus-only\]/);
  assert.match(diffErr.text, /Fix:.*Rerun: `pdd lint --diff`/);

  // Remove .only and verify Astra #9: untrusted working-tree lint.commands are SKIPPED unless committed on base or --trust-working-tree!
  writeFileSync(join(repo, 'test', 'price.test.mjs'), "test('clean', () => {});\n");
  writeFileSync(
    join(repo, 'pdd.json'),
    JSON.stringify({ lint: { commands: [`${JSON.stringify(process.execPath)} -e "console.error('custom linter failed'); process.exit(1)"`] } }, null, 2) + '\n',
  );
  execFileSync('git', ['add', 'pdd.json'], { cwd: repo });

  const untrustedOut = makeSink(), untrustedErr = makeSink();
  const untrustedCode = runLocalLint({ cwd: repo, runCommands: true }, { stdout: untrustedOut, stderr: untrustedErr });
  assert.equal(untrustedCode, 0, 'untrusted working-tree lint.commands must NOT execute by default');
  assert.match(untrustedOut.text, /\[lint-commands-untrusted\]/);

  // Explicit trustWorkingTree: true opts in locally.
  const optInOut = makeSink(), optInErr = makeSink();
  const optInCode = runLocalLint({ cwd: repo, runCommands: true, trustWorkingTree: true }, { stdout: optInOut, stderr: optInErr });
  assert.equal(optInCode, 1);
  assert.match(optInErr.text, /\[lint-command-failed(?::[^\]]+)?\]/);
  assert.match(optInErr.text, /custom linter failed/);

  // Once committed on merge base (`main`), base-trusted lint.commands run automatically without --trust-working-tree.
  execFileSync('git', ['commit', '-q', '-m', 'trust lint command on base'], { cwd: repo });
  const baseOut = makeSink(), baseErr = makeSink();
  const baseCode = runLocalLint({ cwd: repo, runCommands: true }, { stdout: baseOut, stderr: baseErr });
  assert.equal(baseCode, 1);
  assert.match(baseErr.text, /\[lint-command-failed(?::[^\]]+)?\]/);
});
