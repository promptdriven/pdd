import '../../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { lintRepoProject } from '../../../src/core/lint/project-lint.mjs';
import { formatDiagnosticLine } from '../../../src/core/lint/diagnostics.mjs';
import { lintRepoAntiPatterns } from '../../../src/repo-hygiene-lint.mjs';
import { lintTestFixedSleeps, lintTestUnexcusedSkips } from '../../../src/autopilot/lint-sleep-skip.mjs';

function initGitRepo(t, prefix) {
  const dir = mkdtempSync(join(tmpdir(), prefix));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q'], { cwd: dir });
  execFileSync('git', ['config', 'user.name', 'Test'], { cwd: dir });
  execFileSync('git', ['config', 'user.email', 'test@example.com'], { cwd: dir });
  return dir;
}

function commitAll(dir, msg = 'init') {
  execFileSync('git', ['add', '.'], { cwd: dir });
  execFileSync('git', ['commit', '-q', '-m', msg], { cwd: dir });
}

test('broken-prompt-header fails as error on nonexistent prompt path with 4-part fix and ignores stale sha256 when prompt exists', t => {
  const repo = initGitRepo(t, 'pdd-core-header-');
  mkdirSync(join(repo, 'prompts'), { recursive: true });
  mkdirSync(join(repo, 'src'), { recursive: true });

  writeFileSync(join(repo, 'prompts', 'ok.prompt.md'), '# Ok\n\nOwn `src/ok.mjs`.\n\n## Dependencies\nNone.\n');
  writeFileSync(
    join(repo, 'src', 'ok.mjs'),
    `// Generated from prompts/ok.prompt.md (sha256: ${'0'.repeat(64)}).\nexport const ok = () => 1;\n`,
  );
  writeFileSync(
    join(repo, 'src', 'orphan.mjs'),
    '// Generated from prompts/deleted-module.prompt.md.\nexport const orphan = () => 0;\n',
  );
  commitAll(repo);

  const report = lintRepoProject({ root: repo });
  assert.equal(report.ok, false);
  const broken = report.findings.filter(f => f.code === 'broken-prompt-header');
  assert.equal(broken.length, 1);
  assert.equal(broken[0].severity, 'error');
  assert.equal(broken[0].path, 'src/orphan.mjs');
  assert.match(report.errors[0], /Error: prompt ownership: src\/orphan\.mjs:1 \[broken-prompt-header\]/);
  assert.match(broken[0].message, /prompts\/deleted-module\.prompt\.md/);
  assert.match(broken[0].message, /Fix:/);
  assert.match(broken[0].message, /Rerun: `pdd lint/);
  assert.equal(report.findings.some(f => f.path === 'src/ok.mjs' && f.code === 'broken-prompt-header'), false);
});

test('broken-dependency-link accepts existing files and directories, fails closed on missing targets, and prompt-dependency-cycle warns', t => {
  const repo = initGitRepo(t, 'pdd-core-deps-');
  mkdirSync(join(repo, 'prompts', 'sub'), { recursive: true });
  mkdirSync(join(repo, 'src', 'pkg'), { recursive: true });

  writeFileSync(join(repo, 'src', 'pkg', 'index.mjs'), 'export const x = 1;\n');
  writeFileSync(
    join(repo, 'prompts', 'a.prompt.md'),
    '# A\n\n## Dependencies\n- [B](b.prompt.md)\n- [pkg dir](../src/pkg)\n- [missing](ghost.prompt.md)\n',
  );
  writeFileSync(
    join(repo, 'prompts', 'b.prompt.md'),
    '# B\n\n## Dependencies\n- [A](a.prompt.md)\n',
  );
  commitAll(repo);

  const report = lintRepoProject({ root: repo });
  assert.equal(report.ok, false);
  const broken = report.findings.filter(f => f.code === 'broken-dependency-link');
  assert.equal(broken.length, 1, `only missing file should fail, directory link must pass: ${JSON.stringify(broken)}`);
  assert.equal(broken[0].severity, 'error');
  assert.match(broken[0].message, /prompts\/ghost\.prompt\.md/);
  assert.match(broken[0].message, /Fix:.*Rerun: `pdd lint/);

  const cycles = report.findings.filter(f => f.code === 'prompt-dependency-cycle');
  assert.equal(cycles.length, 1);
  assert.equal(cycles[0].severity, 'warn');
});

test('structural Story hard error (story-missing-criteria) fails closed while domain specs pass cleanly in lintRepoProject', t => {
  const repo = initGitRepo(t, 'pdd-core-story-err-');
  mkdirSync(join(repo, 'user_stories'), { recursive: true });
  mkdirSync(join(repo, 'pdd', 'stories'), { recursive: true });

  writeFileSync(
    join(repo, 'user_stories', 'domain-rich.md'),
    '# Inspect opcode on macOS (Apple Silicon)\n\nAs a hardware engineer, I want `draft => published` status and opcode `0x38` AST bitmask shown for `0123456789abcdef0123456789abcdef01234567`.\n\n## Acceptance criteria\n\n1. Shows "0x38" and exits with code 0.\n',
  );
  writeFileSync(
    join(repo, 'pdd', 'stories', 'no-criteria.md'),
    '# Missing criteria\n\nAs a shopper, I want a receipt printed after checkout.\n',
  );
  commitAll(repo);

  const report = lintRepoProject({ root: repo });
  assert.equal(report.ok, false);
  assert.equal(report.findings.some(f => f.path === 'user_stories/domain-rich.md'), false, `domain-rich Story must produce 0 findings: ${JSON.stringify(report.findings)}`);
  assert.ok(report.errors.some(e => e.includes('pdd/stories/no-criteria.md') && e.includes('[story-missing-criteria]') && e.includes('Fix:')));
});

test('Layer-2 autopilot/lint-sleep-skip catches unexcused JS/Python skips and Atomics.wait/timers sleeps while honoring tracking refs and polling', () => {
  const jsSkips = [
    "test.skip('broken without reason', () => {});",
    "it('skipped bool', { skip: true }, () => {});",
    "test('placeholder', { skip: 'todo' }, () => {});",
    "test('runtime skip', t => { t.skip(); });",
    "test.skip('tracked by #1234', () => {});",
    "test('substantive reason', { skip: 'Requires macOS Metal GPU hardware unavailable in CI' }, () => {});",
    "// pdd-allow-skip: platform guard",
    "it.skip('annotated skip', () => {});",
  ].join('\n');
  const skipWarns = lintTestUnexcusedSkips(jsSkips, { path: 'test/skips.test.mjs' });
  assert.equal(skipWarns.length, 4, skipWarns.join('\n'));
  assert.match(skipWarns[0], /:1 \[test-unexcused-skip\]/);
  assert.match(skipWarns[1], /:2 \[test-unexcused-skip\]/);
  assert.match(skipWarns[2], /:3 \[test-unexcused-skip\]/);
  assert.match(skipWarns[3], /:4 \[test-unexcused-skip\]/);

  const pySkips = [
    'import pytest, unittest',
    '@pytest.mark.skip',
    'def test_bare(): pass',
    '@unittest.skip("todo")',
    'def test_placeholder(): pass',
    '@pytest.mark.skip(reason="Tracked in #4021 for upstream fix")',
    'def test_tracked(): pass',
    'def test_inline():',
    '    pytest.skip()',
  ].join('\n');
  const pySkipWarns = lintTestUnexcusedSkips(pySkips, { path: 'tests/test_skips.py' });
  assert.equal(pySkipWarns.length, 3, pySkipWarns.join('\n'));

  const atomicsAndTimers = [
    "import { setTimeout as delay } from 'node:timers/promises';",
    "test('sleeps', async () => {",
    '  const sab = new Int32Array(new SharedArrayBuffer(4));',
    '  Atomics.wait(sab, 0, 0, 250);',
    '  await delay(100);',
    '  // pdd-allow-sleep: intentional TTL expiry',
    '  await delay(100);',
    '});',
  ].join('\n');
  const sleepWarns = lintTestFixedSleeps(atomicsAndTimers, { path: 'test/timers.test.mjs' });
  assert.equal(sleepWarns.length, 2, sleepWarns.join('\n'));
  assert.match(sleepWarns[0], /:4 \[test-fixed-sleep\]/);
  assert.match(sleepWarns[1], /:5 \[test-fixed-sleep\]/);
});

test('Astra #13: lintRepoAntiPatterns compat export and 4-part fallback with separate Rerun:', t => {
  const line = formatDiagnosticLine(
    { filePath: 'src/billing/tax.mjs', line: 9, code: 'broken-prompt-header', category: 'prompt ownership', detail: 'Missing owner prompt' },
    'error',
  );
  assert.match(line, /^Error: prompt ownership: src\/billing\/tax\.mjs:9 \[broken-prompt-header\] Missing owner prompt\. Fix: Update src\/billing\/tax\.mjs:9 to fix prompt ownership rule "broken-prompt-header".*\. Rerun: `pdd lint`\.$/);

  const warnWithFix = formatDiagnosticLine(
    { filePath: 'prompts/billing.prompt.md', line: 1, code: 'prompt-missing-dependencies', category: 'prompt structure', detail: 'Missing Dependencies', fix: 'Add a `## Dependencies` section' },
    'warn',
  );
  assert.match(warnWithFix, /^Warning: prompt structure: prompts\/billing\.prompt\.md:1 \[prompt-missing-dependencies\] Missing Dependencies\. Fix: Add a `## Dependencies` section\. Rerun: `pdd lint`\.$/);

  const repo = initGitRepo(t, 'pdd-compat-export-');
  mkdirSync(join(repo, 'prompts'), { recursive: true });
  mkdirSync(join(repo, 'src'), { recursive: true });
  writeFileSync(join(repo, 'prompts', 'no-deps.prompt.md'), '# No Deps\n\nOwn `src/no-deps.mjs`.\n');
  writeFileSync(join(repo, 'src', 'no-deps.mjs'), '// Prompt: prompts/no-deps.prompt.md\nexport const x = 1;\n');
  commitAll(repo);
  const compatWarns = lintRepoAntiPatterns({ root: repo });
  assert.deepEqual(compatWarns, lintRepoProject({ root: repo }).warnings);
  assert.ok(compatWarns.some(w => w.includes('[prompt-missing-dependencies]')));
});
