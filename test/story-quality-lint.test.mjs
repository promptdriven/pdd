import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { findTestPromptViolations, isTestPromptPath, runOwner } from '../src/file-owner.mjs';
import { formatStoryLint, isLintableStoryPath, lintStories, lintStory } from '../src/story-lint.mjs';

const packageRoot = resolve(import.meta.dirname, '..');

const harborDir = join(packageRoot, 'test', 'fixtures', 'harbor');

test('3362 isLintableStoryPath selects Story files under user_stories/ and pdd/stories/ while skipping PLAN.md, README.md and unsafe paths', () => {
  assert.equal(isLintableStoryPath('user_stories/place-order.md'), true);
  assert.equal(isLintableStoryPath('user_stories/journeys/J1-order.md'), true);
  assert.equal(isLintableStoryPath('pdd/stories/place-order.md'), true);
  assert.equal(isLintableStoryPath('examples/shop/user_stories/checkout.md'), true);
  assert.equal(isLintableStoryPath('user_stories/PLAN.md'), false);
  assert.equal(isLintableStoryPath('pdd/stories/PLAN.md'), false);
  assert.equal(isLintableStoryPath('user_stories/plan.md'), false);
  assert.equal(isLintableStoryPath('user_stories/README.md'), false);
  assert.equal(isLintableStoryPath('docs/story-guide.md'), false);
  assert.equal(isLintableStoryPath('../user_stories/escape.md'), false);
  assert.equal(isLintableStoryPath('/abs/user_stories/escape.md'), false);
});

test('3362 lintStory accepts clean user-observable Stories, Rules to check, comments, fenced blocks and trailing blank lines', () => {
  for (const name of ['place-order.md', 'unknown-item.md']) {
    const text = readFileSync(join(harborDir, 'user_stories', name), 'utf8');
    const res = lintStory(text, { path: `user_stories/${name}` });
    assert.equal(res.ok, true, formatStoryLint(res));
  }

  const richClean = [
    '# Finish a task',
    '',
    '<!-- internal note: src/todo.mjs should stay untouched -->',
    'As a person who keeps a to-do list in the terminal, I want to mark a task as done, so that I see what is left.',
    '',
    '```pdd-boundary',
    'prompts/cli/todo.prompt.md',
    '```',
    '',
    '## Acceptance criteria',
    '',
    '1. `todo done 4` prints "Done #4: Call mom", updates `notes.txt` and `report.csv`, and exits with code 0.',
    '2. When the person passes `"node --test test/new.test.mjs"`, the literal command string is preserved.',
    '',
    '## What must not change',
    '',
    '- Task #1 in `pdd.json` stays open.',
    '',
    '## Rules to check',
    '',
    '- Total cents never overflow; see `src/todo.mjs` and `prompts/cli/todo.prompt.md` for formal boundary.',
  ].join('\n');

  const res = lintStory(richClean, { path: 'user_stories/finish-task.md' });
  assert.equal(res.ok, true, formatStoryLint(res));
  assert.equal(formatStoryLint(res), '');

  const batch = lintStories([
    { path: 'user_stories/PLAN.md', text: '# Plan\n1. Touch src/internal.mjs and 0xdeadbeef.\n' },
    { path: 'user_stories/finish-task.md', text: richClean },
  ]);
  assert.equal(batch.ok, true);
  assert.deepEqual(batch.problems, []);

  // Trailing blank lines past line 35 do NOT falsely trigger story-bloated-criteria.
  const withTrailingBlanks = [
    '# Export report',
    '',
    'As an analyst, I want a CSV download, so that I can open it in a spreadsheet.',
    '',
    '## Acceptance criteria',
    '',
    '1. Clicking Export downloads `report.csv` with header `date,total`.',
    '2. Empty months download a header-only file.',
    ...Array.from({ length: 40 }, () => ''),
  ].join('\n');
  const trailingRes = lintStory(withTrailingBlanks, { path: 'user_stories/export-report.md', includeHygiene: true });
  assert.equal(trailingRes.ok, true, formatStoryLint(trailingRes));
  assert.deepEqual(trailingRes.problems, []);

  // Framework/domain names, narrowed roles, quoted UI literals, grounded outcomes and short sample tokens do not false-fail.
  const nuancedClean = [
    '# Save storefront settings on shop.rs',
    '',
    'As a user of a Next.js storefront on https://shop.rs/admin, I want to save settings with Node.js, Chart.js and p5.js previews, so that updates go live.',
    '',
    '## Acceptance criteria',
    '',
    '1. Clicking Save shows "Saved correctly" with coupon code `deadbeefcafe` and exits with code 0.',
    "2. When offline, the page recovers gracefully by showing 'Offline'.",
  ].join('\n');
  const nuancedRes = lintStory(nuancedClean, { path: 'user_stories/storefront-settings.md' });
  assert.equal(nuancedRes.ok, true, formatStoryLint(nuancedRes));
});

test('3362/3642 lintStory keeps structural/clarity rules and allows legitimate domain syntax without brittle regex false positives', () => {
  const domainStory = [
    '# Pin Apple Silicon model release and transition draft => published',
    '',
    'As a release engineer on macOS (Apple Silicon), I want to verify commit `0123456789abcdef0123456789abcdef01234567` and opcode `0x38` AST bitmask output, so that model releases stay reproducible.',
    '',
    '## Acceptance criteria',
    '',
    '1. Running `release promote` transitions status `draft => published` and prints header byte `0x38` on macOS (Apple Silicon).',
    '2. Output displays pinned revision `0123456789abcdef0123456789abcdef01234567` and exits with code 0.',
    '',
    '```text',
    'status: draft => published',
    'rev: 0123456789abcdef0123456789abcdef01234567',
    '```',
  ].join('\n');

  const cleanRes = lintStory(domainStory, { path: 'user_stories/release-promote.md' });
  assert.equal(cleanRes.ok, true, formatStoryLint(cleanRes));
  assert.deepEqual(cleanRes.problems, []);

  const vagueRoleStory = [
    '# Update profile',
    '',
    'As a user, I want profile saves, so that settings persist.',
    '',
    '## Acceptance criteria',
    '',
    '1. Saving settings handles errors gracefully.',
    '2. Profile loads as expected.',
  ].join('\n');

  const res = lintStory(vagueRoleStory, { path: 'user_stories/vague.md' });
  assert.equal(res.ok, false);
  const codes = new Set(res.problems.map(item => item.code));
  assert.deepEqual([...codes].sort(), ['story-generic-role', 'story-vague-criterion']);
  assert.ok(res.problems.some(p => p.line === 3 && p.code === 'story-generic-role'));
  assert.ok(res.problems.some(p => p.line === 7 && p.code === 'story-vague-criterion'));
  assert.ok(res.problems.some(p => p.line === 8 && p.code === 'story-vague-criterion'));

  const formatted = formatStoryLint(res);
  assert.match(formatted, /^Story quality check failed:/);
  assert.match(formatted, /user_stories\/vague\.md:7 \[story-vague-criterion\]/);
  assert.match(formatted, /Rewrite the Story in user-observable terms/);
});

test('3362 isTestPromptPath, findTestPromptViolations and pdd owner refuse prompts/test/** while keeping legacy prose warnings non-blocking', t => {
  for (const bad of [
    'prompts/test/calc.prompt.md',
    'prompts/tests/unit/calc.prompt.md',
    'prompts/__tests__/calc.prompt.md',
    'test/calc.prompt.md',
    'tests/calc.prompt.md',
    '__tests__/calc.prompt.md',
    'prompts/calc.test.prompt.md',
    'prompts/calc.spec.prompt.md',
  ]) {
    assert.equal(isTestPromptPath(bad), true, bad);
  }
  for (const ok of [
    'prompts/bound.prompt.md',
    'prompts/cli/test-selection.prompt.md',
    'prompts/cli/compiled-test.prompt.md',
    'test/fixtures/harbor/prompts/place_order.prompt.md',
    '../prompts/test/escape.prompt.md',
    'test/calc.test.mjs',
  ]) {
    assert.equal(isTestPromptPath(ok), false, ok);
  }

  const root = mkdtempSync(join(tmpdir(), 'pdd-owner-test-prompt-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q'], { cwd: root });
  mkdirSync(join(root, 'prompts', 'test'), { recursive: true });
  mkdirSync(join(root, 'test'), { recursive: true });
  writeFileSync(join(root, 'prompts', 'test', 'calc.prompt.md'), '# Calc test\n\nOwn test/calc.test.mjs.\n');
  writeFileSync(join(root, 'test', 'calc.test.mjs'), '// Generated from prompts/test/calc.prompt.md.\nexport const ok = true;\n');
  writeFileSync(join(root, 'prompts', 'prose.prompt.md'), '# Prose\n\nOwn test/prose.test.mjs.\n');
  writeFileSync(join(root, 'test', 'prose.test.mjs'), 'export const prose = true;\n');

  const run = (paths, json = false) => {
    let stdout = '', stderr = '';
    const code = runOwner({ cwd: root, paths, json }, {
      stdout: { write: s => { stdout += s; } },
      stderr: { write: s => { stderr += s; } },
    });
    return { code, stdout, stderr };
  };

  const direct = run(['prompts/test/calc.prompt.md']);
  assert.equal(direct.code, 1);
  assert.match(direct.stderr, /Error: misplaced test prompt: prompts\/test\/calc\.prompt\.md\. Prompts own production modules, not test files; delete prompts\/test\/calc\.prompt\.md and keep tests in test\/\./);

  const byTarget = run(['test/calc.test.mjs'], true);
  assert.equal(byTarget.code, 1);
  assert.match(byTarget.stderr, /Error: misplaced test prompt: test\/calc\.test\.mjs is claimed by prompts\/test\/calc\.prompt\.md \(header\)\./);
  assert.equal(JSON.parse(byTarget.stdout).files[0].owner, 'prompts/test/calc.prompt.md');

  const legacy = run(['prompts/prose.prompt.md']);
  assert.equal(legacy.code, 0);
  assert.match(legacy.stderr, /Warning: misplaced prompt owner: prompts\/prose\.prompt\.md claims test\/prose\.test\.mjs\./);

  writeFileSync(join(root, 'prompts', 'clean.prompt.md'), '# Clean\n\nOwn src/clean.mjs.\n');
  const check = findTestPromptViolations({ root, promptPaths: ['prompts/clean.prompt.md'], checkPaths: [] });
  assert.equal(check.ok, true);
});
