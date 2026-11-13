import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, unlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { Readable } from 'node:stream';
import { findTestPromptViolations, isTestPromptPath, runOwner } from '../src/file-owner.mjs';
import { runApprove } from '../src/prompt-approve.mjs';
import { formatStoryLint, isLintableStoryPath, lintStories, lintStory } from '../src/story-lint.mjs';
import { approveRun, startRun, stepDone } from '../src/workflow-runner.mjs';
import { PLACE, harbor, sink } from './helpers/runtime-fake.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const GOLDEN = 'd5958a8577dcb8dd6ff25c8df4ea3b85e8c5dcf7c16863d8e502a24095db6abb';
const asDraft = text => text.replace('"status": "approved"', '"status": "draft"').replace(GOLDEN, '');
const harborDir = join(packageRoot, 'test', 'fixtures', 'harbor');

test('3362 isLintableStoryPath selects Story files and skips PLAN.md, README.md and unsafe paths', () => {
  assert.equal(isLintableStoryPath('user_stories/place-order.md'), true);
  assert.equal(isLintableStoryPath('user_stories/journeys/J1-order.md'), true);
  assert.equal(isLintableStoryPath('examples/shop/user_stories/checkout.md'), true);
  assert.equal(isLintableStoryPath('user_stories/PLAN.md'), false);
  assert.equal(isLintableStoryPath('user_stories/plan.md'), false);
  assert.equal(isLintableStoryPath('user_stories/README.md'), false);
  assert.equal(isLintableStoryPath('docs/story-guide.md'), false);
  assert.equal(isLintableStoryPath('../user_stories/escape.md'), false);
  assert.equal(isLintableStoryPath('/abs/user_stories/escape.md'), false);
});

test('3362 lintStory accepts clean user-observable Stories, Rules to check, comments and fenced blocks', () => {
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
    '2. When theperson passes `"node --test test/new.test.mjs"`, the literal command string is preserved.',
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
});

test('3362 lintStory flags implementation paths, code internals, raw hashes/UUIDs, generic roles and vague criteria', () => {
  const plumbingStory = [
    '# Validate AST bit-flips in src/validator.mjs',
    '',
    'As a user, I want `resolveOwners(input, ports)` to validate `prompts/cli/validator.prompt.md`, so that it works.',
    '',
    '## Acceptance criteria',
    '',
    '1. `lib/check.ts` masks flags with `0x1f` into a `Uint8Array` and handles errors gracefully.',
    '2. Commit `0123456789abcdef0123456789abcdef01234567` and digest `ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad` match.',
    '3. Session `123e4567-e89b-12d3-a456-426614174000` calls `export async function run()` => `process.exit(0)` as expected.',
    '',
    '## What must not change',
    '',
    '- `components/Card.tsx` keeps rendering.',
  ].join('\n');

  const res = lintStory(plumbingStory, { path: 'user_stories/plumbing.md' });
  assert.equal(res.ok, false);
  const codes = new Set(res.problems.map(item => item.code));
  for (const expected of [
    'story-implementation-path',
    'story-code-internals',
    'story-raw-digest',
    'story-generic-role',
    'story-vague-criterion',
  ]) {
    assert.ok(codes.has(expected), `missing diagnostic code ${expected} in ${JSON.stringify(res.problems)}`);
  }
  assert.ok(res.problems.some(p => p.line === 1 && p.code === 'story-implementation-path'));
  assert.ok(res.problems.some(p => p.line === 3 && p.code === 'story-generic-role'));
  assert.ok(res.problems.some(p => p.line === 7 && p.code === 'story-vague-criterion'));
  assert.ok(res.problems.some(p => p.line === 8 && p.code === 'story-raw-digest'));
  assert.ok(res.problems.some(p => p.line === 13 && p.code === 'story-implementation-path'));

  const formatted = formatStoryLint(res);
  assert.match(formatted, /^Story quality check failed:/);
  assert.match(formatted, /user_stories\/plumbing\.md:7 \[story-vague-criterion\]/);
  assert.match(formatted, /Rewrite the Story in user-observable terms/);
});

test('3362 isTestPromptPath and pdd owner refuse prompts/test/** while keeping legacy prose warnings non-blocking', t => {
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
});

test('3362 pdd approve refuses misplaced test prompts, prompts claiming test files and low-level Story plumbing', async t => {
  const setup = harbor(t, repo => {
    const file = join(repo, PLACE);
    writeFileSync(file, asDraft(readFileSync(file, 'utf8')));
  });
  const callApprove = async target => {
    const ports = { stdout: sink(), stderr: sink(), stdin: Readable.from(['y\n']), interactive: true };
    const code = await runApprove({ words: [target], cwd: setup.repo }, ports);
    return { code, out: ports.stdout.text, err: ports.stderr.text };
  };

  // 1. Refuse prompts/test/*.prompt.md directly.
  mkdirSync(join(setup.repo, 'prompts', 'test'), { recursive: true });
  writeFileSync(join(setup.repo, 'prompts', 'test', 'order.prompt.md'), '# Order test\n\nCheck order math.\n');
  const badTestPrompt = await callApprove('prompts/test/order.prompt.md');
  assert.equal(badTestPrompt.code, 4);
  assert.match(badTestPrompt.err, /Error: misplaced test prompt: prompts\/test\/order\.prompt\.md/);
  unlinkSync(join(setup.repo, 'prompts', 'test', 'order.prompt.md'));

  // 2. Refuse an ordinary prompt that claims a test file in prose.
  const draftContent = readFileSync(join(setup.repo, PLACE), 'utf8');
  writeFileSync(join(setup.repo, 'prompts', 'claims-test.prompt.md'), `# Claims test\n\nOwn test/order.test.mjs.\n\n${draftContent.slice(draftContent.indexOf('<details>'))}`);
  const badClaim = await callApprove('prompts/claims-test.prompt.md');
  assert.equal(badClaim.code, 4);
  assert.match(badClaim.err, /Error: misplaced prompt owner: prompts\/claims-test\.prompt\.md claims test\/order\.test\.mjs\./);
  unlinkSync(join(setup.repo, 'prompts', 'claims-test.prompt.md'));

  // 3. Refuse approval when a changed Story contains implementation plumbing, then succeed after rewrite.
  const storyFile = join(setup.repo, 'user_stories', 'place-order.md');
  const cleanStory = readFileSync(storyFile, 'utf8');
  writeFileSync(storyFile, [
    '# Place an order in src/place-order.mjs',
    '',
    'As a user, I want `placeOrder(cart)` to handle bit-flip masks `0xff`, so that orders work.',
    '',
    '## Acceptance criteria',
    '',
    '1. Placing an order works correctly.',
  ].join('\n'));
  const badStory = await callApprove(PLACE);
  assert.equal(badStory.code, 4);
  assert.match(badStory.err, /Story quality check failed:/);
  assert.match(badStory.err, /\[story-implementation-path\]/);
  assert.match(badStory.err, /\[story-code-internals\]/);
  assert.match(badStory.err, /\[story-generic-role\]/);
  assert.match(badStory.err, /\[story-vague-criterion\]/);

  writeFileSync(storyFile, cleanStory);
  const approved = await callApprove(PLACE);
  assert.equal(approved.code, 0, approved.err);
  assert.match(approved.out, /Approved prompts\/place_order\.prompt\.md\./);
});

test('3362 workflow Story gate and workflow approve refuse test-prompt ownership and Story plumbing until fixed', async t => {
  const f = await fixture(t, { name: 'feature', agent: 'codex' });
  f.ports.env.PDD_STATE_DIR = join(f.state, 'runtime');
  const started = await startRun({ name: 'feature', issue: '17', agent: 'codex', cwd: f.source, packageRoot }, f.ports);
  assert.equal(started.exitCode, 0, started.message);
  const run = f.record();

  const callDone = async (step, extra = {}) => {
    f.tick();
    return stepDone({ step, summary: step, cwd: run.root, ...extra }, f.agentPorts());
  };

  assert.equal((await callDone('understand')).exitCode, 0);
  assert.equal((await callDone('visual', { skipped: 'no screen' })).exitCode, 0);

  for (const dir of ['prompts/test', 'user_stories', 'tests', 'test']) mkdirSync(join(run.root, dir), { recursive: true });
  cpSync(join(harborDir, PLACE), join(run.root, PLACE));
  cpSync(join(harborDir, 'tests/place-order.json'), join(run.root, 'tests/place-order.json'));

  // 1. Misplaced test prompt blocks finishing the Story area.
  writeFileSync(join(run.root, 'prompts/test/order.prompt.md'), '# Misplaced\n\nOwn test/order.test.mjs.\n');
  writeFileSync(join(run.root, 'user_stories/place-order.md'), readFileSync(join(harborDir, 'user_stories/place-order.md'), 'utf8'));
  const refusedTestPrompt = await callDone('prompt-story');
  assert.equal(refusedTestPrompt.exitCode, 1);
  assert.match(refusedTestPrompt.message, /Error: misplaced test prompt: prompts\/test\/order\.prompt\.md/);
  assert.equal(f.record().done['prompt-story'], undefined, 'refused final step must not be recorded');
  unlinkSync(join(run.root, 'prompts/test/order.prompt.md'));

  // 2. Test file claiming Generated from header blocks finishing the Story area.
  writeFileSync(join(run.root, 'test/order.test.mjs'), `// Generated from ${PLACE}.\nexport const x = 1;\n`);
  const refusedHeader = await callDone('prompt-story');
  assert.equal(refusedHeader.exitCode, 1);
  assert.match(refusedHeader.message, /Error: misplaced prompt owner: test\/order\.test\.mjs is claimed by prompts\/place_order\.prompt\.md \(header\)\./);
  unlinkSync(join(run.root, 'test/order.test.mjs'));

  // 3. Low-level Story plumbing blocks finishing the Story area before showing the card.
  writeFileSync(join(run.root, 'user_stories/place-order.md'), [
    '# Place an order',
    '',
    'As the system, I want `src/order.mjs` to hash `sha256:abcdef0123456789` without AST bit-flips.',
    '',
    '## Acceptance criteria',
    '',
    '1. The order total is computed as expected.',
  ].join('\n'));
  const refusedStory = await callDone('prompt-story');
  assert.equal(refusedStory.exitCode, 1);
  assert.match(refusedStory.message, /Story quality check failed:/);
  assert.equal(f.record().gate, null);

  // 4. Rewriting the Story in user-observable terms opens the Story card cleanly.
  cpSync(join(harborDir, 'user_stories/place-order.md'), join(run.root, 'user_stories/place-order.md'));
  const cardOut = await callDone('prompt-story');
  assert.equal(cardOut.exitCode, 0, cardOut.message);
  assert.match(cardOut.message, /Story card:/);

  // 5. Adding a misplaced test prompt after the gate opened is refused by workflow approve too.
  mkdirSync(join(run.root, 'prompts/test'), { recursive: true });
  writeFileSync(join(run.root, 'prompts/test/late.prompt.md'), '# Late\n');
  f.tick();
  const refusedApprove = await approveRun(
    { ref: '17', cwd: run.root, said: '-' },
    { ...f.agentPorts(), stdin: (async function* () { yield 'Approved.'; })() },
  );
  assert.equal(refusedApprove.exitCode, 1);
  assert.match(refusedApprove.message, /Error: misplaced test prompt: prompts\/test\/late\.prompt\.md/);
  unlinkSync(join(run.root, 'prompts/test/late.prompt.md'));

  // 6. Once removed, workflow approve succeeds cleanly.
  f.tick();
  const approved = await approveRun(
    { ref: '17', cwd: run.root, said: '-' },
    { ...f.agentPorts(), stdin: (async function* () { yield 'Approved.'; })() },
  );
  assert.equal(approved.exitCode, 0, approved.message);

  // 7. findTestPromptViolations never opens non-Git-visible files.
  const check = findTestPromptViolations({ root: run.root, promptPaths: [PLACE], checkPaths: [] });
  assert.equal(check.ok, true);
});
