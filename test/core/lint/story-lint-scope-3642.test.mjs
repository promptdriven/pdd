import '../../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, unlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { buildAiLintPrompt } from '../../../src/autopilot/ai-lint.mjs';
import { gitFiles, runtimePreflightSlice, sharedSourceFiles } from '../../../src/runtime-seam.mjs';

const REPO_ROOT = resolve(import.meta.dirname, '../../..');
const PDD_BIN = join(REPO_ROOT, 'bin', 'pdd.mjs');

function makeTempGitRepo(t, prefix) {
  const scratch = mkdtempSync(join(tmpdir(), prefix));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));
  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  const state = join(scratch, 'state');
  mkdirSync(repo, { recursive: true });
  mkdirSync(home, { recursive: true });
  mkdirSync(state, { recursive: true });
  execFileSync('git', ['init', '-q', '-b', 'main'], { cwd: repo });
  execFileSync('git', ['config', 'user.name', 'Test'], { cwd: repo });
  execFileSync('git', ['config', 'user.email', 'test@example.com'], { cwd: repo });
  const env = { ...process.env, HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'invalid' };
  return { repo, env };
}

function writeRepoFile(repo, rel, content) {
  const full = join(repo, rel);
  mkdirSync(dirname(full), { recursive: true });
  writeFileSync(full, content);
}

function commitAll(repo, message) {
  execFileSync('git', ['add', '-A'], { cwd: repo });
  execFileSync('git', ['commit', '-q', '-m', message], { cwd: repo });
}

function runCli(repo, env, args) {
  return spawnSync(process.execPath, [PDD_BIN, ...args], {
    cwd: repo,
    env,
    encoding: 'utf8',
    timeout: 15_000,
  });
}

test('3642 Test A: domain-rich Story with macOS (Apple Silicon), draft => published, 0x38, 40-char pinned SHA, AST, and bitmask passes offline pdd lint with 0 errors and 0 warnings', t => {
  const { repo, env } = makeTempGitRepo(t, 'pdd-3642-a-');
  writeRepoFile(repo, 'user_stories/model-release.md', [
    '# Publish pinned model on macOS (Apple Silicon)',
    '',
    'As a release engineer running macOS (Apple Silicon), I want to inspect opcode `0x38` AST bitmask flags and promote a release `draft => published`, so that exact revisions ship predictably.',
    '',
    '## Acceptance criteria',
    '',
    '1. Promoting pinned HuggingFace commit `0123456789abcdef0123456789abcdef01234567` transitions status `draft => published` and exits with code 0.',
    '2. CLI output shows platform "macOS (Apple Silicon)", opcode `0x38`, and AST bitmask summary.',
    '',
    '```text',
    'platform: macOS (Apple Silicon)',
    'state: draft => published',
    'commit: 0123456789abcdef0123456789abcdef01234567',
    '```',
  ].join('\n') + '\n');
  commitAll(repo, 'init');

  for (const args of [['lint', '--local'], ['lint'], ['lint', '--local', '--json']]) {
    const res = runCli(repo, env, args);
    assert.equal(res.status, 0, `${args.join(' ')} failed: stdout=${res.stdout} stderr=${res.stderr}`);
    assert.equal(res.stderr, '', `${args.join(' ')} expected empty stderr`);
    if (args.includes('--json')) {
      const doc = JSON.parse(res.stdout);
      assert.equal(doc.ok, true);
      assert.deepEqual(doc.problems, []);
      assert.deepEqual(doc.warnings, []);
    } else {
      assert.match(res.stdout, /Local lint: 0 errors, 0 warnings\./);
    }
  }
});

test('3642 Test B: missing or empty ## Acceptance criteria fails offline pdd lint as hard error while structural warnings remain active', t => {
  const { repo, env } = makeTempGitRepo(t, 'pdd-3642-b-');
  writeRepoFile(repo, 'user_stories/no-criteria.md', [
    '# Missing acceptance section',
    '',
    'As a shopper, I want a receipt emailed after purchase, so that I keep a record.',
  ].join('\n') + '\n');
  commitAll(repo, 'missing criteria');

  const missingRes = runCli(repo, env, ['lint', '--local']);
  assert.equal(missingRes.status, 1, `expected exit 1: stdout=${missingRes.stdout}`);
  assert.match(missingRes.stderr, /user_stories\/no-criteria\.md.*\[story-missing-criteria\]/);

  // Empty ## Acceptance criteria (even with a fenced block inside) must also fail as hard error.
  writeRepoFile(repo, 'user_stories/no-criteria.md', [
    '# Empty acceptance section',
    '',
    'As a shopper, I want a receipt emailed after purchase, so that I keep a record.',
    '',
    '## Acceptance criteria',
    '',
    '```text',
    '1. Not an acceptance item inside a fence',
    '```',
  ].join('\n') + '\n');
  const emptyRes = runCli(repo, env, ['lint', '--local']);
  assert.equal(emptyRes.status, 1);
  assert.match(emptyRes.stderr, /\[story-missing-criteria\]/);

  // Structural/clarity warnings (bloated >6, long >35 lines, generic role, vague criterion) warn without failing exit code.
  writeRepoFile(repo, 'user_stories/no-criteria.md', [
    '# Verbose story',
    '',
    'As a user, I want many behaviors, so that everything works.',
    '',
    '## Acceptance criteria',
    '',
    '1. Saving handles errors gracefully.',
    ...Array.from({ length: 6 }, (_, i) => `${i + 2}. Item ${i + 2} prints "OK ${i + 2}".`),
    '',
    '## Notes',
    '',
    ...Array.from({ length: 26 }, (_, i) => `Detail line ${i + 1}.`),
  ].join('\n') + '\n');
  const warnRes = runCli(repo, env, ['lint', '--local', '--json']);
  assert.equal(warnRes.status, 0, warnRes.stderr);
  const parsed = JSON.parse(warnRes.stdout);
  assert.equal(parsed.ok, true);
  assert.deepEqual(parsed.problems, []);
  const codes = new Set(parsed.findings.map(f => f.code));
  for (const expected of ['story-generic-role', 'story-vague-criterion', 'story-bloated-criteria', 'story-too-long']) {
    assert.ok(codes.has(expected), `missing expected warning ${expected} in ${JSON.stringify(parsed.findings)}`);
  }
});

test('3642 Test C: 10+ prompts mentioning shared model-manifest.json and scripts/probe.py in prose emit 0 duplicate-owner warnings while explicit duplicate ownership (headers and pdd-bindings.json) IS flagged', t => {
  const { repo, env } = makeTempGitRepo(t, 'pdd-3642-c-');
  writeRepoFile(repo, 'model-manifest.json', JSON.stringify({ models: ['alpha'] }, null, 2) + '\n');
  writeRepoFile(repo, 'scripts/probe.py', 'def probe():\n    return True\n');

  for (let i = 1; i <= 12; i++) {
    writeRepoFile(
      repo,
      `prompts/worker-${i}.prompt.md`,
      `# Worker ${i}\n\nOwn \`src/worker_${i}.py\` while reading \`model-manifest.json\` and invoking \`scripts/probe.py\`.\n\n## Dependencies\n\nNone.\n`,
    );
    writeRepoFile(
      repo,
      `src/worker_${i}.py`,
      `# Prompt: prompts/worker-${i}.prompt.md\n\ndef run():\n    return ${i}\n`,
    );
  }
  commitAll(repo, '12 prompts with shared read-only manifest and probe script');

  // 1. Offline CLI lint (`pdd lint --local` and `pdd lint`) -> 0 errors, 0 warnings!
  for (const args of [['lint', '--local', '--json'], ['lint', '--json']]) {
    const res = runCli(repo, env, args);
    assert.equal(res.status, 0, `${args.join(' ')} stderr=${res.stderr}`);
    const doc = JSON.parse(res.stdout);
    assert.deepEqual(doc.problems, []);
    assert.deepEqual(doc.warnings, [], `expected 0 duplicate-owner noise from prose mentions: ${JSON.stringify(doc.warnings)}`);
  }

  // 2. Runtime seam `sharedSourceFiles` & `lintLocalHygiene` -> 0 duplicate-owner warnings!
  const visible = gitFiles(repo);
  const sharedClean = sharedSourceFiles(repo, visible);
  assert.deepEqual(sharedClean, [], `sharedSourceFiles must not warn on prose mentions: ${JSON.stringify(sharedClean)}`);
  const hygieneClean = runtimePreflightSlice().lintLocalHygiene({ root: repo, files: visible });
  assert.equal(hygieneClean.some(w => w.includes('duplicate-owner') || w.includes('model-manifest.json') || w.includes('scripts/probe.py')), false, JSON.stringify(hygieneClean));

  // 3. Real duplicate ownership: two prompts explicitly owning src/foo.py via headers AND two prompts bound to model-manifest.json via pdd-bindings.json!
  writeRepoFile(
    repo,
    'src/foo.py',
    '# Prompt: prompts/worker-1.prompt.md\n# Prompt: prompts/worker-2.prompt.md\n\ndef foo():\n    return 1\n',
  );
  writeRepoFile(
    repo,
    'pdd-bindings.json',
    JSON.stringify({
      schema_version: 'pdd.bindings.v1',
      modules: [
        { module: 'model-manifest.json', stories: [], prompt: 'prompts/worker-1.prompt.md' },
        { module: 'model-manifest.json', stories: [], prompt: 'prompts/worker-2.prompt.md' },
      ],
    }, null, 2) + '\n',
  );
  commitAll(repo, 'add explicit duplicate owners');

  const dupCli = runCli(repo, env, ['lint', '--local', '--json']);
  assert.equal(dupCli.status, 0, dupCli.stderr);
  const dupDoc = JSON.parse(dupCli.stdout);
  const dupFindings = dupDoc.findings.filter(f => f.code === 'duplicate-owner');
  assert.deepEqual(dupFindings.map(f => f.path).sort(), ['model-manifest.json', 'src/foo.py']);
  assert.equal(dupFindings.some(f => f.path === 'scripts/probe.py'), false, 'read-only prose-only scripts/probe.py must stay clean');

  const sharedDup = sharedSourceFiles(repo, gitFiles(repo));
  assert.ok(sharedDup.some(w => w.includes('src/foo.py') && w.includes('2 prompts')), JSON.stringify(sharedDup));
  assert.ok(sharedDup.some(w => w.includes('model-manifest.json') && w.includes('2 prompts')), JSON.stringify(sharedDup));
  assert.equal(sharedDup.some(w => w.includes('scripts/probe.py')), false);
});

test('3642 Test D: upfront target and --diff scoping isolates untouched broken files, keeps full lookup index, and catches broken callers on delete/rename', t => {
  const { repo, env } = makeTempGitRepo(t, 'pdd-3642-d-');

  // Clean files
  writeRepoFile(repo, 'prompts/helper.prompt.md', '# Helper\n\nProvide shared math.\n\n## Dependencies\n\nNone.\n');
  writeRepoFile(repo, 'prompts/target.prompt.md', '# Target\n\nOwn `src/caller.mjs`.\n\n## Dependencies\n\n- [Helper](helper.prompt.md)\n');
  writeRepoFile(repo, 'prompts/dep-on-target.prompt.md', '# Dependent\n\nUses target.\n\n## Dependencies\n\n- [Target](target.prompt.md)\n');
  writeRepoFile(repo, 'src/caller.mjs', '// Prompt: prompts/target.prompt.md\nexport const call = () => 1;\n');
  writeRepoFile(repo, 'user_stories/clean.md', [
    '# Clean flow',
    '',
    'As a customer, I want a subtotal shown, so that I know the cost.',
    '',
    '## Acceptance criteria',
    '',
    '1. Showing 2 items prints "$2.00" and exits with code 0.',
  ].join('\n') + '\n');

  // Pre-existing untouched broken files
  writeRepoFile(repo, 'user_stories/broken.md', '# Broken untouched story\n\nAs a shopper, I forgot acceptance criteria.\n');
  writeRepoFile(repo, 'src/old.mjs', '// Prompt: prompts/never-existed.prompt.md\nexport const old = () => 0;\n');
  writeRepoFile(repo, 'app-map.json', JSON.stringify({
    schema_version: 'prompt-runtime.app-map.v1',
    name: 'BrokenMap',
    screens: [{ id: 'main', prompt_path: 'prompts/ghost-screen.prompt.md' }],
  }, null, 2) + '\n');
  commitAll(repo, 'base commit with untouched broken files');

  // D1: Targeted `pdd lint --local user_stories/clean.md` and `pdd lint user_stories/clean.md` -> exit 0, 0 errors, 0 warnings!
  for (const args of [['lint', '--local', 'user_stories/clean.md'], ['lint', 'user_stories/clean.md']]) {
    const res = runCli(repo, env, args);
    assert.equal(res.status, 0, `${args.join(' ')} failed: stdout=${res.stdout} stderr=${res.stderr}`);
    assert.equal(res.stderr, '');
    assert.match(res.stdout, /Local lint: 0 errors, 0 warnings\./);
  }

  // D2: Bare `pdd lint --local` (full repo) STILL catches untouched broken files!
  const fullRes = runCli(repo, env, ['lint', '--local']);
  assert.equal(fullRes.status, 1);
  assert.match(fullRes.stderr, /user_stories\/broken\.md.*\[story-missing-criteria\]/);
  assert.match(fullRes.stderr, /src\/old\.mjs.*\[broken-prompt-header\]/);
  assert.match(fullRes.stdout, /app-map\.json.*ghost-screen\.prompt\.md/);

  // D3: `pdd lint --diff HEAD~1` touching ONLY `user_stories/clean.md` -> exit 0, 0 errors, 0 warnings!
  writeRepoFile(repo, 'user_stories/clean.md', [
    '# Clean flow',
    '',
    'As a customer, I want a subtotal shown, so that I know the total cost.',
    '',
    '## Acceptance criteria',
    '',
    '1. Showing 2 items prints "$2.00" and exits with code 0.',
  ].join('\n') + '\n');
  commitAll(repo, 'edit only clean story');

  const diffClean = runCli(repo, env, ['lint', '--diff', 'HEAD~1']);
  assert.equal(diffClean.status, 0, `stdout=${diffClean.stdout} stderr=${diffClean.stderr}`);
  assert.equal(diffClean.stderr, '');
  assert.match(diffClean.stdout, /Local lint: 0 errors, 0 warnings\./);

  // D4: Lookup index vs reporting scope: edit `prompts/target.prompt.md` (which links untouched `prompts/helper.prompt.md`)
  // and `src/caller.mjs` -> unchanged dependency resolves cleanly with 0 false missing-dependency errors and 0 noise from broken files!
  writeRepoFile(repo, 'prompts/target.prompt.md', '# Target\n\nOwn `src/caller.mjs`. Updated wording.\n\n## Dependencies\n\n- [Helper](helper.prompt.md)\n');
  commitAll(repo, 'edit target prompt with unchanged dependency');

  const diffLookup = runCli(repo, env, ['lint', '--diff', 'HEAD~1']);
  assert.equal(diffLookup.status, 0, `lookup index failed: stdout=${diffLookup.stdout} stderr=${diffLookup.stderr}`);
  assert.equal(diffLookup.stderr, '');
  assert.match(diffLookup.stdout, /Local lint: 0 errors, 0 warnings\./);

  // D5: Deleting a prompt in a PR MUST catch untouched `src/caller.mjs` (`broken-prompt-header`) AND `prompts/dep-on-target.prompt.md` (`broken-dependency-link`)
  // while still omitting unrelated `src/old.mjs` and `user_stories/broken.md`!
  execFileSync('git', ['rm', '-q', 'prompts/target.prompt.md'], { cwd: repo });
  commitAll(repo, 'delete target prompt');

  const diffDeleted = runCli(repo, env, ['lint', '--diff', 'HEAD~1']);
  assert.equal(diffDeleted.status, 1, `expected delete to fail: stdout=${diffDeleted.stdout}`);
  assert.match(diffDeleted.stderr, /src\/caller\.mjs.*\[broken-prompt-header\]/);
  assert.match(diffDeleted.stderr, /prompts\/dep-on-target\.prompt\.md.*\[broken-dependency-link\]/);
  assert.doesNotMatch(diffDeleted.stderr, /src\/old\.mjs/);
  assert.doesNotMatch(diffDeleted.stderr, /user_stories\/broken\.md/);
  assert.doesNotMatch(diffDeleted.stdout, /app-map\.json/);

  // D6: Unstaged working-tree deletion (`rm`) ALSO catches `src/caller.mjs`!
  execFileSync('git', ['reset', '--hard', '-q', 'HEAD~1'], { cwd: repo });
  unlinkSync(join(repo, 'prompts/target.prompt.md'));
  const diffUnstagedDel = runCli(repo, env, ['lint', '--diff', 'HEAD']);
  assert.equal(diffUnstagedDel.status, 1, `expected unstaged delete to fail: stdout=${diffUnstagedDel.stdout}`);
  assert.match(diffUnstagedDel.stderr, /src\/caller\.mjs.*\[broken-prompt-header\]/);
  assert.doesNotMatch(diffUnstagedDel.stderr, /src\/old\.mjs/);

  // D7: Renaming `prompts/target.prompt.md` -> `prompts/renamed-target.prompt.md` without updating `src/caller.mjs` catches `src/caller.mjs`!
  execFileSync('git', ['checkout', '--', 'prompts/target.prompt.md'], { cwd: repo });
  execFileSync('git', ['mv', 'prompts/target.prompt.md', 'prompts/renamed-target.prompt.md'], { cwd: repo });
  commitAll(repo, 'rename target prompt');

  const diffRenamed = runCli(repo, env, ['lint', '--diff', 'HEAD~1']);
  assert.equal(diffRenamed.status, 1, `expected rename to fail stale caller: stdout=${diffRenamed.stdout}`);
  assert.match(diffRenamed.stderr, /src\/caller\.mjs.*\[broken-prompt-header\]/);
  assert.match(diffRenamed.stderr, /prompts\/dep-on-target\.prompt\.md.*\[broken-dependency-link\]/);
  assert.doesNotMatch(diffRenamed.stderr, /src\/old\.mjs/);
  assert.doesNotMatch(diffRenamed.stderr, /user_stories\/broken\.md/);

  // D8: Untracked broken Story in working tree IS caught by `--diff`!
  execFileSync('git', ['reset', '--hard', '-q', 'HEAD~1'], { cwd: repo });
  writeRepoFile(repo, 'user_stories/untracked-bad.md', '# New broken story\n\nAs a shopper, I forgot acceptance criteria.\n');
  const diffUntracked = runCli(repo, env, ['lint', '--diff', 'HEAD']);
  assert.equal(diffUntracked.status, 1);
  assert.match(diffUntracked.stderr, /user_stories\/untracked-bad\.md.*\[story-missing-criteria\]/);
  assert.doesNotMatch(diffUntracked.stderr, /user_stories\/broken\.md/);
});

test('3642 Test E: AI lint prompt and reviewer/skill guides explicitly inspect fenced code blocks for implementation code dumps while allowing user-visible examples', () => {
  const prompt = buildAiLintPrompt([
    {
      path: 'user_stories/example.md',
      kind: 'story',
      text: '# Example\n\nAs a shopper, I want totals.\n\n## Acceptance criteria\n\n1. Prints total.\n\n```js\nexport function sum(a, b) { return a + b; }\n```\n',
    },
  ]);
  assert.match(prompt, /ENTIRE Story, including all fenced code blocks/i);
  assert.match(prompt, /implementation code/i);
  assert.match(prompt, /owning \.prompt\.md/i);
  assert.match(prompt, /tests\/ or fixtures\//i);
  assert.match(prompt, /short examples/i);

  for (const rel of [
    'src/autopilot/job-rules.md',
    'skills/pdd/references/stories.md',
    'skills/pdd/references/verification.md',
  ]) {
    const text = readFileSync(join(REPO_ROOT, rel), 'utf8');
    assert.match(text, /fenced code blocks/i, `${rel} must cover fenced code blocks in Stories`);
    assert.match(text, /implementation code/i, `${rel} must flag implementation code in Stories`);
    assert.match(text, /`\.prompt\.md`/, `${rel} must direct implementation details to .prompt.md`);
  }
});

test('3642 Test F: targeted pdd lint --local in a scenario-bearing repo scopes cleanly, catches prompt/cwd-relative errors, and handles non-scenario targets without exit 2', t => {
  const { repo, env } = makeTempGitRepo(t, 'pdd-3642-f-');
  writeRepoFile(repo, 'prompts/shared.prompt.md', '# Shared\n\nOwn `src/clean.mjs`.\n\n## Dependencies\n\nNone.\n');
  writeRepoFile(repo, 'prompts/broken.prompt.md', '# Broken prompt\n\n## Dependencies\n\n- [Ghost](does-not-exist.prompt.md)\n');
  writeRepoFile(repo, 'src/clean.mjs', '// Prompt: prompts/shared.prompt.md\nexport const ok = () => true;\n');
  writeRepoFile(repo, 'src/old.mjs', '// Prompt: prompts/never-existed.prompt.md\nexport const old = () => false;\n');
  writeRepoFile(repo, 'user_stories/clean.md', [
    '# Clean checkout',
    '',
    'As a shopper, I want the subtotal displayed, so that I see the charge.',
    '',
    '## Acceptance criteria',
    '',
    '1. Checkout prints "$10.00" and exits with code 0.',
  ].join('\n') + '\n');
  writeRepoFile(repo, 'tests/clean.json', JSON.stringify({
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/clean.md',
    criteria: [{ id: 'AC1', text: 'Checkout prints "$10.00" and exits with code 0.' }],
    initial_world: {},
    simulation: {},
    steps: [{
      step_id: 's1',
      entry_path: 'prompts/shared.prompt.md',
      operation: 'checkout',
      input: {},
      checks: [{ criterion_id: 'AC1', target: 'result', path: '/total', op: 'equals', value: '$10.00' }],
    }],
  }, null, 2) + '\n');
  writeRepoFile(repo, 'user_stories/sibling.md', [
    '# Sibling story sharing prompts/shared.prompt.md',
    '',
    'As a user, I want sibling behavior, so that everything works.',
    '',
    '## Acceptance criteria',
    '',
    '1. Sibling handles errors gracefully.',
  ].join('\n') + '\n');
  writeRepoFile(repo, 'tests/sibling.json', JSON.stringify({
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/sibling.md',
    criteria: [{ id: 'AC1', text: 'Sibling handles errors gracefully.' }],
    initial_world: {},
    simulation: {},
    steps: [{
      step_id: 's1',
      entry_path: 'prompts/shared.prompt.md',
      operation: 'sibling',
      input: {},
      checks: [{ criterion_id: 'AC1', target: 'result', path: '/ok', op: 'equals', value: true }],
    }],
  }, null, 2) + '\n');
  writeRepoFile(repo, 'user_stories/no-scenario.md', [
    '# Story without scenario json',
    '',
    'As an editor, I want preview text shown, so that I verify formatting.',
    '',
    '## Acceptance criteria',
    '',
    '1. Preview prints "Ready" and exits with code 0.',
  ].join('\n') + '\n');
  writeRepoFile(repo, 'user_stories/broken.md', '# Broken story\n\nAs a shopper, I forgot acceptance criteria.\n');
  mkdirSync(join(repo, 'sub'), { recursive: true });
  commitAll(repo, 'scenario-bearing repo fixture');

  // 1. Targeted scenario Story: 0 sibling Story warnings, 0 src/old.mjs or broken.md errors.
  const cleanRes = runCli(repo, env, ['lint', '--local', 'user_stories/clean.md', '--json']);
  assert.equal(cleanRes.status, 0, `stdout=${cleanRes.stdout} stderr=${cleanRes.stderr}`);
  const cleanDoc = JSON.parse(cleanRes.stdout);
  assert.equal(cleanDoc.exit_code, 0);
  assert.deepEqual(cleanDoc.problems, []);
  assert.equal((cleanDoc.warnings ?? []).some(w => /sibling|old\.mjs|broken/i.test(w)), false, JSON.stringify(cleanDoc.warnings));

  // 2. Targeted broken prompt under --local in scenario-bearing repo MUST catch [broken-dependency-link] (exit 1, not silently dropped!).
  const promptRes = runCli(repo, env, ['lint', '--local', 'prompts/broken.prompt.md']);
  assert.equal(promptRes.status, 1, `expected exit 1: stdout=${promptRes.stdout} stderr=${promptRes.stderr}`);
  assert.match(promptRes.stderr, /prompts\/broken\.prompt\.md.*\[broken-dependency-link\]/);
  assert.doesNotMatch(promptRes.stderr, /src\/old\.mjs/);
  assert.doesNotMatch(promptRes.stderr, /user_stories\/broken\.md/);

  // 3. Non-scenario targets (`user_stories/no-scenario.md`, `src/clean.mjs`) succeed with exit 0 (not exit 2!).
  for (const target of ['user_stories/no-scenario.md', 'src/clean.mjs']) {
    const res = runCli(repo, env, ['lint', '--local', target]);
    assert.equal(res.status, 0, `${target} failed: stdout=${res.stdout} stderr=${res.stderr}`);
    assert.equal(res.stderr, '');
  }

  // 4. cwd-relative targets from a subdirectory catch hard errors deterministically.
  const subBrokenStory = spawnSync(process.execPath, [PDD_BIN, 'lint', '--local', '../user_stories/broken.md'], {
    cwd: join(repo, 'sub'),
    env,
    encoding: 'utf8',
    timeout: 15_000,
  });
  assert.equal(subBrokenStory.status, 1, `stdout=${subBrokenStory.stdout} stderr=${subBrokenStory.stderr}`);
  assert.match(subBrokenStory.stderr, /user_stories\/broken\.md.*\[story-missing-criteria\]/);

  const subBrokenPrompt = spawnSync(process.execPath, [PDD_BIN, 'lint', '--local', '../prompts/broken.prompt.md'], {
    cwd: join(repo, 'sub'),
    env,
    encoding: 'utf8',
    timeout: 15_000,
  });
  assert.equal(subBrokenPrompt.status, 1, `stdout=${subBrokenPrompt.stdout} stderr=${subBrokenPrompt.stderr}`);
  assert.match(subBrokenPrompt.stderr, /prompts\/broken\.prompt\.md.*\[broken-dependency-link\]/);
});

test('3642 Test G: adversarial scope edge cases — rename+replacement, inverted native-only, app-map CSS & custom app_maps, trailing slash, reference SVG delete, combined --diff+target, product plan drift', t => {
  const { repo, env } = makeTempGitRepo(t, 'pdd-3642-g-');

  // 1. Inverted native-only chain: tests/order.json -> prompts/order.prompt.md -> prompts/mid.prompt.md -> prompts/db.prompt.md (native-only)
  writeRepoFile(repo, 'prompts/db.prompt.md', '---\nkind: native-only\n---\n\n# DB\n\nHandles storage.\n\n## Dependencies\n\nNone.\n');
  writeRepoFile(repo, 'prompts/mid.prompt.md', '# Mid\n\nCalls db.\n\n## Dependencies\n\n- [DB](db.prompt.md)\n');
  writeRepoFile(repo, 'prompts/order.prompt.md', '# Order\n\nCalls mid.\n\n## Dependencies\n\n- [Mid](mid.prompt.md)\n');
  writeRepoFile(repo, 'user_stories/order.md', [
    '# Place order',
    '',
    'As a buyer, I want an order placed, so that items ship.',
    '',
    '## Acceptance criteria',
    '',
    '1. Placing an order prints "Placed" and exits with code 0.',
  ].join('\n') + '\n');
  writeRepoFile(repo, 'tests/order.json', JSON.stringify({
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/order.md',
    criteria: [{ id: 'AC1', text: 'Placing an order prints "Placed" and exits with code 0.' }],
    initial_world: {},
    simulation: {},
    steps: [{
      step_id: 's1',
      entry_path: 'prompts/order.prompt.md',
      operation: 'place_order',
      input: {},
      checks: [{ criterion_id: 'AC1', target: 'result', path: '/status', op: 'equals', value: 'Placed' }],
    }],
  }, null, 2) + '\n');

  // 2. App-map CSS warning isolation & custom scenario app_maps path
  writeRepoFile(repo, 'prompts/good-screen.prompt.md', '# Good Screen\n\nRender clean screen.\n\n## Dependencies\n\nNone.\n');
  writeRepoFile(repo, 'app/maps/good.json', JSON.stringify({
    schema_version: 'prompt-runtime.app-map.v1',
    name: 'GoodMap',
    screens: [{ id: 'home', prompt_path: 'prompts/good-screen.prompt.md' }],
  }, null, 2) + '\n');
  writeRepoFile(repo, 'app/maps/broken.json', JSON.stringify({
    schema_version: 'prompt-runtime.app-map.v1',
    name: 'BrokenMap',
    stylesheets: ['styles/missing-broken.css'],
    screens: [
      { id: 'home', prompt_path: 'prompts/good-screen.prompt.md', source: 'operation', format: 'html' },
      { id: 'bad', prompt_path: 'prompts/missing-screen.prompt.md' },
    ],
  }, null, 2) + '\n');
  writeRepoFile(repo, 'ui/custom-map.json', JSON.stringify({
    schema_version: 'prompt-runtime.app-map.v1',
    name: 'CustomMap',
    screens: [{ id: 'custom', prompt_path: 'prompts/missing-custom-screen.prompt.md' }],
  }, null, 2) + '\n');
  writeRepoFile(repo, 'user_stories/custom.md', [
    '# Custom screen',
    '',
    'As an operator, I want the custom screen rendered, so that metrics appear.',
    '',
    '## Acceptance criteria',
    '',
    '1. Opening custom screen prints "Metrics".',
  ].join('\n') + '\n');
  writeRepoFile(repo, 'tests/custom.json', JSON.stringify({
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/custom.md',
    app_maps: ['ui/custom-map.json'],
    criteria: [{ id: 'AC1', text: 'Opening custom screen prints "Metrics".' }],
    initial_world: {},
    simulation: {},
    steps: [{
      step_id: 's1',
      entry_path: 'prompts/good-screen.prompt.md',
      operation: 'render',
      input: {},
      checks: [{ criterion_id: 'AC1', target: 'result', path: '/text', op: 'equals', value: 'Metrics' }],
    }],
  }, null, 2) + '\n');

  // 3. Reference-style SVG link + target/caller + product/plan.md
  writeRepoFile(repo, 'prompts/screen.ui.svg', '<svg xmlns="http://www.w3.org/2000/svg" width="200" height="100"><text x="10" y="20">OK</text></svg>\n');
  writeRepoFile(repo, 'prompts/ref-svg.prompt.md', '# Ref SVG\n\n![Screen][mockup]\n\n[mockup]: screen.ui.svg\n\n## Dependencies\n\nNone.\n');
  writeRepoFile(repo, 'prompts/target.prompt.md', '# Target\n\nOwn `src/caller.mjs`.\n\n## Dependencies\n\nNone.\n');
  writeRepoFile(repo, 'src/caller.mjs', '// Prompt: prompts/target.prompt.md\nexport const call = () => 1;\n');
  writeRepoFile(repo, 'product/plan.md', [
    '# Product Plan',
    '',
    '## Prompts',
    '',
    '- `prompts/db.prompt.md`',
    '- `prompts/mid.prompt.md`',
    '- `prompts/order.prompt.md`',
    '- `prompts/good-screen.prompt.md`',
    '- `prompts/ref-svg.prompt.md`',
    '- `prompts/target.prompt.md`',
  ].join('\n') + '\n');

  commitAll(repo, 'adversarial scope base');

  // G1 (P1 #3): Targeted intermediate prompt STILL reports inverted native-only dependency from full lookup index!
  const midRes = runCli(repo, env, ['lint', 'prompts/mid.prompt.md', '--json']);
  assert.equal(midRes.status, 0, midRes.stderr);
  const midDoc = JSON.parse(midRes.stdout);
  assert.ok(midDoc.warnings.some(w => /checkable prompt links kind: native-only prompt prompts\/db\.prompt\.md/.test(w)), JSON.stringify(midDoc.warnings));
  assert.equal(midDoc.warnings.some(w => /app\/maps\/broken\.json|ui\/custom-map\.json/.test(w)), false, JSON.stringify(midDoc.warnings));

  // G2 (P1 #4 & P2 #5): app/maps/good.json isolates broken.json (including CSS warnings on shared prompt!); tests/custom.json pulls custom ui/custom-map.json only!
  const goodMapRes = runCli(repo, env, ['lint', 'app/maps/good.json', '--json']);
  assert.equal(goodMapRes.status, 0, goodMapRes.stderr);
  const goodMapDoc = JSON.parse(goodMapRes.stdout);
  assert.deepEqual(goodMapDoc.warnings, [], JSON.stringify(goodMapDoc.warnings));

  const customRes = runCli(repo, env, ['lint', 'tests/custom.json', '--json']);
  assert.equal(customRes.status, 0, customRes.stderr);
  const customDoc = JSON.parse(customRes.stdout);
  assert.ok(customDoc.warnings.some(w => w.includes('ui/custom-map.json') && w.includes('missing-custom-screen.prompt.md')), JSON.stringify(customDoc.warnings));
  assert.equal(customDoc.warnings.some(w => w.includes('app/maps/broken.json')), false, JSON.stringify(customDoc.warnings));

  // G3 (P2 #6): Trailing slash (`user_stories/`) and `.` from inside subdir work cleanly without unmatched-target exit 2.
  const trailingRes = runCli(repo, env, ['lint', 'user_stories/']);
  assert.equal(trailingRes.status, 0, `stdout=${trailingRes.stdout} stderr=${trailingRes.stderr}`);
  const dotFromSubdir = spawnSync(process.execPath, [PDD_BIN, 'lint', '.'], {
    cwd: join(repo, 'user_stories'),
    env,
    encoding: 'utf8',
    timeout: 15_000,
  });
  assert.equal(dotFromSubdir.status, 0, `stdout=${dotFromSubdir.stdout} stderr=${dotFromSubdir.stderr}`);

  // G4 (P2 #7): Deleting SVG referenced via reference-style link pulls prompts/ref-svg.prompt.md into --diff scope!
  unlinkSync(join(repo, 'prompts/screen.ui.svg'));
  const svgDelRes = runCli(repo, env, ['lint', '--diff', 'HEAD', '--json']);
  assert.equal(svgDelRes.status, 0, svgDelRes.stderr);
  const svgDelDoc = JSON.parse(svgDelRes.stdout);
  assert.ok(svgDelDoc.warnings.some(w => w.includes('prompts/ref-svg.prompt.md') && w.includes('screen.ui.svg')), JSON.stringify(svgDelDoc.warnings));
  execFileSync('git', ['checkout', '--', 'prompts/screen.ui.svg'], { cwd: repo });

  // G5 (P2 #8): Combined `--diff HEAD src/caller.mjs` with unstaged delete of target.prompt.md STILL catches caller, and bad base ref fails closed (exit 2)!
  unlinkSync(join(repo, 'prompts/target.prompt.md'));
  const comboDelRes = runCli(repo, env, ['lint', '--diff', 'HEAD', 'src/caller.mjs']);
  assert.equal(comboDelRes.status, 1, `stdout=${comboDelRes.stdout} stderr=${comboDelRes.stderr}`);
  assert.match(comboDelRes.stderr, /src\/caller\.mjs.*\[broken-prompt-header\]/);

  const badBaseRes = runCli(repo, env, ['lint', '--diff', 'nonexistent-ref-3642', 'src/caller.mjs']);
  assert.equal(badBaseRes.status, 1, `expected exit 1 fail-closed on bad base ref: stdout=${badBaseRes.stdout} stderr=${badBaseRes.stderr}`);
  assert.match(badBaseRes.stderr, /\[diff-base-unavailable\]/);

  // G6 (P2 #9): Deleting prompts/target.prompt.md triggers product-prompt-inventory-drift in --diff!
  const driftRes = runCli(repo, env, ['lint', '--diff', 'HEAD', '--json']);
  assert.equal(driftRes.status, 1);
  const driftDoc = JSON.parse(driftRes.stdout);
  assert.ok(driftDoc.findings.some(f => f.code === 'product-prompt-inventory-drift' && f.path === 'product/plan.md'), JSON.stringify(driftDoc.findings));
  execFileSync('git', ['checkout', '--', 'prompts/target.prompt.md'], { cwd: repo });

  // G7 (P1 #2): `git mv prompts/target.prompt.md prompts/moved.prompt.md` + untracked replacement at oldPath MUST NOT falsely mark target deleted, AND MUST lint the new untracked file!
  execFileSync('git', ['mv', 'prompts/target.prompt.md', 'prompts/moved.prompt.md'], { cwd: repo });
  writeRepoFile(repo, 'prompts/target.prompt.md', '# Replaced target\n\n## Dependencies\n\n- [Ghost](never-existed.prompt.md)\n');
  const replaceRes = runCli(repo, env, ['lint', '--diff', 'HEAD']);
  assert.equal(replaceRes.status, 1, `stdout=${replaceRes.stdout} stderr=${replaceRes.stderr}`);
  assert.match(replaceRes.stderr, /prompts\/target\.prompt\.md.*\[broken-dependency-link\]/);
  assert.doesNotMatch(replaceRes.stderr, /src\/caller\.mjs.*\[broken-prompt-header\]/);
});

test('3642 Test H: Round 2 edge cases — non-runtime test JSONs, bare prompt slug, transitive prompt error under --local, slug collision, malformed scenario JSON, ./ app_maps, and no cross-kind mismatch', t => {
  const { repo, env } = makeTempGitRepo(t, 'pdd-3642-h-');

  // Story + scenario + prompt sharing the exact same stem `alpha` (slug collision test).
  writeRepoFile(repo, 'prompts/alpha.prompt.md', '# Alpha\n\nGreet visitor.\n\n## Dependencies\n\nNone.\n');
  writeRepoFile(repo, 'user_stories/alpha.md', [
    '# Alpha greeting',
    '',
    'As a visitor, I want a greeting, so that I know the app responded.',
    '',
    '## Acceptance',
    '',
    '1. Greeting prints "Hello".',
  ].join('\n') + '\n');
  writeRepoFile(repo, 'tests/alpha.json', JSON.stringify({
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/alpha.md',
    criteria: [{ id: 'AC1', text: 'Greeting prints "Hello".' }],
    initial_world: {},
    simulation: {},
    steps: [{
      step_id: 's1',
      entry_path: 'prompts/alpha.prompt.md',
      operation: 'greet',
      input: {},
      checks: [{ criterion_id: 'AC1', target: 'result', path: '/msg', op: 'equals', value: 'Hello' }],
    }],
  }, null, 2) + '\n');
  writeRepoFile(repo, 'tests/dotmap-rel.json', JSON.stringify({
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/alpha.md',
    app_maps: ['./ui/dot-map.json'],
    criteria: [{ id: 'AC1', text: 'Greeting prints "Hello".' }],
    initial_world: {},
    simulation: {},
    steps: [{
      step_id: 's1',
      entry_path: 'prompts/alpha.prompt.md',
      operation: 'greet',
      input: {},
      checks: [{ criterion_id: 'AC1', target: 'result', path: '/msg', op: 'equals', value: 'Hello' }],
    }],
  }, null, 2) + '\n');
  writeRepoFile(repo, 'ui/dot-map.json', JSON.stringify({
    schema_version: 'prompt-runtime.app-map.v1',
    name: 'DotMap',
    screens: [{ id: 'main', prompt_path: 'prompts/missing-dot-screen.prompt.md' }],
  }, null, 2) + '\n');

  // Transitive prompt hard error: tests/trans.json -> prompts/entry.prompt.md -> prompts/dep-broken.prompt.md (caught ONLY via lintRepoProject + onProjectLintResult!)
  writeRepoFile(repo, 'pdd.json', JSON.stringify({
    lint: {
      custom_rules: [
        {
          id: 'no-forbidden-transitive-token',
          target: 'prompt',
          severity: 'error',
          forbid_pattern: 'FORBIDDEN_TRANSITIVE_TOKEN',
          message: 'Transitive prompt contains forbidden token',
        },
      ],
    },
  }, null, 2) + '\n');
  writeRepoFile(repo, 'prompts/dep-broken.prompt.md', '# Dep Broken\n\nContains FORBIDDEN_TRANSITIVE_TOKEN.\n\n## Dependencies\n\nNone.\n');
  writeRepoFile(repo, 'prompts/broken-slug.prompt.md', '# Broken Slug\n\n## Dependencies\n\n- [Ghost](ghost-dep.prompt.md)\n');
  writeRepoFile(repo, 'prompts/entry.prompt.md', '# Entry\n\nCalls dep.\n\n## Dependencies\n\n- [Dep](dep-broken.prompt.md)\n');
  writeRepoFile(repo, 'user_stories/trans.md', [
    '# Transitive chain',
    '',
    'As a buyer, I want checkout confirmed, so that I get a receipt.',
    '',
    '## Acceptance criteria',
    '',
    '1. Checkout prints "Done".',
  ].join('\n') + '\n');
  writeRepoFile(repo, 'tests/trans.json', JSON.stringify({
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/trans.md',
    criteria: [{ id: 'AC1', text: 'Checkout prints "Done".' }],
    initial_world: {},
    simulation: {},
    steps: [{
      step_id: 's1',
      entry_path: 'prompts/entry.prompt.md',
      operation: 'checkout',
      input: {},
      checks: [{ criterion_id: 'AC1', target: 'result', path: '/status', op: 'equals', value: 'Done' }],
    }],
  }, null, 2) + '\n');

  // Malformed JSON scenario paired by stem with user_stories/badjson.md
  writeRepoFile(repo, 'user_stories/badjson.md', [
    '# Bad json story',
    '',
    'As a shopper, I want valid responses, so that checkout works.',
    '',
    '## Acceptance criteria',
    '',
    '1. Checkout prints "OK".',
  ].join('\n') + '\n');
  writeRepoFile(repo, 'tests/badjson.json', '{not valid json\n');

  // Non-runtime JSONs under tests/
  writeRepoFile(repo, 'tests/orphan.json', JSON.stringify({ custom: true }) + '\n');
  writeRepoFile(repo, 'tests/cases.json', JSON.stringify({ cases: [] }) + '\n');
  writeRepoFile(repo, 'user_stories/only-story.md', [
    '# Only story',
    '',
    'As a reader, I want text shown, so that I read it.',
    '',
    '## Acceptance criteria',
    '',
    '1. Page shows "Welcome".',
  ].join('\n') + '\n');

  commitAll(repo, 'round 2 edge cases');

  // H1: Story slug collision (`alpha` matches story+scenario+prompt) + `## Acceptance` heading runs runtime local lint!
  const alphaRes = runCli(repo, env, ['lint', '--local', 'alpha', '--json']);
  assert.equal(alphaRes.status, 0, `stdout=${alphaRes.stdout} stderr=${alphaRes.stderr}`);
  const alphaDoc = JSON.parse(alphaRes.stdout);
  assert.equal(alphaDoc.local_only, true);
  assert.deepEqual(alphaDoc.problems, []);

  // H1b: Leading `./` in scenario app_maps normalizes identically across lint-scope and app-map-lint!
  const dotMapRes = runCli(repo, env, ['lint', 'tests/dotmap-rel.json', '--json']);
  assert.equal(dotMapRes.status, 0, dotMapRes.stderr);
  const dotMapDoc = JSON.parse(dotMapRes.stdout);
  assert.ok((dotMapDoc.warnings ?? []).some(w => w.includes('ui/dot-map.json') && w.includes('missing-dot-screen.prompt.md')), JSON.stringify(dotMapDoc.warnings));

  // H2: Transitive prompt hard error in targeted `pdd lint --local user_stories/trans.md` MUST fail with exit 1 via onProjectLintResult!
  const transRes = runCli(repo, env, ['lint', '--local', 'user_stories/trans.md']);
  assert.equal(transRes.status, 1, `expected transitive error exit 1: stdout=${transRes.stdout} stderr=${transRes.stderr}`);
  assert.match(transRes.stderr, /prompts\/dep-broken\.prompt\.md.*\[no-forbidden-transitive-token\]/);

  // H3: Non-runtime test JSONs (`tests/orphan.json`, `tests/cases.json`) under `--local` exit 0 (not exit 2!).
  for (const target of ['tests/orphan.json', 'tests/cases.json']) {
    const res = runCli(repo, env, ['lint', '--local', target]);
    assert.equal(res.status, 0, `${target} failed: stdout=${res.stdout} stderr=${res.stderr}`);
  }

  // H4: Bare prompt slug (`broken-slug.prompt.md`) falls back to runLocalLint and catches [broken-dependency-link] (exit 1, not exit 2!).
  const bareSlugRes = runCli(repo, env, ['lint', '--local', 'broken-slug.prompt.md']);
  assert.equal(bareSlugRes.status, 1, `stdout=${bareSlugRes.stdout} stderr=${bareSlugRes.stderr}`);
  assert.match(bareSlugRes.stderr, /prompts\/broken-slug\.prompt\.md.*\[broken-dependency-link\]/);

  // H5: Malformed scenario JSON paired by stem IS still reported when targeting `user_stories/badjson.md`!
  const badJsonRes = runCli(repo, env, ['lint', 'user_stories/badjson.md', '--json']);
  assert.equal(badJsonRes.status, 0, badJsonRes.stderr);
  const badJsonDoc = JSON.parse(badJsonRes.stdout);
  assert.ok(badJsonDoc.warnings.some(w => w.includes('tests/badjson.json') && /not valid JSON/i.test(w)), JSON.stringify(badJsonDoc.warnings));

  // H6: Nonexistent explicit filename (`only-story.prompt.md`) and empty operand (`""`) report unmatched (exit 2), no cross-kind mismatch!
  const crossKindRes = runCli(repo, env, ['lint', 'only-story.prompt.md']);
  assert.equal(crossKindRes.status, 2, `expected exit 2: stdout=${crossKindRes.stdout} stderr=${crossKindRes.stderr}`);
  const emptyWordRes = runCli(repo, env, ['lint', '']);
  assert.equal(emptyWordRes.status, 2, `expected exit 2: stdout=${emptyWordRes.stdout} stderr=${emptyWordRes.stderr}`);
});
