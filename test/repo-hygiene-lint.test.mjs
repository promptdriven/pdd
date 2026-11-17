import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import {
  isInspectableTestCodePath,
  lintFakeTests,
  lintPromptCodeBlocks,
  lintRepoAntiPatterns,
} from '../src/repo-hygiene-lint.mjs';
import { runCheck, runtimePreflightSlice } from '../src/runtime-seam.mjs';
import { lintStories, lintStory } from '../src/story-lint.mjs';
import { portsFor, sink } from './helpers/runtime-fake.mjs';

test('3453 lintFakeTests warns on prompt reads, repo existence checks and source text matching with path:line', () => {
  assert.equal(isInspectableTestCodePath('test/order.test.mjs'), true);
  assert.equal(isInspectableTestCodePath('tests/unit/calc.spec.ts'), true);
  assert.equal(isInspectableTestCodePath('tests/place-order.json'), false);
  assert.equal(isInspectableTestCodePath('test/fixtures/sample.test.mjs'), false);
  assert.equal(isInspectableTestCodePath('test/helpers/fake.mjs'), false);
  assert.equal(isInspectableTestCodePath('test/runtime-seam.test.mjs'), false);

  const fakeSuite = [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { existsSync, readFileSync, statSync } from 'node:fs';",
    "import { join } from 'node:path';",
    '',
    "test('anti-patterns', () => {",
    "  const prompt = readFileSync('prompts/cli/order.prompt.md', 'utf8');",
    "  assert.ok(prompt.includes('total'));",
    "  assert.equal(existsSync('src/order.mjs'), true);",
    "  assert.ok(statSync(join(process.cwd(), 'prompts/cli/order.prompt.md')).isFile());",
    "  const impl = readFileSync('src/order.mjs', 'utf8');",
    '  assert.match(impl, /export function placeOrder/);',
    "  assert.ok(readFileSync('src/pricing.mjs', 'utf8').includes('discount'));",
    '});',
  ].join('\n');

  const warnings = lintFakeTests(fakeSuite, { path: 'test/order.test.mjs' });
  assert.ok(warnings.every(w => w.startsWith('Warning:')));
  assert.ok(warnings.some(w => w.includes('test/order.test.mjs:7') && w.includes('[fake-test-prompt-read]')));
  assert.ok(warnings.some(w => w.includes('test/order.test.mjs:9') && w.includes('[fake-test-exists-check]')));
  assert.ok(warnings.some(w => w.includes('test/order.test.mjs:10') && w.includes('[fake-test-exists-check]')));
  assert.ok(warnings.some(w => w.includes('test/order.test.mjs:12') && w.includes('[fake-test-source-match]')));
  assert.ok(warnings.some(w => w.includes('test/order.test.mjs:13') && w.includes('[fake-test-source-match]')));

  // Clean behavioral tests, comments, string literals for temp sandboxes and structural seam files produce 0 warnings.
  const cleanBehavioral = [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { existsSync, mkdtempSync, readFileSync, writeFileSync } from 'node:fs';",
    "import { tmpdir } from 'node:os';",
    "import { join } from 'node:path';",
    "import { placeOrder } from '../src/order.mjs';",
    '',
    "// Comment mentioning readFileSync('prompts/cli/order.prompt.md') does not warn.",
    "test('behavioral check', () => {",
    "  const sandbox = mkdtempSync(join(tmpdir(), 'pdd-sandbox-'));",
    "  writeFileSync(join(sandbox, 'src-copy.txt'), \"readFileSync('prompts/cli/order.prompt.md')\");",
    "  assert.equal(existsSync(join(sandbox, 'src-copy.txt')), true);",
    "  const fixtureText = readFileSync('test/fixtures/harbor/prompts/place_order.prompt.md', 'utf8');",
    '  assert.ok(fixtureText.length > 0);',
    "  assert.deepEqual(placeOrder({ items: ['drip'] }), { totalCents: 210 });",
    '});',
  ].join('\n');

  assert.deepEqual(lintFakeTests(cleanBehavioral, { path: 'test/order-behavior.test.mjs' }), []);
  assert.deepEqual(lintFakeTests(fakeSuite, { path: 'test/runtime-seam.test.mjs' }), []);
  assert.deepEqual(lintFakeTests(fakeSuite, { path: 'test/fixtures/fake.test.mjs' }), []);
});

test('3453 lintPromptCodeBlocks allows mermaid and short declarative examples while warning on long or imperative fences', () => {
  const longMermaid = [
    '---',
    'kind: native-only',
    'reason: Local parser.',
    '---',
    '',
    '# Order flow',
    '',
    'Own `src/order-flow.mjs`. Validate state transitions.',
    '',
    '```mermaid',
    'flowchart TD',
    ...Array.from({ length: 22 }, (_, i) => `  S${i} --> S${i + 1}`),
    '```',
    '',
    'Short declarative JSON payload:',
    '',
    '```json',
    '{',
    '  "customer": "Sam",',
    '  "totalCents": 900',
    '}',
    '```',
    '',
    '<details><summary>Runtime interface</summary>',
    '',
    '```json',
    JSON.stringify({
      status: 'draft',
      prose_sha256: '',
      entries: Array.from({ length: 10 }, (_, idx) => ({
        operation: `op_${idx}`,
        input_schema: { type: 'object' },
        result_schema: { type: 'object' },
      })),
    }, null, 2),
    '```',
    '</details>',
  ].join('\n');

  assert.deepEqual(lintPromptCodeBlocks(longMermaid, { path: 'prompts/cli/order-flow.prompt.md' }), []);

  // Imperative control-flow tokens warn with accurate 1-based line numbers even after frontmatter.
  for (const snippet of [
    'export function compute(x) { return x + 1; }',
    'const total = items.reduce((a, b) => a + b, 0);',
    'let count = 0;\nwhile (count < 3) { count++; }',
    'if (price < 0) {\n  return 0;\n}',
    'for (const row of rows) {}',
    'def calculate_tax(cents):',
    'impl OrderTotal {',
    'try {\n  parse();\n}',
  ]) {
    const promptWithCode = [
      '# Bad prompt',
      '',
      'Own `src/bad.mjs`.',
      '',
      '```',
      snippet,
      '```',
    ].join('\n');
    const out = lintPromptCodeBlocks(promptWithCode, { path: 'prompts/cli/bad.prompt.md' });
    assert.ok(out.some(w => w.includes('prompts/cli/bad.prompt.md:6') && w.includes('[prompt-imperative-code]')), snippet);
  }

  // > 15 lines in a single non-mermaid fence and > 30 total non-mermaid fenced lines warn at opening fence lines.
  const bloatedPrompt = [
    '# Bloated examples',
    '',
    'Own `src/bloated.mjs`.',
    '',
    '```txt',
    ...Array.from({ length: 18 }, (_, i) => `row-${i + 1}: value`),
    '```',
    '',
    '```txt',
    ...Array.from({ length: 16 }, (_, i) => `more-${i + 1}: value`),
    '```',
  ].join('\n');

  const bloatedWarnings = lintPromptCodeBlocks(bloatedPrompt, { path: 'prompts/cli/bloated.prompt.md' });
  assert.ok(bloatedWarnings.some(w => w.includes('prompts/cli/bloated.prompt.md:5') && w.includes('[prompt-code-fence-length]')));
  assert.ok(bloatedWarnings.some(w => w.includes('prompts/cli/bloated.prompt.md:26') && w.includes('[prompt-code-fence-length]')));
  assert.ok(bloatedWarnings.some(w => w.includes('prompts/cli/bloated.prompt.md:5') && w.includes('[prompt-code-fence-total]')));
});

test('3453 lintStory checks missing and bloated acceptance criteria while keeping lintStories gate-compatible by default', () => {
  const noHeading = '# Export receipt\n\nAs a shop owner, I want a receipt PDF, so that I can file taxes.\n';
  const resNoHeading = lintStory(noHeading, { path: 'user_stories/no-heading.md' });
  assert.equal(resNoHeading.ok, false);
  assert.ok(resNoHeading.problems.some(p => p.line === 1 && p.code === 'story-missing-criteria'));

  const emptyCriteria = [
    '# Export receipt',
    '',
    'As a shop owner, I want a receipt PDF, so that I can file taxes.',
    '',
    '## Acceptance criteria',
    '',
    '## Rules to check',
    '',
    '- Totals match line items.',
  ].join('\n');
  const resEmpty = lintStory(emptyCriteria, { path: 'user_stories/empty-criteria.md' });
  assert.equal(resEmpty.ok, false);
  assert.ok(resEmpty.problems.some(p => p.line === 5 && p.code === 'story-missing-criteria'));

  const sixBullets = [
    '# Export receipt',
    '',
    'As a shop owner, I want a receipt summary, so that I can reconcile daily sales.',
    '',
    '## Acceptance criteria',
    '',
    ...Array.from({ length: 6 }, (_, i) => `- AC${i + 1}: Summary row ${i + 1} prints "$${i + 1}.00"\n  with two decimal places.`),
  ].join('\n');
  assert.equal(lintStory(sixBullets, { path: 'user_stories/six.md' }).ok, true);

  const sevenNumbered = [
    '# Export receipt',
    '',
    'As a shop owner, I want a receipt summary, so that I can reconcile daily sales.',
    '',
    '## Acceptance criteria',
    '',
    ...Array.from({ length: 7 }, (_, i) => `${i + 1}. Summary row ${i + 1} prints "$${i + 1}.00".`),
  ].join('\n');
  const resSeven = lintStory(sevenNumbered, { path: 'user_stories/seven.md' });
  assert.equal(resSeven.ok, false);
  assert.ok(resSeven.problems.some(p => p.line === 13 && p.code === 'story-bloated-criteria'));

  const longStory = [
    '# Export receipt',
    '',
    'As a shop owner, I want a receipt summary, so that I can reconcile daily sales.',
    '',
    '## Acceptance criteria',
    '',
    '1. Summary row 1 prints "$1.00".',
    '',
    '## Rules to check',
    '',
    ...Array.from({ length: 28 }, (_, i) => `- Invariant ${i + 1}: row ${i + 1} stays balanced.`),
  ].join('\n');
  const resLong = lintStory(longStory, { path: 'user_stories/long.md' });
  assert.equal(resLong.ok, false);
  assert.ok(resLong.problems.some(p => p.line === 36 && p.code === 'story-too-long'));

  // Default lintStories keeps existing workflow/approve gates non-blocking on criteria count and Story length unless opted in.
  assert.equal(lintStories([{ path: 'user_stories/seven.md', text: sevenNumbered }, { path: 'user_stories/long.md', text: longStory }]).ok, true);
  assert.equal(lintStories([{ path: 'user_stories/seven.md', text: sevenNumbered }], { criteriaHygiene: true }).ok, false);
});

test('3453 pdd lint --local emits advisory repo-hygiene warnings with exit code 0, honors Story scope and preserves port overrides', async t => {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-hygiene-3453-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));

  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  const state = join(scratch, 'state');
  for (const dir of [
    home,
    state,
    join(repo, 'prompts'),
    join(repo, 'src'),
    join(repo, 'user_stories'),
    join(repo, 'tests'),
    join(repo, 'test'),
  ]) {
    mkdirSync(dir, { recursive: true });
  }

  writeFileSync(join(repo, 'prompts/clean.prompt.md'), '# Clean order\n\nOwn `src/clean.mjs`. Compute order total in cents.\n\n## Dependencies\n\nNone.\n');
  writeFileSync(join(repo, 'src/clean.mjs'), '// Generated from prompts/clean.prompt.md\nexport const clean = () => 100;\n');
  writeFileSync(
    join(repo, 'user_stories/clean-order.md'),
    '# Clean order\n\nAs a customer, I want my order total in cents, so that I know the price.\n\n## Acceptance criteria\n\n1. Ordering 1 item returns 100 cents.\n',
  );
  writeFileSync(
    join(repo, 'tests/clean-order.json'),
    JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/clean-order.md',
      criteria: [{ id: 'AC1', text: 'Ordering 1 item returns 100 cents.' }],
      initial_world: {},
      steps: [{
        step_id: 's1',
        entry_path: 'prompts/clean.prompt.md',
        operation: 'clean',
        input: {},
        checks: [{ criterion_id: 'AC1', target: 'result', path: '', op: 'equals', value: 100 }],
      }],
    }, null, 2) + '\n',
  );

  // Add unrelated anti-patterns across prompt, Story, and code test files.
  writeFileSync(
    join(repo, 'prompts/bloated.prompt.md'),
    [
      '# Bloated module',
      '',
      'Own `src/bloated.mjs`.',
      '',
      '```js',
      'export function bloated(items) {',
      '  return items.map(x => x + 1);',
      '}',
      '```',
    ].join('\n'),
  );
  writeFileSync(join(repo, 'src/bloated.mjs'), '// Generated from prompts/bloated.prompt.md\nexport const bloated = () => [];\n');
  writeFileSync(
    join(repo, 'user_stories/bloated-story.md'),
    [
      '# Bloated story',
      '',
      'As a customer, I want everything checked at once, so that it is bundled.',
      '',
      '## Acceptance criteria',
      '',
      ...Array.from({ length: 9 }, (_, i) => `${i + 1}. Step ${i + 1} prints "OK ${i + 1}".`),
    ].join('\n'),
  );
  writeFileSync(
    join(repo, 'test/fake-bloated.test.mjs'),
    [
      "import test from 'node:test';",
      "import assert from 'node:assert/strict';",
      "import { readFileSync } from 'node:fs';",
      "test('fake check', () => {",
      "  const txt = readFileSync('prompts/bloated.prompt.md', 'utf8');",
      "  assert.ok(txt.includes('Bloated'));",
      '});',
    ].join('\n'),
  );

  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });

  const env = { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'invalid' };

  // 1. Repo-wide pdd lint --local --json exits 0 and emits all three advisory warning categories.
  const jsonOut = sink(), jsonErr = sink();
  const exitJson = await runPdd(['lint', '--local', '--json'], { cwd: repo, env, stdout: jsonOut, stderr: jsonErr });
  assert.equal(exitJson, 0, jsonErr.text);
  const parsed = JSON.parse(jsonOut.stdout ?? jsonOut.text);
  assert.equal(parsed.exit_code, 0);
  assert.deepEqual(parsed.problems, []);
  assert.ok(parsed.warnings.some(w => w.startsWith('Warning:') && w.includes('prompts/bloated.prompt.md:6') && w.includes('[prompt-imperative-code]')));
  assert.ok(parsed.warnings.some(w => w.startsWith('Warning:') && w.includes('user_stories/bloated-story.md:13') && w.includes('[story-bloated-criteria]')));
  assert.ok(parsed.warnings.some(w => w.startsWith('Warning:') && w.includes('test/fake-bloated.test.mjs:5') && w.includes('[fake-test-prompt-read]')));

  // 2. Plain-text pdd lint --local also exits 0 and prints Warning: lines.
  const txtOut = sink(), txtErr = sink();
  const exitTxt = await runPdd(['lint', '--local'], { cwd: repo, env, stdout: txtOut, stderr: txtErr });
  assert.equal(exitTxt, 0, txtErr.text);
  assert.match(txtOut.text, /Warning:.*prompts\/bloated\.prompt\.md:6/);
  assert.match(txtOut.text, /Warning:.*user_stories\/bloated-story\.md:13/);
  assert.match(txtOut.text, /Warning:.*test\/fake-bloated\.test\.mjs:5/);

  // 3. Story-scoped pdd lint --local clean-order omits unrelated prompts, Stories and fake tests.
  const scopedOut = sink(), scopedErr = sink();
  const exitScoped = await runPdd(['lint', '--local', 'clean-order', '--json'], { cwd: repo, env, stdout: scopedOut, stderr: scopedErr });
  assert.equal(exitScoped, 0, scopedErr.text);
  const scopedParsed = JSON.parse(scopedOut.text);
  assert.equal(scopedParsed.exit_code, 0);
  assert.ok(!scopedParsed.warnings.some(w => w.includes('bloated')));

  // 4. Direct runtimePreflightSlice().lintLocalHygiene includes lintRepoAntiPatterns warnings.
  const { lintLocalHygiene } = runtimePreflightSlice();
  const directWarnings = lintLocalHygiene({ root: repo });
  assert.ok(directWarnings.some(w => w.includes('prompts/bloated.prompt.md:6')));
  assert.ok(directWarnings.some(w => w.includes('user_stories/bloated-story.md:13')));
  assert.ok(directWarnings.some(w => w.includes('test/fake-bloated.test.mjs:5')));
  assert.ok(lintRepoAntiPatterns({ root: repo }).length >= 3);

  // 5. Explicit ports.lintSvgLayouts override on runCheck still wins (SEAM9 parity).
  const overridePorts = portsFor(env, {
    gh: () => assert.fail('No auth in --local'),
    fetch: () => assert.fail('No network in --local'),
    lintSvgLayouts: () => ['Warning: custom caller override warning'],
  }).ports;
  const overrideCode = await runCheck({ cwd: repo, options: { '--lint': true, '--local': true, '--json': true } }, overridePorts);
  assert.equal(overrideCode, 0, overridePorts.stderr.text);
  const overrideParsed = JSON.parse(overridePorts.stdout.text);
  assert.ok(overrideParsed.warnings.includes('Warning: custom caller override warning'));
  assert.ok(!overrideParsed.warnings.some(w => w.includes('test/fake-bloated.test.mjs')));
});
