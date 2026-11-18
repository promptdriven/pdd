import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { isAbsolute, join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { buildCodexLintPrompt, runCodexLint } from '../src/codex-lint.mjs';
import {
  isInspectableTestCodePath,
  lintFakeTests,
  lintPromptCodeBlocks,
  lintPromptSize,
  lintPromptStructure,
  lintPublicInterfaceTests,
  lintRepoAntiPatterns,
  lintRepoProject,
  loadProjectLintConfig,
  stripPromptMetadata,
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

test('3499 lintPromptSize enforces prompt lines strictly smaller than owned generated code lines while stripping metadata', () => {
  const promptWithMetadata = [
    '---',
    'kind: native-only',
    'reason: Local helper.',
    '---',
    '# Price calculator',
    '',
    'Own `src/price.mjs`. Return total price in integer cents.',
    '',
    '## Dependencies',
    'None.',
    '',
    '<details><summary>Runtime interface</summary>',
    '',
    '```json',
    ...Array.from({ length: 45 }, (_, i) => `  "line_${i}": ${i},`),
    '```',
    '</details>',
  ].join('\n');

  const stripped = stripPromptMetadata(promptWithMetadata).trim();
  assert.ok(stripped.startsWith('# Price calculator'));
  assert.ok(!stripped.includes('Runtime interface'));
  assert.ok(!stripped.includes('native-only'));

  // 6 authored prose lines < 8 generated code lines -> passes cleanly even with 45 lines of Runtime interface metadata.
  const eightLineCode = Array.from({ length: 8 }, (_, i) => `export const v${i} = ${i};`).join('\n');
  assert.deepEqual(
    lintPromptSize(promptWithMetadata, [{ path: 'src/price.mjs', text: eightLineCode }], { path: 'prompts/price.prompt.md' }),
    [],
  );

  // Strict inequality: prompt lines === code lines (6 === 6) warns with [prompt-larger-than-code].
  const sixLineCode = Array.from({ length: 6 }, (_, i) => `export const v${i} = ${i};`).join('\n');
  const equalWarnings = lintPromptSize(
    promptWithMetadata,
    [{ path: 'src/price.mjs', text: sixLineCode }],
    { path: 'prompts/price.prompt.md' },
  );
  assert.equal(equalWarnings.length, 1);
  assert.match(equalWarnings[0], /prompts\/price\.prompt\.md:1 \[prompt-larger-than-code\].*spans 6 lines.*src\/price\.mjs.*spans 6 lines/);

  // Prompt lines > code lines (6 > 3) warns; summing across multiple owned code files (3 + 5 = 8 > 6) passes.
  const threeLineCode = 'export function price(qty) {\n  return qty * 250;\n}';
  const fiveLineCode = Array.from({ length: 5 }, (_, i) => `export const extra${i} = ${i};`).join('\n');
  assert.equal(
    lintPromptSize(promptWithMetadata, [{ path: 'src/price.mjs', text: threeLineCode }], { path: 'prompts/price.prompt.md' }).length,
    1,
  );
  assert.deepEqual(
    lintPromptSize(
      promptWithMetadata,
      [
        { path: 'src/price.mjs', text: threeLineCode },
        { path: 'src/price-format.mjs', text: fiveLineCode },
      ],
      { path: 'prompts/price.prompt.md' },
    ),
    [],
  );

  // Prompts with no generated code yet are skipped without warnings.
  assert.deepEqual(lintPromptSize(promptWithMetadata, [], { path: 'prompts/uncompiled.prompt.md' }), []);
});

test('3499 lintPublicInterfaceTests warns on private module imports, private symbols, private member access, rewire hooks and vm source eval', () => {
  const reachingIntoInternals = [
    "import test from 'node:test';",
    "import { readFileSync } from 'node:fs';",
    "import { runInNewContext } from 'node:vm';",
    "import { quote } from '../src/internal/pricing.mjs';",
    "import secret from '../src/_secret.mjs';",
    "import { calculateTax, _roundHalfEven } from '../src/tax.mjs';",
    "import * as ledger from '../src/ledger.mjs';",
    "import { OrderService, createStore } from '../src/orders.mjs';",
    "const { _buildCache } = require('../src/cache.cjs');",
    '',
    "test('reaches into internals', async () => {",
    "  const priv = await import('../src/private/engine.mjs');",
    '  ledger._resetState();',
    '  const svc = new OrderService();',
    '  svc._pendingQueue.push(1);',
    '  const store = createStore();',
    '  store?._flush();',
    "  const mod = rewire('../src/tax.mjs');",
    "  mod.__get__('RATE');",
    "  const raw = readFileSync('src/tax.mjs', 'utf8');",
    '  runInNewContext(raw, {});',
    '  void quote; void secret; void calculateTax; void _roundHalfEven; void _buildCache; void priv;',
    '});',
  ].join('\n');

  const warnings = lintPublicInterfaceTests(reachingIntoInternals, { path: 'test/orders.test.mjs' });
  assert.ok(warnings.every(w => w.startsWith('Warning: public-interface test:')));
  assert.ok(warnings.some(w => w.includes('test/orders.test.mjs:4') && w.includes('[test-private-import]') && w.includes('../src/internal/pricing.mjs')));
  assert.ok(warnings.some(w => w.includes('test/orders.test.mjs:5') && w.includes('[test-private-import]') && w.includes('../src/_secret.mjs')));
  assert.ok(warnings.some(w => w.includes('test/orders.test.mjs:6') && w.includes('[test-private-import]') && w.includes('_roundHalfEven')));
  assert.ok(warnings.some(w => w.includes('test/orders.test.mjs:9') && w.includes('[test-private-import]') && w.includes('_buildCache')));
  assert.ok(warnings.some(w => w.includes('test/orders.test.mjs:12') && w.includes('[test-private-import]') && w.includes('../src/private/engine.mjs')));
  assert.ok(warnings.some(w => w.includes('test/orders.test.mjs:13') && w.includes('[test-private-access]') && w.includes('ledger._resetState')));
  assert.ok(warnings.some(w => w.includes('test/orders.test.mjs:15') && w.includes('[test-private-access]') && w.includes('svc._pendingQueue')));
  assert.ok(warnings.some(w => w.includes('test/orders.test.mjs:17') && w.includes('[test-private-access]') && w.includes('store._flush')));
  assert.ok(warnings.some(w => w.includes('test/orders.test.mjs:18') && w.includes('[test-private-access]') && w.includes('rewire')));
  assert.ok(warnings.some(w => w.includes('test/orders.test.mjs:19') && w.includes('[test-private-access]') && w.includes('__get__')));
  assert.ok(warnings.some(w => w.includes('test/orders.test.mjs:21') && w.includes('[test-private-access]') && w.includes('src/tax.mjs')));

  // Python test suite importing private module paths, private symbols, and accessing private members.
  const pyBad = [
    'from billing._internal import quote_cents',
    'from billing.tax import calculate_tax, _round_cents, __version__',
    'import billing._secret as sec',
    '',
    'def test_tax():',
    '    assert calculate_tax(100) == 108',
    '    assert sec._raw_key() is not None',
  ].join('\n');
  const pyWarnings = lintPublicInterfaceTests(pyBad, { path: 'tests/test_tax.py' });
  assert.ok(pyWarnings.some(w => w.includes('tests/test_tax.py:1') && w.includes('[test-private-import]') && w.includes('billing._internal')));
  assert.ok(pyWarnings.some(w => w.includes('tests/test_tax.py:2') && w.includes('[test-private-import]') && w.includes('_round_cents')));
  assert.ok(!pyWarnings.some(w => w.includes('__version__')));
  assert.ok(pyWarnings.some(w => w.includes('tests/test_tax.py:3') && w.includes('[test-private-import]') && w.includes('billing._secret')));
  assert.ok(pyWarnings.some(w => w.includes('tests/test_tax.py:7') && w.includes('[test-private-access]') && w.includes('sec._raw_key')));

  // Clean public interface tests, test helpers, local mock objects, comments and strings emit 0 warnings.
  const cleanPublicSuite = [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { placeOrder } from '../src/orders.mjs';",
    "import { _seedFakeClock } from './helpers/fake-clock.mjs';",
    '',
    "// Comment mentioning ../src/internal/pricing.mjs and orders._secret should not warn.",
    "test('uses only public interface', () => {",
    '  const localMock = { _calls: 0, _lastOrder: null };',
    '  localMock._calls += 1;',
    "  const note = 'svc._pendingQueue and mod.__get__(\"x\")';",
    '  _seedFakeClock();',
    "  assert.equal(placeOrder({ sku: 'latte' }).ok, true);",
    '  assert.equal(localMock._calls, 1);',
    '  assert.ok(note.length > 0);',
    '});',
  ].join('\n');
  assert.deepEqual(lintPublicInterfaceTests(cleanPublicSuite, { path: 'test/orders-public.test.mjs' }), []);
  assert.deepEqual(lintPublicInterfaceTests(reachingIntoInternals, { path: 'test/runtime-seam.test.mjs' }), []);
  assert.deepEqual(lintPublicInterfaceTests(reachingIntoInternals, { path: 'test/helpers/internal-harness.mjs' }), []);
});

test('3499 lintPromptStructure checks top-level title, Dependencies section and diagrams or tables on multi-branch or state-machine prompts', () => {
  // Missing # <Title> and missing ## Dependencies when owning production code.
  const missingTitleAndDeps = 'Own `src/ship.mjs`. Compute shipping rates in cents.\n';
  const structWarnings = lintPromptStructure(missingTitleAndDeps, {
    path: 'prompts/ship.prompt.md',
    hasOwnedCode: true,
  });
  assert.ok(structWarnings.some(w => w.includes('prompts/ship.prompt.md:1') && w.includes('[prompt-missing-title]')));
  assert.ok(structWarnings.some(w => w.includes('prompts/ship.prompt.md:1') && w.includes('[prompt-missing-dependencies]')));

  // Short standalone draft leaf prompt with no owned code, no Runtime interface and no peer links only checks title.
  assert.deepEqual(
    lintPromptStructure('# Greeting\n\nReturn a plain-English welcome greeting for the signed-in visitor.\n', {
      path: 'prompts/greeting.prompt.md',
      hasOwnedCode: false,
    }),
    [],
  );

  // Dense multi-branch prose (>= 18 prose lines & >= 5 conditional lines) without diagram or table warns [prompt-missing-diagram].
  const denseBranchBody = [
    '# Checkout state routing',
    '',
    'Own `src/checkout-router.mjs`. Route checkout requests to the next step.',
    '',
    '## Rules',
    'If the cart is empty, reject with code EMPTY_CART.',
    'When the customer has an expired card, route to payment_retry.',
    'If the shipping address lacks a postal code, reject with INVALID_ADDRESS.',
    'Unless inventory holds succeed for all items, release partial holds.',
    'Otherwise when fraud score exceeds 80, hold the order in manual_review.',
    ...Array.from({ length: 12 }, (_, idx) => `Requirement ${idx + 1}: record audit event step_${idx + 1} with UTC timestamp.`),
    '',
    '## Dependencies',
    'None.',
  ].join('\n');

  const branchWarnings = lintPromptStructure(denseBranchBody, {
    path: 'prompts/checkout-router.prompt.md',
    hasOwnedCode: true,
  });
  assert.equal(branchWarnings.length, 1);
  assert.match(branchWarnings[0], /prompts\/checkout-router\.prompt\.md:6 \[prompt-missing-diagram\]/);

  // Adding a mermaid flowchart satisfies the diagram requirement.
  const withMermaid = `${denseBranchBody}\n\`\`\`mermaid\nflowchart TD\n  Start --> CheckCart\n  CheckCart --> HoldInventory\n\`\`\`\n`;
  assert.deepEqual(
    lintPromptStructure(withMermaid, { path: 'prompts/checkout-router.prompt.md', hasOwnedCode: true }),
    [],
  );

  // State-transition prose (>= 3 transition lines) warns without a diagram/table, and passes with a Markdown table.
  const stateMachinePrompt = [
    '# Subscription lifecycle',
    '',
    'Own `src/subscription.mjs`. Track subscription state changes.',
    '- Trial transitions from Trial to Active on first captured invoice.',
    '- Active transitions to PastDue after a failed renewal charge.',
    '- PastDue moves from PastDue to Canceled after three failed retries.',
    '',
    '## Dependencies',
    'None.',
  ].join('\n');
  const stateWarnings = lintPromptStructure(stateMachinePrompt, {
    path: 'prompts/subscription.prompt.md',
    hasOwnedCode: true,
  });
  assert.equal(stateWarnings.length, 1);
  assert.match(stateWarnings[0], /\[prompt-missing-diagram\]/);

  const withDecisionTable = [
    stateMachinePrompt,
    '',
    '| From | Event | To |',
    '| --- | --- | --- |',
    '| Trial | invoice_paid | Active |',
    '| Active | charge_failed | PastDue |',
    '| PastDue | retries_exhausted | Canceled |',
  ].join('\n');
  assert.deepEqual(
    lintPromptStructure(withDecisionTable, { path: 'prompts/subscription.prompt.md', hasOwnedCode: true }),
    [],
  );
});

test('3499 pdd.json lint config supports disabling rules, promoting rules to error, custom rules across targets and invalid config reporting', async t => {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-lint-config-3499-'));
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

  // Prompt (8 lines, missing ## Dependencies) >= owned code (3 lines) -> triggers prompt-larger-than-code & prompt-missing-dependencies.
  writeFileSync(
    join(repo, 'prompts/calc.prompt.md'),
    [
      '# Tax calculator',
      '',
      'Own `src/calc.mjs`.',
      'Compute sales tax in integer cents.',
      'Round half-up to the nearest cent.',
      'Reject negative subtotals.',
      'TODO: add multi-jurisdiction table.',
      'Return `{ taxCents }`.',
    ].join('\n') + '\n',
  );
  writeFileSync(
    join(repo, 'src/calc.mjs'),
    '// Generated from prompts/calc.prompt.md\nexport const calcTax = cents => Math.round(cents * 0.08);\n',
  );
  writeFileSync(
    join(repo, 'user_stories/tax-calc.md'),
    '# Tax calculation\n\nAs a shopper, I want tax shown in cents, so that I see the exact total.\n\n## Acceptance criteria\n\n1. A 100-cent subtotal yields 8 cents tax.\n',
  );
  writeFileSync(
    join(repo, 'tests/tax-calc.json'),
    JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/tax-calc.md',
      criteria: [{ id: 'AC1', text: 'A 100-cent subtotal yields 8 cents tax.' }],
      initial_world: {},
      steps: [{
        step_id: 's1',
        entry_path: 'prompts/calc.prompt.md',
        operation: 'calcTax',
        input: { cents: 100 },
        checks: [{ criterion_id: 'AC1', target: 'result', path: '', op: 'equals', value: 8 }],
      }],
    }, null, 2) + '\n',
  );
  writeFileSync(
    join(repo, 'test/calc.test.mjs'),
    [
      "import test from 'node:test';",
      "import { calcTax, _internalRound } from '../src/calc.mjs';",
      "test('tax', () => { void calcTax; void _internalRound; });",
    ].join('\n') + '\n',
  );

  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });

  const env = { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'invalid' };

  // 1. Default without pdd.json: built-in rules emit advisory warnings and pdd lint --local exits 0.
  const baseProject = lintRepoProject({ root: repo });
  assert.equal(baseProject.ok, true);
  assert.equal(baseProject.configured, false);
  assert.ok(baseProject.warnings.some(w => w.includes('[prompt-larger-than-code]')));
  assert.ok(baseProject.warnings.some(w => w.includes('[prompt-missing-dependencies]')));
  assert.ok(baseProject.warnings.some(w => w.includes('[test-private-import]')));

  // 2. Configure pdd.json with disabled rules, promoted "error" built-in rule, and custom_rules across prompt/story/test/code.
  writeFileSync(
    join(repo, 'pdd.json'),
    JSON.stringify({
      lint: {
        disable: ['prompt-missing-dependencies'],
        rules: {
          'test-private-import': 'off',
          'prompt-larger-than-code': 'error',
        },
        custom_rules: [
          {
            id: 'no-todo-in-prompts',
            target: 'prompt',
            severity: 'error',
            forbid_pattern: '\\bTODO:',
            message: 'Resolve TODO markers in prompts before checking in.',
          },
          {
            id: 'story-rules-heading',
            target: 'story',
            severity: 'warn',
            require_heading: '## Rules to check',
            message: 'Include a "## Rules to check" section on billing Stories.',
          },
          {
            id: 'test-requires-assert',
            target: 'test',
            include: 'test/*.test.mjs',
            severity: 'warn',
            require_pattern: 'node:assert',
            message: 'Tests should import node:assert.',
          },
          {
            id: 'code-max-lines',
            target: 'code',
            include: 'src/**/*.mjs',
            severity: 'warn',
            max_lines: 1,
            message: 'Keep sample generated module to 1 line',
          },
        ],
      },
    }, null, 2) + '\n',
  );
  execFileSync('git', ['add', 'pdd.json'], { cwd: repo });

  const configuredProject = lintRepoProject({ root: repo });
  assert.equal(configuredProject.ok, false);
  assert.equal(configuredProject.configured, true);
  assert.ok(!configuredProject.warnings.some(w => w.includes('[prompt-missing-dependencies]')));
  assert.ok(!configuredProject.warnings.some(w => w.includes('[test-private-import]')));
  assert.ok(configuredProject.warnings.some(w => w.includes('[story-rules-heading]')));
  assert.ok(configuredProject.warnings.some(w => w.includes('[test-requires-assert]')));
  assert.ok(configuredProject.warnings.some(w => w.includes('[code-max-lines]')));
  assert.ok(configuredProject.errors.some(e => e.startsWith('Error:') && e.includes('[prompt-larger-than-code]')));
  assert.ok(configuredProject.errors.some(e => e.startsWith('Error:') && e.includes('prompts/calc.prompt.md:7 [no-todo-in-prompts]')));

  // CLI pdd lint --local --json surfaces "error"-severity findings in problems and exits 1.
  const errJsonOut = sink(), errJsonErr = sink();
  const exitErrJson = await runPdd(['lint', '--local', '--json'], { cwd: repo, env, stdout: errJsonOut, stderr: errJsonErr });
  assert.equal(exitErrJson, 1, errJsonErr.text);
  const parsedErr = JSON.parse(errJsonOut.text);
  assert.equal(parsedErr.ok, false);
  assert.equal(parsedErr.exit_code, 1);
  assert.ok(parsedErr.problems.some(p => p.includes('[prompt-larger-than-code]')));
  assert.ok(parsedErr.problems.some(p => p.includes('[no-todo-in-prompts]')));
  assert.ok(parsedErr.warnings.some(w => w.includes('[story-rules-heading]')));

  // CLI plain-text pdd lint --local prints Error: lines to stderr and exits 1, while inspection mode (test --files) stays 0.
  const errTxtOut = sink(), errTxtErr = sink();
  const exitErrTxt = await runPdd(['lint', '--local'], { cwd: repo, env, stdout: errTxtOut, stderr: errTxtErr });
  assert.equal(exitErrTxt, 1);
  assert.match(errTxtErr.text, /Error:.*\[prompt-larger-than-code\]/);
  assert.match(errTxtErr.text, /Error:.*\[no-todo-in-prompts\]/);

  const filesOut = sink(), filesErr = sink();
  const exitFiles = await runPdd(['test', '--files'], { cwd: repo, env, stdout: filesOut, stderr: filesErr });
  assert.equal(exitFiles, 0, filesErr.text);

  // 3. Invalid custom rule regex reports [lint-config-invalid] without throwing.
  const invalidCfg = loadProjectLintConfig({
    lint: {
      custom_rules: [{ id: 'broken-regex', forbid_pattern: '[unclosed' }],
    },
  });
  assert.equal(invalidCfg.configured, true);
  assert.equal(invalidCfg.configErrors.length, 1);
  assert.equal(invalidCfg.configErrors[0].code, 'lint-config-invalid');
});

test('3499 pdd lint --codex runs read-only Codex Prompt and Story readability/quality lint with clear pass/fail output, JSON mode and Story scoping', async t => {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-codex-lint-3499-'));
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
  ]) {
    mkdirSync(dir, { recursive: true });
  }

  writeFileSync(
    join(repo, 'prompts/checkout.prompt.md'),
    [
      '# Checkout total',
      '',
      'Own `src/checkout.mjs`. Return integer cent totals for valid cart items.',
      '',
      '## Dependencies',
      '',
      'None.',
      '',
      '<details><summary>Runtime interface</summary>',
      '```json',
      '{"status":"draft","secret_marker":"SHOULD_BE_STRIPPED"}',
      '```',
      '</details>',
    ].join('\n') + '\n',
  );
  writeFileSync(
    join(repo, 'src/checkout.mjs'),
    Array.from({ length: 12 }, (_, i) => `// line ${i}\nexport const checkout${i} = () => ${i};`).join('\n') + '\n',
  );
  writeFileSync(
    join(repo, 'user_stories/checkout.md'),
    '# Checkout total\n\nAs a shopper, I want an itemised cent total, so that I know the final charge.\n\n## Acceptance criteria\n\n1. Two 250-cent drinks return 500 cents.\n',
  );
  writeFileSync(
    join(repo, 'tests/checkout.json'),
    JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/checkout.md',
      criteria: [{ id: 'AC1', text: 'Two 250-cent drinks return 500 cents.' }],
      initial_world: {},
      steps: [{
        step_id: 's1',
        entry_path: 'prompts/checkout.prompt.md',
        operation: 'checkout0',
        input: {},
        checks: [{ criterion_id: 'AC1', target: 'result', path: '', op: 'equals', value: 0 }],
      }],
    }, null, 2) + '\n',
  );
  writeFileSync(
    join(repo, 'prompts/vague.prompt.md'),
    '# Vague dump\n\nlet x = 1; do stuff cleanly and handle errors fast.\n\n## Dependencies\n\nNone.\n',
  );
  writeFileSync(
    join(repo, 'src/vague.mjs'),
    Array.from({ length: 10 }, (_, i) => `export const vague${i} = ${i};`).join('\n') + '\n',
  );
  writeFileSync(join(repo, '.env'), 'OPENAI_API_KEY=never-send-me\n');

  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });

  const env = {
    HOME: home,
    PDD_STATE_DIR: state,
    GH_TOKEN: 'ghs_should_not_leak',
    GITHUB_TOKEN: 'ghp_should_not_leak',
  };

  // Verify buildCodexLintPrompt numbers lines and labels prompt vs story.
  const builtPrompt = buildCodexLintPrompt([
    { path: 'prompts/checkout.prompt.md', kind: 'prompt', text: '# Checkout total\n\nCompute total.' },
    { path: 'user_stories/checkout.md', kind: 'story', text: '# Checkout total' },
  ]);
  assert.match(builtPrompt, /=== FILE: prompts\/checkout\.prompt\.md \(kind: prompt\) ===/);
  assert.match(builtPrompt, /1: # Checkout total/);
  assert.match(builtPrompt, /=== FILE: user_stories\/checkout\.md \(kind: story\) ===/);

  // 1. Story-scoped PASS run: verifies read-only sandbox flags, token stripping, secret & Runtime-interface exclusion, and PASS output.
  const calls = [];
  const passRunner = async (command, args, opts) => {
    calls.push({ command, args, ...opts });
    const outIdx = args.indexOf('--output-last-message');
    const outFile = args[outIdx + 1];
    writeFileSync(outFile, JSON.stringify({
      files: [
        { path: 'prompts/checkout.prompt.md', verdict: 'pass', summary: 'Concise domain contract with clear integer-cent behavior.', issues: [] },
        { path: 'user_stories/checkout.md', verdict: 'pass', summary: 'Clear shopper role and concrete acceptance criterion.', issues: [] },
      ],
    }));
    return { code: 0, stdout: '', stderr: '' };
  };

  const passOut = sink(), passErr = sink();
  const passCode = await runPdd(['lint', '--codex', 'checkout'], {
    cwd: repo,
    env,
    stdout: passOut,
    stderr: passErr,
    codexLintPorts: { runAgentProcess: passRunner },
  });
  assert.equal(passCode, 0, passErr.text);
  assert.equal(calls.length, 1);
  assert.equal(calls[0].command, 'codex');
  assert.ok(calls[0].args.includes('exec'));
  assert.equal(calls[0].args[calls[0].args.indexOf('--sandbox') + 1], 'read-only');
  assert.equal(calls[0].env.GH_TOKEN, undefined);
  assert.equal(calls[0].env.GITHUB_TOKEN, undefined);
  assert.ok(!calls[0].input.includes('SHOULD_BE_STRIPPED'));
  assert.ok(!calls[0].input.includes('never-send-me'));
  assert.ok(!calls[0].input.includes('prompts/vague.prompt.md'));
  assert.match(passOut.text, /PASS prompts\/checkout\.prompt\.md — Concise domain contract/);
  assert.match(passOut.text, /PASS user_stories\/checkout\.md — Clear shopper role/);
  assert.match(passOut.text, /Lint \(Codex\): PASS \(2\/2 files passed\)/);

  // 2. Repo-wide FAIL run (plain text + --json): reports actionable line-numbered readability issues and exits 1.
  const failRunner = async (_command, args) => {
    const outFile = args[args.indexOf('--output-last-message') + 1];
    writeFileSync(outFile, JSON.stringify({
      files: [
        { path: 'prompts/checkout.prompt.md', verdict: 'pass', summary: 'Clear contract.', issues: [] },
        {
          path: 'prompts/vague.prompt.md',
          verdict: 'fail',
          summary: 'Uses imperative variable assignment and vague non-observable prose.',
          issues: [{ line: 3, rule: 'prompt-readability', message: 'Replace "let x = 1; do stuff cleanly" with observable inputs, outputs, and error rules.' }],
        },
        { path: 'user_stories/checkout.md', verdict: 'pass', summary: 'Testable acceptance criterion.', issues: [] },
      ],
    }));
    return { code: 0, stdout: '', stderr: '' };
  };

  const failOut = sink(), failErr = sink();
  const failCode = await runPdd(['lint', '--codex'], {
    cwd: repo,
    env,
    stdout: failOut,
    stderr: failErr,
    codexLintPorts: { runAgentProcess: failRunner },
  });
  assert.equal(failCode, 1);
  assert.match(failOut.text, /FAIL prompts\/vague\.prompt\.md — Uses imperative variable assignment/);
  assert.match(failOut.text, /prompts\/vague\.prompt\.md:3 \[prompt-readability\] Replace "let x = 1/);
  assert.match(failOut.text, /Lint \(Codex\): FAIL \(2\/3 files passed, 1 failed\)/);

  const jsonOut = sink(), jsonErr = sink();
  const jsonCode = await runPdd(['lint', '--codex', '--json'], {
    cwd: repo,
    env,
    stdout: jsonOut,
    stderr: jsonErr,
    codexLintPorts: { runAgentProcess: failRunner },
  });
  assert.equal(jsonCode, 1);
  const parsedCodexJson = JSON.parse(jsonOut.text);
  assert.equal(parsedCodexJson.schema_version, 'pdd.codex-lint.v1');
  assert.equal(parsedCodexJson.ok, false);
  assert.equal(parsedCodexJson.exit_code, 1);
  assert.equal(parsedCodexJson.passed, 2);
  assert.equal(parsedCodexJson.failed, 1);
  assert.equal(parsedCodexJson.files.find(f => f.path === 'prompts/vague.prompt.md')?.status, 'fail');

  // 3. Unknown target and invalid option combinations exit 2 with clear guidance.
  const unknownOut = sink(), unknownErr = sink();
  assert.equal(
    await runPdd(['lint', '--codex', 'missing-story'], {
      cwd: repo,
      env,
      stdout: unknownOut,
      stderr: unknownErr,
      codexLintPorts: { runAgentProcess: passRunner },
    }),
    2,
  );
  assert.match(unknownErr.text, /Unknown Story or prompt path: missing-story/);

  const badTestFlagErr = sink();
  assert.equal(await runPdd(['test', '--codex'], { cwd: repo, env, stdout: sink(), stderr: badTestFlagErr }), 2);
  assert.match(badTestFlagErr.text, /Use pdd lint --codex/);

  const badComboErr = sink();
  assert.equal(await runPdd(['lint', '--codex', '--local'], { cwd: repo, env, stdout: sink(), stderr: badComboErr }), 2);
  assert.match(badComboErr.text, /accepts only Story or prompt paths, --json, and --timeout MIN/);
});

test('3499 ReDoS regex/glob guards and no-symlink pdd.json checks reject unsafe custom_rules and symlinked configs', async t => {
  // 1. Unsafe backreferences, nested quantifiers, overlapping repeated alternations, and unbounded lookarounds fail closed.
  const unsafePatterns = [
    '(a+)+',
    '([a-z]+)*',
    '((a+))+',
    '(?:foo|foobar)+',
    '(\\w+)\\1',
    '(?<dup>\\w+)\\k<dup>',
    '(?=.*secret)foo',
    '(?<=a+)b',
  ];
  for (const unsafe of unsafePatterns) {
    const cfg = loadProjectLintConfig({
      lint: {
        custom_rules: [{ id: 'unsafe-re', forbid_pattern: unsafe }],
      },
    });
    assert.equal(cfg.customRules.length, 0, `expected unsafe regex to be rejected: ${unsafe}`);
    assert.ok(cfg.configErrors.some(e => e.code === 'lint-config-invalid'), `expected lint-config-invalid for ${unsafe}`);
  }

  // Disjoint repeated literal alternation and bounded lookbehind remain accepted, and >12 glob wildcards are rejected.
  const validAndBoundedGlob = loadProjectLintConfig({
    lint: {
      custom_rules: [
        {
          id: 'collapsed-glob-rule',
          target: 'code',
          include: '**/a/**/**/b/*.mjs',
          forbid_pattern: '(?<!safe_)(?:GET|POST)+',
        },
        {
          id: 'excessive-wildcards',
          target: 'code',
          include: 'a/*/*/*/*/*/*/*/*/*/*/*/*/*.mjs',
          forbid_pattern: 'TODO',
        },
      ],
    },
  });
  assert.equal(validAndBoundedGlob.customRules.length, 1);
  assert.equal(validAndBoundedGlob.customRules[0].id, 'collapsed-glob-rule');
  assert.ok(validAndBoundedGlob.customRules[0].includeMatchers[0].test('x/a/y/z/b/handler.mjs'));
  assert.ok(validAndBoundedGlob.customRules[0].includeMatchers[0].test('a/b/handler.mjs'));
  assert.ok(validAndBoundedGlob.configErrors.some(e => e.code === 'lint-config-invalid' && e.detail.includes('excessive-wildcards')));

  // 2. Symlinked pdd.json is ignored safely by both loadProjectLintConfig and CLI hasProjectLintConfig.
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-symlink-cfg-3499-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));

  const outsideConfig = join(scratch, 'outside-pdd.json');
  writeFileSync(outsideConfig, JSON.stringify({
    lint: {
      custom_rules: [{ id: 'outside-error', target: 'prompt', severity: 'error', forbid_pattern: 'Order' }],
    },
  }));

  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  const state = join(scratch, 'state');
  for (const dir of [home, state, join(repo, 'prompts'), join(repo, 'src')]) mkdirSync(dir, { recursive: true });
  writeFileSync(join(repo, 'prompts/order.prompt.md'), '# Order\n\nOwn `src/order.mjs`.\n\n## Dependencies\n\nNone.\n');
  writeFileSync(join(repo, 'src/order.mjs'), Array.from({ length: 8 }, (_, i) => `export const o${i} = ${i};`).join('\n') + '\n');
  symlinkSync(outsideConfig, join(repo, 'pdd.json'));

  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', 'prompts/order.prompt.md', 'src/order.mjs'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });

  assert.equal(loadProjectLintConfig(repo).configured, false);
  const out = sink(), err = sink();
  const code = await runPdd(['lint', '--local'], {
    cwd: repo,
    env: { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'invalid' },
    stdout: out,
    stderr: err,
  });
  assert.equal(code, 0, err.text);
  assert.ok(!err.text.includes('outside-error'));
});

test('3499 runCodexLint enforces --ignore-rules, -- end-of-options, global batch deadline, full credential/session scrubbing and output redaction', async t => {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-codex-hardening-3499-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));

  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  const state = join(scratch, 'state');
  for (const dir of [home, state, join(repo, 'prompts'), join(repo, 'src')]) mkdirSync(dir, { recursive: true });

  // Create 7 prompts (> 6 files per batch) with an embedded secret value to test redaction + 2-batch global deadline.
  for (let idx = 0; idx < 7; idx++) {
    writeFileSync(
      join(repo, `prompts/mod-${idx}.prompt.md`),
      `# Module ${idx}\n\nOwn \`src/mod-${idx}.mjs\`. Reference value: sec_live_verysecretvalue999.\n\n## Dependencies\n\nNone.\n`,
    );
    writeFileSync(
      join(repo, `src/mod-${idx}.mjs`),
      Array.from({ length: 8 }, (_, line) => `export const m${idx}_${line} = ${line};`).join('\n') + '\n',
    );
  }
  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });

  const sensitiveEnv = {
    HOME: home,
    PDD_STATE_DIR: state,
    PATH: process.env.PATH,
    GH_TOKEN: 'ghs_tok1234567890abcdef',
    GITHUB_TOKEN: 'ghp_tok1234567890abcdef',
    GITHUB_PAT: 'github_pat_1234567890abcdef',
    GH_PAT: 'ghp_pat1234567890abcdef',
    PDD_CLOUD_TOKEN: 'pddg_cloudtoken1234567890',
    NPM_TOKEN: 'npm_secret_token_12345',
    AWS_SECRET_ACCESS_KEY: 'aws_secret_access_key_val',
    AWS_SESSION_TOKEN: 'aws_session_token_val',
    OPENAI_API_KEY: 'sk-proj-1234567890abcdef',
    ANTHROPIC_API_KEY: 'sk-ant-1234567890abcdef',
    CODEX_THREAD_ID: 'thread-parent-1',
    CODEX_SANDBOX_NETWORK_DISABLED: '1',
    CLAUDECODE: '1',
    HERDR_SESSION: 'pdd',
    PDD_AGENT_SESSION: 'sess-1',
    PDD_AUTOPILOT_CONTEXT: 'auto-1',
    CUSTOM_SERVICE_SECRET: 'sec_live_verysecretvalue999',
  };

  // 1. Single-file run checks clamped timeoutMinutes, --ignore-rules, resolved outFile, trailing ['--', '-'], env scrubbing, and input/output redaction.
  const observedCalls = [];
  const leakingFailRunner = async (command, args, opts) => {
    observedCalls.push({ command, args, ...opts });
    const outFile = args[args.indexOf('--output-last-message') + 1];
    writeFileSync(outFile, JSON.stringify({
      files: [{
        path: 'prompts/mod-0.prompt.md',
        verdict: 'fail',
        summary: 'Leaked secret sec_live_verysecretvalue999 and ghp_tok1234567890abcdef in summary.',
        issues: [{ line: 3, rule: 'prompt-readability', message: 'Remove sec_live_verysecretvalue999 from prose.' }],
      }],
    }));
    return { code: 0, stdout: '', stderr: '' };
  };

  const jsonOut = sink(), jsonErr = sink();
  const singleExit = await runCodexLint(
    { cwd: repo, words: ['prompts/mod-0.prompt.md'], timeoutMinutes: 999, json: true, env: sensitiveEnv },
    { stdout: jsonOut, stderr: jsonErr, now: () => 1_000_000, runAgentProcess: leakingFailRunner },
  );
  assert.equal(singleExit, 1);
  assert.equal(observedCalls.length, 1);
  const call = observedCalls[0];
  assert.equal(call.timeoutMs, 120 * 60 * 1000, 'timeoutMinutes > 120 clamps to 120 minutes');
  assert.ok(call.args.includes('--ignore-rules'));
  const outFileArg = call.args[call.args.indexOf('--output-last-message') + 1];
  assert.equal(isAbsolute(outFileArg), true);
  assert.deepEqual(call.args.slice(-2), ['--', '-']);

  for (const strippedKey of [
    'GH_TOKEN', 'GITHUB_TOKEN', 'GITHUB_PAT', 'GH_PAT', 'PDD_CLOUD_TOKEN', 'NPM_TOKEN',
    'AWS_SECRET_ACCESS_KEY', 'AWS_SESSION_TOKEN', 'OPENAI_API_KEY', 'ANTHROPIC_API_KEY',
    'CODEX_THREAD_ID', 'CODEX_SANDBOX_NETWORK_DISABLED', 'CLAUDECODE', 'HERDR_SESSION',
    'PDD_AGENT_SESSION', 'PDD_AUTOPILOT_CONTEXT',
  ]) {
    assert.equal(call.env[strippedKey], undefined, `${strippedKey} must be scrubbed from Codex env`);
  }
  assert.ok(!call.input.includes('sec_live_verysecretvalue999'), 'known env secret must be redacted from prompt input');
  assert.ok(call.input.includes('[redacted]'));

  const parsedJson = JSON.parse(jsonOut.text);
  assert.equal(parsedJson.ok, false);
  assert.ok(!jsonOut.text.includes('sec_live_verysecretvalue999'));
  assert.ok(!jsonOut.text.includes('ghp_tok1234567890abcdef'));
  assert.match(parsedJson.files[0].summary, /\[redacted\]/);
  assert.match(parsedJson.files[0].issues[0].message, /\[redacted\]/);

  // 2. Multi-batch global deadline: 7 files (batch 1 = 6 files, batch 2 = 1 file) share one overall budget instead of multiplying.
  let fakeNow = 1_000_000;
  const batchTimeouts = [];
  const clockAdvancingRunner = async (_cmd, args, opts) => {
    batchTimeouts.push(opts.timeoutMs);
    const outFile = args[args.indexOf('--output-last-message') + 1];
    writeFileSync(outFile, JSON.stringify({
      files: Array.from({ length: 6 }, (_, idx) => ({
        path: `prompts/mod-${idx}.prompt.md`,
        verdict: 'pass',
        summary: 'Clean.',
        issues: [],
      })),
    }));
    // Advance clock past the clamped 0.1-minute (6000ms) overall deadline during batch 1.
    fakeNow += 6_500;
    return { code: 0, stdout: '', stderr: '' };
  };

  const deadlineOut = sink(), deadlineErr = sink();
  const deadlineExit = await runCodexLint(
    { cwd: repo, words: [], timeoutMinutes: 0.01, json: false, env: { HOME: home, PDD_STATE_DIR: state } },
    { stdout: deadlineOut, stderr: deadlineErr, now: () => fakeNow, runAgentProcess: clockAdvancingRunner },
  );
  assert.equal(deadlineExit, 1);
  assert.deepEqual(batchTimeouts, [6000], 'timeoutMinutes < 0.1 clamps to 6000ms and batch 2 stops once overall deadline expires');
  assert.match(deadlineErr.text, /Codex lint timed out after 6s/);
});

test('3499 + 3522 Short JSON scenarios omitting story_path with singular entry_path scope Story and Prompt rules in lint --local and lint --codex while keeping --emit-v1 and --bind-criteria clean', async t => {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-short-json-lint-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));

  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  const state = join(scratch, 'state');
  for (const dir of [home, state, join(repo, 'prompts'), join(repo, 'user_stories'), join(repo, 'tests')]) {
    mkdirSync(dir, { recursive: true });
  }
  const env = { HOME: home, PDD_STATE_DIR: state };

  writeFileSync(
    join(repo, 'prompts/calc.prompt.md'),
    '# Calculator\n\nAdd two numbers.\n\n## Dependencies\n\nNone.\n',
  );
  writeFileSync(
    join(repo, 'user_stories/calc.md'),
    '# Calculator\n\nAs a shopper, I want totals added, so that I see my bill.\n\n## Acceptance criteria\n\n1. Adding 2 and 3 returns 5.\n',
  );
  writeFileSync(
    join(repo, 'tests/calc.json'),
    JSON.stringify({
      schema_version: 'pdd.scenario.short.v1',
      entry_path: 'prompts/calc.prompt.md',
      steps: [{ op: 'add', input: { a: 2, b: 3 }, checks: [['1', 'result', '/sum', '=', 5]] }],
    }, null, 2) + '\n',
  );
  writeFileSync(
    join(repo, 'pdd.json'),
    JSON.stringify({
      lint: {
        custom_rules: [
          {
            id: 'story-must-have-notes',
            target: 'story',
            severity: 'error',
            require_heading: '## Notes',
            message: 'Include a "## Notes" section on Stories.',
          },
        ],
      },
    }, null, 2) + '\n',
  );

  execFileSync('git', ['init'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });

  // 1. Scoped `pdd lint --local calc --json` catches custom Story error rules via Short JSON stem pairing + singular entry_path.
  const localOut = sink(), localErr = sink();
  const localExit = await runPdd(['lint', '--local', 'calc', '--json'], {
    cwd: repo,
    env,
    stdout: localOut,
    stderr: localErr,
  });
  assert.equal(localExit, 1, localErr.text);
  const localJson = JSON.parse(localOut.text);
  assert.equal(localJson.ok, false);
  assert.ok(localJson.problems.some(p => p.includes('user_stories/calc.md') && p.includes('[story-must-have-notes]')));

  // 2. Scoped `pdd lint --codex calc --json` selects BOTH `prompts/calc.prompt.md` and `user_stories/calc.md`.
  const codexRunner = async (_cmd, args) => {
    const outFile = args[args.indexOf('--output-last-message') + 1];
    writeFileSync(outFile, JSON.stringify({
      files: [
        { path: 'prompts/calc.prompt.md', verdict: 'pass', summary: 'Clear calculator prompt.', issues: [] },
        { path: 'user_stories/calc.md', verdict: 'pass', summary: 'Clear shopper Story.', issues: [] },
      ],
    }));
    return { code: 0, stdout: '', stderr: '' };
  };
  const codexOut = sink(), codexErr = sink();
  const codexExit = await runCodexLint(
    { cwd: repo, words: ['calc'], json: true, env },
    { stdout: codexOut, stderr: codexErr, runAgentProcess: codexRunner },
  );
  assert.equal(codexExit, 1, 'deterministic story error rule fails calc.md');
  const codexJson = JSON.parse(codexOut.text);
  assert.deepEqual(
    codexJson.files.map(f => f.path).sort(),
    ['prompts/calc.prompt.md', 'user_stories/calc.md'],
  );

  // 3. Inspection/transform modes (`--emit-v1` and `--bind-criteria`) stay clean (exit 0) despite `pdd.json` error rules.
  const emitOut = sink(), emitErr = sink();
  const emitExit = await runPdd(['lint', '--emit-v1', 'calc', '--json'], {
    cwd: repo,
    env,
    stdout: emitOut,
    stderr: emitErr,
  });
  assert.equal(emitExit, 0, emitErr.text);
  const emitted = JSON.parse(emitOut.text);
  assert.equal(emitted.ok, true);
  assert.equal(emitted.scenarios[0].scenario.story_path, 'user_stories/calc.md');

  writeFileSync(
    join(repo, 'tests/calc.json'),
    JSON.stringify({
      schema_version: 'pdd.scenario.short.v1',
      story_path: 'user_stories/calc.md',
      entry_path: 'prompts/calc.prompt.md',
      steps: [{ op: 'add', input: { a: 2, b: 3 }, checks: [['1', 'result', '/sum', '=', 5]] }],
    }, null, 2) + '\n',
  );
  const bindOut = sink(), bindErr = sink();
  const bindExit = await runPdd(['lint', '--bind-criteria', 'calc', '--json'], {
    cwd: repo,
    env,
    stdout: bindOut,
    stderr: bindErr,
  });
  assert.equal(bindExit, 0, bindErr.text);
  assert.equal(JSON.parse(bindOut.text).ok, true);
});
