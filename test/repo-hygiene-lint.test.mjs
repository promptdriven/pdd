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
  lintNativeOnlyPortParity,
  lintPromptCodeBlocks,
  lintPromptSize,
  lintPromptStructure,
  lintRepoProject,
  loadProjectLintConfig,
  stripPromptMetadata,
} from '../src/repo-hygiene-lint.mjs';
import { lintTestFixedSleeps } from '../src/autopilot/lint-sleep-skip.mjs';
import { lint as seamLint, runCheck } from '../src/runtime-seam.mjs';
import { lintStories, lintStory } from '../src/story-lint.mjs';
import { fakeRuntime, harbor, portsFor, sink, TOKEN } from './helpers/runtime-fake.mjs';

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

  // 1. Repo-wide pdd lint --local --json exits 0, emits PDD-file warnings, and skips code-test regex noise.
  const jsonOut = sink(), jsonErr = sink();
  const exitJson = await runPdd(['lint', '--local', '--json'], { cwd: repo, env, stdout: jsonOut, stderr: jsonErr });
  assert.equal(exitJson, 0, jsonErr.text);
  const parsed = JSON.parse(jsonOut.stdout ?? jsonOut.text);
  assert.equal(parsed.exit_code, 0);
  assert.deepEqual(parsed.problems, []);
  assert.ok(parsed.warnings.some(w => w.startsWith('Warning:') && w.includes('prompts/bloated.prompt.md:6') && w.includes('[prompt-imperative-code]')));
  assert.ok(parsed.warnings.some(w => w.startsWith('Warning:') && w.includes('user_stories/bloated-story.md:13') && w.includes('[story-bloated-criteria]')));
  assert.equal(parsed.warnings.some(w => w.includes('test/fake-bloated.test.mjs')), false, 'core lint stays PDD-files-only');

  // 2. Plain-text pdd lint --local also exits 0 and prints Warning: lines.
  const txtOut = sink(), txtErr = sink();
  const exitTxt = await runPdd(['lint', '--local'], { cwd: repo, env, stdout: txtOut, stderr: txtErr });
  assert.equal(exitTxt, 0, txtErr.text);
  assert.match(txtOut.text, /Warning:.*prompts\/bloated\.prompt\.md:6/);
  assert.match(txtOut.text, /Warning:.*user_stories\/bloated-story\.md:13/);

  // 3. Story-scoped pdd lint --local clean-order omits unrelated prompts and Stories.
  const scopedOut = sink(), scopedErr = sink();
  const exitScoped = await runPdd(['lint', '--local', 'clean-order', '--json'], { cwd: repo, env, stdout: scopedOut, stderr: scopedErr });
  assert.equal(exitScoped, 0, scopedErr.text);
  const scopedParsed = JSON.parse(scopedOut.text);
  assert.equal(scopedParsed.exit_code, 0);
  assert.ok(!scopedParsed.warnings.some(w => w.includes('bloated')));

  // 4. Direct lintRepoProject returns PDD-file warnings cleanly without scanning code tests.
  const directReport = lintRepoProject({ root: repo });
  assert.ok(directReport.warnings.some(w => w.includes('prompts/bloated.prompt.md:6')));
  assert.ok(directReport.warnings.some(w => w.includes('user_stories/bloated-story.md:13')));
  assert.equal(directReport.warnings.some(w => w.includes('test/fake-bloated.test.mjs')), false);

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

  // Prompt (30 lines, missing ## Dependencies) >= owned code (26 lines >= 25 floor) -> triggers prompt-larger-than-code & prompt-missing-dependencies.
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
      ...Array.from({ length: 22 }, (_, i) => `- Jurisdiction rule ${i + 1}: apply standard rate.`),
    ].join('\n') + '\n',
  );
  writeFileSync(
    join(repo, 'src/calc.mjs'),
    [
      '// Generated from prompts/calc.prompt.md',
      'export function calcTax(cents) {',
      '  if (!Number.isInteger(cents) || cents < 0) throw new RangeError("invalid cents");',
      ...Array.from({ length: 22 }, (_, i) => `  const r${i} = cents + ${i}; void r${i};`),
      '  return Math.round(cents * 0.08);',
      '}',
    ].join('\n') + '\n',
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

  // 2. Configure pdd.json with disabled rules, promoted "error" built-in rule, and custom_rules across prompt/story/test/code.
  writeFileSync(
    join(repo, 'pdd.json'),
    JSON.stringify({
      lint: {
        disable: ['prompt-missing-dependencies'],
        rules: {
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

test('3574 Part A: kind: native-only exempts declarative schema fences while still flagging procedural fences and keeping checkable prompts unchanged', () => {
  // 1. kind: native-only with 35-line sql DDL + 20-line openapi yaml + 20-line protobuf -> 0 fence warnings.
  const nativeOnlySchemas = [
    '---',
    'kind: native-only',
    'reason: Owns SQLite schema, OpenAPI HTTP contract, and protobuf wire types.',
    '---',
    '',
    '# Storage & transport schema',
    '',
    '```sql',
    'CREATE TABLE access_records (',
    ...Array.from({ length: 33 }, (_, i) => `  col_${i + 1} TEXT NOT NULL, -- return value ${i + 1}`),
    '  id TEXT PRIMARY KEY',
    ');',
    '```',
    '',
    '```openapi',
    'openapi: 3.1.0',
    ...Array.from({ length: 19 }, (_, i) => `  description_${i + 1}: return payload ${i + 1}`),
    '```',
    '',
    '```protobuf',
    'syntax = "proto3";',
    ...Array.from({ length: 18 }, (_, i) => `  string field_${i + 1} = ${i + 1};`),
    '```',
    '',
    '## Dependencies',
    'None.',
  ].join('\n');
  assert.deepEqual(lintPromptCodeBlocks(nativeOnlySchemas, { path: 'prompts/trust/service.prompt.md' }), []);

  // 2. kind: native-only still flags oversized/imperative procedural fences and excludes exempted SQL lines from total count.
  const nativeOnlyMixed = [
    '---',
    'kind: native-only',
    'reason: Owns SQLite transactions.',
    '---',
    '',
    '# Mixed adapter',
    '',
    '```sql',
    ...Array.from({ length: 35 }, (_, i) => `CREATE INDEX idx_${i} ON items(col_${i});`),
    '```',
    '',
    '```js',
    ...Array.from({ length: 18 }, (_, i) => `const v${i} = ${i};`),
    '```',
    '',
    '```python',
    ...Array.from({ length: 16 }, (_, i) => `def helper_${i}(x):\n    return x`),
    '```',
  ].join('\n');
  const mixedWarnings = lintPromptCodeBlocks(nativeOnlyMixed, { path: 'prompts/trust/mixed.prompt.md' });
  assert.ok(mixedWarnings.some(w => w.includes('prompts/trust/mixed.prompt.md:46') && w.includes('[prompt-code-fence-length]')));
  assert.ok(mixedWarnings.some(w => w.includes('prompts/trust/mixed.prompt.md:47') && w.includes('[prompt-imperative-code]')));
  assert.ok(mixedWarnings.some(w => w.includes('prompts/trust/mixed.prompt.md:67') && w.includes('[prompt-code-fence-length]')));
  assert.ok(mixedWarnings.some(w => w.includes('prompts/trust/mixed.prompt.md:68') && w.includes('[prompt-imperative-code]')));
  assert.ok(mixedWarnings.some(w => w.includes('prompts/trust/mixed.prompt.md:46') && w.includes('[prompt-code-fence-total]') && w.includes('across 2 blocks')));
  assert.ok(!mixedWarnings.some(w => w.includes(':8 ')), 'exempted sql fence line must not be reported');

  // 3. Non-native-only prompts keep existing fence limits on sql/yaml/jsonschema unchanged.
  const checkableWithLongSql = [
    '# Access rules',
    '',
    'Own `src/access.mjs`.',
    '',
    '```sql',
    ...Array.from({ length: 18 }, (_, i) => `SELECT ${i} AS n;`),
    '```',
    '',
    '```yaml',
    ...Array.from({ length: 16 }, (_, i) => `field_${i}: string`),
    '```',
    '',
    '## Dependencies',
    'None.',
  ].join('\n');
  const checkableWarnings = lintPromptCodeBlocks(checkableWithLongSql, { path: 'prompts/trust/access.prompt.md' });
  assert.ok(checkableWarnings.some(w => w.includes('prompts/trust/access.prompt.md:5') && w.includes('[prompt-code-fence-length]')));
  assert.ok(checkableWarnings.some(w => w.includes('prompts/trust/access.prompt.md:26') && w.includes('[prompt-code-fence-length]')));
  assert.ok(checkableWarnings.some(w => w.includes('prompts/trust/access.prompt.md:5') && w.includes('[prompt-code-fence-total]')));
});

test('3574 Part B: lintNativeOnlyPortParity flags undeclared ports while ignoring filenames, versions, URLs, host builtins and SQL columns', () => {
  const accessPrompt = [
    '# Trust access control',
    '',
    'Own `src/trust/access.mjs`.',
    '- Read via `store.load({ tenantId })` and save via `store.save({ tenantId, grant })`.',
    '- Log events with audit.append.',
    '',
    '## Dependencies',
    'None.',
  ].join('\n');

  const servicePrompt = [
    '---',
    'kind: native-only',
    'reason: Runs SQLite and outbound webhooks.',
    '---',
    '',
    '# Trust service',
    '',
    'Own `src/trust/service.mjs`. Config lives in `package.json`, `pdd.json`, `yarn.lock`, `schema.sql`, `v1.0`, and `spec.v2`.',
    'Call `https://hooks.example.com/v1` using `env.WEBHOOK_TOKEN`, `process.env`, `ports.fs`, `req.body`, `res.status`, `JSON.stringify(x)`, `Intl.DateTimeFormat`, and `items.length`.',
    '',
    '```sql',
    'CREATE TABLE access_records (',
    '  id TEXT PRIMARY KEY,',
    '  tenant_id TEXT NOT NULL,',
    '  status TEXT NOT NULL',
    ');',
    'SELECT a.id, access_records.status FROM access_records a;',
    '```',
    '',
    '## Port wiring',
    '',
    'Index `access_records.tenant_id` for lookups.',
    '- `store.load`: valid declared port.',
    '- `access_state.read`: missing read port.',
    '- `access.commit(tx)`: missing commit port.',
    '- notice.deliver: missing unbackticked port.',
    '',
    '## Dependencies',
    '- [access](access.prompt.md)',
  ].join('\n');

  const errors = lintNativeOnlyPortParity(servicePrompt, [{ path: 'prompts/trust/access.prompt.md', text: accessPrompt }], {
    path: 'prompts/trust/service.prompt.md',
    dependencyPaths: ['prompts/trust/access.prompt.md'],
  });
  assert.equal(errors.length, 3, errors.join('\n'));
  assert.ok(errors[0].includes('prompts/trust/service.prompt.md:24 [native-only-unknown-port]') && errors[0].includes('"access_state.read"'));
  assert.ok(errors[1].includes('prompts/trust/service.prompt.md:25 [native-only-unknown-port]') && errors[1].includes('"access.commit"'));
  assert.ok(errors[2].includes('prompts/trust/service.prompt.md:26 [native-only-unknown-port]') && errors[2].includes('"notice.deliver"'));
  assert.ok(errors[0].includes('declared ports: audit.append, store.load, store.save'));

  // Embedded Runtime interface resources on dependency prompt also satisfy parity cleanly.
  const embeddedDep = [
    '# Embedded port owner',
    'Reads via KEY.load.',
    '<details><summary>Runtime interface</summary>',
    '```json',
    JSON.stringify({
      resources: [
        { name: 'access_state', operations: [{ name: 'read' }] },
        { name: 'access', operations: [{ name: 'commit' }] },
        { name: 'notice', operations: [{ name: 'deliver' }] },
        { name: 'store', operations: [{ name: 'load' }] },
      ],
    }),
    '```',
    '</details>',
  ].join('\n');
  assert.deepEqual(
    lintNativeOnlyPortParity(servicePrompt, [{ path: 'prompts/trust/access.prompt.md', text: embeddedDep }], {
      path: 'prompts/trust/service.prompt.md',
    }),
    [],
  );

  // Non-native-only prompt is skipped by native-only parity lint.
  assert.deepEqual(
    lintNativeOnlyPortParity('# Regular\n\nUses `missing.port`.\n', [{ path: 'prompts/trust/access.prompt.md', text: accessPrompt }]),
    [],
  );
});

test('3574 + 3578: default-on native-only-unknown-port fails closed without pdd.json, honors transitive deps/contracts and pdd.json overrides, and keeps warnings advisory', async t => {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-3574-3578-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));

  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  const state = join(scratch, 'state');
  for (const dir of [home, state, join(repo, 'prompts/trust'), join(repo, 'contracts'), join(repo, 'test')]) {
    mkdirSync(dir, { recursive: true });
  }
  const env = { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'invalid' };

  writeFileSync(
    join(repo, 'contracts/ports.md'),
    '# Shared ports\n\nExternal contract port: `telemetry.emit`.\n',
  );
  writeFileSync(
    join(repo, 'prompts/trust/audit.prompt.md'),
    '# Audit log\n\nOwn `src/trust/audit.mjs`. Append records via `audit.append`.\n\n## Dependencies\n\n- [Shared ports](../../contracts/ports.md)\n',
  );
  writeFileSync(
    join(repo, 'prompts/trust/access.prompt.md'),
    '# Trust access\n\nOwn `src/trust/access.mjs`. Use `store.load` and `store.save`.\n\n## Dependencies\n\n- [audit](audit.prompt.md)\n',
  );
  // Standalone native-only prompt with no checkable dependencies should never trigger native-only-unknown-port.
  writeFileSync(
    join(repo, 'prompts/trust/standalone.prompt.md'),
    '---\nkind: native-only\nreason: Standalone OS socket helper.\n---\n\n# Standalone\n\nUses `socket.bind`.\n\n## Dependencies\n\nNone.\n',
  );
  // Advisory fake test warning in the repo must stay warn-only and never cause exit 1 by itself.
  writeFileSync(
    join(repo, 'test/advisory.test.mjs'),
    "import { readFileSync } from 'node:fs';\nreadFileSync('prompts/trust/access.prompt.md', 'utf8');\n",
  );

  const sqlDdl = [
    '```sql',
    'CREATE TABLE access_records (',
    ...Array.from({ length: 34 }, (_, i) => `  field_${i + 1} TEXT NOT NULL,`),
    '  id TEXT PRIMARY KEY',
    ');',
    '```',
  ].join('\n');

  const brokenService = [
    '---',
    'kind: native-only',
    'reason: SQLite and webhook adapter for trust access.',
    '---',
    '',
    '# Trust service',
    '',
    sqlDdl,
    '',
    '## Port wiring',
    '',
    '- `store.load`: valid direct port.',
    '- `audit.append`: valid transitive checkable prompt port.',
    '- `telemetry.emit`: valid transitive shared contract port.',
    '- `access_state.read`: dead port 1.',
    '- `access.commit`: dead port 2.',
    '- `notice.deliver`: dead port 3.',
    '',
    '## Dependencies',
    '',
    '- [access](access.prompt.md)',
  ].join('\n') + '\n';

  writeFileSync(join(repo, 'prompts/trust/service.prompt.md'), brokenService);

  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });

  // 1. With NO pdd.json at all, pdd lint --local (plain & --json) fails closed with exit 1 on the 3 dead ports and emits 0 SQL fence warnings.
  const brokenOut = sink(), brokenErr = sink();
  const brokenCode = await runPdd(['lint', '--local'], { cwd: repo, env, stdout: brokenOut, stderr: brokenErr });
  assert.equal(brokenCode, 1);
  assert.match(brokenErr.text, /\[native-only-unknown-port\].*"access_state\.read"/);
  assert.match(brokenErr.text, /\[native-only-unknown-port\].*"access\.commit"/);
  assert.match(brokenErr.text, /\[native-only-unknown-port\].*"notice\.deliver"/);
  assert.ok(!brokenErr.text.includes('"store.load"'));
  assert.ok(!brokenErr.text.includes('"audit.append"'));
  assert.ok(!brokenErr.text.includes('"telemetry.emit"'));
  assert.ok(!brokenErr.text.includes('socket.bind'));
  assert.ok(!brokenOut.text.includes('prompt-code-fence-length'));
  assert.ok(!brokenOut.text.includes('prompt-code-fence-total'));

  const brokenJsonOut = sink(), brokenJsonErr = sink();
  const brokenJsonCode = await runPdd(['lint', '--local', '--json'], { cwd: repo, env, stdout: brokenJsonOut, stderr: brokenJsonErr });
  assert.equal(brokenJsonCode, 1, brokenJsonErr.text);
  const brokenParsed = JSON.parse(brokenJsonOut.text);
  assert.equal(brokenParsed.ok, false);
  assert.equal(brokenParsed.exit_code, 1);
  assert.equal(brokenParsed.problems.length, 3);
  assert.ok(brokenParsed.warnings.some(w => w.includes('[native-only-contract-incomplete]')), 'advisory warnings remain visible');
  assert.ok(!brokenParsed.warnings.some(w => w.includes('prompt-code-fence-')));

  // 2. pdd.json without a "lint" key still fails closed by default.
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'off' } }, null, 2) + '\n');
  execFileSync('git', ['add', 'pdd.json'], { cwd: repo });
  const noLintKeyCode = await runPdd(['lint', '--local'], { cwd: repo, env, stdout: sink(), stderr: sink() });
  assert.equal(noLintKeyCode, 1);

  // 3. pdd.json "lint" override ("warn") downgrades native-only-unknown-port to advisory warning (exit 0).
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({ lint: { rules: { 'native-only-unknown-port': 'warn' } } }, null, 2) + '\n');
  const warnOverrideOut = sink(), warnOverrideErr = sink();
  const warnOverrideCode = await runPdd(['lint', '--local', '--json'], { cwd: repo, env, stdout: warnOverrideOut, stderr: warnOverrideErr });
  assert.equal(warnOverrideCode, 0, warnOverrideErr.text);
  const warnParsed = JSON.parse(warnOverrideOut.text);
  assert.deepEqual(warnParsed.problems, []);
  assert.ok(warnParsed.warnings.some(w => w.includes('[native-only-unknown-port]') && w.includes('"access_state.read"')));

  // 4. pdd.json "lint" disable ("off") suppresses native-only-unknown-port completely (exit 0).
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({ lint: { disable: ['native-only-unknown-port'] } }, null, 2) + '\n');
  const offOverrideOut = sink(), offOverrideErr = sink();
  const offOverrideCode = await runPdd(['lint', '--local', '--json'], { cwd: repo, env, stdout: offOverrideOut, stderr: offOverrideErr });
  assert.equal(offOverrideCode, 0, offOverrideErr.text);
  const offParsed = JSON.parse(offOverrideOut.text);
  assert.deepEqual(offParsed.problems, []);
  assert.ok(!offParsed.warnings.some(w => w.includes('[native-only-unknown-port]')));

  // 5. Removing pdd.json and replacing the 3 dead ports with valid ones makes pdd lint --local exit 0 even with advisory fake-test warnings present.
  rmSync(join(repo, 'pdd.json'));
  const fixedService = brokenService
    .replace('- `access_state.read`: dead port 1.', '- `store.save`: valid direct save port.')
    .replace('- `access.commit`: dead port 2.\n', '')
    .replace('- `notice.deliver`: dead port 3.\n', '');
  writeFileSync(join(repo, 'prompts/trust/service.prompt.md'), fixedService);

  const fixedOut = sink(), fixedErr = sink();
  const fixedCode = await runPdd(['lint', '--local', '--json'], { cwd: repo, env, stdout: fixedOut, stderr: fixedErr });
  assert.equal(fixedCode, 0, fixedErr.text);
  const fixedParsed = JSON.parse(fixedOut.text);
  assert.equal(fixedParsed.exit_code, 0);
  assert.deepEqual(fixedParsed.problems, []);
  assert.ok(fixedParsed.warnings.some(w => w.includes('[native-only-contract-incomplete]')), 'warn-only rule still never fails exit code');
});

test('3574 adversarial review fixes: linear ReDoS safety, scoped table/prose extraction, split/nested/subheading port declarations, Runtime interface headings, SQL DDL extensions and single-scan seam collector', async t => {
  // P0-1: No O(N^2) URL/token backtracking and no O(N^3) unclosed <details> backtracking.
  const bigWire = `---\nkind: native-only\nreason: Perf check.\n---\n\n# Perf\n\nwire ${'a.b.'.repeat(25000)} https://example.com\n`;
  const t0 = performance.now();
  const bigRes = lintNativeOnlyPortParity(bigWire, ['# Dep\nUses `store.load`.\n']);
  const bigMs = performance.now() - t0;
  assert.deepEqual(bigRes, []);
  assert.ok(bigMs < 500, `expected linear scan on 100KB a.b. input, got ${bigMs.toFixed(1)}ms`);

  const unclosedDetails = '<details><summary>Runtime interface</summary>'.repeat(400);
  const t1 = performance.now();
  assert.equal(stripPromptMetadata(unclosedDetails), unclosedDetails);
  assert.deepEqual(lintPromptCodeBlocks(unclosedDetails, { path: 'prompts/evil.prompt.md' }), []);
  const detailParity = lintNativeOnlyPortParity(
    '---\nkind: native-only\nreason: Perf check.\n---\n\n# Service\n\n## Ports\n- `store.load`\n',
    [unclosedDetails],
  );
  const detailMs = performance.now() - t1;
  assert.equal(detailParity.length, 1);
  assert.ok(detailMs < 500, `expected linear scan on 400 unclosed details tags, got ${detailMs.toFixed(1)}ms`);

  // P1-1: Zero false positives on non-port tables, excluded columns, TCP/HTTP network port prose, expanded extensions & framework prefixes;
  // high-signal <declaredPrefix>.<unknownOp> still caught in general prose; split/nested/subheading port declarations recognized.
  const structuredDep = [
    '# Ledger domain',
    '',
    'Own `src/ledger.mjs`. Uses `store.load` and `store.save`.',
    '',
    '| Port | Operation | Description |',
    '| --- | --- | --- |',
    '| `ledger_state` | `read(id)` | Read state |',
    '| `ledger_state` | `write(id, row)` | Write state |',
    '',
    '| Resource | Operation |',
    '| --- | --- |',
    '| `notifier` | `send, flush` |',
    '',
    '## Ports',
    '',
    '- `quota`',
    '  - `check(tenant)`',
    '  - `consume(tenant, n)`',
    '',
    '### `metrics_sink`',
    '',
    '- `record(name, value)`: record counter',
    '',
    '## Dependencies',
    'None.',
  ].join('\n');

  const cleanAdapter = [
    '---',
    'kind: native-only',
    'reason: Runs FastAPI/uvicorn HTTP server and SQLite WAL storage.',
    '---',
    '',
    '# Ledger HTTP & SQLite adapter',
    '',
    '## HTTP Port Binding',
    '',
    'Bind the server to port 8080 using `uvicorn.run`, `app.get`, `router.post`, `server.listen`, and `asyncio.run`.',
    'Listen on TCP port 8080 and read `config.port`, `ctx.user`, `db.execute`, `pool.query`, `conn.commit`, `tx.rollback`, `sqlite3.connect`, `sqlalchemy.create_engine`, `httpx.post`, `requests.post`, `json.loads`, and `excluded.flag`.',
    'Runtime files: `app.log`, `tls.key`, `server.cert`, `prod.env`, `app.wal`, `app.shm`, `api.service`, `sync.timer`, `app.socket`, `nginx.conf`, `env.example`.',
    '',
    '| Field | Type |',
    '| --- | --- |',
    '| `user.email` | string |',
    '| `order.total_cents` | integer |',
    '',
    '| Table Column | Type |',
    '| --- | --- |',
    '| `audit_events.actor_id` | text |',
    '',
    '```sql',
    'CREATE UNLOGGED TABLE ledger_cache (',
    '  cache_key TEXT PRIMARY KEY,',
    '  payload TEXT NOT NULL',
    ');',
    'CREATE VIRTUAL TABLE search_idx USING fts5(doc_id, body);',
    'ALTER TABLE ledger_cache ADD COLUMN expires_at TEXT;',
    '```',
    '',
    '## Port wiring',
    '',
    '| Port | SQL Column |',
    '| --- | --- |',
    '| `store.load` | `ledger_cache.cache_key` |',
    '| `ledger_state.read` | `ledger_cache.expires_at` |',
    '| `ledger_state.write` | `search_idx.body` |',
    '| `notifier.send` | `unlisted.column` |',
    '',
    '- `notifier.flush`: flushes queued `payload.items` without failing on RHS field names.',
    '- `quota.check`: validates quota using `ledger_cache.expires_at`.',
    '- `quota.consume`: decrements quota.',
    '- `metrics_sink.record`: writes to `search_idx.doc_id`.',
    '',
    '## Dependencies',
    '- [ledger](ledger.prompt.md)',
  ].join('\n');

  assert.deepEqual(
    lintNativeOnlyPortParity(cleanAdapter, [{ path: 'prompts/ledger.prompt.md', text: structuredDep }], {
      path: 'prompts/ledger-adapter.prompt.md',
    }),
    [],
  );

  // High-signal <declaredPrefix>.<unknownOp> in general prose + dead port on SQL table name are still caught!
  const adapterWithDeadOps = [
    cleanAdapter,
    '',
    '## Background maintenance',
    '',
    'Nightly cleanup calls `store.purge(cutoff)` in general prose.',
    '',
    '## Bound ports',
    '',
    '- `search_idx.query`: undeclared port sharing a SQL virtual table name.',
  ].join('\n');
  const deadOpErrors = lintNativeOnlyPortParity(adapterWithDeadOps, [{ path: 'prompts/ledger.prompt.md', text: structuredDep }], {
    path: 'prompts/ledger-adapter.prompt.md',
  });
  assert.equal(deadOpErrors.length, 2, deadOpErrors.join('\n'));
  assert.ok(deadOpErrors.some(e => e.includes('"store.purge"')));
  assert.ok(deadOpErrors.some(e => e.includes('"search_idx.query"')));

  // P1-2: `## Runtime interface` heading extraction (both mid-file and EOF) works for stripPromptMetadata, dependency resources, and native-only classification.
  const headingResourceDep = [
    '# Heading interface checkable dep',
    '',
    'Own `src/dep.mjs`.',
    '',
    '## Runtime interface',
    '',
    '```json',
    JSON.stringify({
      resources: [
        { name: 'vault', operations: [{ name: 'fetch' }, { name: 'rotate' }] },
      ],
    }, null, 2),
    '```',
    '',
    '## Dependencies',
    '',
    'None.',
  ].join('\n');

  const strippedHeading = stripPromptMetadata(headingResourceDep);
  assert.ok(strippedHeading.includes('# Heading interface checkable dep'));
  assert.ok(strippedHeading.includes('## Dependencies'));
  assert.ok(!strippedHeading.includes('vault'), '## Runtime interface JSON block must be stripped completely');

  const vaultAdapter = [
    '---',
    'kind: native-only',
    'reason: Calls live HSM.',
    '---',
    '',
    '# Vault adapter',
    '',
    '## Ports',
    '- `vault.fetch`: valid heading-interface resource op.',
    '- `vault.destroy`: undeclared op.',
    '',
    '## Dependencies',
    '- [dep](dep.prompt.md)',
  ].join('\n');
  const headingErrors = lintNativeOnlyPortParity(vaultAdapter, [{ path: 'prompts/dep.prompt.md', text: headingResourceDep }], {
    path: 'prompts/vault-adapter.prompt.md',
  });
  assert.equal(headingErrors.length, 1, headingErrors.join('\n'));
  assert.ok(headingErrors[0].includes('"vault.destroy"'));
  assert.ok(!headingErrors[0].includes('"vault.fetch"'));

  // P1-2 + P1-3: Repo test verifying heading-style native-only dep is skipped as non-checkable AND seam.lint invokes onProjectLintResult exactly once.
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-3574-adv-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));
  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  const state = join(scratch, 'state');
  for (const dir of [home, state, join(repo, 'prompts')]) mkdirSync(dir, { recursive: true });

  writeFileSync(
    join(repo, 'prompts/native-peer.prompt.md'),
    [
      '# Native peer with heading Runtime interface',
      '',
      'Own `src/native-peer.mjs`.',
      '',
      '## Runtime interface',
      '',
      '```json',
      '{"kind":"native-only","reason":"Heading-style native-only peer."}',
      '```',
    ].join('\n') + '\n',
  );
  writeFileSync(
    join(repo, 'prompts/only-native-dep.prompt.md'),
    [
      '---',
      'kind: native-only',
      'reason: Links only a heading-style native-only peer.',
      '---',
      '',
      '# Wrapper',
      '',
      '## Ports',
      '- `internal.call`: should not fail because linked peer is native-only.',
      '',
      '## Dependencies',
      '- [native peer](native-peer.prompt.md)',
    ].join('\n') + '\n',
  );
  writeFileSync(
    join(repo, 'prompts/checkable.prompt.md'),
    '# Checkable\n\nOwn `src/checkable.mjs`. Uses `store.load`.\n\n## Dependencies\n\nNone.\n',
  );
  writeFileSync(
    join(repo, 'prompts/broken-adapter.prompt.md'),
    '---\nkind: native-only\nreason: Native DB.\n---\n\n# Broken\n\n## Ports\n- `store.load`\n- `store.missing`\n\n## Dependencies\n- [checkable](checkable.prompt.md)\n',
  );

  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });

  const report = lintRepoProject({ root: repo });
  assert.equal(report.ok, false);
  assert.equal(report.errors.length, 1);
  assert.ok(report.errors[0].includes('prompts/broken-adapter.prompt.md') && report.errors[0].includes('"store.missing"'));
  assert.ok(!report.errors.some(e => e.includes('only-native-dep.prompt.md')), 'heading-style native-only peer must be recognized as native-only');
});

test('3574 + 3578 Round 2 regressions: Story-scoped sibling isolation (P1-A), ## Ports subheadings (P1-B), adapter/idiom/separator false-positive guards (P1-C), and O(N) SQL/heading scans (P1-D)', async t => {
  // P1-A: Two sibling Stories sharing one prompt — lint --local user_stories/good.md must exit 0 even when sibling bad.md fails an error rule.
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-r2-p1a-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));
  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  const state = join(scratch, 'state');
  for (const dir of [home, state, join(repo, 'prompts'), join(repo, 'user_stories'), join(repo, 'tests')]) {
    mkdirSync(dir, { recursive: true });
  }
  writeFileSync(
    join(repo, 'prompts/shared.prompt.md'),
    '# Shared pricing\n\nOwn `src/shared.mjs`. Compute totals in cents.\n\n## Dependencies\n\nNone.\n',
  );
  writeFileSync(
    join(repo, 'user_stories/good.md'),
    '# Good story\n\nAs a shopper, I want my subtotal shown in cents, so that I know the price.\n\n## Acceptance criteria\n\n1. One item costs 100 cents.\n',
  );
  writeFileSync(
    join(repo, 'tests/good.json'),
    JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/good.md',
      criteria: [{ id: 'AC1', text: 'One item costs 100 cents.' }],
      initial_world: {},
      steps: [{ step_id: 's1', entry_path: 'prompts/shared.prompt.md', operation: 'price', input: {}, checks: [{ criterion_id: 'AC1', target: 'result', path: '', op: 'equals', value: 100 }] }],
    }, null, 2) + '\n',
  );
  writeFileSync(
    join(repo, 'user_stories/bad.md'),
    [
      '# Bad story',
      '',
      'As a shopper, I want seven things at once, so that it is bloated.',
      '',
      '## Acceptance criteria',
      '',
      ...Array.from({ length: 7 }, (_, i) => `${i + 1}. Check ${i + 1} returns ${i + 1}.`),
    ].join('\n') + '\n',
  );
  writeFileSync(
    join(repo, 'tests/bad.json'),
    JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/bad.md',
      criteria: [{ id: 'AC1', text: 'Check 1 returns 1.' }],
      initial_world: {},
      steps: [{ step_id: 's1', entry_path: 'prompts/shared.prompt.md', operation: 'price', input: {}, checks: [{ criterion_id: 'AC1', target: 'result', path: '', op: 'equals', value: 1 }] }],
    }, null, 2) + '\n',
  );
  writeFileSync(
    join(repo, 'pdd.json'),
    JSON.stringify({ lint: { rules: { 'story-bloated-criteria': 'error' } } }, null, 2) + '\n',
  );
  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });

  const env = { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'invalid' };
  const goodOut = sink(), goodErr = sink();
  const goodCode = await runPdd(['lint', '--local', 'user_stories/good.md'], { cwd: repo, env, stdout: goodOut, stderr: goodErr });
  assert.equal(goodCode, 0, `expected good.md to ignore sibling bad.md, stderr: ${goodErr.text}`);

  const goodJsonOut = sink(), goodJsonErr = sink();
  const goodJsonCode = await runPdd(['lint', '--local', 'user_stories/good.md', '--json'], { cwd: repo, env, stdout: goodJsonOut, stderr: goodJsonErr });
  assert.equal(goodJsonCode, 0, goodJsonErr.text);
  assert.deepEqual(JSON.parse(goodJsonOut.text).problems, []);

  const badOut = sink(), badErr = sink();
  const badCode = await runPdd(['lint', '--local', 'user_stories/bad.md'], { cwd: repo, env, stdout: badOut, stderr: badErr });
  assert.equal(badCode, 1);
  assert.match(badErr.text, /user_stories\/bad\.md.*\[story-bloated-criteria\]/);

  const repoOut = sink(), repoErr = sink();
  const repoCode = await runPdd(['lint', '--local'], { cwd: repo, env, stdout: repoOut, stderr: repoErr });
  assert.equal(repoCode, 1);
  assert.match(repoErr.text, /user_stories\/bad\.md.*\[story-bloated-criteria\]/);

  // P1-B: Subheadings like `### \`store\` port`, `### \`vault\` resource`, `### \`notice\`` under `## Ports` preserve portsSectionDepth and extract all 4 ports.
  const subheadingDep = [
    '# Domain ports via subheadings',
    '',
    '## Ports',
    '',
    '### `store` port',
    '- `load(id)`',
    '- `save(id, row)`',
    '',
    '### `vault` resource',
    '- `fetch(key)`',
    '',
    '### `notice`',
    '- `deliver(msg)`',
    '',
    '## Dependencies',
    'None.',
  ].join('\n');

  const subheadingAdapter = [
    '---',
    'kind: native-only',
    'reason: Real DB, HSM, and webhook transport.',
    '---',
    '',
    '# Adapter',
    '',
    '## Port wiring',
    '- `store.load`: read row',
    '- `store.save`: write row',
    '- `vault.fetch`: read secret',
    '- `notice.deliver`: post webhook',
    '',
    '## Dependencies',
    '- [domain](domain.prompt.md)',
  ].join('\n');
  assert.deepEqual(
    lintNativeOnlyPortParity(subheadingAdapter, [{ path: 'prompts/domain.prompt.md', text: subheadingDep }]),
    [],
  );
  const subheadingDead = lintNativeOnlyPortParity(
    `${subheadingAdapter}\n## Bound ports\n- \`vault.delete\`\n`,
    [{ path: 'prompts/domain.prompt.md', text: subheadingDep }],
  );
  assert.equal(subheadingDead.length, 1);
  assert.ok(subheadingDead[0].includes('"vault.delete"'));

  // P1-C: Zero false positives on generic `## SQLite Adapter` / `## Storage Adapter`, `Upper bound on retries`,
  // blank-line reset after cue lines, `Bind SQL parameters`, `wire format`, `Bind 0.0.0.0 on port 8080`, and ASCII ` - ` bullet separators.
  const realisticNativeAdapter = [
    '---',
    'kind: native-only',
    'reason: SQLite storage, protobuf wire serialization, and hypercorn HTTP server.',
    '---',
    '',
    '# Storage and transport service',
    '',
    '## SQLite Adapter',
    '',
    'Read `settings.db_path`, open a connection, run `cursor.execute`, and finalize with `session.commit`.',
    'Bind SQL parameters using `cursor.execute` and `statement.bind_values`.',
    '',
    '## Storage Adapter',
    '',
    'Encode the wire format using `protobuf.encode` and decode via `protobuf.decode`.',
    'Bind 0.0.0.0 on port 8080 using `hypercorn.serve`.',
    'Upper bound on retries is 3.',
    '',
    '- `cursor.execute` runs retryable queries.',
    '',
    'Wire `store.load` for [domain](domain.prompt.md).',
    '',
    '- `session.commit` flushes pending local state after a blank line.',
    '',
    '## Port wiring',
    '',
    '- `store.load` - reads rows via `cursor.execute` and `session.commit`.',
    '- `store.save` - writes rows via `cursor.execute`.',
    '- `vault.fetch` - fetches key material.',
    '- `notice.deliver` - sends HTTP notification.',
    '',
    '## Dependencies',
    '- [domain](domain.prompt.md)',
  ].join('\n');
  assert.deepEqual(
    lintNativeOnlyPortParity(realisticNativeAdapter, [{ path: 'prompts/domain.prompt.md', text: subheadingDep }], {
      path: 'prompts/service.prompt.md',
    }),
    [],
  );

  // ASCII ` - ` separator still catches declared-prefix undeclared op on RHS while ignoring `cursor.execute`.
  const asciiDashDead = lintNativeOnlyPortParity(
    realisticNativeAdapter.replace(
      '- `store.load` - reads rows via `cursor.execute` and `session.commit`.',
      '- `store.load` - reads rows via `cursor.execute` and calls `store.purge`.',
    ),
    [{ path: 'prompts/domain.prompt.md', text: subheadingDep }],
  );
  assert.equal(asciiDashDead.length, 1, asciiDashDead.join('\n'));
  assert.ok(asciiDashDead[0].includes('"store.purge"'));

  // P1-D: Both newly identified O(N^2) patterns run in strictly linear time.
  const unclosedSql = `---\nkind: native-only\nreason: Perf.\n---\n\n# SQL\n\n\`\`\`sql\n${'CREATE TABLE t (\n'.repeat(5000)}\`\`\`\n\n## Ports\n- \`store.load\`\n`;
  const tSql = performance.now();
  const sqlRes = lintNativeOnlyPortParity(unclosedSql, [{ path: 'prompts/domain.prompt.md', text: subheadingDep }]);
  const msSql = performance.now() - tSql;
  assert.deepEqual(sqlRes, []);
  assert.ok(msSql < 200, `expected linear SQL paren scan on 5000 unclosed CREATE TABLE statements, got ${msSql.toFixed(1)}ms`);

  const manyHeadings = '## Runtime interface\n```json\n{}\n```\n## Other\nline\n'.repeat(2500);
  const tHead = performance.now();
  const strippedHeadings = stripPromptMetadata(manyHeadings);
  const msHead = performance.now() - tHead;
  assert.ok(!strippedHeadings.includes('Runtime interface'));
  assert.ok(msHead < 200, `expected linear heading scan on 15k lines, got ${msHead.toFixed(1)}ms`);
});

test('3574 + 3578 Round 3 regressions: hosted repo-wide pdd lint catches native-only adapter dead ports, seam suppresses onProjectLintResult on filtered scans, and backticked IPv4/IPv6 binds produce zero false positives', async t => {
  // P2: Backticked IPv4/IPv6/localhost binds alongside "adapter" produce 0 errors.
  const dep = '# Order domain\n\nOwn `src/order.mjs`. Uses `store.load`.\n\n## Dependencies\n\nNone.\n';
  const ipBindingPrompt = [
    '---',
    'kind: native-only',
    'reason: Runs live HTTP listener.',
    '---',
    '',
    '# HTTP server',
    '',
    'The HTTP adapter binds `0.0.0.0` on port 8080 using `hypercorn.serve`.',
    'The HTTP adapter binds `[::1]` on port `8080` using `hypercorn.serve`.',
    'The HTTP adapter binds `::` on port 8080 using `hypercorn.serve`.',
    'The HTTP adapter binds `localhost` on port 8080 using `hypercorn.serve`.',
    '',
    '## Dependencies',
    '- [order](order.prompt.md)',
  ].join('\n');
  assert.deepEqual(
    lintNativeOnlyPortParity(ipBindingPrompt, [{ path: 'prompts/order.prompt.md', text: dep }], {
      path: 'prompts/http-server.prompt.md',
    }),
    [],
  );

  // P1: Hosted repo-wide `pdd lint` & `pdd lint --json` (without `--local`) must NOT mask native-only adapter errors behind Story-filtered lintSvgLayouts.
  const h = harbor(t, repo => {
    writeFileSync(
      join(repo, 'prompts/adapter.prompt.md'),
      [
        '---',
        'kind: native-only',
        'reason: Live persistence adapter for Harbor place_order.',
        '---',
        '',
        '# Harbor adapter',
        '',
        '## Port wiring',
        '- `store.missing`: dead port not declared in place_order.',
        '',
        '## Dependencies',
        '- [place_order](place_order.prompt.md)',
      ].join('\n') + '\n',
    );
  });

  const fake = await fakeRuntime(t, entry => fake.normal(entry));
  const fakeBin = join(h.sandbox, 'bin');
  mkdirSync(fakeBin, { recursive: true });
  const fakeGh = join(fakeBin, 'gh');
  writeFileSync(
    fakeGh,
    `#!/bin/sh\nif [ "$1" = "auth" ]; then echo "${TOKEN}"; else echo "octo 4242"; fi\n`,
    { mode: 0o755 },
  );
  const env = {
    HOME: h.home,
    PDD_STATE_DIR: h.state,
    PDD_RUNTIME_URL: fake.origin,
    PATH: `${fakeBin}:${process.env.PATH ?? ''}`,
  };

  // Defense-in-depth: seam.lint (hosted, which passes filtered promptPaths: capture.files) never invokes onProjectLintResult.
  const filteredResults = [];
  const seamHostedPorts = portsFor(env, { onProjectLintResult: r => filteredResults.push(r) }).ports;
  const seamHostedCode = await seamLint({ cwd: h.repo }, seamHostedPorts);
  assert.equal(seamHostedCode, 0, seamHostedPorts.stderr.text);
  assert.equal(filteredResults.length, 0, 'filtered hosted lintSvgLayouts scan must not invoke onProjectLintResult');

  // Hosted repo-wide `pdd lint` (plain text) fails closed with exit 1 naming prompts/adapter.prompt.md and store.missing.
  const hostedOut = sink(), hostedErr = sink();
  const hostedCode = await runPdd(['lint'], { cwd: h.repo, env, stdout: hostedOut, stderr: hostedErr });
  assert.equal(hostedCode, 1, `expected hosted pdd lint to fail closed on native-only adapter, stdout: ${hostedOut.text}\nstderr: ${hostedErr.text}`);
  assert.match(hostedErr.text, /Error:.*prompts\/adapter\.prompt\.md.*\[native-only-unknown-port\].*"store\.missing"/);

  // Hosted repo-wide `pdd lint --json` fails closed with exit 1, ok: false, exit_code: 1, and exact error in problems.
  const hostedJsonOut = sink(), hostedJsonErr = sink();
  const hostedJsonCode = await runPdd(['lint', '--json'], { cwd: h.repo, env, stdout: hostedJsonOut, stderr: hostedJsonErr });
  assert.equal(hostedJsonCode, 1, hostedJsonErr.text);
  const hostedParsed = JSON.parse(hostedJsonOut.text);
  assert.equal(hostedParsed.ok, false);
  assert.equal(hostedParsed.exit_code, 1);
  assert.ok(
    hostedParsed.problems.some(p => p.includes('prompts/adapter.prompt.md') && p.includes('[native-only-unknown-port]') && p.includes('"store.missing"')),
    `expected [native-only-unknown-port] in hosted JSON problems, got: ${JSON.stringify(hostedParsed.problems)}`,
  );
});

test('3574 Part 1: lintRepoProject emits advisory native-only-contract-incomplete warning on thin native-only stubs while staying quiet on complete specs', (t) => {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-3574-contract-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));
  mkdirSync(join(scratch, 'prompts'), { recursive: true });

  writeFileSync(
    join(scratch, 'prompts/stub.prompt.md'),
    '---\nkind: native-only\nreason: SQLite adapter.\n---\n\n# Stub\n\nOwn `src/stub.mjs`.\n\n## Dependencies\nNone.\n',
  );
  writeFileSync(
    join(scratch, 'prompts/complete.prompt.md'),
    [
      '---',
      'kind: native-only',
      'reason: SQLite WAL adapter.',
      '---',
      '',
      '# Complete adapter',
      '',
      'Own `src/complete.mjs`.',
      '',
      '## Storage schema',
      '```sql',
      'CREATE TABLE items (id TEXT PRIMARY KEY);',
      '```',
      '',
      '## Error mapping',
      'Rollback and fail closed on SQLITE_BUSY timeouts.',
      '',
      '## Real-host verification',
      'Run real SQLite file smoke test (`node --test test/complete-smoke.test.mjs`).',
      '',
      '## Dependencies',
      'None.',
    ].join('\n') + '\n',
  );
  execFileSync('git', ['init', '-q'], { cwd: scratch });
  execFileSync('git', ['add', '.'], { cwd: scratch });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: scratch });

  const report = lintRepoProject({ root: scratch });
  assert.equal(report.ok, true, 'native-only-contract-incomplete defaults to advisory warn');
  assert.equal(report.findings.filter(f => f.code === 'native-only-contract-incomplete').length, 1);
  assert.equal(report.findings.find(f => f.code === 'native-only-contract-incomplete').path, 'prompts/stub.prompt.md');
});

test('3574 reopened: lintNativeOnlyPortParity recognizes exported <stem>.<op> operations from linked checkable prompts while still failing fake/typo ports with 4-part remediation', () => {
  const accessPrompt = [
    '# Remote MCP connector access',
    '',
    '## Public operations',
    '',
    '### invoke_tool',
    'Runs read-only MCP tool.',
    '',
    '### redeem_view',
    'Redeems authenticated view.',
    '',
    '## Ports',
    '- `tokens.verify`',
    '- `audit_log.append`',
    '',
    '## Dependencies',
    'None.',
  ].join('\n');

  const governancePrompt = [
    '# Remote MCP connector governance',
    '',
    '## Public operations',
    '',
    '### `register_client`',
    'Registers OAuth client.',
    '',
    '### manage_grant and rotate_token',
    'Issues, revokes, and rotates grants.',
    '',
    '## Ports',
    '- `grant_store.save`',
    '',
    '## Dependencies',
    'None.',
  ].join('\n');

  const interimPrompt = [
    '# Interim authority',
    '',
    '## Operations',
    '',
    '`activate_interim_authority` and `reauthorize_interim_authority` take `{ issuer_id }`.',
    '',
    '## Dependencies',
    'None.',
  ].join('\n');

  const embeddedEntriesPrompt = [
    '# Vendor CLI',
    '',
    'Export `run_vendor_cli(argv)`.',
    '',
    '<details><summary>Runtime interface</summary>',
    '```json',
    JSON.stringify({ entries: [{ name: 'main' }] }),
    '```',
    '</details>',
  ].join('\n');

  const deps = [
    { path: 'prompts/connector/access.prompt.md', text: accessPrompt, isPrompt: true },
    { path: 'prompts/connector/governance.prompt.md', text: governancePrompt, isPrompt: true },
    { path: 'prompts/continuity/interim-authority.prompt.md', text: interimPrompt, isPrompt: true },
    { path: 'prompts/cli/vendor-cli.prompt.md', text: embeddedEntriesPrompt, isPrompt: true },
  ];

  const validServerPrompt = [
    '---',
    'kind: native-only',
    'reason: HTTPS remote MCP transport and OAuth token plumbing.',
    '---',
    '',
    '# Remote MCP connector server adapter',
    '',
    'Route MCP calls to `access.invoke_tool` and browser redemptions to `access.redeem_view`.',
    '',
    '## Port wiring',
    '- Wire `access.invoke_tool` and `access.redeem_view` to `tokens.verify` and `audit_log.append`.',
    '- Invoke `governance.register_client`, `governance.manage_grant`, and `governance.rotate_token` wired to `grant_store.save`.',
    '- Route authority checks through `interim-authority.activate_interim_authority` and `interim_authority.reauthorize_interim_authority`.',
    '- Dispatch CLI calls to `vendor-cli.main` and `vendor_cli.run_vendor_cli`.',
    '',
    '## Dependencies',
    '- [access](access.prompt.md)',
    '- [governance](governance.prompt.md)',
    '- [interim](../continuity/interim-authority.prompt.md)',
    '- [vendor-cli](../cli/vendor-cli.prompt.md)',
  ].join('\n');

  assert.deepEqual(
    lintNativeOnlyPortParity(validServerPrompt, deps, { path: 'prompts/connector/mcp-server.prompt.md' }),
    [],
    'exported <stem>.<op> operations across all declaration forms must pass with 0 errors',
  );

  // Negative control: typo on exported op + completely undeclared port MUST fail with 4-part remediation.
  const brokenServerPrompt = validServerPrompt
    .replace('`access.invoke_tool`', '`access.invoke_tools`')
    .replace('`grant_store.save`', '`phantom_store.save`');
  const negErrors = lintNativeOnlyPortParity(brokenServerPrompt, deps, { path: 'prompts/connector/mcp-server.prompt.md' });
  assert.equal(negErrors.length, 2, negErrors.join('\n'));
  assert.match(negErrors[0], /prompts\/connector\/mcp-server\.prompt\.md:8 \[native-only-unknown-port\].*"access\.invoke_tools"/);
  assert.match(negErrors[0], /access\.invoke_tool/);
  assert.match(negErrors[0], /Fix: declare "access\.invoke_tools".*pdd lint/);
  assert.match(negErrors[1], /prompts\/connector\/mcp-server\.prompt\.md:12 \[native-only-unknown-port\].*"phantom_store\.save"/);
  assert.match(negErrors[1], /Fix: declare "phantom_store\.save".*pdd lint/);
});

test('3562 polling FP fix: test-fixed-sleep exempts waitFor/until polling helpers, bounded retry loops, and Promise.race watchdogs while still flagging bare unguarded sleeps', () => {
  const safePollingJs = [
    "import { setTimeout } from 'node:timers/promises';",
    'const until = async (check, ms = 5000) => {',
    '  const deadline = Date.now() + ms;',
    '  while (Date.now() < deadline) {',
    '    const val = check();',
    '    if (val) return val;',
    '    await new Promise(r => setTimeout(r, 25));',
    '  }',
    '  throw new Error("timeout");',
    '};',
    'async function waitForFile(path) {',
    '  for (let i = 0; i < 100; i++) {',
    '    if (exists(path)) return true;',
    '    await sleep(10);',
    '  }',
    '  return false;',
    '}',
    "test('polling and retry backoff loops', async () => {",
    '  const end = Date.now() + 5000;',
    '  while (Date.now() < end && !ready()) await new Promise(r => setTimeout(r, 20));',
    '  while (!stopped() && performance.now() < end) await setTimeout(10);',
    '  for (let i = 0; i < 20 && !isReady(); i++) await new Promise(r => setTimeout(r, 15));',
    '  for (;;) {',
    '    try { readReady(); break; } catch { await new Promise(r => setTimeout(r, 5)); }',
    '  }',
    '  for (const delayMs of [10, 20, 40]) {',
    '    if (checkDone()) break;',
    '    await new Promise(r => setTimeout(r, 15));',
    '  }',
    '  await Promise.race([pendingOp(), new Promise(resolve => setTimeout(() => resolve(null), 5000))]);',
    '  void until; void waitForFile;',
    '});',
  ].join('\n');
  assert.deepEqual(
    lintTestFixedSleeps(safePollingJs, { path: 'test/polling-safe.test.mjs' }),
    [],
    'legitimate polling helpers, bounded retry loops, and Promise.race watchdogs must emit 0 warnings',
  );

  const safePollingPy = [
    'import time',
    'def wait_for_ready(check):',
    '    deadline = time.time() + 5',
    '    while time.time() < deadline:',
    '        if check():',
    '            return True',
    '        time.sleep(0.05)',
    '    return False',
    'def test_retry_loop():',
    '    for _ in range(10):',
    '        try:',
    '            probe()',
    '            break',
    '        except RuntimeError:',
    '            time.sleep(0.02)',
  ].join('\n');
  assert.deepEqual(
    lintTestFixedSleeps(safePollingPy, { path: 'tests/test_polling_safe.py' }),
    [],
    'Python polling and bounded retry loops must emit 0 warnings',
  );

  // Bare unguarded sleeps (including inside data-driven test loops or unconditional loops) MUST STILL FAIL!
  const badUnguardedJs = [
    "test('bare sleep', async () => {",
    '  await new Promise(r => setTimeout(r, 200));',
    '  await sleep(150);',
    '  for (let i = 0; i < 3; i++) { await sleep(50); }',
    '  while (true) { await sleep(50); }',
    '});',
    'for (const size of [1, 2]) {',
    "  test('data loop with bare sleep', async () => {",
    '    await new Promise(r => setTimeout(r, 30));',
    '  });',
    '}',
  ].join('\n');
  const badWarnings = lintTestFixedSleeps(badUnguardedJs, { path: 'test/bare-sleeps.test.mjs' });
  assert.equal(badWarnings.length, 5, `expected 5 bare unguarded sleep warnings, got:\n${badWarnings.join('\n')}`);

  const badUnguardedPy = [
    'import time',
    'def test_bare_sleep():',
    '    time.sleep(0.5)',
    'def test_unconditional_for():',
    '    for _ in range(3):',
    '        time.sleep(0.1)',
  ].join('\n');
  const badPyWarnings = lintTestFixedSleeps(badUnguardedPy, { path: 'tests/test_bare_sleep.py' });
  assert.equal(badPyWarnings.length, 2, `expected 2 bare Python sleep warnings, got:\n${badPyWarnings.join('\n')}`);
});

test('3574 + 3562 cross-family review regressions (Astra #1-#4): strict export clauses, top-level-only bullets, Operations and ports, signature tails, polling classification, Promise.race arm isolation, and Python O(N)', () => {
  // #1 & #2: `Export \`read\` with the \`cursor\` field.` never exports `cursor`; indented sub-bullets never export;
  // `## Operations and ports` keeps BOTH exports and ports; paragraph-leading `read({ id }) -> { value }` extracts `read`.
  const combinedDep = [
    '# Record store',
    '',
    'Export `load_record` with the `cursor` field and `page_size` option.',
    '',
    '## Operations and ports',
    '',
    '`read({ id }) -> { value }`',
    '',
    '  - `list_items({ cursor }) -> { items }`: lists records.',
    '    - `cursor`: opaque pagination token.',
    '    - `limit`: max items per page.',
    '  - `store.fetch({ id })`: reads persisted record.',
    '',
    '### `search_records` with the `next_token` field',
    'Returns matching records.',
    '',
    '## Dependencies',
    'None.',
  ].join('\n');

  const adapterOk = [
    '---',
    'kind: native-only',
    'reason: Real SQLite adapter.',
    '---',
    '# Adapter',
    '## Port wiring',
    '- `records.load_record`',
    '- `records.read`',
    '- `records.list_items`',
    '- `records.search_records`',
    '- `store.fetch`',
    '## Dependencies',
    '- [records](records.prompt.md)',
  ].join('\n');
  assert.deepEqual(
    lintNativeOnlyPortParity(adapterOk, [{ path: 'prompts/records.prompt.md', text: combinedDep, isPrompt: true }], { path: 'prompts/adapter.prompt.md' }),
    [],
    'Operations and ports + 2-space top-level bullets + heading stop-before-prose + signature tails must all pass',
  );

  const adapterFieldSpoof = [
    '---',
    'kind: native-only',
    'reason: Real SQLite adapter.',
    '---',
    '# Adapter',
    '## Port wiring',
    '- `records.cursor`',
    '- `records.page_size`',
    '- `records.limit`',
    '- `records.next_token`',
    '## Dependencies',
    '- [records](records.prompt.md)',
  ].join('\n');
  const spoofErrors = lintNativeOnlyPortParity(adapterFieldSpoof, [{ path: 'prompts/records.prompt.md', text: combinedDep, isPrompt: true }], { path: 'prompts/adapter.prompt.md' });
  assert.equal(spoofErrors.length, 4, `field names in prose, sub-bullets, or headings must NEVER be accepted as exported ops:\n${spoofErrors.join('\n')}`);
  assert.match(spoofErrors[0], /"records\.cursor"/);
  assert.match(spoofErrors[1], /"records\.page_size"/);
  assert.match(spoofErrors[2], /"records\.limit"/);
  assert.match(spoofErrors[3], /"records\.next_token"/);

  // #3: Polling classification (state === PENDING exempt without `.`; data-draining while(rows.length){rows.pop()} flagged;
  // Promise.race ONLY exempts direct timeout arm, NEVER sleep inside sibling work callback!).
  const statePollJs = [
    "test('state polling without dot', async () => {",
    '  while (state === PENDING) { await sleep(10); }',
    '  do { await sleep(10); } while (status !== READY);',
    '});',
  ].join('\n');
  assert.deepEqual(lintTestFixedSleeps(statePollJs, { path: 'test/state-poll.test.mjs' }), []);

  const dataDrainAndRaceWorkJs = [
    "test('data drain, pure counters, and race chained work', async () => {",
    '  while (rows.length) { rows.pop(); await sleep(10); }',
    '  while (queue.length > 0) { queue.shift(); await new Promise(r => setTimeout(r, 10)); }',
    '  while (i !== limit) { i++; await sleep(10); }',
    '  for (let i = 0; i !== limit; i++) { await sleep(10); }',
    '  for (let i = 0; i !== batch.length; i++) { await sleep(10); }',
    '  await Promise.race([',
    '    (async () => { await sleep(500); return "work"; })(),',
    '    sleep(50).then(() => doWork()),',
    '    new Promise(resolve => setTimeout(() => resolve(null), 5000)),',
    '  ]);',
    '});',
  ].join('\n');
  const drainRaceWarnings = lintTestFixedSleeps(dataDrainAndRaceWorkJs, { path: 'test/drain-race.test.mjs' });
  assert.equal(drainRaceWarnings.length, 7, `expected 7 warnings (2 drains + 3 pure counters + sibling callback + chained .then arm, 0 on direct timeout arm), got:\n${drainRaceWarnings.join('\n')}`);
  assert.match(drainRaceWarnings[0], /:2 \[test-fixed-sleep\]/);
  assert.match(drainRaceWarnings[1], /:3 \[test-fixed-sleep\]/);
  assert.match(drainRaceWarnings[2], /:4 \[test-fixed-sleep\]/);
  assert.match(drainRaceWarnings[3], /:5 \[test-fixed-sleep\]/);
  assert.match(drainRaceWarnings[4], /:6 \[test-fixed-sleep\]/);
  assert.match(drainRaceWarnings[5], /:8 \[test-fixed-sleep\]/);
  assert.match(drainRaceWarnings[6], /:9 \[test-fixed-sleep\]/);

  // #3 & #4 Python: state == PENDING exempt (including tab-indented!), rows.pop() drain & pure counter flagged, and 4,000 sleeps inside 1 loop stay strictly O(N) (< 400ms)!
  const pyMixed = [
    'import time',
    'def test_py_poll_and_drain():',
    '    while state == PENDING:',
    '        time.sleep(0.05)',
    '    while rows:',
    '        rows.pop()',
    '        time.sleep(0.05)',
    '    while i != limit:',
    '        i += 1',
    '        time.sleep(0.05)',
    'def test_py_tab_indented():',
    '\twhile state == PENDING:',
    '\t\ttime.sleep(0.05)',
    '\twhile i != batch.size:',
    '\t\ti += 1',
    '\t\ttime.sleep(0.05)',
  ].join('\n');
  const pyMixedWarnings = lintTestFixedSleeps(pyMixed, { path: 'tests/test_py_mixed.py' });
  assert.equal(pyMixedWarnings.length, 3, `expected rows.pop() drain + 2 pure counters flagged (and tab-indented polling exempt), got:\n${pyMixedWarnings.join('\n')}`);
  assert.match(pyMixedWarnings[0], /:7 \[test-fixed-sleep\]/);
  assert.match(pyMixedWarnings[1], /:10 \[test-fixed-sleep\]/);
  assert.match(pyMixedWarnings[2], /:16 \[test-fixed-sleep\]/);

  const hugePyInOneLoop = `import time\ndef test_many_in_one_loop():\n    while i != limit:\n        i += 1\n${'        time.sleep(0.01)\n'.repeat(4000)}`;
  const t0 = performance.now();
  const hugePyWarnings = lintTestFixedSleeps(hugePyInOneLoop, { path: 'tests/test_many_sleeps.py' });
  const elapsedMs = performance.now() - t0;
  assert.equal(hugePyWarnings.length, 4000);
  assert.ok(elapsedMs < 400, `expected linear O(N) memoized scan on 4,000 Python sleeps inside 1 loop, took ${elapsedMs.toFixed(1)}ms`);
});
