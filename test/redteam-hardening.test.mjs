import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { chmodSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { lintNativeOnlyPortParity } from '../src/core/lint/native-port-parity.mjs';
import { extractFrontmatterPorts } from '../src/core/lint/prompt-metadata.mjs';
import { lintRepoProject } from '../src/core/lint/project-lint.mjs';
import { runLocalLint } from '../src/core/lint/run-local-lint.mjs';
import { analyzeDiffEntries, runDiffSpotlight } from '../src/core/lint/test-inventory.mjs';
import { auditProductPlan } from '../src/core/product/plan-audit.mjs';
import { resolveProductRepository } from '../src/core/product/github-state.mjs';
import { EXIT_FAILED, EXIT_NOT_PROVED, EXIT_PROVED, OUTCOME_FAILED, OUTCOME_NOT_PROVED, OUTCOME_PROVED, runProve } from '../src/core/prove.mjs';
import { inspectMultiPartIntegrationGuard } from '../src/core/verify-paths.mjs';
import { NO_TESTS as SEAM_NO_TESTS } from '../src/runtime-seam.mjs';
import { NO_TESTS as SEL_NO_TESTS } from '../src/test-selection.mjs';

function makeSink() {
  let text = '';
  return { write(s) { text += String(s); }, get text() { return text; } };
}

function initGitRepo(t, prefix, files = {}) {
  const dir = mkdtempSync(join(tmpdir(), prefix));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q', '-b', 'main'], { cwd: dir });
  execFileSync('git', ['config', 'user.name', 'Test'], { cwd: dir });
  execFileSync('git', ['config', 'user.email', 'test@example.com'], { cwd: dir });
  for (const [rel, content] of Object.entries(files)) {
    const abs = join(dir, rel);
    mkdirSync(dirname(abs), { recursive: true });
    writeFileSync(abs, content, 'utf8');
  }
  execFileSync('git', ['add', '-A'], { cwd: dir });
  execFileSync('git', ['commit', '-qm', 'base'], { cwd: dir });
  return dir;
}

function writeFiles(dir, files) {
  for (const [rel, content] of Object.entries(files)) {
    const abs = join(dir, rel);
    mkdirSync(dirname(abs), { recursive: true });
    writeFileSync(abs, content, 'utf8');
  }
}

const HELPERS_PROMPT = [
  '# Helpers',
  '',
  'Own `src/helpers.mjs`.',
  '',
  '## Public operations',
  '- `clamp(value, min, max)`: clamps value inclusively.',
  '',
  '## Dependencies',
  'None.',
].join('\n') + '\n';

test('Attack 6 (all 10 bypasses): YAML 1.2 zero-indent, Port Endpoint col, return-type call, post-colon bullet, SQL collision, JSON native-only, zero deps, non-contract docs, and base-trusted lint config', t => {
  const dep = [{ path: 'prompts/helpers.prompt.md', text: HELPERS_PROMPT, isPrompt: true }];

  // 1. YAML 1.2 zero-indented block list under ports:
  const zeroIndentPrompt = [
    '---',
    'kind: native-only',
    'reason: OS HSM secret minting.',
    'ports:',
    '- vault.mint_secret',
    '---',
    '# Vault',
    '## Dependencies',
    '- [helpers](helpers.prompt.md)',
  ].join('\n');
  assert.deepEqual(extractFrontmatterPorts(zeroIndentPrompt).map(p => p.port), ['vault.mint_secret']);
  const e1 = lintNativeOnlyPortParity(zeroIndentPrompt, dep, { path: 'prompts/vault.prompt.md' });
  assert.equal(e1.length, 1, e1.join('\n'));
  assert.match(e1[0], /"vault\.mint_secret"/);

  // 2. | Port Endpoint | column header is NOT dropped by TABLE_EXCL_COL_RE
  const tableColPrompt = [
    '---',
    'kind: native-only',
    'reason: OS HSM secret minting.',
    '---',
    '# Vault',
    '## Ports',
    '| Port Endpoint | Behavior |',
    '|---|---|',
    '| `vault.mint_secret` | Mints secret |',
    '## Dependencies',
    '- [helpers](helpers.prompt.md)',
  ].join('\n');
  const e2 = lintNativeOnlyPortParity(tableColPrompt, dep, { path: 'prompts/vault.prompt.md' });
  assert.equal(e2.length, 1, e2.join('\n'));
  assert.match(e2[0], /"vault\.mint_secret"/);

  // 3. Backticked call with return-type signature in ## Ports bullet
  const retSigPrompt = [
    '---',
    'kind: native-only',
    'reason: OS HSM secret minting.',
    '---',
    '# Vault',
    '## Ports',
    '- `vault.mint_secret(scope, ttlSeconds) -> { secret: string }`: mints secret.',
    '- `vault.rotate_key(id): Promise<void>`: rotates key.',
    '## Dependencies',
    '- [helpers](helpers.prompt.md)',
  ].join('\n');
  const e3 = lintNativeOnlyPortParity(retSigPrompt, dep, { path: 'prompts/vault.prompt.md' });
  assert.equal(e3.length, 2, e3.join('\n'));
  assert.ok(e3.some(x => x.includes('"vault.mint_secret"')));
  assert.ok(e3.some(x => x.includes('"vault.rotate_key"')));

  // 4. Post-delimiter backtick span inside ## Ports bullet
  const postDelimPrompt = [
    '---',
    'kind: native-only',
    'reason: OS HSM secret minting.',
    '---',
    '# Vault',
    '## Ports',
    '- `helpers.clamp`: bounds TTL before delegating issuance to `vault.mint_secret`.',
    '## Dependencies',
    '- [helpers](helpers.prompt.md)',
  ].join('\n');
  const e4 = lintNativeOnlyPortParity(postDelimPrompt, dep, { path: 'prompts/vault.prompt.md' });
  assert.equal(e4.length, 1, e4.join('\n'));
  assert.match(e4[0], /"vault\.mint_secret"/);

  // 5. SQL column collision MUST NEVER suppress frontmatter ports: or ## Ports entries
  const sqlCollisionPrompt = [
    '---',
    'kind: native-only',
    'reason: SQLite vault adapter.',
    'ports:',
    '  - vault.mint_secret',
    '---',
    '# Vault',
    '```sql',
    'CREATE TABLE vault (mint_secret TEXT NOT NULL, revoke_key TEXT NOT NULL);',
    '```',
    '## Ports',
    '- `vault.revoke_key`: revokes key.',
    '## Dependencies',
    '- [helpers](helpers.prompt.md)',
  ].join('\n');
  const e5 = lintNativeOnlyPortParity(sqlCollisionPrompt, dep, { path: 'prompts/vault.prompt.md' });
  assert.equal(e5.length, 2, e5.join('\n'));
  assert.ok(e5.some(x => x.includes('"vault.mint_secret"')));
  assert.ok(e5.some(x => x.includes('"vault.revoke_key"')));

  // 6. Runtime-interface JSON {"kind":"native-only"} without YAML frontmatter
  const jsonNativeOnlyPrompt = [
    '# Vault JSON native-only',
    '## Ports',
    '- `vault.mint_secret`: mints secret.',
    '## Dependencies',
    '- [helpers](helpers.prompt.md)',
    '<details><summary>Runtime interface</summary>',
    '```json',
    '{"kind":"native-only","reason":"OS HSM secret minting."}',
    '```',
    '</details>',
  ].join('\n');
  const e6 = lintNativeOnlyPortParity(jsonNativeOnlyPrompt, dep, { path: 'prompts/vault.prompt.md' });
  assert.equal(e6.length, 1, e6.join('\n'));
  assert.match(e6[0], /"vault\.mint_secret"/);

  // 7. Zero checkable dependencies (`## Dependencies\n\nNone.`) still catches explicit frontmatter/## Ports refs,
  //    while standalone prose-only native-only prompt has 0 false positives!
  const noDepsExplicit = [
    '---',
    'kind: native-only',
    'reason: Standalone vault.',
    'ports:',
    '- vault.mint_secret',
    '---',
    '# Vault',
    '## Ports',
    '- `vault.revoke_key`: revokes.',
    '## Dependencies',
    'None.',
  ].join('\n');
  const e7 = lintNativeOnlyPortParity(noDepsExplicit, [], { path: 'prompts/vault.prompt.md' });
  assert.equal(e7.length, 2, e7.join('\n'));
  const standaloneProse = '---\nkind: native-only\nreason: Standalone.\n---\n# Standalone\nCalls `custom.helper` in prose.\n## Dependencies\nNone.\n';
  assert.deepEqual(lintNativeOnlyPortParity(standaloneProse, [], { path: 'prompts/standalone.prompt.md' }), []);

  // 8 + 9 + 10 (integration in git repo): arbitrary docs/*.md cannot whitelist ports,
  // and working-tree pdd.json lint.disable / rules/lint/*.json cannot silence errors in lint --diff or prove!
  const nodeBin = JSON.stringify(process.execPath);
  const repo = initGitRepo(t, 'pdd-redteam-atk6-', {
    'package.json': JSON.stringify({ name: 'atk6', type: 'module', scripts: { test: `${nodeBin} -e "process.exit(0)"` } }),
    'pdd.json': JSON.stringify({ verify: { test: 'npm test', paths: [{ id: 'core', when: ['src/**'], run: 'npm test' }] } }),
    'prompts/helpers.prompt.md': HELPERS_PROMPT,
    'src/helpers.mjs': '// Prompt: prompts/helpers.prompt.md\nexport const clamp = x => x;\n',
  });
  execFileSync('git', ['checkout', '-q', '-b', 'attack'], { cwd: repo });

  // Bypass 8: link docs/vault-notes.md mentioning vault.mint_secret under ## Dependencies
  writeFiles(repo, {
    'docs/vault-notes.md': '# Notes\n\nMentions `vault.mint_secret`.\n',
    'prompts/vault.prompt.md': [
      '---',
      'kind: native-only',
      'reason: OS HSM secret minting.',
      '---',
      '# Vault',
      '## Ports',
      '- `vault.mint_secret`: mints secret.',
      '## Dependencies',
      '- [helpers](helpers.prompt.md)',
      '- [notes](../docs/vault-notes.md)',
    ].join('\n') + '\n',
  });
  const docRes = lintRepoProject({ root: repo });
  assert.equal(docRes.ok, false, 'docs/*.md must NOT whitelist undeclared ports');
  assert.ok(docRes.errors.some(e => e.includes('[native-only-unknown-port]') && e.includes('vault.mint_secret')));

  // Bypass 9/10: working-tree pdd.json lint.disable + rules/lint/disable.json MUST NOT silence error in lint --diff or prove!
  writeFiles(repo, {
    'pdd.json': JSON.stringify({
      verify: { test: 'npm test', paths: [{ id: 'core', when: ['src/**'], run: 'npm test' }] },
      lint: { disable: ['native-only-unknown-port'], rules: { 'native-only-unknown-port': 'off' } },
    }),
    'rules/lint/disable.json': JSON.stringify({ disable: ['native-only-unknown-port'] }),
  });
  const diffOut = makeSink(), diffErr = makeSink();
  const diffCode = runLocalLint({ cwd: repo, diff: 'main', json: true }, { stdout: diffOut, stderr: diffErr });
  assert.equal(diffCode, 1, 'working-tree lint.disable must NOT silence error in pdd lint --diff');
  const diffPayload = JSON.parse(diffOut.text);
  assert.ok(diffPayload.problems.some(p => p.includes('[native-only-unknown-port]')));
  assert.ok(diffPayload.warnings.some(w => w.includes('[lint-config-untrusted]')));

  const proveRes = runProve({ cwd: repo, base: 'main', json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(proveRes.exitCode, EXIT_FAILED);
  assert.equal(proveRes.outcome, OUTCOME_FAILED);
  assert.ok(proveRes.receipt.lint.errors.some(e => e.includes('[native-only-unknown-port]')));
  assert.ok(proveRes.receipt.notProvedReasons.some(r => r.includes('lint overrides')));
});

test('Attack 2 & Attack 1 Probe A: shadow node_modules/.bin/node fails closed, package.json scripts.test tamper -> Not proved, pdd.json/rules/lint in HARNESS_PATH, and assertionDrops/newSkips/removedTests -> Not proved', t => {
  const nodeBin = JSON.stringify(process.execPath);
  const repo = initGitRepo(t, 'pdd-redteam-atk2-', {
    '.gitignore': 'node_modules/\n',
    'package.json': JSON.stringify({ name: 'atk2', type: 'module', scripts: { test: `${nodeBin} --test test/app.test.mjs` } }),
    'pdd.json': JSON.stringify({ verify: { test: 'npm test', paths: [{ id: 'core', when: ['src/**'], run: 'npm test' }] } }),
    'src/app.mjs': 'export const add = (a, b) => a + b;\n',
    'test/app.test.mjs': [
      "import test from 'node:test';",
      "import assert from 'node:assert/strict';",
      "import { add } from '../src/app.mjs';",
      "test('adds', () => {",
      '  assert.equal(add(1, 2), 3);',
      '  assert.equal(add(2, 3), 5);',
      '});',
    ].join('\n') + '\n',
  });
  execFileSync('git', ['checkout', '-q', '-b', 'tamper'], { cwd: repo });

  // 1. Untracked gitignored node_modules/.bin/node shadows PATH -> FAIL CLOSED [diff-shadow-bin] (exit 1)!
  writeFiles(repo, { 'node_modules/.bin/node': '#!/bin/sh\nexit 0\n' });
  chmodSync(join(repo, 'node_modules/.bin/node'), 0o755);

  const shadowLint = runDiffSpotlight({ cwd: repo, baseRef: 'main' });
  assert.equal(shadowLint.ok, false);
  assert.ok(shadowLint.errors.some(e => e.code === 'diff-shadow-bin' && e.path === 'node_modules/.bin/node'));

  const shadowProve = runProve({ cwd: repo, base: 'main', json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(shadowProve.exitCode, EXIT_FAILED);
  assert.equal(shadowProve.outcome, OUTCOME_FAILED);
  assert.equal(shadowProve.receipt.test, null, 'must fail closed before executing shadowed test command');
  assert.ok(shadowProve.receipt.diff.errors.some(e => e.includes('[diff-shadow-bin]')));
  rmSync(join(repo, 'node_modules'), { recursive: true, force: true });

  // 2. Tampering package.json scripts.test = "true" -> Not proved (exit 3), NEVER Proved!
  writeFiles(repo, {
    'package.json': JSON.stringify({ name: 'atk2', type: 'module', scripts: { test: 'true' } }),
    'src/app.mjs': 'export const add = (a, b) => a - b;\n',
  });
  const pkgProve = runProve({ cwd: repo, base: 'main', json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(pkgProve.exitCode, EXIT_NOT_PROVED);
  assert.equal(pkgProve.outcome, OUTCOME_NOT_PROVED);
  assert.ok(pkgProve.receipt.notProvedReasons.some(r => r.includes('package.json test scripts')));

  // Restore package.json and src/app.mjs.
  execFileSync('git', ['checkout', '--', 'package.json', 'src/app.mjs'], { cwd: repo });

  // 3. pdd.json and rules/lint/*.json trigger harnessEdits advisory in runDiffSpotlight
  writeFiles(repo, { 'rules/lint/custom.json': JSON.stringify({ custom_rules: [] }) });
  const harnessDiff = runDiffSpotlight({ cwd: repo, baseRef: 'main' });
  assert.ok(harnessDiff.harnessEdits.includes('rules/lint/custom.json'));
  rmSync(join(repo, 'rules'), { recursive: true, force: true });

  // 4. Attack 1 Probe A: dropping an assertion in kept test (2 -> 1) prevents silent Proved!
  writeFiles(repo, {
    'test/app.test.mjs': [
      "import test from 'node:test';",
      "import assert from 'node:assert/strict';",
      "import { add } from '../src/app.mjs';",
      "test('adds', () => {",
      '  assert.equal(add(1, 2), 3);',
      '});',
    ].join('\n') + '\n',
  });
  const dropProve = runProve({ cwd: repo, base: 'main', json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(dropProve.exitCode, EXIT_NOT_PROVED);
  assert.equal(dropProve.outcome, OUTCOME_NOT_PROVED);
  assert.ok(dropProve.receipt.notProvedReasons.some(r => r.includes('[diff-assertion-drops]')));
});

test('Attack 5: fail-closed multi-part plan/map aliases, unparseable plan/boundaries, and prove blocks unwired boundaries', t => {
  const nodeBin = JSON.stringify(process.execPath);
  const mapBullets = [
    '# ShopFlow: map',
    '',
    '## Parts',
    '- **pricing** (`src/pricing`): Pricing service.',
    '- **checkout** (`src/checkout`): Checkout service.',
  ].join('\n') + '\n';
  const planAliases = [
    '# ShopFlow: plan',
    '',
    '## Boundaries',
    '| Consumer | Provider | Interface | Contract |',
    '|---|---|---|---|',
    '| checkout | pricing | pricing/pricing.quote | contracts/pricing.md |',
    '',
    '## Runs',
    '| Run | Service | Slice | Stories | Needs |',
    '|---|---|---|---|---|',
    '| run-pricing | pricing | 1 | S1 | - |',
    '| run-checkout | checkout | 1 | S2 | run-pricing |',
  ].join('\n') + '\n';

  // 1. Bullet ## Parts + Consumer/Provider/Interface + Service columns parse >=2 parts AND detect unwired boundary!
  const repo = initGitRepo(t, 'pdd-redteam-atk5-', {
    'package.json': JSON.stringify({ name: 'atk5', type: 'module', scripts: { test: `${nodeBin} -e "process.exit(0)"` } }),
    'pdd.json': JSON.stringify({ verify: { test: 'npm test', paths: [{ id: 'core', when: ['src/**'], run: 'npm test' }] } }),
    'contracts/pricing.md': '# Pricing contract\n',
    'product/map.md': mapBullets,
    'product/plan.md': planAliases,
    'prompts/pricing.prompt.md': '# Pricing\n\nOwn `src/pricing/service.mjs`.\n\n## Dependencies\nNone.\n',
    'prompts/checkout.prompt.md': '# Checkout\n\nOwn `src/checkout/service.mjs`.\n\n## Dependencies\nNone.\n',
    'src/pricing/service.mjs': '// Prompt: prompts/pricing.prompt.md\nexport const quote = () => 1;\n',
    'src/checkout/service.mjs': '// Prompt: prompts/checkout.prompt.md\nexport const placeOrder = () => 1;\n',
  });
  execFileSync('git', ['checkout', '-q', '-b', 'silo'], { cwd: repo });
  writeFiles(repo, { 'src/checkout/service.mjs': '// Prompt: prompts/checkout.prompt.md\nexport const placeOrder = () => 2;\n' });

  const guard = inspectMultiPartIntegrationGuard(repo, { paths: [{ id: 'core', when: ['src/**'], run: 'npm test' }] });
  assert.equal(guard.applicable, true);
  assert.equal(guard.covered, false);
  assert.deepEqual(guard.parts, ['checkout', 'pricing']);
  assert.match(guard.reason, /\[multi-part-integration-missing\]/);

  const audit = auditProductPlan({
    mapText: mapBullets,
    planText: planAliases,
    promptFiles: [
      { path: 'prompts/pricing.prompt.md', content: readFileSync(join(repo, 'prompts/pricing.prompt.md'), 'utf8') },
      { path: 'prompts/checkout.prompt.md', content: readFileSync(join(repo, 'prompts/checkout.prompt.md'), 'utf8') },
    ],
  });
  assert.equal(audit.unwiredBoundaries.length, 1);

  const pv = runProve({ cwd: repo, base: 'main', json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(pv.exitCode, EXIT_NOT_PROVED);
  assert.equal(pv.outcome, OUTCOME_NOT_PROVED);
  assert.ok(pv.receipt.notProvedReasons.some(r => r.includes('[multi-part-integration-missing]')));
  assert.ok(pv.receipt.notProvedReasons.some(r => r.includes('[product-boundary-unwired]')));

  // 2. Unparseable ## Boundaries table emits [product-boundaries-unparseable] and unparseable multi-part plan fails closed!
  const garbagePlan = '# ShopFlow: plan\n\n## Boundaries\n| Alpha | Beta | Gamma |\n|---|---|---|\n| a | b | c |\n';
  const garbageAudit = auditProductPlan({ mapText: '# ShopFlow: map\n', planText: garbagePlan, promptFiles: [] });
  assert.ok(garbageAudit.findings.some(f => f.code === 'product-boundaries-unparseable'));

  writeFiles(repo, { 'product/map.md': '# ShopFlow: map\n\nProse only.\n', 'product/plan.md': garbagePlan });
  const unparseableGuard = inspectMultiPartIntegrationGuard(repo, { paths: [] });
  assert.equal(unparseableGuard.applicable, true);
  assert.equal(unparseableGuard.covered, false);
  assert.match(unparseableGuard.reason, /\[multi-part-plan-unparseable\]/);
});

test('Attack 4: mock-only I/O & subprocess boundary tests flagged in Core diff & prove while real unmocked boundary tests pass cleanly', t => {
  const nodeBin = JSON.stringify(process.execPath);
  const repo = initGitRepo(t, 'pdd-redteam-atk4-', {
    'package.json': JSON.stringify({ name: 'atk4', type: 'module', scripts: { test: `${nodeBin} --test test/*.test.mjs` } }),
    'pdd.json': JSON.stringify({ verify: { test: 'npm test', paths: [{ id: 'core', when: ['src/**'], run: 'npm test' }] } }),
    'src/helpers.mjs': 'export const ok = () => true;\n',
    'test/helpers.test.mjs': "import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { ok } from '../src/helpers.mjs';\ntest('ok', () => assert.equal(ok(), true));\n",
  });
  execFileSync('git', ['checkout', '-q', '-b', 'mock-only'], { cwd: repo });

  writeFiles(repo, {
    'src/http-cli.mjs': "import http from 'node:http';\nimport { spawn } from 'node:child_process';\nexport const start = () => http.createServer((_req, res) => res.end('ok'));\nexport const run = () => spawn('echo', ['hi']);\n",
    'test/http-cli.test.mjs': [
      "import test from 'node:test';",
      "import assert from 'node:assert/strict';",
      "const vi = { mock() {}, fn: f => f };",
      "vi.mock('node:child_process', () => ({ spawn: () => ({}) }));",
      "const mockFetch = async () => ({ ok: true });",
      "test('mocked only', () => { assert.ok(mockFetch); });",
    ].join('\n') + '\n',
  });
  const pvMockOnly = runProve({ cwd: repo, base: 'main', json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(pvMockOnly.exitCode, EXIT_NOT_PROVED);
  assert.equal(pvMockOnly.outcome, OUTCOME_NOT_PROVED);
  assert.ok(pvMockOnly.receipt.notProvedReasons.some(r => r.includes('[diff-mock-only-boundary]')));

  // Adding a real unmocked subprocess test clears the mock-only warning and proves cleanly!
  writeFiles(repo, {
    'test/http-cli-real.test.mjs': [
      "import test from 'node:test';",
      "import assert from 'node:assert/strict';",
      "import { spawnSync } from 'node:child_process';",
      "test('real subprocess', () => {",
      "  const res = spawnSync(process.execPath, ['-e', 'process.exit(0)']);",
      '  assert.equal(res.status, 0);',
      '});',
    ].join('\n') + '\n',
  });
  const pvReal = runProve({ cwd: repo, base: 'main', json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(pvReal.exitCode, EXIT_PROVED, JSON.stringify(pvReal.receipt));
  assert.equal(pvReal.outcome, OUTCOME_PROVED);

  // Pure unit diff without boundary primitives never triggers mockOnlyBoundaryTests.
  const pureDiff = analyzeDiffEntries([
    { oldPath: '', newPath: 'src/math.mjs', before: '', after: 'export const double = x => x * 2;\n' },
    { oldPath: '', newPath: 'test/math.test.mjs', before: '', after: "import test from 'node:test';\nconst mockFetch = () => {};\ntest('double', () => {});\n" },
  ]);
  assert.deepEqual(pureDiff.mockOnlyBoundaryTests, []);
});

test('Attack 3: Story with unbound acceptance criteria in paired runtime JSON fires [story-unbound-criteria] and blocks prove on touched Story', t => {
  const nodeBin = JSON.stringify(process.execPath);
  const repo = initGitRepo(t, 'pdd-redteam-atk3-', {
    'package.json': JSON.stringify({ name: 'atk3', type: 'module', scripts: { test: `${nodeBin} -e "process.exit(0)"` } }),
    'pdd.json': JSON.stringify({ verify: { test: 'npm test', paths: [{ id: 'core', when: ['src/**'], run: 'npm test' }] } }),
    'prompts/helpers.prompt.md': HELPERS_PROMPT,
    'src/helpers.mjs': '// Prompt: prompts/helpers.prompt.md\nexport const clamp = (v, lo, hi) => Math.min(Math.max(v, lo), hi);\n',
  });
  execFileSync('git', ['checkout', '-q', '-b', 'unbound-ac'], { cwd: repo });

  writeFiles(repo, {
    'user_stories/clamp-zero.md': [
      '# Clamp zero ceiling',
      '',
      'As a developer, I want clamp to honor a zero upper bound and reject inverted limits.',
      '',
      '## Acceptance criteria',
      '',
      '1. Clamping 5 between -10 and 0 returns 0.',
      '2. Clamping -15 between -10 and 0 returns -10.',
      '3. Clamping 5 between 10 and 0 returns an "invalid_range" error.',
    ].join('\n') + '\n',
    'test/runtime/clamp-zero.json': JSON.stringify({
      entry_path: 'prompts/helpers.prompt.md',
      steps: [
        { id: 's1', op: 'clamp', input: { value: 5, min: -10, max: 0 }, checks: { '1': [['result', '/value', '=', 0]] } },
        { id: 's2', op: 'clamp', input: { value: -15, min: -10, max: 0 }, checks: { '2': [['result', '/value', '=', -10]] } },
      ],
    }, null, 2) + '\n',
  });

  const lintRes = lintRepoProject({ root: repo });
  assert.ok(lintRes.findings.some(f => f.code === 'story-unbound-criteria' && f.message.includes('#3')));

  const pvUnbound = runProve({ cwd: repo, base: 'main', json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(pvUnbound.exitCode, EXIT_NOT_PROVED);
  assert.equal(pvUnbound.outcome, OUTCOME_NOT_PROVED);
  assert.ok(pvUnbound.receipt.notProvedReasons.some(r => r.includes('[story-unbound-criteria]')));

  // Covering AC #3 clears [story-unbound-criteria] and proves cleanly!
  writeFiles(repo, {
    'test/runtime/clamp-zero.json': JSON.stringify({
      entry_path: 'prompts/helpers.prompt.md',
      steps: [
        { id: 's1', op: 'clamp', input: { value: 5, min: -10, max: 0 }, checks: { '1': [['result', '/value', '=', 0]] } },
        { id: 's2', op: 'clamp', input: { value: -15, min: -10, max: 0 }, checks: { '2': [['result', '/value', '=', -10]] } },
        { id: 's3', op: 'clamp', input: { value: 5, min: 10, max: 0 }, checks: { '3': [['error', '=', 'invalid_range']] } },
      ],
    }, null, 2) + '\n',
  });
  const pvBound = runProve({ cwd: repo, base: 'main', json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(pvBound.exitCode, EXIT_PROVED, JSON.stringify(pvBound.receipt));
  assert.equal(pvBound.outcome, OUTCOME_PROVED);
});

test('Dogfood fixes: no stale RUNBOOK.md in NO_TESTS and actionable error when git origin remote is missing', async t => {
  assert.equal(SEAM_NO_TESTS, SEL_NO_TESTS);
  assert.equal(SEAM_NO_TESTS.includes('RUNBOOK.md'), false);
  assert.match(SEAM_NO_TESTS, /skills\/pdd\/references\/stories\.md/);

  const noRemoteRepo = initGitRepo(t, 'pdd-no-origin-', { 'README.md': '# Local only\n' });
  await assert.rejects(
    resolveProductRepository({ cwd: noRemoteRepo }),
    err => err.message.includes('No Git "origin" remote configured in this repository') && !err.message.includes('Could not run git'),
  );
});
