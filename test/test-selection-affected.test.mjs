import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import {
  classifyGlobalSuiteTrigger,
  formatAffectedTestsSummary,
  isRunnableTestPath,
  selectAffectedTests,
} from '../src/test-selection.mjs';
import {
  proveAffectedRun,
  resolveVerifyPlan,
  validateProofRecord,
  verifyAffected,
} from '../src/workflow-prove.mjs';
import { runOwner } from '../src/file-owner.mjs';
import { promptRefusal, runtimePreflightSlice } from '../src/runtime-seam.mjs';

const { gitFiles, readPrompt } = runtimePreflightSlice();

function virtualPorts(fileMap, changedFiles) {
  const files = Object.keys(fileMap).sort();
  return {
    options: {
      root: '/virtual-repo',
      files,
      ...(changedFiles !== undefined ? { changedFiles } : {}),
    },
    ports: {
      listFiles: () => files,
      readFile: relPath => (Object.hasOwn(fileMap, relPath) ? fileMap[relPath] : null),
      readChangedFiles: () => changedFiles ?? null,
    },
  };
}

function makeGitFixture(t) {
  const parent = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-affected-3065-')));
  const root = join(parent, 'repo');
  const bare = join(parent, 'origin.git');
  mkdirSync(root, { recursive: true });
  t.after(() => rmSync(parent, { recursive: true, force: true }));

  const git = (...args) =>
    execFileSync('git', args, { cwd: root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }).trim();
  const put = (relPath, text) => {
    const abs = join(root, relPath);
    mkdirSync(dirname(abs), { recursive: true });
    writeFileSync(abs, text);
  };

  git('init', '--bare', '-q', bare);
  git('init', '-qb', 'main');
  git('config', 'user.name', 'Affected Test');
  git('config', 'user.email', 'affected@example.invalid');
  git('remote', 'add', 'origin', bare);

  put('package.json', JSON.stringify({ name: 'sample-pkg', type: 'module', scripts: { test: 'node --test test/*.test.mjs' } }, null, 2));
  put('src/calc.mjs', 'export const add = (a, b) => a - b;\n');
  put('src/billing.mjs', "import { add } from './calc.mjs';\nexport const invoiceTotal = (a, b) => add(a, b);\n");
  put('src/unrelated.mjs', 'export const untouched = () => 42;\n');
  put(
    'test/billing.test.mjs',
    "import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { invoiceTotal } from '../src/billing.mjs';\ntest('invoice sum', () => assert.equal(invoiceTotal(2, 3), 5, 'DEFECT_CALC_3065'));\n",
  );
  put(
    'test/unrelated.test.mjs',
    "import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { untouched } from '../src/unrelated.mjs';\ntest('untouched suite check', () => assert.equal(untouched(), 42));\n",
  );

  git('add', '.');
  git('commit', '-qm', 'base');
  git('push', '-q', 'origin', 'main');
  const baseSha = git('rev-parse', 'HEAD');
  git('switch', '-qc', 'topic');

  const runDir = join(root, '.git/pdd/runs/3065');
  mkdirSync(runDir, { recursive: true });
  writeFileSync(
    join(runDir, 'status.json'),
    JSON.stringify({ v: 1, number: 3065, runId: 'run-3065', root, runDir, baseBranch: 'main', baseSha }),
  );

  return { root, runDir, baseSha, git, put };
}

test('3065 isRunnableTestPath identifies runnable test entries and excludes helpers, fixtures, and src', () => {
  assert.equal(isRunnableTestPath('test/order.test.mjs'), true);
  assert.equal(isRunnableTestPath('tests/unit/order.spec.ts'), true);
  assert.equal(isRunnableTestPath('test/workflow-prove.vectors.test.mjs'), true);
  assert.equal(isRunnableTestPath('./test/order.test.js'), true);

  assert.equal(isRunnableTestPath('test/helpers/test-home.mjs'), false);
  assert.equal(isRunnableTestPath('test/helpers/fake.test.mjs'), false);
  assert.equal(isRunnableTestPath('test/fixtures/sample.test.mjs'), false);
  assert.equal(isRunnableTestPath('src/order.test.mjs'), false);
  assert.equal(isRunnableTestPath('node_modules/pkg/index.test.js'), false);
  assert.equal(isRunnableTestPath('tests/place-order.json'), false);
  assert.equal(isRunnableTestPath('../test/escape.test.mjs'), false);
});

test('3065 selectAffectedTests resolves multi-hop reverse imports, stem variants, deleted modules, and ignores comments/string literals', () => {
  const repo = {
    'src/math_core.mjs': 'export function cents(n) { return n * 100; }\n',
    'src/tax.mjs': "import { cents } from './math_core.mjs';\nexport const withTax = n => cents(n) + 10;\n",
    'src/checkout.mjs': "export { withTax } from './tax.mjs';\n",
    'src/unrelated.mjs': [
      "// import { cents } from './math_core.mjs';",
      "/* import './tax.mjs' */",
      'const sample = "import { cents } from \'./math_core.mjs\'";',
      'export const keep = () => sample;',
    ].join('\n'),
    'test/local-checkout-helper.mjs': "import { withTax } from '../src/checkout.mjs';\nexport const checkTax = withTax;\n",
    'test/math-core.test.mjs': "import test from 'node:test';\ntest('stem match', () => {});\n",
    'test/checkout-flow.test.mjs': "import { checkTax } from './local-checkout-helper.mjs';\n",
    'test/dynamic-import.test.mjs': "const mod = await import('../src/tax.mjs');\n",
    'test/legacy-deleted.test.mjs': "import { oldFn } from '../src/deleted-legacy.mjs';\n",
    'test/unrelated.test.mjs': "import { keep } from '../src/unrelated.mjs';\n",
  };

  // 1. Multi-hop src -> src -> local test helper -> test + underscore/hyphen stem match
  const v1 = virtualPorts(repo, ['src/math_core.mjs']);
  const res1 = selectAffectedTests(v1.options, v1.ports);
  assert.equal(res1.mode, 'affected');
  assert.equal(res1.fallbackReason, null);
  assert.equal(res1.totalCount, 5);
  assert.deepEqual(res1.selectedTests, [
    'test/checkout-flow.test.mjs',
    'test/dynamic-import.test.mjs',
    'test/math-core.test.mjs',
  ]);
  assert.equal(res1.selectedCount, 3);
  assert.match(res1.summary, /Affected tests: selected 3 of 5 test files/);

  // 2. Deleted module still selects existing importers; deleted test file is excluded from runner args
  const v2 = virtualPorts(repo, ['src/deleted-legacy.mjs', 'test/removed-file.test.mjs']);
  const res2 = selectAffectedTests(v2.options, v2.ports);
  assert.equal(res2.mode, 'affected');
  assert.deepEqual(res2.selectedTests, ['test/legacy-deleted.test.mjs']);
  assert.equal(res2.selectedCount, 1);
});

test('3065 dispatcher hubs bound unrelated fan-out while bridging re-exported symbols to consuming tests', () => {
  const deps = Object.fromEntries(
    Array.from({ length: 12 }, (_, idx) => [`src/mod-${idx}.mjs`, `export const fn${idx} = () => ${idx};\n`]),
  );
  const hubImports = Array.from({ length: 12 }, (_, idx) => `import { fn${idx} } from './mod-${idx}.mjs';`).join('\n');
  const repo = {
    ...deps,
    'src/hub.mjs': `${hubImports}\nexport { fn0 };\nexport const runHub = () => fn1();\n`,
    'test/uses-reexport.test.mjs': "import { fn0 } from '../src/hub.mjs';\n",
    'test/uses-hub-only.test.mjs': "import { runHub } from '../src/hub.mjs';\n",
    'test/mod-1-direct.test.mjs': "import { fn1 } from '../src/mod-1.mjs';\n",
  };

  // Editing mod-0 bridges re-exported fn0 through hub.mjs to uses-reexport.test.mjs without pulling uses-hub-only.test.mjs
  const v0 = virtualPorts(repo, ['src/mod-0.mjs']);
  const r0 = selectAffectedTests(v0.options, v0.ports);
  assert.deepEqual(r0.selectedTests, ['test/uses-reexport.test.mjs']);

  // Editing mod-1 selects its direct test without fanning out to unrelated hub tests
  const v1 = virtualPorts(repo, ['src/mod-1.mjs']);
  const r1 = selectAffectedTests(v1.options, v1.ports);
  assert.deepEqual(r1.selectedTests, ['test/mod-1-direct.test.mjs']);

  // Editing hub.mjs directly selects all tests importing hub.mjs
  const vHub = virtualPorts(repo, ['src/hub.mjs']);
  const rHub = selectAffectedTests(vHub.options, vHub.ports);
  assert.deepEqual(rHub.selectedTests, ['test/uses-hub-only.test.mjs', 'test/uses-reexport.test.mjs']);
});

test('3065 prompts, Stories, docs, and skills select owned dependents, scenario tests, and contract suites without global fallback', () => {
  const repo = {
    'prompts/cli/invoice.prompt.md': '# Invoice\n\nOwn `src/invoice-engine.mjs`.\n',
    'src/invoice-engine.mjs': '// Prompt: prompts/cli/invoice.prompt.md\nexport const makeInvoice = () => ({ ok: true });\n',
    'user_stories/pay-invoice.md': '# Pay invoice\n\n## Acceptance criteria\n\n1. Pays invoice.\n',
    'test/runtime/pay-invoice.json': JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/pay-invoice.md',
      steps: [{ step_id: 's1', entry_path: 'prompts/cli/invoice.prompt.md', operation: 'makeInvoice' }],
    }),
    'docs/cli.md': '# CLI Reference\n',
    'skills/pdd-bug/SKILL.md': '---\nname: pdd-bug\ndescription: Use when fixing bugs.\n---\n',
    'test/invoice-engine-unit.test.mjs': "import { makeInvoice } from '../src/invoice-engine.mjs';\n",
    'test/pay-invoice.vectors.test.mjs': 'export const replay = true;\n',
    'test/plain-prompts-and-frontmatter.test.mjs': 'export const promptContract = true;\n',
    'test/repo-hygiene-lint.test.mjs': 'export const hygieneContract = true;\n',
    'test/story-quality-lint.test.mjs': 'export const storyContract = true;\n',
    'test/docs-commands.test.mjs': "const doc = new URL('../docs/cli.md', import.meta.url);\n",
    'test/skills.test.mjs': "const skill = 'skills/pdd-bug/SKILL.md';\n",
    'test/skill-frontmatter.test.mjs': 'export const skillFrontmatter = true;\n',
    'test/autopilot-smoke.test.mjs': 'export const smoke = true;\n',
    'test/completely-unrelated.test.mjs': 'export const unrelated = true;\n',
  };

  // Prompt change -> owned src reverse-import test + scenario vector test + prompt contract tests + optional smoke
  const vp = virtualPorts(repo, ['prompts/cli/invoice.prompt.md']);
  const rp = selectAffectedTests({ ...vp.options, smokeTests: ['test/autopilot-smoke.test.mjs'] }, vp.ports);
  assert.equal(rp.mode, 'affected');
  assert.ok(rp.selectedTests.includes('test/invoice-engine-unit.test.mjs'));
  assert.ok(rp.selectedTests.includes('test/pay-invoice.vectors.test.mjs'));
  assert.ok(rp.selectedTests.includes('test/plain-prompts-and-frontmatter.test.mjs'));
  assert.ok(rp.selectedTests.includes('test/repo-hygiene-lint.test.mjs'));
  assert.ok(rp.selectedTests.includes('test/autopilot-smoke.test.mjs'));
  assert.equal(rp.selectedTests.includes('test/completely-unrelated.test.mjs'), false);

  // Story change -> Story vector test + Story contract tests
  const vs = virtualPorts(repo, ['user_stories/pay-invoice.md']);
  const rs = selectAffectedTests(vs.options, vs.ports);
  assert.equal(rs.mode, 'affected');
  assert.ok(rs.selectedTests.includes('test/pay-invoice.vectors.test.mjs'));
  assert.ok(rs.selectedTests.includes('test/story-quality-lint.test.mjs'));
  assert.equal(rs.selectedTests.includes('test/completely-unrelated.test.mjs'), false);

  // Docs change -> docs contract tests + referencing tests
  const vd = virtualPorts(repo, ['docs/cli.md']);
  const rd = selectAffectedTests(vd.options, vd.ports);
  assert.equal(rd.mode, 'affected');
  assert.ok(rd.selectedTests.includes('test/docs-commands.test.mjs'));
  assert.ok(rd.selectedTests.includes('test/skills.test.mjs'));
  assert.equal(rd.selectedTests.includes('test/completely-unrelated.test.mjs'), false);

  // Skills change -> skill contract tests
  const vsk = virtualPorts(repo, ['skills/pdd-bug/SKILL.md']);
  const rsk = selectAffectedTests(vsk.options, vsk.ports);
  assert.equal(rsk.mode, 'affected');
  assert.ok(rsk.selectedTests.includes('test/skills.test.mjs'));
  assert.ok(rsk.selectedTests.includes('test/skill-frontmatter.test.mjs'));
  assert.equal(rsk.selectedTests.includes('test/completely-unrelated.test.mjs'), false);
});

test('3065 global test helpers, package/config files, core shared infrastructure, and missing diffs trigger safe full-suite fallback', () => {
  const repo = {
    'src/feature.mjs': 'export const ok = true;\n',
    'test/feature.test.mjs': "import { ok } from '../src/feature.mjs';\n",
    'test/other.test.mjs': 'export const other = true;\n',
  };

  for (const [changed, expectedCategory] of [
    [['test/helpers/test-home.mjs'], 'global-test-helper'],
    [['test/fixtures/harbor/pdd.json'], 'global-test-helper'],
    [['test/setup.mjs'], 'global-test-helper'],
    [['package.json'], 'package-config'],
    [['package-lock.json'], 'package-config'],
    [['pdd.json'], 'package-config'],
    [['pdd-bindings.json'], 'package-config'],
    [['vitest.config.ts'], 'package-config'],
    [['bin/pdd.mjs'], 'core-shared-infrastructure'],
    [['src/test-suite-queue.mjs'], 'core-shared-infrastructure'],
    [['src/runtime-seam.mjs'], 'core-shared-infrastructure'],
    [['prompts/cli/runtime-seam.prompt.md'], 'core-shared-infrastructure'],
    [['../outside.mjs'], 'unsafe-path'],
  ]) {
    const check = classifyGlobalSuiteTrigger(changed);
    assert.equal(check.fallback, true, `expected fallback for ${changed.join(',')}`);
    assert.equal(check.category, expectedCategory);

    const v = virtualPorts(repo, changed);
    const res = selectAffectedTests(v.options, v.ports);
    assert.equal(res.mode, 'full');
    assert.equal(res.selectedCount, 2);
    assert.equal(res.totalCount, 2);
    assert.equal(res.fallbackCategory, expectedCategory);
    assert.match(res.summary, /Affected tests: running full suite \(2 of 2 test files; fallback:/);
  }

  // Unavailable diff (null from readChangedFiles) falls back safely
  const vNull = virtualPorts(repo, undefined);
  const resNull = selectAffectedTests({ root: '/virtual-repo', files: Object.keys(repo) }, {
    ...vNull.ports,
    readChangedFiles: () => null,
  });
  assert.equal(resNull.mode, 'full');
  assert.equal(resNull.fallbackCategory, 'changed-files-unavailable');

  // Empty diff selects 0 of 2 without running full suite
  const vEmpty = virtualPorts(repo, []);
  const resEmpty = selectAffectedTests(vEmpty.options, vEmpty.ports);
  assert.equal(resEmpty.mode, 'affected');
  assert.equal(resEmpty.selectedCount, 0);
  assert.equal(resEmpty.summary, formatAffectedTestsSummary(resEmpty));
  assert.match(resEmpty.summary, /Affected tests: selected 0 of 2 test files \(no changed files\)\./);
});

test('3065 resolveVerifyPlan and verifyAffected run only affected tests iteratively and reserve full suite for final mode', async t => {
  const f = makeGitFixture(t);
  // Fix src/calc.mjs and break src/unrelated.mjs ONLY in final full suite check to prove iterative verify skips unrelated.test.mjs!
  f.put('src/calc.mjs', 'export const add = (a, b) => a + b;\n');
  f.git('add', 'src/calc.mjs');
  f.git('commit', '-qm', 'fix calc');

  // 1. Iterative plan selects ONLY test/billing.test.mjs (1 of 2 test files)
  const iterPlan = resolveVerifyPlan({ root: f.root, baseBranch: 'main', mode: 'iterative', concurrency: 2 });
  assert.equal(iterPlan.executionMode, 'affected');
  assert.equal(iterPlan.selectionMode, 'affected');
  assert.deepEqual(iterPlan.selectedTests, ['test/billing.test.mjs']);
  assert.equal(iterPlan.selectedCount, 1);
  assert.equal(iterPlan.totalCount, 2);
  assert.equal(iterPlan.command, 'node --test-concurrency=2 --test test/billing.test.mjs');

  // 2. Final pre-merge plan selects the full suite (2 of 2 test files)
  const finalPlan = resolveVerifyPlan({ root: f.root, baseBranch: 'main', mode: 'final' });
  assert.equal(finalPlan.mode, 'final');
  assert.equal(finalPlan.executionMode, 'full');
  assert.equal(finalPlan.selectedCount, 2);
  assert.equal(finalPlan.totalCount, 2);
  assert.equal(finalPlan.command, 'npm test');
  assert.match(finalPlan.summary, /Full test suite \(before merge\): running all 2 of 2 test files\./);

  // 3. Execute verifyAffected iteratively on real git repo: runs 1 of 2 tests, records cost, writes affected-verify.json
  const costs = [];
  const verifyRes = await verifyAffected(
    { ref: '3065', cwd: f.root, mode: 'verify' },
    { recordSuiteCost: async m => costs.push(m) },
  );
  assert.equal(verifyRes.exitCode, 0, verifyRes.message);
  assert.equal(verifyRes.executed, true);
  assert.equal(verifyRes.executionMode, 'affected');
  assert.equal(verifyRes.selectedCount, 1);
  assert.equal(verifyRes.totalCount, 2);
  assert.match(verifyRes.message, /Affected tests: ✓ passed \(1 of 2 test files: test\/billing\.test\.mjs\)\./);
  assert.equal(costs.length, 1);
  assert.ok(costs[0].suiteMinutes >= 0);

  const savedVerify = JSON.parse(readFileSync(join(f.runDir, 'affected-verify.json'), 'utf8'));
  assert.equal(savedVerify.origin, 'pdd.workflow-verify-affected.v1');
  assert.equal(savedVerify.selectedCount, 1);
  assert.equal(savedVerify.totalCount, 2);
  assert.deepEqual(savedVerify.selectedTests, ['test/billing.test.mjs']);

  // 4. proveAffectedRun auto-selects only test/billing.test.mjs, proves old-code failure -> new-code pass, and preserves v2 proof schema
  const proofRes = await proveAffectedRun({ ref: '3065', cwd: f.root, expect: 'DEFECT_CALC_3065' });
  assert.equal(proofRes.exitCode, 0, proofRes.message);
  assert.equal(proofRes.selection.mode, 'affected');
  assert.equal(proofRes.selection.selectedCount, 1);
  assert.equal(proofRes.selection.totalCount, 2);
  assert.match(proofRes.message, /Old-code proof: ✓ `node --test test\/billing\.test\.mjs`/);
  assert.match(proofRes.message, /Affected tests: selected 1 of 2 test files/);

  const savedProof = JSON.parse(readFileSync(join(f.runDir, 'old-code-proof.json'), 'utf8'));
  assert.equal(validateProofRecord(savedProof), true);
  assert.equal(savedProof.outcome, 'proved');
  assert.equal(savedProof.test, 'node --test test/billing.test.mjs');

  // 5. verifyAffected skips runner when 0 affected tests match, fails cleanly when an affected test fails, and validates options
  const skipRes = await verifyAffected({ root: f.root, changedFiles: [], mode: 'iterative' });
  assert.equal(skipRes.exitCode, 0);
  assert.equal(skipRes.executed, false);
  assert.equal(skipRes.executionMode, 'skip');
  assert.match(skipRes.message, /selected 0 of 2 test files/);

  const badTimeout = await verifyAffected({ root: f.root, timeoutMinutes: 0 });
  assert.equal(badTimeout.exitCode, 2);
  const badMode = await verifyAffected({ root: f.root, mode: 'unknown-mode' });
  assert.equal(badMode.exitCode, 2);

  const failRes = await verifyAffected(
    { root: f.root, changedFiles: ['src/calc.mjs'], mode: 'iterative' },
    {
      runProcess: async () => ({
        result: {
          exitCode: 1,
          signal: '',
          timedOut: false,
          outputLimited: false,
          expectedFound: false,
          stdout: '',
          stderr: 'AssertionError: expected 5 to equal 6\n',
          error: '',
          setupError: '',
        },
      }),
    },
  );
  assert.equal(failRes.exitCode, 1);
  assert.equal(failRes.selectedCount, 1);
  assert.equal(failRes.totalCount, 2);
  assert.match(failRes.message, /Affected tests: ✗ failed \(1 of 2 test files\)/);
  assert.match(failRes.message, /AssertionError: expected 5 to equal 6/);

  // 6. Preload helper injection, global-helper fallback execution in verifyAffected, and explicit test passthrough in proveAffectedRun
  f.put('test/helpers/test-home.mjs', 'export const isolatedHome = true;\n');
  f.put('test/helpers/test-net-guard.mjs', 'export const netGuard = true;\n');
  const preloadPlan = resolveVerifyPlan({
    root: f.root,
    changedFiles: ['src/calc.mjs'],
    mode: 'iterative',
    concurrency: 3,
  });
  assert.equal(
    preloadPlan.command,
    'node --import ./test/helpers/test-home.mjs --import ./test/helpers/test-net-guard.mjs --test-concurrency=3 --test test/billing.test.mjs',
  );

  let fallbackCmd = '';
  const fallbackVerify = await verifyAffected(
    { root: f.root, changedFiles: ['test/helpers/test-home.mjs'], mode: 'iterative' },
    {
      runProcess: async ({ command }) => {
        fallbackCmd = command;
        return {
          result: {
            exitCode: 0,
            signal: '',
            timedOut: false,
            outputLimited: false,
            expectedFound: false,
            stdout: 'ok\n',
            stderr: '',
            error: '',
            setupError: '',
          },
        };
      },
    },
  );
  assert.equal(fallbackVerify.exitCode, 0);
  assert.equal(fallbackVerify.mode, 'full');
  assert.equal(fallbackVerify.executionMode, 'full');
  assert.equal(fallbackCmd, 'npm test');
  assert.match(fallbackVerify.message, /Affected tests: ✓ passed \(2 of 2 test files; fallback: global test helper changed/);

  const explicitProof = await proveAffectedRun({
    ref: '3065',
    cwd: f.root,
    test: 'node --test test/billing.test.mjs',
    expect: 'DEFECT_CALC_3065',
  });
  assert.equal(explicitProof.exitCode, 0, explicitProof.message);
  assert.equal(explicitProof.selection, undefined);
});

test('3065 real repository prompt sync and affected selection remain aligned', () => {
  const repoRoot = process.cwd();
  const visible = new Set(gitFiles(repoRoot));
  for (const promptPath of ['prompts/cli/test-selection.prompt.md', 'prompts/cli/workflow-prove.prompt.md']) {
    const parsed = readPrompt(repoRoot, visible, promptPath);
    assert.equal(promptRefusal(parsed, 'prompt'), null, `${promptPath} must have valid current prose_sha256`);
  }

  let ownerOut = '', ownerErr = '';
  const ownerCode = runOwner(
    {
      cwd: repoRoot,
      paths: [
        'prompts/cli/test-selection.prompt.md',
        'src/test-selection.mjs',
        'prompts/cli/workflow-prove.prompt.md',
        'src/workflow-prove.mjs',
      ],
      json: true,
    },
    {
      stdout: { write: s => { ownerOut += s; } },
      stderr: { write: s => { ownerErr += s; } },
    },
  );
  assert.equal(ownerCode, 0, ownerErr);
  assert.equal(ownerErr, '');
  const ownerJson = JSON.parse(ownerOut);
  assert.equal(ownerJson.files.find(f => f.path === 'src/test-selection.mjs')?.owner, 'prompts/cli/test-selection.prompt.md');
  assert.equal(ownerJson.files.find(f => f.path === 'src/workflow-prove.mjs')?.owner, 'prompts/cli/workflow-prove.prompt.md');

  const realSelection = selectAffectedTests({
    root: repoRoot,
    changedFiles: ['prompts/cli/test-selection.prompt.md', 'src/test-selection.mjs'],
  });
  assert.equal(realSelection.mode, 'affected');
  assert.ok(
    realSelection.selectedCount > 0 && realSelection.selectedCount < Math.ceil(realSelection.totalCount * 0.15),
    `expected focused subset (<15% of ${realSelection.totalCount}), got ${realSelection.selectedCount}`,
  );
  assert.ok(realSelection.selectedTests.includes('test/test-selection-affected.test.mjs'));
  assert.ok(realSelection.selectedTests.includes('test/tests-found-by-name.test.mjs'));
  assert.ok(realSelection.selectedTests.includes('test/workflow-prove.test.mjs'));
});
