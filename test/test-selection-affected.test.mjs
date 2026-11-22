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
import { lintSvgLayouts } from '../src/svg-layout.mjs';
import { promptRefusal, runtimePreflightSlice } from '../src/runtime-seam.mjs';

const { gitFiles, readPrompt } = runtimePreflightSlice();
const quotedExec = /^[A-Za-z0-9_@%+=:,./-]+$/.test(process.execPath)
  ? process.execPath
  : `'${process.execPath.replaceAll("'", `'\\''`)}'`;

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

test('3065 isRunnableTestPath and Windows path normalization handle POSIX and Windows separators safely', () => {
  assert.equal(isRunnableTestPath('test/order.test.mjs'), true);
  assert.equal(isRunnableTestPath('test\\order.test.mjs'), true);
  assert.equal(isRunnableTestPath('.\\tests\\unit\\order.spec.ts'), true);
  assert.equal(isRunnableTestPath('tests/unit/order.spec.ts'), true);
  assert.equal(isRunnableTestPath('test/workflow-prove.vectors.test.mjs'), true);
  assert.equal(isRunnableTestPath('./test/order.test.js'), true);

  assert.equal(isRunnableTestPath('test/helpers/test-home.mjs'), false);
  assert.equal(isRunnableTestPath('test\\helpers\\test-home.mjs'), false);
  assert.equal(isRunnableTestPath('test/helpers/fake.test.mjs'), false);
  assert.equal(isRunnableTestPath('test/fixtures/sample.test.mjs'), false);
  assert.equal(isRunnableTestPath('src/order.test.mjs'), false);
  assert.equal(isRunnableTestPath('node_modules/pkg/index.test.js'), false);
  assert.equal(isRunnableTestPath('tests/place-order.json'), false);
  assert.equal(isRunnableTestPath('../test/escape.test.mjs'), false);
  assert.equal(isRunnableTestPath('..\\test\\escape.test.mjs'), false);
  assert.equal(isRunnableTestPath('C:\\repo\\test\\escape.test.mjs'), false);
  assert.equal(isRunnableTestPath('C:..\\escape.test.mjs'), false);
  assert.equal(isRunnableTestPath('C:test\\escape.test.mjs'), false);
  assert.equal(isRunnableTestPath('\\\\server\\share\\test\\escape.test.mjs'), false);

  assert.equal(classifyGlobalSuiteTrigger(['src\\foo.mjs']).fallback, false);
  assert.equal(classifyGlobalSuiteTrigger(['test\\helpers\\test-home.mjs']).category, 'global-test-helper');
  assert.equal(classifyGlobalSuiteTrigger(['..\\outside.mjs']).category, 'unsafe-path');
  assert.equal(classifyGlobalSuiteTrigger(['C:\\outside\\foo.mjs']).category, 'unsafe-path');
  assert.equal(classifyGlobalSuiteTrigger(['C:..\\escape.test.mjs']).category, 'unsafe-path');
  assert.equal(classifyGlobalSuiteTrigger(['d:relative\\foo.mjs']).category, 'unsafe-path');

  const winRepo = {
    'src\\foo.mjs': 'export const runFoo = () => 1;\n',
    'test\\foo-runner.test.mjs': "import { runFoo } from '../src/foo.mjs';\n",
    'test\\other.test.mjs': 'export const ok = true;\n',
  };
  const winRes = selectAffectedTests(
    { root: '/virtual-win', files: Object.keys(winRepo), changedFiles: ['src\\foo.mjs'] },
    { readFile: p => winRepo[p] ?? null },
  );
  assert.equal(winRes.mode, 'affected');
  assert.deepEqual(winRes.selectedTests, ['test/foo-runner.test.mjs']);
});

test('3065 scanModuleSource handles regex literals with quotes/classes and nested template interpolations', () => {
  const repo = {
    'src/after-regex.mjs': 'export const afterRegex = () => 1;\n',
    'src/after-template.mjs': 'export const afterTemplate = () => 2;\n',
    'src/inside-interpolation.mjs': 'export const insideInterp = () => 3;\n',
    'src/other.mjs': 'export const other = () => 4;\n',
    'test/regex-and-template.test.mjs': [
      "const importPattern = /\\bimport\\s+(?:[^;]*?\\bfrom\\s*)?(['\"`])((?:\\\\[\\s\\S]|(?!\\1)[\\s\\S])*)\\1/g;",
      "const slashInClass = /[/'\"`]/;",
      'const nested = `${String("a").replace(\'a\', `inner ${1 + 2} end`)}`;',
      'const adjacentInterp = `${req}${"../src/other.mjs"}`;',
      'const dynInTemplate = `${await import(\'../src/inside-interpolation.mjs\')}`;',
      "const modA = await import('../src/after-regex.mjs');",
      "const modB = await import('../src/after-template.mjs');",
      'export { importPattern, slashInClass, nested, adjacentInterp, dynInTemplate, modA, modB };',
    ].join('\n'),
    'test/other-only.test.mjs': "import { other } from '../src/other.mjs';\n",
  };

  for (const target of ['src/after-regex.mjs', 'src/after-template.mjs', 'src/inside-interpolation.mjs']) {
    const v = virtualPorts(repo, [target]);
    const res = selectAffectedTests(v.options, v.ports);
    assert.equal(res.mode, 'affected');
    assert.deepEqual(res.selectedTests, ['test/regex-and-template.test.mjs'], `failed for ${target}`);
  }

  // Adjacent `${req}${"../src/other.mjs"}` must not merge `req` + `(` across template close
  const vOther = virtualPorts(repo, ['src/other.mjs']);
  assert.deepEqual(selectAffectedTests(vOther.options, vOther.ports).selectedTests, ['test/other-only.test.mjs']);
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

test('3065 dispatcher hubs bridge export *, aliased re-exports, 1-char symbols, test helpers, and never leave changed code at 0 tests', () => {
  const deps = Object.fromEntries(
    Array.from({ length: 12 }, (_, idx) => {
      if (idx === 0) return ['src/mod-0.mjs', 'export const fn0 = () => 0;\nexport const $tag = () => "ok";\n'];
      if (idx === 2) return ['src/mod-2.mjs', 'export const x = () => 2;\n'];
      if (idx === 3) return ['src/mod-3.mjs', 'export const internalCalc = () => 3;\n'];
      if (idx === 4) return ['src/mod-4.mjs', 'export const unexportedLeaf = () => 4;\n'];
      if (idx === 5) return ['src/mod-5.mjs', 'export const leafFive = () => 5;\n'];
      if (idx === 6) return ['src/mod-6.mjs', 'export const leafSix = () => 6;\n'];
      if (idx === 7) return ['src/mod-7.mjs', 'export const leafSeven = () => 7;\n'];
      if (idx === 8) return ['src/mod-8.mjs', 'const p = "v";\nexport const firstDecl = `${p}`, afterInterpExport = 8;\n'];
      return [`src/mod-${idx}.mjs`, `export const fn${idx} = () => ${idx};\n`];
    }),
  );
  const hubImports = Array.from({ length: 12 }, (_, idx) => {
    if (idx === 0) return "import { fn0, $tag } from './mod-0.mjs';";
    if (idx === 2) return "export * from './mod-2.mjs';";
    if (idx === 3) return "export { internalCalc as publicAlias } from './mod-3.mjs';";
    if (idx === 4) return "import { unexportedLeaf } from './mod-4.mjs';";
    if (idx === 5) return "import { leafFive as twoStmtImportedAlias } from './mod-5.mjs';";
    if (idx === 6) return "import { leafSix } from './mod-6.mjs';";
    if (idx === 7) return "import * as mod7Ns from './mod-7.mjs';";
    if (idx === 8) return "export * from './mod-8.mjs';";
    return `import { fn${idx} } from './mod-${idx}.mjs';`;
  }).join('\n');
  const repo = {
    ...deps,
    'src/standalone-unmapped.mjs': 'export const orphanFn = () => 99;\n',
    'src/schema.sql': 'CREATE TABLE items (id INTEGER PRIMARY KEY);\n',
    'lib/rules.json': '{"strict":true}\n',
    'src/hub.mjs': [
      hubImports,
      'export { fn0, $tag };',
      'export { twoStmtImportedAlias };',
      'export { leafSix as twoStmtExportAlias };',
      'export { mod7Ns };',
      'export const runHub = () => fn1() + unexportedLeaf();',
    ].join('\n'),
    'test/hub-local-helper.mjs': "import { publicAlias } from '../src/hub.mjs';\nexport const callAlias = () => publicAlias();\n",
    'test/uses-reexport.test.mjs': "import { $tag } from '../src/hub.mjs';\n",
    'test/uses-star-1char.test.mjs': "import { x } from '../src/hub.mjs';\n",
    'test/uses-alias-via-helper.test.mjs': "import { callAlias } from './hub-local-helper.mjs';\n",
    'test/uses-two-stmt-import-alias.test.mjs': "import { twoStmtImportedAlias } from '../src/hub.mjs';\n",
    'test/uses-two-stmt-export-alias.test.mjs': "import { twoStmtExportAlias } from '../src/hub.mjs';\n",
    'test/uses-two-stmt-ns.test.mjs': "import { mod7Ns } from '../src/hub.mjs';\n",
    'test/uses-after-interp-export.test.mjs': "import { afterInterpExport } from '../src/hub.mjs';\n",
    'test/uses-hub-only.test.mjs': "import { runHub } from '../src/hub.mjs';\n",
    'test/mod-1-direct.test.mjs': "import { fn1 } from '../src/mod-1.mjs';\n",
  };

  // Editing mod-0 bridges re-exported $tag through hub.mjs to uses-reexport.test.mjs without pulling uses-hub-only.test.mjs
  const v0 = virtualPorts(repo, ['src/mod-0.mjs']);
  assert.deepEqual(selectAffectedTests(v0.options, v0.ports).selectedTests, ['test/uses-reexport.test.mjs']);

  // Editing mod-1 selects its direct test without fanning out to unrelated hub tests
  const v1 = virtualPorts(repo, ['src/mod-1.mjs']);
  assert.deepEqual(selectAffectedTests(v1.options, v1.ports).selectedTests, ['test/mod-1-direct.test.mjs']);

  // Editing mod-2 bridges 1-char symbol `x` via `export * from './mod-2.mjs'`
  const v2 = virtualPorts(repo, ['src/mod-2.mjs']);
  assert.deepEqual(selectAffectedTests(v2.options, v2.ports).selectedTests, ['test/uses-star-1char.test.mjs']);

  // Editing mod-3 bridges `export { internalCalc as publicAlias } from './mod-3.mjs'` across local test/hub-local-helper.mjs
  const v3 = virtualPorts(repo, ['src/mod-3.mjs']);
  assert.deepEqual(selectAffectedTests(v3.options, v3.ports).selectedTests, ['test/uses-alias-via-helper.test.mjs']);

  // Editing mod-5, mod-6, mod-7 bridges 2-statement `import ...; export { ... };` re-exports through hub.mjs
  const v5 = virtualPorts(repo, ['src/mod-5.mjs']);
  assert.deepEqual(selectAffectedTests(v5.options, v5.ports).selectedTests, ['test/uses-two-stmt-import-alias.test.mjs']);

  const v6 = virtualPorts(repo, ['src/mod-6.mjs']);
  assert.deepEqual(selectAffectedTests(v6.options, v6.ports).selectedTests, ['test/uses-two-stmt-export-alias.test.mjs']);

  const v7 = virtualPorts(repo, ['src/mod-7.mjs']);
  assert.deepEqual(selectAffectedTests(v7.options, v7.ports).selectedTests, ['test/uses-two-stmt-ns.test.mjs']);

  // Editing mod-8 bridges `afterInterpExport` declared after `${p}` on the same `export const` line
  const v8 = virtualPorts(repo, ['src/mod-8.mjs']);
  assert.deepEqual(selectAffectedTests(v8.options, v8.ports).selectedTests, ['test/uses-after-interp-export.test.mjs']);

  // Editing mod-4 (imported by hub without re-export or direct test) bridges to hub's test importers instead of returning 0 tests
  const v4 = virtualPorts(repo, ['src/mod-4.mjs']);
  const r4 = selectAffectedTests(v4.options, v4.ports);
  assert.equal(r4.mode, 'affected');
  assert.ok(r4.selectedCount > 0);
  assert.ok(r4.selectedTests.includes('test/uses-hub-only.test.mjs'));

  // Editing standalone-unmapped.mjs or non-JS production files (src/schema.sql, lib/rules.json) with 0 mapped tests safely falls back to full suite
  for (const unmappedProd of ['src/standalone-unmapped.mjs', 'src/schema.sql', 'lib/rules.json']) {
    const vUnmapped = virtualPorts(repo, [unmappedProd]);
    const rUnmapped = selectAffectedTests(vUnmapped.options, vUnmapped.ports);
    assert.equal(rUnmapped.mode, 'full', `expected full fallback for ${unmappedProd}`);
    assert.equal(rUnmapped.fallbackCategory, 'unmapped-code-change');
    assert.equal(rUnmapped.selectedCount, 9);
  }

  // Editing hub.mjs directly selects all tests importing hub.mjs (including via local test helper)
  const vHub = virtualPorts(repo, ['src/hub.mjs']);
  assert.deepEqual(selectAffectedTests(vHub.options, vHub.ports).selectedTests, [
    'test/uses-after-interp-export.test.mjs',
    'test/uses-alias-via-helper.test.mjs',
    'test/uses-hub-only.test.mjs',
    'test/uses-reexport.test.mjs',
    'test/uses-star-1char.test.mjs',
    'test/uses-two-stmt-export-alias.test.mjs',
    'test/uses-two-stmt-import-alias.test.mjs',
    'test/uses-two-stmt-ns.test.mjs',
  ]);
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

  // 1. Iterative plan selects ONLY test/billing.test.mjs (1 of 2 test files) using quoted process.execPath and preserves mode: 'iterative'
  const iterPlan = resolveVerifyPlan({ root: f.root, baseBranch: 'main', mode: 'iterative', concurrency: 2 });
  assert.equal(iterPlan.mode, 'iterative');
  assert.equal(iterPlan.executionMode, 'affected');
  assert.equal(iterPlan.selectionMode, 'affected');
  assert.deepEqual(iterPlan.selectedTests, ['test/billing.test.mjs']);
  assert.equal(iterPlan.selectedCount, 1);
  assert.equal(iterPlan.totalCount, 2);
  assert.equal(iterPlan.command, `${quotedExec} --test-concurrency=2 --test test/billing.test.mjs`);

  // Custom execPath with spaces is shell-quoted, and maxCommandLength falls back to fullCommand safely while preserving mode: 'iterative'
  const spacedExecPlan = resolveVerifyPlan(
    { root: f.root, changedFiles: ['src/calc.mjs'], mode: 'iterative' },
    { execPath: '/opt/node custom/bin/node' },
  );
  assert.equal(spacedExecPlan.mode, 'iterative');
  assert.equal(spacedExecPlan.command, "'/opt/node custom/bin/node' --test test/billing.test.mjs");

  const argMaxFallback = resolveVerifyPlan({
    root: f.root,
    changedFiles: ['src/calc.mjs'],
    mode: 'iterative',
    maxCommandLength: 24,
    fullTestCommand: 'npm run test:ci',
  });
  assert.equal(argMaxFallback.mode, 'iterative');
  assert.equal(argMaxFallback.executionMode, 'full');
  assert.equal(argMaxFallback.selectionMode, 'full');
  assert.equal(argMaxFallback.fallbackCategory, 'command-length-limit');
  assert.equal(argMaxFallback.command, 'npm run test:ci');
  assert.equal(argMaxFallback.selectedCount, 2);

  // Global-fallback and skip plans also preserve mode: 'iterative'; repos with 0 JS/TS test files never skip production changes
  const globalIterPlan = resolveVerifyPlan({ root: f.root, changedFiles: ['package.json'], mode: 'verify' });
  assert.equal(globalIterPlan.mode, 'iterative');
  assert.equal(globalIterPlan.executionMode, 'full');
  assert.equal(globalIterPlan.selectionMode, 'full');

  const skipIterPlan = resolveVerifyPlan({ root: f.root, changedFiles: [], mode: 'affected' });
  assert.equal(skipIterPlan.mode, 'iterative');
  assert.equal(skipIterPlan.executionMode, 'skip');
  assert.equal(skipIterPlan.selectionMode, 'affected');

  const nonJsProdPlan = resolveVerifyPlan(
    {
      root: '/virtual-py',
      files: ['src/worker.py', 'pyproject.toml'],
      changedFiles: ['src/worker.py'],
      fullTestCommand: 'pytest -q',
      mode: 'iterative',
    },
    { readFile: () => '' },
  );
  assert.equal(nonJsProdPlan.mode, 'iterative');
  assert.equal(nonJsProdPlan.executionMode, 'full');
  assert.equal(nonJsProdPlan.selectionMode, 'full');
  assert.equal(nonJsProdPlan.totalCount, 0);
  assert.equal(nonJsProdPlan.fallbackCategory, 'unmapped-code-change');
  assert.equal(nonJsProdPlan.command, 'pytest -q');

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
  assert.equal(savedVerify.mode, 'iterative');
  assert.equal(savedVerify.selectedCount, 1);
  assert.equal(savedVerify.totalCount, 2);
  assert.deepEqual(savedVerify.selectedTests, ['test/billing.test.mjs']);

  // 4. proveAffectedRun auto-selects only test/billing.test.mjs, proves old-code failure -> new-code pass, and preserves v2 proof schema
  const proofRes = await proveAffectedRun({ ref: '3065', cwd: f.root, expect: 'DEFECT_CALC_3065' });
  assert.equal(proofRes.exitCode, 0, proofRes.message);
  assert.equal(proofRes.selection.mode, 'affected');
  assert.equal(proofRes.selection.selectedCount, 1);
  assert.equal(proofRes.selection.totalCount, 2);
  assert.match(proofRes.message, /--test test\/billing\.test\.mjs`/);
  assert.match(proofRes.message, /Affected tests: selected 1 of 2 test files/);

  const savedProof = JSON.parse(readFileSync(join(f.runDir, 'old-code-proof.json'), 'utf8'));
  assert.equal(validateProofRecord(savedProof), true);
  assert.equal(savedProof.outcome, 'proved');
  assert.equal(savedProof.test, `${quotedExec} --test test/billing.test.mjs`);

  // When 0 affected tests match a non-code snapshot, proveAffectedRun forwards fullTestCommand and truthfully reports full execution (never 0 of 2)
  const skipUpgradeCommands = [];
  const skipUpgradeProof = await proveAffectedRun(
    {
      ref: '3065',
      cwd: f.root,
      expect: 'DEFECT_NOTES_3065',
      fullTestCommand: 'npm run custom-full',
      files: ['package.json', 'test/billing.test.mjs', 'test/unrelated.test.mjs'],
    },
    {
      readRun: async () => ({
        run: { runId: 'run-3065', runDir: f.runDir, root: f.root, baseSha: f.baseSha, baseBranch: 'main' },
        error: '',
      }),
      snapshot: async () => ({
        snapshot: {
          baseSha: f.baseSha,
          headSha: f.baseSha,
          baseAvailable: true,
          headAvailable: true,
          files: [{ path: 'notes.txt', status: 'M', mode: '100644' }],
          error: '',
        },
      }),
      createWorktree: async ({ phase }) => ({ worktree: join(f.root, `.fake-${phase}`), error: '' }),
      cleanup: async () => ({ error: '' }),
      saveProof: async () => ({ error: '' }),
      runProcess: async ({ command, cwd: phaseCwd }) => {
        skipUpgradeCommands.push(command);
        const isBase = phaseCwd.endsWith('.fake-base');
        return {
          result: {
            exitCode: isBase ? 1 : 0,
            signal: '',
            timedOut: false,
            outputLimited: false,
            stdout: '',
            stderr: isBase ? 'AssertionError: DEFECT_NOTES_3065\n' : '',
            error: '',
            setupError: '',
          },
        };
      },
    },
  );
  assert.deepEqual(skipUpgradeCommands, ['npm run custom-full', 'npm run custom-full']);
  assert.equal(skipUpgradeProof.selection.mode, 'full');
  assert.equal(skipUpgradeProof.selection.executionMode, 'full');
  assert.equal(skipUpgradeProof.selection.selectedCount, 2);
  assert.equal(skipUpgradeProof.selection.fallbackCategory, 'prove-requires-execution');
  assert.match(skipUpgradeProof.message, /running full suite \(2 of 2 test files; fallback: 0 affected test files matched/);

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
    `${quotedExec} --import ./test/helpers/test-home.mjs --import ./test/helpers/test-net-guard.mjs --test-concurrency=3 --test test/billing.test.mjs`,
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
  const tsOwner = ownerJson.files.find(f => f.path === 'src/test-selection.mjs');
  const wpOwner = ownerJson.files.find(f => f.path === 'src/workflow-prove.mjs');
  assert.equal(tsOwner?.owner, 'prompts/cli/test-selection.prompt.md');
  assert.equal(wpOwner?.owner, 'prompts/cli/workflow-prove.prompt.md');
  assert.equal(tsOwner?.headers?.[0]?.state, 'current');
  assert.equal(tsOwner?.headers?.[0]?.legacy, false);
  assert.equal(wpOwner?.headers?.[0]?.state, 'current');
  assert.equal(wpOwner?.headers?.[0]?.legacy, false);

  // Checkable workflow-prove.prompt.md must not emit inverted native-only dependency warnings
  const proveLintWarnings = lintSvgLayouts({ root: repoRoot, files: [...visible] }).filter(w =>
    w.includes('prompts/cli/workflow-prove.prompt.md'),
  );
  assert.deepEqual(proveLintWarnings, []);

  // Real-repo lexer & hub-leaf regression assertions (#3065 review)
  const tryDoors = selectAffectedTests({ root: repoRoot, changedFiles: ['src/try-doors.mjs'] });
  assert.ok(tryDoors.selectedTests.includes('test/runtime-seam.test.mjs'));

  const launcher = selectAffectedTests({ root: repoRoot, changedFiles: ['src/autopilot-launcher.mjs'] });
  assert.ok(launcher.selectedTests.includes('test/autopilot-core-evidence.test.mjs'));

  const compiledTest = selectAffectedTests({ root: repoRoot, changedFiles: ['src/compiled-test.mjs'] });
  assert.ok(compiledTest.selectedCount > 0);
  assert.ok(compiledTest.selectedTests.includes('test/compiled-story-tests.test.mjs'));

  const projectFiles = selectAffectedTests({ root: repoRoot, changedFiles: ['src/project-files.mjs'] });
  assert.ok(projectFiles.selectedCount > 0);
  assert.ok(projectFiles.selectedTests.includes('test/plain-prompts-and-frontmatter.test.mjs'));
  assert.ok(projectFiles.selectedTests.includes('test/runtime-seam.test.mjs'));

  const setupInteraction = selectAffectedTests({ root: repoRoot, changedFiles: ['src/setup-interaction.mjs'] });
  assert.ok(setupInteraction.selectedCount > 0);
  assert.ok(setupInteraction.selectedTests.includes('test/setup.test.mjs'));
  assert.ok(setupInteraction.selectedTests.includes('test/setup-defaults.test.mjs'));

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

test('S4 Stage 1: matchTests excludes brownfield fixtures/mocks/snapshots/tsconfig JSONs while keeping real orphans and nested fixture projects', async () => {
  const { matchTests } = await import('../src/test-selection.mjs');
  const stories = ['user_stories/place-order.md', 'test/fixtures/demo/user_stories/x.md'];
  const files = [
    'user_stories/place-order.md',
    'tests/place-order.json',
    'tests/fixtures/seed.json',
    'test/fixtures/data.json',
    'tests/__fixtures__/nested/sample.json',
    'tests/mocks/api.json',
    'test/__mocks__/client.json',
    'tests/snapshots/render.json',
    'tests/__snapshots__/card.json',
    'tests/data/sample.json',
    'tests/testdata/fixture.json',
    'test/golden/expected.json',
    'tests/cassettes/vcr.json',
    'tests/tsconfig.json',
    'test/tsconfig.test.json',
    'tests/package.json',
    'tests/real-orphan.json',
    'test/fixtures/demo/user_stories/x.md',
    'test/fixtures/demo/tests/x.json',
  ];
  const matched = matchTests(stories, files);
  assert.deepEqual(matched.tests.map(t => t.path), ['test/fixtures/demo/tests/x.json', 'tests/place-order.json']);
  assert.deepEqual(matched.orphans.map(o => o.path), ['tests/real-orphan.json']);
});

test('S4 Stage 1: selectAffectedTests matches contract tests under test/core/lint/', () => {
  const memFiles = {
    'prompts/cli/sample.prompt.md': '# Sample\n',
    'user_stories/sample.md': '# Sample\n\n## Acceptance criteria\n\n1. Works.\n',
    'test/core/lint/repo-hygiene-lint.test.mjs': 'import test from "node:test";\n',
    'test/core/lint/story-quality-lint.test.mjs': 'import test from "node:test";\n',
    'test/core/lint/authoring-lint-parity.test.mjs': 'import test from "node:test";\n',
  };
  const ports = {
    listFiles: () => Object.keys(memFiles),
    readFile: p => memFiles[p] ?? null,
  };
  const promptPlan = selectAffectedTests({ root: '/repo', changedFiles: ['prompts/cli/sample.prompt.md'] }, ports);
  assert.equal(promptPlan.mode, 'affected');
  assert.ok(promptPlan.selectedTests.includes('test/core/lint/repo-hygiene-lint.test.mjs'));
  assert.ok(promptPlan.selectedTests.includes('test/core/lint/story-quality-lint.test.mjs'));
  assert.ok(promptPlan.selectedTests.includes('test/core/lint/authoring-lint-parity.test.mjs'));

  const storyPlan = selectAffectedTests({ root: '/repo', changedFiles: ['user_stories/sample.md'] }, ports);
  assert.equal(storyPlan.mode, 'affected');
  assert.ok(storyPlan.selectedTests.includes('test/core/lint/story-quality-lint.test.mjs'));
});
