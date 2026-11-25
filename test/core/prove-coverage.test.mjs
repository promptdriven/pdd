import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawn, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { resolvePythonBinary } from '../../src/core/polyglot-runners.mjs';
import {
  aggregateCoverageSplit,
  collectDiffLines,
  parseCoveragePyJson,
  parseGoCoverProfile,
  parsePythonTestPipeline,
  parseUnifiedDiffAddedLines,
  resolveV8FileCoverage,
  runProveCoverage,
  validateProveOptInFlags,
} from '../../src/core/prove-coverage.mjs';
import { EXIT_NOT_PROVED, EXIT_PROVED, EXIT_USAGE, OUTCOME_NOT_PROVED, OUTCOME_PROVED, runProve } from '../../src/core/prove.mjs';

const BIN_PATH = fileURLToPath(new URL('../../bin/pdd.mjs', import.meta.url));
const HAS_PYTHON3 = spawnSync('python3', ['--version'], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }).status === 0;

function makeSink() {
  let text = '';
  return { write(s) { text += String(s); }, get text() { return text; } };
}

function initGitRepo(t, prefix) {
  const dir = mkdtempSync(join(tmpdir(), prefix));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q', '-b', 'main'], { cwd: dir });
  execFileSync('git', ['config', 'user.name', 'Test'], { cwd: dir });
  execFileSync('git', ['config', 'user.email', 'test@example.com'], { cwd: dir });
  return dir;
}

function commitAll(dir, msg) {
  execFileSync('git', ['add', '.'], { cwd: dir });
  execFileSync('git', ['commit', '-q', '-m', msg], { cwd: dir });
}

test('parseUnifiedDiffAddedLines extracts exact added lines and ignores pure deletions and /dev/null', () => {
  const diffText = [
    'diff --git a/src/a.mjs b/src/a.mjs',
    '--- a/src/a.mjs',
    '+++ b/src/a.mjs',
    '@@ -1,0 +2,3 @@',
    '+line2',
    '+line3',
    '+line4',
    '@@ -10,2 +13,0 @@',
    '-removed1',
    '-removed2',
    '@@ -20 +21 @@',
    '-old',
    '+new',
    'diff --git a/src/deleted.mjs b/src/deleted.mjs',
    '--- a/src/deleted.mjs',
    '+++ /dev/null',
    '@@ -1,2 +0,0 @@',
    '-bye',
  ].join('\n');
  const parsed = parseUnifiedDiffAddedLines({ diffText });
  assert.deepEqual(parsed.files, { 'src/a.mjs': [2, 3, 4, 21] });
});

test('resolveV8FileCoverage accurately resolves nested count=0 inner branches inside count=1 outer functions', () => {
  const src = [
    'export function classify(x) {',
    '  if (x < 0) {',
    '    return "neg";',
    '  }',
    '  return "pos";',
    '}',
  ].join('\n') + '\n';
  const negStart = src.indexOf('{', src.indexOf('if (x < 0)'));
  const negEnd = src.indexOf('}', negStart) + 1;
  const cov = resolveV8FileCoverage({
    sourceText: src,
    functions: [
      { functionName: '', isBlockCoverage: true, ranges: [{ startOffset: 0, endOffset: src.length, count: 1 }] },
      {
        functionName: 'classify',
        isBlockCoverage: true,
        ranges: [
          { startOffset: 7, endOffset: src.length - 1, count: 1 },
          { startOffset: negStart, endOffset: negEnd, count: 0 },
        ],
      },
    ],
  });
  assert.ok(cov.executedLines.includes(2), 'if guard line is executed');
  assert.ok(cov.executedLines.includes(5), 'pos return line is executed');
  assert.deepEqual(cov.missedLines, [3], 'neg return inside count=0 block MUST be marked missed');
  assert.equal(cov.totalBranches, 1);
  assert.equal(cov.coveredBranches, 0);
});

test('parseCoveragePyJson and parseGoCoverProfile normalize canonical production file lines and branches', () => {
  const pyJson = JSON.stringify({
    files: {
      'src/ledger.py': {
        executed_lines: [1, 2, 5],
        missing_lines: [3, 4],
        summary: { num_statements: 5, covered_lines: 3, num_branches: 4, covered_branches: 2 },
      },
      'tests/test_ledger.py': {
        executed_lines: [1, 2],
        missing_lines: [],
        summary: { num_statements: 2, covered_lines: 2, num_branches: 0, covered_branches: 0 },
      },
    },
  });
  const pyParsed = parseCoveragePyJson({ jsonText: pyJson });
  assert.deepEqual(Object.keys(pyParsed), ['src/ledger.py']);
  assert.deepEqual(pyParsed['src/ledger.py'].executedLines, [1, 2, 5]);
  assert.deepEqual(pyParsed['src/ledger.py'].missedLines, [3, 4]);
  assert.equal(pyParsed['src/ledger.py'].totalBranches, 4);
  assert.equal(pyParsed['src/ledger.py'].coveredBranches, 2);

  const goProfile = [
    'mode: count',
    'example.com/demo/pkg/calc.go:3.25,5.2 2 1',
    'example.com/demo/pkg/calc.go:6.2,8.2 2 0',
    'example.com/demo/pkg/calc_test.go:1.1,5.2 2 1',
  ].join('\n');
  const goParsed = parseGoCoverProfile({ profileText: goProfile, modulePath: 'example.com/demo' });
  assert.deepEqual(Object.keys(goParsed), ['pkg/calc.go']);
  assert.deepEqual(goParsed['pkg/calc.go'].executedLines, [3, 4, 5]);
  assert.deepEqual(goParsed['pkg/calc.go'].missedLines, [6, 7, 8]);
});

test('AC1/AC2/AC5/AC6: pdd prove --coverage --json splits formal, vectors, and all on real Node repo, exposes uncovered diff lines, leaves working tree untouched, and preserves zero-flag prove', t => {
  const repo = initGitRepo(t, 'pdd-prove-cov-js-');
  const nodeBin = JSON.stringify(process.execPath);
  mkdirSync(join(repo, 'src'), { recursive: true });
  mkdirSync(join(repo, 'test'), { recursive: true });

  writeFileSync(join(repo, 'package.json'), JSON.stringify({
    name: 'cov-demo',
    type: 'module',
    scripts: { test: `${nodeBin} --test test/*.test.mjs` },
  }, null, 2) + '\n');
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({
    verify: {
      test: `${nodeBin} --test test/*.test.mjs`,
      paths: [{ id: 'core', when: ['src/**/*.mjs'], run: `${nodeBin} --test test/*.test.mjs` }],
    },
  }, null, 2) + '\n');
  writeFileSync(join(repo, 'src', 'ledger.mjs'), 'export function credit(bal, amt) {\n  return bal + amt;\n}\n');
  writeFileSync(join(repo, 'test', 'ledger.test.mjs'), [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { credit } from '../src/ledger.mjs';",
    "test('credit adds', () => assert.equal(credit(10, 5), 15));",
  ].join('\n') + '\n');
  commitAll(repo, 'base');

  execFileSync('git', ['checkout', '-q', '-b', 'feat-cov'], { cwd: repo });
  const prodBody = [
    'export function credit(bal, amt) {',
    '  if (amt < 0) {',
    '    throw new RangeError("NEGATIVE");',
    '  }',
    '  if (amt === 0) {',
    '    return bal;',
    '  }',
    '  if (amt > 1000000) {',
    '    return bal + 1000000;',
    '  }',
    '  return bal + amt;',
    '}',
  ].join('\n') + '\n';
  writeFileSync(join(repo, 'src', 'ledger.mjs'), prodBody);
  // Untouched by any test: must honestly show 0% uncovered diff lines!
  writeFileSync(join(repo, 'src', 'orphan.mjs'), 'export function deadBranch(x) {\n  if (x > 10) {\n    return x * 2;\n  }\n  return x;\n}\n');
  // Formal test covers amt < 0 and normal amt > 0, misses amt === 0 and amt > 1000000.
  writeFileSync(join(repo, 'test', 'ledger.formal.test.mjs'), [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { credit } from '../src/ledger.mjs';",
    "test('formal invariants', () => {",
    '  for (let i = 1; i <= 50; i++) {',
    '    assert.equal(credit(100, i), 100 + i);',
    '    assert.throws(() => credit(100, -i), /NEGATIVE/);',
    '  }',
    '});',
  ].join('\n') + '\n');
  // Vector test covers amt === 0 and normal amt > 0, misses amt < 0 and amt > 1000000.
  writeFileSync(join(repo, 'test', 'ledger.vectors.test.mjs'), [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { credit } from '../src/ledger.mjs';",
    "test('vector replay', () => {",
    '  assert.equal(credit(50, 0), 50);',
    '  assert.equal(credit(50, 10), 60);',
    '});',
  ].join('\n') + '\n');
  commitAll(repo, 'add guards and split suites');

  // 1. Default zero-flag prove omits `coverage` and `mutation` cleanly (zero behavior change).
  const baseOut = makeSink(), baseErr = makeSink();
  const zeroRes = runProve({ cwd: repo, base: 'main', json: true }, { stdout: baseOut, stderr: baseErr });
  assert.equal(zeroRes.exitCode, EXIT_PROVED, baseOut.text || baseErr.text);
  const zeroReceipt = JSON.parse(baseOut.text);
  assert.equal(Object.hasOwn(zeroReceipt, 'coverage'), false);
  assert.equal(Object.hasOwn(zeroReceipt, 'mutation'), false);

  // 2. Opt-in `--coverage --json` via real CLI subprocess!
  const cliRes = spawnSync(process.execPath, [BIN_PATH, 'prove', '--coverage', '--base', 'main', '--json'], {
    cwd: repo,
    encoding: 'utf8',
    timeout: 30_000,
  });
  assert.equal(cliRes.status, EXIT_PROVED, `stderr: ${cliRes.stderr}\nstdout: ${cliRes.stdout}`);
  const receipt = JSON.parse(cliRes.stdout);
  assert.equal(receipt.outcome, OUTCOME_PROVED);
  assert.equal(receipt.coverage.tool, 'node-v8');
  assert.equal(receipt.coverage.status, 'ok');
  assert.deepEqual(receipt.coverage.suites.formal.testFiles, ['test/ledger.formal.test.mjs']);
  assert.deepEqual(receipt.coverage.suites.vectors.testFiles, ['test/ledger.vectors.test.mjs']);

  // Formal hits line 3 (throw NEGATIVE), misses line 6 (amt === 0) and line 9 (amt > 1000000).
  const fLedger = receipt.coverage.suites.formal.files['src/ledger.mjs'];
  assert.ok(fLedger.diffCoveredLines.includes(3), JSON.stringify(fLedger));
  assert.ok(fLedger.diffMissedLines.includes(6), JSON.stringify(fLedger));
  assert.ok(fLedger.diffMissedLines.includes(9), JSON.stringify(fLedger));

  // Vectors hits line 6 (amt === 0), misses line 3 (throw NEGATIVE) and line 9 (amt > 1000000).
  const vLedger = receipt.coverage.suites.vectors.files['src/ledger.mjs'];
  assert.ok(vLedger.diffCoveredLines.includes(6), JSON.stringify(vLedger));
  assert.ok(vLedger.diffMissedLines.includes(3), JSON.stringify(vLedger));
  assert.ok(vLedger.diffMissedLines.includes(9), JSON.stringify(vLedger));

  // Union shows formalOnlyLines >= 1 and vectorsOnlyLines >= 1!
  assert.ok(receipt.coverage.unionFormalVectors.formalOnlyLines >= 1, JSON.stringify(receipt.coverage.unionFormalVectors));
  assert.ok(receipt.coverage.unionFormalVectors.vectorsOnlyLines >= 1, JSON.stringify(receipt.coverage.unionFormalVectors));

  // Uncovered diff lines catch BOTH line 9 in src/ledger.mjs AND all executable lines of unimported src/orphan.mjs!
  const ledgerGap = receipt.coverage.uncoveredDiffLines.find(g => g.file === 'src/ledger.mjs');
  assert.ok(ledgerGap && ledgerGap.lines.includes(9), JSON.stringify(receipt.coverage.uncoveredDiffLines));
  const orphanGap = receipt.coverage.uncoveredDiffLines.find(g => g.file === 'src/orphan.mjs');
  assert.ok(orphanGap && orphanGap.lines.length >= 3, JSON.stringify(receipt.coverage.uncoveredDiffLines));
  assert.equal(receipt.coverage.suites.all.files['src/orphan.mjs'].diffPct, 0);

  // AC5: Zero workspace pollution!
  const statusAfter = execFileSync('git', ['status', '--porcelain'], { cwd: repo, encoding: 'utf8' });
  assert.equal(statusAfter, '', 'prove --coverage MUST leave working tree completely clean');
  assert.equal(readFileSync(join(repo, 'src', 'ledger.mjs'), 'utf8'), prodBody);

  // AC6: Combining --coverage with --test/--expect exits 2 before running anything!
  const badCombo = spawnSync(process.execPath, [BIN_PATH, 'prove', '--coverage', '--base', 'main', '--test', 'npm test', '--expect', 'ERR'], {
    cwd: repo,
    encoding: 'utf8',
    timeout: 10_000,
  });
  assert.equal(badCombo.status, EXIT_USAGE);
  assert.equal(badCombo.stdout, '');
  assert.match(badCombo.stderr, /--coverage.*--mutation-check.*cannot be combined/i);
  assert.equal(validateProveOptInFlags({ coverage: true, test: 'npm test' }).exitCode, 2);
});

test('AC1/AC2 (Python live): runProveCoverage splits formal, vectors, and all on real Python repo with zero workspace pollution', { skip: !HAS_PYTHON3 }, t => {
  const repo = initGitRepo(t, 'pdd-prove-cov-py-');
  mkdirSync(join(repo, 'pkg'), { recursive: true });
  mkdirSync(join(repo, 'tests', 'formal'), { recursive: true });
  writeFileSync(join(repo, 'pkg', '__init__.py'), '');
  writeFileSync(join(repo, 'pkg', 'tax.py'), 'def calc(cents):\n    return cents\n');
  writeFileSync(join(repo, 'tests', 'test_tax.py'), [
    'import unittest',
    'from pkg.tax import calc',
    'class TaxUnit(unittest.TestCase):',
    '    def test_basic(self):',
    '        self.assertEqual(calc(100), 100)',
  ].join('\n') + '\n');
  commitAll(repo, 'py base');

  execFileSync('git', ['checkout', '-q', '-b', 'feat-py-cov'], { cwd: repo });
  writeFileSync(join(repo, 'pkg', 'tax.py'), [
    'def calc(cents):',
    '    if cents < 0:',
    '        raise ValueError("NEG")',
    '    if cents == 0:',
    '        return 0',
    '    if cents > 10000:',
    '        return cents + 50',
    '    return cents',
  ].join('\n') + '\n');
  writeFileSync(join(repo, 'tests', 'formal', 'test_tax_invariants.py'), [
    'import unittest',
    'from pkg.tax import calc',
    'class TaxFormal(unittest.TestCase):',
    '    def test_non_negative_and_neg_reject(self):',
    '        for v in range(1, 30):',
    '            self.assertEqual(calc(v), v)',
    '            with self.assertRaises(ValueError):',
    '                calc(-v)',
  ].join('\n') + '\n');
  writeFileSync(join(repo, 'tests', 'test_vectors_tax.py'), [
    'import unittest',
    'from pkg.tax import calc',
    'class TaxVectors(unittest.TestCase):',
    '    def test_zero_vector(self):',
    '        self.assertEqual(calc(0), 0)',
  ].join('\n') + '\n');
  commitAll(repo, 'py guards and split suites');

  const baseSha = execFileSync('git', ['rev-parse', 'main'], { cwd: repo, encoding: 'utf8' }).trim();
  const cov = runProveCoverage({
    root: repo,
    baseSha,
    baseRef: 'main',
    touchedFiles: ['pkg/tax.py', 'tests/formal/test_tax_invariants.py', 'tests/test_vectors_tax.py'],
    testCommand: 'python3 -m unittest discover -s tests',
  });
  assert.equal(cov.status, 'ok', JSON.stringify(cov));
  assert.ok(['coverage.py', 'python-trace'].includes(cov.tool), cov.tool);
  assert.deepEqual(cov.suites.formal.testFiles, ['tests/formal/test_tax_invariants.py']);
  assert.deepEqual(cov.suites.vectors.testFiles, ['tests/test_vectors_tax.py']);
  assert.ok(cov.suites.formal.files['pkg/tax.py'].diffCoveredLines.includes(3));
  assert.ok(cov.suites.formal.files['pkg/tax.py'].diffMissedLines.includes(5));
  assert.ok(cov.suites.vectors.files['pkg/tax.py'].diffCoveredLines.includes(5));
  assert.ok(cov.suites.vectors.files['pkg/tax.py'].diffMissedLines.includes(3));
  const taxGap = cov.uncoveredDiffLines.find(g => g.file === 'pkg/tax.py');
  assert.ok(taxGap && taxGap.lines.includes(7), JSON.stringify(cov.uncoveredDiffLines));
  assert.equal(execFileSync('git', ['status', '--porcelain'], { cwd: repo, encoding: 'utf8' }), '');
});

test('aggregateCoverageSplit handles zero production files as not-applicable cleanly', () => {
  const agg = aggregateCoverageSplit({ tool: 'node-v8', diffLinesByFile: {}, suites: {} });
  assert.equal(agg.status, 'not-applicable');
  assert.equal(agg.suites.all.total.pct, null);
  assert.deepEqual(agg.uncoveredDiffLines, []);
});

test('resolvePythonBinary accepts untracked Linux venv interpreter symlinks while refusing symlinked .venv dirs and git-tracked binaries', { skip: !HAS_PYTHON3 }, t => {
  const realPy3 = execFileSync('which', ['python3'], { encoding: 'utf8' }).trim();
  const repo = initGitRepo(t, 'pdd-pybin-venv-');
  writeFileSync(join(repo, '.gitignore'), '.venv/\n');
  writeFileSync(join(repo, 'app.py'), 'x = 1\n');
  commitAll(repo, 'base');

  // 1. Standard Linux venv interpreter symlink `.venv/bin/python3 -> /usr/bin/python3` (untracked) MUST resolve!
  mkdirSync(join(repo, '.venv', 'bin'), { recursive: true });
  symlinkSync(realPy3, join(repo, '.venv', 'bin', 'python3'));
  assert.equal(resolvePythonBinary(repo), join(repo, '.venv', 'bin', 'python3'));

  // 2. Git-tracked `.venv/bin/python3` MUST be refused!
  rmSync(join(repo, '.gitignore'));
  execFileSync('git', ['add', '-f', '.venv/bin/python3'], { cwd: repo });
  commitAll(repo, 'track evil venv python');
  assert.equal(resolvePythonBinary(repo), 'python3');

  // 3. Symlinked `.venv` directory MUST be refused!
  const repoSym = initGitRepo(t, 'pdd-pybin-symdir-');
  const outsideVenv = mkdtempSync(join(tmpdir(), 'pdd-outside-venv-'));
  t.after(() => rmSync(outsideVenv, { recursive: true, force: true }));
  mkdirSync(join(outsideVenv, 'bin'), { recursive: true });
  symlinkSync(realPy3, join(outsideVenv, 'bin', 'python3'));
  symlinkSync(outsideVenv, join(repoSym, '.venv'));
  assert.equal(resolvePythonBinary(repoSym), 'python3');
});

test('Finding 4: parsePythonTestPipeline supports &&-chained Python commands and fails closed on unsupported shell operators', { skip: !HAS_PYTHON3 }, t => {
  // Pure parser unit checks
  const chained = parsePythonTestPipeline('PYTHONPATH=src pytest tests/test_a.py && PYTHONPATH=src python3 -m unittest tests/test_b.py');
  assert.equal(chained.ok, true);
  assert.equal(chained.segments.length, 2);
  assert.equal(chained.segments[0].moduleName, 'pytest');
  assert.deepEqual(chained.segments[0].args, ['tests/test_a.py']);
  assert.equal(chained.segments[1].moduleName, 'unittest');
  assert.deepEqual(chained.segments[1].args, ['tests/test_b.py']);

  for (const bad of [
    'pytest tests/test_a.py || true',
    'pytest tests/test_a.py; echo ok',
    'pytest tests/test_a.py | cat',
    'pytest $(echo tests/test_a.py)',
    'pytest tests/test_a.py > /dev/null',
    'pytest tests/test_a.py &&',
  ]) {
    const parsed = parsePythonTestPipeline(bad);
    assert.equal(parsed.ok, false, `expected fail-closed for: ${bad}`);
  }

  // Real Python repo with &&-chained unittest verify.test -> coverage merges BOTH segments cleanly (Proved, exit 0)!
  const repo = initGitRepo(t, 'pdd-prove-cov-py-chain-');
  mkdirSync(join(repo, 'pkg'), { recursive: true });
  mkdirSync(join(repo, 'tests'), { recursive: true });
  writeFileSync(join(repo, 'pkg', '__init__.py'), '');
  writeFileSync(join(repo, 'pkg', 'ops.py'), 'def check(x):\n    return x\n');
  writeFileSync(join(repo, 'tests', 'test_a.py'), [
    'import unittest',
    'from pkg.ops import check',
    'class A(unittest.TestCase):',
    '    def test_neg(self):',
    '        self.assertEqual(check(-1), -1)',
  ].join('\n') + '\n');
  writeFileSync(join(repo, 'tests', 'test_b.py'), [
    'import unittest',
    'from pkg.ops import check',
    'class B(unittest.TestCase):',
    '    def test_pos(self):',
    '        self.assertEqual(check(5), 5)',
  ].join('\n') + '\n');
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({
    verify: {
      test: 'python3 -m unittest tests/test_a.py && python3 -m unittest tests/test_b.py',
      paths: [{ id: 'ops', when: ['pkg/**/*.py'], run: 'python3 -m unittest tests/test_a.py && python3 -m unittest tests/test_b.py' }],
    },
  }, null, 2) + '\n');
  commitAll(repo, 'base');

  execFileSync('git', ['checkout', '-q', '-b', 'feat-chain'], { cwd: repo });
  writeFileSync(join(repo, 'pkg', 'ops.py'), [
    'def check(x):',
    '    if x < 0:',
    '        return -1',
    '    if x > 0:',
    '        return 5',
    '    return 0',
  ].join('\n') + '\n');
  commitAll(repo, 'add branches');

  const okRes = runProve({ cwd: repo, base: 'main', coverage: true, json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(okRes.exitCode, EXIT_PROVED, JSON.stringify(okRes.receipt));
  assert.equal(okRes.receipt.coverage.status, 'ok');
  const allCov = okRes.receipt.coverage.suites.all.files['pkg/ops.py'];
  assert.ok(allCov.diffCoveredLines.includes(3), `line 3 covered by test_a: ${JSON.stringify(allCov)}`);
  assert.ok(allCov.diffCoveredLines.includes(5), `line 5 covered by test_b: ${JSON.stringify(allCov)}`);
  assert.ok(allCov.diffMissedLines.includes(6), `line 6 uncovered: ${JSON.stringify(allCov)}`);

  // Unsupported shell operator `|| true` in Python verify.test MUST fail closed as Not proved (exit 3), NEVER false Failed (exit 1)!
  const repoBad = initGitRepo(t, 'pdd-prove-cov-py-shell-');
  mkdirSync(join(repoBad, 'pkg'), { recursive: true });
  mkdirSync(join(repoBad, 'tests'), { recursive: true });
  writeFileSync(join(repoBad, 'pkg', '__init__.py'), '');
  writeFileSync(join(repoBad, 'pkg', 'ops.py'), 'def check(x):\n    return x\n');
  writeFileSync(join(repoBad, 'tests', 'test_a.py'), 'import unittest\nfrom pkg.ops import check\nclass A(unittest.TestCase):\n    def test_a(self): self.assertEqual(check(1), 1)\n');
  writeFileSync(join(repoBad, 'pdd.json'), JSON.stringify({
    verify: {
      test: 'python3 -m unittest tests/test_a.py || true',
      paths: [{ id: 'ops', when: ['pkg/**/*.py'], run: 'python3 -m unittest tests/test_a.py' }],
    },
  }, null, 2) + '\n');
  commitAll(repoBad, 'base');

  execFileSync('git', ['checkout', '-q', '-b', 'feat-bad-op'], { cwd: repoBad });
  writeFileSync(join(repoBad, 'pkg', 'ops.py'), 'def check(x):\n    if x < 0: return 0\n    return x\n');
  commitAll(repoBad, 'touch');

  const unavailRes = runProve({ cwd: repoBad, base: 'main', coverage: true, json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(unavailRes.exitCode, EXIT_NOT_PROVED, JSON.stringify(unavailRes.receipt));
  assert.equal(unavailRes.outcome, OUTCOME_NOT_PROVED);
  assert.equal(unavailRes.receipt.coverage.suites.all.status, 'unavailable');
  assert.deepEqual(unavailRes.receipt.coverage.errors, []);
});

test('Reviewer P1 #1 & P2 #6: V8 coverage aligns offsets with // Prompt headers and quote-bearing regexes; diff handles +++ body lines, mnemonicPrefix, and Python ENOENT', async t => {
  // 1. V8 coverage on a PDD-owned JS file starting with `// Prompt: ...`, inline `//`, and `/^['"]|['"]$/g` regex
  const src = [
    '// Prompt: prompts/cli/demo.prompt.md',
    '',
    '// Strip quotes before checking guard',
    'export function cleanCheck(raw) {',
    '  const s = String(raw).replace(/^[\'"]|[\'"]$/g, "");',
    '  if (s.length === 0) {',
    '    return false;',
    '  }',
    '  return true;',
    '}',
  ].join('\n') + '\n';
  const blockStart = src.indexOf('{', src.indexOf('if (s.length === 0)'));
  const blockEnd = src.indexOf('}', blockStart) + 1;
  const cov = resolveV8FileCoverage({
    sourceText: src,
    functions: [
      { functionName: '', isBlockCoverage: true, ranges: [{ startOffset: 0, endOffset: src.length, count: 1 }] },
      {
        functionName: 'cleanCheck',
        isBlockCoverage: true,
        ranges: [
          { startOffset: src.indexOf('export function'), endOffset: src.length - 1, count: 1 },
          { startOffset: blockStart, endOffset: blockEnd, count: 0 },
        ],
      },
    ],
  });
  assert.equal(cov.executedLines.includes(1), false, `comment line 1 MUST NOT be executed: ${JSON.stringify(cov)}`);
  assert.equal(cov.executedLines.includes(3), false, `comment line 3 MUST NOT be executed: ${JSON.stringify(cov)}`);
  assert.ok(cov.executedLines.includes(5), `regex line 5 MUST be executed: ${JSON.stringify(cov)}`);
  assert.ok(cov.executedLines.includes(6), `if line 6 MUST be executed: ${JSON.stringify(cov)}`);
  assert.ok(cov.executedLines.includes(9), `return true line 9 MUST be executed: ${JSON.stringify(cov)}`);
  assert.deepEqual(cov.missedLines, [7], `return false line 7 MUST be missed: ${JSON.stringify(cov)}`);

  // 2. Added hunk body line starting with `++ ` (rendered as `+++ ...`) MUST NOT hijack curFile
  const trickyDiff = [
    'diff --git a/src/fmt.mjs b/src/fmt.mjs',
    '--- a/src/fmt.mjs',
    '+++ b/src/fmt.mjs',
    '@@ -1,0 +2,2 @@',
    '+++ not-a-file-header',
    '+export const ok = 1;',
    '@@ -10,0 +12,1 @@',
    '+export const stillFmt = 2;',
  ].join('\n');
  assert.deepEqual(parseUnifiedDiffAddedLines({ diffText: trickyDiff }).files, { 'src/fmt.mjs': [2, 3, 12] });

  // 3. `git config diff.mnemonicPrefix true` MUST NOT drop modified files in collectDiffLines
  const repo = initGitRepo(t, 'pdd-cov-mnemonic-');
  execFileSync('git', ['config', 'diff.mnemonicPrefix', 'true'], { cwd: repo });
  mkdirSync(join(repo, 'src'), { recursive: true });
  writeFileSync(join(repo, 'src', 'm.mjs'), '// Prompt: prompts/m.prompt.md\n\nexport const x = 1;\n');
  commitAll(repo, 'base');
  const baseSha = execFileSync('git', ['rev-parse', 'HEAD'], { cwd: repo, encoding: 'utf8' }).trim();
  writeFileSync(join(repo, 'src', 'm.mjs'), '// Prompt: prompts/m.prompt.md\n\nexport const x = 2;\n');
  const collected = collectDiffLines({ root: repo, baseSha });
  assert.deepEqual(collected.diffLinesByFile, { 'src/m.mjs': [3] });

  // 4. Python ENOENT reports status: 'unavailable' (not 'failed')
  const pyRepo = initGitRepo(t, 'pdd-cov-py-enoent-');
  mkdirSync(join(pyRepo, 'pkg'), { recursive: true });
  writeFileSync(join(pyRepo, 'pkg', 'a.py'), 'x = 1\n');
  commitAll(pyRepo, 'base');
  const pyBase = execFileSync('git', ['rev-parse', 'HEAD'], { cwd: pyRepo, encoding: 'utf8' }).trim();
  writeFileSync(join(pyRepo, 'pkg', 'a.py'), 'x = 2\n');
  const enoentCov = runProveCoverage(
    { root: pyRepo, baseSha: pyBase, baseRef: 'main', testCommand: 'python3 -m unittest' },
    { spawnSync: () => ({ status: null, signal: null, stdout: '', stderr: '', error: Object.assign(new Error('spawn python3 ENOENT'), { code: 'ENOENT' }) }) },
  );
  assert.equal(enoentCov.suites.all.status, 'unavailable');
  assert.deepEqual(enoentCov.errors, []);
  assert.ok(enoentCov.notProvedReasons.some(r => /unavailable/i.test(r)));

  // 5. P3: SIGTERM mid-coverage exits promptly with SIGTERM and zero leaked temp dirs
  const sigRepo = initGitRepo(t, 'pdd-cov-sigterm-');
  const nodeBin = JSON.stringify(process.execPath);
  mkdirSync(join(sigRepo, 'src'), { recursive: true });
  mkdirSync(join(sigRepo, 'test'), { recursive: true });
  writeFileSync(join(sigRepo, 'package.json'), JSON.stringify({ name: 'cov-sig', type: 'module', scripts: { test: `${nodeBin} --test test/*.test.mjs` } }, null, 2) + '\n');
  writeFileSync(join(sigRepo, 'pdd.json'), JSON.stringify({
    verify: { test: `${nodeBin} -e "process.exit(0)"`, paths: [{ id: 's', when: ['src/**/*.mjs'], run: `${nodeBin} -e "process.exit(0)"` }] },
  }, null, 2) + '\n');
  writeFileSync(join(sigRepo, 'src', 'slow.mjs'), 'export const f = x => x;\n');
  commitAll(sigRepo, 'base');
  execFileSync('git', ['checkout', '-q', '-b', 'feat-cov-sig'], { cwd: sigRepo });
  writeFileSync(join(sigRepo, 'src', 'slow.mjs'), 'export const f = x => x + 1;\n');
  writeFileSync(join(sigRepo, 'test', 'slow.formal.test.mjs'), [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { f } from '../src/slow.mjs';",
    "test('slow', async () => { await new Promise(r => setTimeout(r, 2000)); assert.equal(f(1), 2); });",
  ].join('\n') + '\n');
  commitAll(sigRepo, 'slow formal');

  const isolatedTmp = mkdtempSync(join(tmpdir(), 'pdd-cov-sig-tmp-'));
  t.after(() => rmSync(isolatedTmp, { recursive: true, force: true }));
  const child = spawn(process.execPath, [BIN_PATH, 'prove', '--coverage', '--base', 'main'], {
    cwd: sigRepo,
    env: { ...process.env, TMPDIR: isolatedTmp },
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  const exitInfo = await new Promise(resolve => {
    const timer = setTimeout(() => { try { child.kill('SIGTERM'); } catch {} }, 600);
    child.on('exit', (code, signal) => { clearTimeout(timer); resolve({ code, signal }); });
  });
  assert.equal(exitInfo.signal, 'SIGTERM', JSON.stringify(exitInfo));
  assert.equal(exitInfo.code, null);
  assert.deepEqual(readdirSync(isolatedTmp).filter(n => n.startsWith('pdd-prove-') || n.startsWith('pdd-formal-run-')), []);
});
