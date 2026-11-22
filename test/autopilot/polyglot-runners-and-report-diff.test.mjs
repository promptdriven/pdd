import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import {
  detectTestRunner,
  extractTestCases,
  parseJunitXml,
  parseTestSummaryOutput,
} from '../../src/autopilot/core/test-runners.mjs';
import {
  CACHE_KEY_FIELDS,
  compareTestReports,
  runBaseOwnedTestOracle,
} from '../../src/autopilot/core/report-diff.mjs';
import { calculateCheckCapacity, runTestSuite } from '../../src/test-suite-queue.mjs';
import { checkMachine, withCheckLifetime } from '../helpers/check-machine.mjs';

const quote = s => `'${s.replaceAll("'", "'\\''")}'`;

const VALID_META = Object.freeze({
  baseSha: 'a'.repeat(40),
  policyDigest: 'pol-sha256-1',
  recipeDigest: 'rec-sha256-1',
  toolchain: 'node-22',
  platform: 'darwin-arm64',
  profile: 'default',
});

test('3561 detectTestRunner auto-detects node:test, vitest, pytest, cargo, and go from files, package.json, and disk', t => {
  assert.equal(detectTestRunner(null, { scripts: { test: 'vitest run' } })?.kind, 'vitest');
  assert.equal(detectTestRunner(null, { devDependencies: { vitest: '^2.0.0' } })?.kind, 'vitest');
  assert.equal(detectTestRunner(null, ['vitest.config.ts', 'src/a.ts'])?.kind, 'vitest');
  assert.equal(detectTestRunner(null, { scripts: { test: 'node --test' } })?.kind, 'node:test');
  assert.equal(detectTestRunner(null, ['Cargo.toml', 'src/lib.rs'])?.kind, 'cargo');
  assert.equal(detectTestRunner(null, ['go.mod', 'pkg/calc_test.go'])?.kind, 'go');
  assert.equal(detectTestRunner(null, ['pytest.ini', 'tests/test_app.py'])?.kind, 'pytest');
  assert.equal(detectTestRunner(null, { files: ['pyproject.toml'], pyprojectText: '[tool.pytest.ini_options]\naddopts = "-q"\n' })?.kind, 'pytest');
  assert.equal(detectTestRunner(null, ['README.md']), null);

  const root = mkdtempSync(join(tmpdir(), 'pdd-detect-runner-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const rustDir = join(root, 'rust'), goDir = join(root, 'go'), pyDir = join(root, 'py');
  mkdirSync(rustDir); mkdirSync(goDir); mkdirSync(pyDir);
  writeFileSync(join(rustDir, 'Cargo.toml'), '[package]\nname = "demo"\n');
  writeFileSync(join(goDir, 'go.mod'), 'module example.com/demo\n');
  writeFileSync(join(pyDir, 'pyproject.toml'), '[tool.pytest.ini_options]\n');
  assert.equal(detectTestRunner(rustDir)?.kind, 'cargo');
  assert.equal(detectTestRunner(goDir)?.kind, 'go');
  assert.equal(detectTestRunner(pyDir)?.kind, 'pytest');
});

test('3561 parseTestSummaryOutput & extractTestCases support all 5 runners and fail closed on incomplete output', () => {
  // 1. node:test TAP v13 (nested subtests + SKIP + duration_ms)
  const tap = [
    'TAP version 13',
    '# Subtest: math',
    '    # Subtest: adds',
    '    ok 1 - adds',
    '      ---',
    '      duration_ms: 1.25',
    '      ...',
    '    # Subtest: skipped case',
    '    ok 2 - skipped case # SKIP pending',
    '      ---',
    '      duration_ms: 0.1',
    '      ...',
    '    # Subtest: fails',
    '    not ok 3 - fails',
    '      ---',
    '      duration_ms: 2.5',
    '      ...',
    '    1..3',
    'not ok 1 - math',
    '  ---',
    '  duration_ms: 4.0',
    "  type: 'suite'",
    '  ...',
    '1..1',
    '# tests 3', '# suites 1', '# pass 1', '# fail 1', '# cancelled 0', '# skipped 1', '# todo 0',
    '',
  ].join('\n');
  assert.deepEqual(parseTestSummaryOutput(tap), { total: 3, passed: 1, failed: 1, skipped: 1, format: 'tap' });
  assert.deepEqual(extractTestCases(tap, 'tap'), [
    { id: 'math > adds', status: 'pass', durationMs: 1.25 },
    { id: 'math > skipped case', status: 'skip', durationMs: 0.1 },
    { id: 'math > fails', status: 'fail', durationMs: 2.5 },
  ]);
  // Incomplete TAP without plan or with Bail out! fails closed.
  assert.equal(parseTestSummaryOutput('TAP version 13\n# tests 2\n# pass 2\n'), null);
  assert.equal(parseTestSummaryOutput('TAP version 13\n1..2\nok 1 - a\nBail out! crashed\n'), null);

  // 2. Vitest (ANSI CLI output)
  const vitestOut = [
    '\x1b[32m Test Files \x1b[0m 2 passed (2)',
    '\x1b[32m      Tests \x1b[0m 10 passed | 1 failed | 2 skipped (13)',
    '   Duration  412ms',
  ].join('\n');
  assert.deepEqual(parseTestSummaryOutput(vitestOut), { total: 13, passed: 10, failed: 1, skipped: 2, format: 'vitest' });

  // 3. Pytest (CLI summary + verbose case lines)
  const pytestOut = [
    'tests/test_math.py::test_add PASSED',
    'tests/test_math.py::test_div FAILED',
    'tests/test_math.py::test_slow SKIPPED',
    'tests/test_math.py::test_setup ERROR',
    '=== 1 passed, 1 failed, 1 skipped, 1 error in 0.42s ===',
  ].join('\n');
  assert.deepEqual(parseTestSummaryOutput(pytestOut), { total: 4, passed: 1, failed: 2, skipped: 1, format: 'pytest' });
  assert.deepEqual(extractTestCases(pytestOut, 'pytest'), [
    { id: 'tests/test_math.py::test_add', status: 'pass', durationMs: null },
    { id: 'tests/test_math.py::test_div', status: 'fail', durationMs: null },
    { id: 'tests/test_math.py::test_slow', status: 'skip', durationMs: null },
    { id: 'tests/test_math.py::test_setup', status: 'error', durationMs: null },
  ]);
  assert.deepEqual(parseTestSummaryOutput('=== no tests ran in 0.01s ==='), { total: 0, passed: 0, failed: 0, skipped: 0, format: 'pytest' });

  // 4. Cargo test (multiple test binaries aggregated; incomplete binary fails closed)
  const cargoOut = [
    'running 2 tests',
    'test alpha::ok_case ... ok',
    'test alpha::skip_case ... ignored',
    'test result: ok. 1 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 0.01s',
    'running 2 tests',
    'test beta::pass_case ... ok',
    'test beta::bad_case ... FAILED',
    'test result: FAILED. 1 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.02s',
  ].join('\n');
  assert.deepEqual(parseTestSummaryOutput(cargoOut), { total: 4, passed: 2, failed: 1, skipped: 1, format: 'cargo' });
  assert.equal(extractTestCases(cargoOut, 'cargo').length, 4);
  assert.equal(parseTestSummaryOutput('running 3 tests\ntest a ... ok\n'), null, 'killed cargo run without test result must fail closed');

  // 5. go test -json (NDJSON events; unfinished run fails closed; build-fail surfaces error case)
  const goJson = [
    JSON.stringify({ Action: 'run', Package: 'example/calc', Test: 'TestAdd' }),
    JSON.stringify({ Action: 'pass', Package: 'example/calc', Test: 'TestAdd', Elapsed: 0.012 }),
    JSON.stringify({ Action: 'run', Package: 'example/calc', Test: 'TestSub' }),
    JSON.stringify({ Action: 'fail', Package: 'example/calc', Test: 'TestSub', Elapsed: 0.05 }),
    JSON.stringify({ Action: 'run', Package: 'example/calc', Test: 'TestSkip' }),
    JSON.stringify({ Action: 'skip', Package: 'example/calc', Test: 'TestSkip', Elapsed: 0 }),
    JSON.stringify({ Action: 'fail', Package: 'example/calc', Elapsed: 0.08 }),
  ].join('\n');
  assert.deepEqual(parseTestSummaryOutput(goJson), { total: 3, passed: 1, failed: 1, skipped: 1, format: 'go-json' });
  assert.deepEqual(extractTestCases(goJson, 'go-json'), [
    { id: 'example/calc::TestAdd', status: 'pass', durationMs: 12 },
    { id: 'example/calc::TestSub', status: 'fail', durationMs: 50 },
    { id: 'example/calc::TestSkip', status: 'skip', durationMs: 0 },
  ]);
  const truncatedGo = JSON.stringify({ Action: 'run', Package: 'example/calc', Test: 'TestHung' }) + '\n';
  assert.equal(parseTestSummaryOutput(truncatedGo), null, 'unfinished go test run must fail closed');
  const buildFailGo = JSON.stringify({ Action: 'build-fail', Package: 'example/broken' }) + '\n';
  assert.deepEqual(extractTestCases(buildFailGo, 'go-json'), [{ id: 'example/broken::<build>', status: 'error', durationMs: null }]);
});

test('G3 parseJunitXml handles CDATA, escaped entities, nested testsuites, and fails closed on malformed/unsafe XML', () => {
  const xml = `<?xml version="1.0" encoding="UTF-8"?>
  <!-- report comment -->
  <testsuites name="root">
    <testsuite name="suiteA" tests="4">
      <testcase classname="pkg.Math" name="adds &amp; rounds &lt;ok&gt;" time="0.125" />
      <testcase classname="pkg.Math" name="skips" time="0.001"><skipped message="env" /></testcase>
      <testsuite name="nested">
        <testcase name="fails_cdata" time="0.2"><failure message="bad"><![CDATA[expected <tag> & <!ENTITY fake>]]></failure></testcase>
        <testcase name="errors_out" time="0.05"><error type="Boom">boom &quot;err&quot; &#39;x&#39;</error></testcase>
      </testsuite>
    </testsuite>
  </testsuites>`;
  const parsed = parseJunitXml(xml);
  assert.equal(parsed.ok, true);
  assert.deepEqual(parsed.counts, { total: 4, passed: 1, failed: 2, skipped: 1, format: 'junit' });
  assert.deepEqual(parsed.cases, [
    { id: 'pkg.Math::adds & rounds <ok>', status: 'pass', durationMs: 125 },
    { id: 'pkg.Math::skips', status: 'skip', durationMs: 1 },
    { id: 'suiteA::nested::fails_cdata', status: 'fail', durationMs: 200 },
    { id: 'suiteA::nested::errors_out', status: 'error', durationMs: 50 },
  ]);

  for (const badXml of [
    '<testsuite><testcase name="a"></testsuite>',
    '<testsuite><testcase name="a"/><![CDATA[unclosed',
    '<!DOCTYPE foo [<!ENTITY xxe "boom">]><testsuite><testcase name="a"/></testsuite>',
    'not xml at all',
  ]) {
    const res = parseJunitXml(badXml);
    assert.equal(res.ok, false, `malformed XML must fail closed: ${badXml}`);
    assert.equal(res.complete, false);
  }
});

test('G3 compareTestReports enforces fail-closed unknowns, cache-key parity, shard integrity, and non-compensatory diffs across JUnit/TAP/go-json', () => {
  const baseXml = `<testsuite name="s">
    <testcase classname="c" name="t1" time="0.1"/>
    <testcase classname="c" name="t2" time="0.1"/>
    <testcase classname="c" name="t3" time="0.1"/>
    <testcase classname="c" name="t4" time="0.1"><failure>preexisting</failure></testcase>
  </testsuite>`;
  const headCleanXml = `<testsuite name="s">
    <testcase classname="c" name="t1" time="0.1"/>
    <testcase classname="c" name="t2" time="0.1"/>
    <testcase classname="c" name="t4" time="0.1"/>
    <testcase classname="c" name="t5" time="0.1"/>
  </testsuite>`;

  // 1. Clean diff with approved removal of t3, fixed t4, added t5 -> ALLOW
  const okDiff = compareTestReports({
    baseReport: baseXml, headReport: headCleanXml,
    baseMeta: VALID_META, headMeta: VALID_META,
    approvedRemovals: ['c::t3'],
  });
  assert.equal(okDiff.status, 'pass');
  assert.equal(okDiff.verdict, 'ALLOW');
  assert.deepEqual(okDiff.missingIds, []);
  assert.deepEqual(okDiff.approvedRemovedIds, ['c::t3']);
  assert.deepEqual(okDiff.fixedIds, ['c::t4']);
  assert.deepEqual(okDiff.addedIds, ['c::t5']);

  // 2. Unapproved missing test + newly skipped + newly failing -> HOLD
  const headRegressedXml = `<testsuite name="s">
    <testcase classname="c" name="t1" time="0.1"><skipped/></testcase>
    <testcase classname="c" name="t2" time="0.1"><failure>regressed</failure></testcase>
    <testcase classname="c" name="t4" time="0.1"><failure>preexisting</failure></testcase>
  </testsuite>`;
  const badDiff = compareTestReports({
    baseReport: baseXml, headReport: headRegressedXml,
    baseMeta: VALID_META, headMeta: VALID_META,
  });
  assert.equal(badDiff.status, 'fail');
  assert.equal(badDiff.verdict, 'HOLD');
  assert.deepEqual(badDiff.missingIds, ['c::t3']);
  assert.deepEqual(badDiff.newlySkippedIds, ['c::t1']);
  assert.deepEqual(badDiff.newlyFailingIds, ['c::t2']);
  assert.deepEqual(badDiff.preexistingFailingIds, ['c::t4']);

  // 3. TAP v13 and go test -json diffs work natively too
  const tapBase = 'TAP version 13\n1..2\nok 1 - alpha\nok 2 - beta\n';
  const tapHead = 'TAP version 13\n1..2\nok 1 - alpha\nok 2 - beta # SKIP lazy\n';
  const tapDiff = compareTestReports({ baseReport: tapBase, headReport: tapHead, baseMeta: VALID_META, headMeta: VALID_META });
  assert.equal(tapDiff.status, 'fail');
  assert.deepEqual(tapDiff.newlySkippedIds, ['beta']);

  const goBase = [
    JSON.stringify({ Action: 'run', Package: 'p', Test: 'TestA' }),
    JSON.stringify({ Action: 'pass', Package: 'p', Test: 'TestA', Elapsed: 0.01 }),
    JSON.stringify({ Action: 'run', Package: 'p', Test: 'TestB' }),
    JSON.stringify({ Action: 'pass', Package: 'p', Test: 'TestB', Elapsed: 0.01 }),
  ].join('\n');
  const goHead = [
    JSON.stringify({ Action: 'run', Package: 'p', Test: 'TestA' }),
    JSON.stringify({ Action: 'pass', Package: 'p', Test: 'TestA', Elapsed: 0.01 }),
  ].join('\n');
  const goDiff = compareTestReports({ baseReport: goBase, headReport: goHead, baseMeta: VALID_META, headMeta: VALID_META });
  assert.equal(goDiff.status, 'fail');
  assert.deepEqual(goDiff.missingIds, ['p::TestB']);

  // 4. Fail closed to status:'unknown' (NEVER green) on every cache key mismatch, shard mismatch, kill, non-zero without failure, missing/malformed, or zero tests
  for (const field of CACHE_KEY_FIELDS) {
    const mismatched = compareTestReports({
      baseReport: baseXml, headReport: baseXml,
      baseMeta: VALID_META, headMeta: { ...VALID_META, [field]: 'different-value' },
    });
    assert.equal(mismatched.status, 'unknown', `cache key mismatch on ${field} must fail closed`);
    assert.equal(mismatched.verdict, 'HOLD');
    assert.equal(mismatched.reason, 'cache_key_mismatch');
    assert.deepEqual(mismatched.mismatches, [field]);
  }

  const zeroTests = compareTestReports({
    baseReport: '<testsuite name="empty"/>', headReport: baseXml,
    baseMeta: VALID_META, headMeta: VALID_META,
  });
  assert.equal(zeroTests.status, 'unknown');
  assert.equal(zeroTests.reason, 'zero_collected_tests');

  const partialShards = compareTestReports({
    baseReport: baseXml, headReport: baseXml,
    baseMeta: { ...VALID_META, expectedShards: 4, completedShards: 4 },
    headMeta: { ...VALID_META, expectedShards: 4, completedShards: 3 },
  });
  assert.equal(partialShards.status, 'unknown');
  assert.equal(partialShards.reason, 'partial_shard_mismatch');

  const killedRun = compareTestReports({
    baseReport: baseXml, headReport: baseXml,
    baseMeta: VALID_META, headMeta: { ...VALID_META, killed: true, signal: 'SIGKILL' },
  });
  assert.equal(killedRun.status, 'unknown');
  assert.equal(killedRun.reason, 'runner_killed');

  const nonZeroCleanXml = '<testsuite name="s"><testcase classname="c" name="t1" time="0.1"/></testsuite>';
  const crashedNoFailures = compareTestReports({
    baseReport: nonZeroCleanXml, headReport: nonZeroCleanXml,
    baseMeta: VALID_META, headMeta: { ...VALID_META, exitCode: 137 },
  });
  assert.equal(crashedNoFailures.status, 'unknown');
  assert.equal(crashedNoFailures.reason, 'runner_nonzero_without_failures');

  const malformed = compareTestReports({
    baseReport: baseXml, headReport: '<testsuite><broken',
    baseMeta: VALID_META, headMeta: VALID_META,
  });
  assert.equal(malformed.status, 'unknown');
  assert.equal(malformed.reason, 'missing_or_malformed_report');
});

test('G3 runBaseOwnedTestOracle catches weakened assertions inside surviving edited test on real git worktrees without mutating headTree', async t => {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-oracle-wt-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));

  const baseRepo = join(scratch, 'base');
  const headWorktree = join(scratch, 'head');
  mkdirSync(join(baseRepo, 'src'), { recursive: true });
  mkdirSync(join(baseRepo, 'test'), { recursive: true });

  writeFileSync(join(baseRepo, 'src/tax.mjs'), 'export const computeTax = cents => Math.round(cents * 0.10);\n');
  writeFileSync(
    join(baseRepo, 'test/tax.test.mjs'),
    [
      "import test from 'node:test';",
      "import assert from 'node:assert/strict';",
      "import { computeTax } from '../src/tax.mjs';",
      "test('computes exact 10 percent tax', () => {",
      '  assert.equal(computeTax(100), 10);',
      '});',
      '',
    ].join('\n'),
  );
  execFileSync('git', ['init', '-q'], { cwd: baseRepo });
  execFileSync('git', ['add', '.'], { cwd: baseRepo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=t@example.com', 'commit', '-q', '-m', 'base'], { cwd: baseRepo });
  execFileSync('git', ['worktree', 'add', '-q', '-b', 'pr-head', headWorktree, 'HEAD'], { cwd: baseRepo });
  t.after(() => {
    try { execFileSync('git', ['worktree', 'remove', '--force', headWorktree], { cwd: baseRepo, stdio: 'ignore' }); } catch {}
  });

  // PR breaks implementation (5% instead of 10%) AND weakens assertion inside surviving test so head alone looks green!
  writeFileSync(join(headWorktree, 'src/tax.mjs'), 'export const computeTax = cents => Math.round(cents * 0.05);\n');
  const weakenedHeadTest = [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { computeTax } from '../src/tax.mjs';",
    "test('computes exact 10 percent tax', () => {",
    '  assert.ok(computeTax(100) > 0);',
    '});',
    '',
  ].join('\n');
  writeFileSync(join(headWorktree, 'test/tax.test.mjs'), weakenedHeadTest);

  // Confirm head tests pass on their own (proving the weakened assertion hides the regression!)
  const cleanChildEnv = { PATH: process.env.PATH, HOME: scratch };
  const headAlone = execFileSync(process.execPath, ['--test', '--test-reporter=tap', 'test/tax.test.mjs'], {
    cwd: headWorktree, env: cleanChildEnv, encoding: 'utf8',
  });
  assert.match(headAlone, /# pass 1\b/);

  // 1. Oracle overlays base test onto clean copy of head and catches unlisted_base_test_regression -> HOLD!
  const cmd = [process.execPath, '--test', '--test-reporter=tap', 'test/tax.test.mjs'];
  const held = await runBaseOwnedTestOracle({
    baseTree: baseRepo,
    headTree: headWorktree,
    editedTestFiles: ['test/tax.test.mjs'],
    testCommand: cmd,
  });
  assert.equal(held.status, 'fail');
  assert.equal(held.verdict, 'HOLD');
  assert.equal(held.reason, 'unlisted_base_test_regression');
  assert.deepEqual(held.overlaidFiles, ['test/tax.test.mjs']);
  assert.equal(held.regressions.length, 1);
  assert.equal(held.regressions[0].id, 'computes exact 10 percent tax');
  // headTree must NEVER be mutated!
  assert.equal(readFileSync(join(headWorktree, 'test/tax.test.mjs'), 'utf8'), weakenedHeadTest);

  // 2. When explicitly declared in intendedChanges, oracle allows it!
  const allowed = await runBaseOwnedTestOracle({
    baseTree: baseRepo,
    headTree: headWorktree,
    editedTestFiles: ['test/tax.test.mjs'],
    testCommand: cmd,
    intendedChanges: ['computes exact 10 percent tax'],
  });
  assert.equal(allowed.status, 'pass');
  assert.equal(allowed.verdict, 'ALLOW');
  assert.equal(allowed.reason, 'intended_changes_only');
  assert.equal(allowed.intendedFailures.length, 1);

  // 3. Symlink and path traversal in editedTestFiles fail closed!
  symlinkSync(join(baseRepo, 'test/tax.test.mjs'), join(headWorktree, 'test/sym.test.mjs'));
  for (const unsafePath of ['../outside.test.mjs', 'test/sym.test.mjs']) {
    const res = await runBaseOwnedTestOracle({
      baseTree: baseRepo,
      headTree: headWorktree,
      editedTestFiles: [unsafePath],
      testCommand: cmd,
    });
    assert.equal(res.status, 'unknown', `unsafe path ${unsafePath} must fail closed`);
    assert.equal(res.verdict, 'HOLD');
    assert.equal(res.reason, 'unsafe_test_path');
  }
});

test('test-suite-queue passes polyglot toolchain env vars and test-suite-recorder records counts for pytest, vitest, cargo, and go test -json', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-polyglot-queue-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const queue = join(root, 'queue'), home = join(root, 'home'), state = join(root, 'state');
  mkdirSync(queue); mkdirSync(home); mkdirSync(state);
  const machine = checkMachine({ taskset: null });
  writeFileSync(join(queue, 'capacity.json'), JSON.stringify(withCheckLifetime(calculateCheckCapacity({ checks: 1 }, machine.ports))));

  const env = {
    PATH: process.env.PATH, HOME: home, PDD_STATE_DIR: state, PDD_SUITE_QUEUE: queue,
    GOPATH: '/opt/go', GOMODCACHE: '/opt/gomodcache', CARGO_HOME: '/opt/cargo', RUSTUP_HOME: '/opt/rustup',
    VIRTUAL_ENV: '/opt/venv', UV_CACHE_DIR: '/opt/uv-cache', PYTEST_ADDOPTS: '-q --tb=short',
    GH_TOKEN: 'ghs_must_be_scrubbed', OPENAI_API_KEY: 'sk-must-be-scrubbed',
  };

  // 1. Verify toolchain env passthrough & secret scrubbing in test-suite-queue
  let capturedEnv = null;
  const envRes = await runTestSuite({ cwd: root, command: 'true', env }, {
    ...machine.ports, say: () => {},
    execute: async (_cmd, opts) => { capturedEnv = opts.env; opts.onChild(process.pid); return { exitCode: 0 }; },
  });
  assert.equal(envRes.exitCode, 0);
  for (const [k, v] of [
    ['GOPATH', '/opt/go'], ['GOMODCACHE', '/opt/gomodcache'], ['CARGO_HOME', '/opt/cargo'],
    ['RUSTUP_HOME', '/opt/rustup'], ['VIRTUAL_ENV', '/opt/venv'], ['UV_CACHE_DIR', '/opt/uv-cache'],
    ['PYTEST_ADDOPTS', '-q --tb=short'],
  ]) {
    assert.equal(capturedEnv[k], v, `${k} must pass through cleanly`);
  }
  assert.equal(capturedEnv.GH_TOKEN, undefined);
  assert.equal(capturedEnv.OPENAI_API_KEY, undefined);

  // 2. Verify test-suite-recorder records polyglot counts for pytest, vitest, cargo, and go test -json
  const samples = [
    ['pytest', '=== 4 passed, 1 failed, 2 skipped in 0.31s ===\n', { tests: 7, pass: 4, fail: 1, skipped: 2, format: 'pytest' }],
    ['vitest', ' Test Files  1 passed (1)\n      Tests  5 passed | 1 skipped (6)\n   Duration  120ms\n', { tests: 6, pass: 5, fail: 0, skipped: 1, format: 'vitest' }],
    ['cargo', 'running 3 tests\ntest a ... ok\ntest b ... ok\ntest c ... ignored\ntest result: ok. 2 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 0.01s\n', { tests: 3, pass: 2, fail: 0, skipped: 1, format: 'cargo' }],
    ['go', `${JSON.stringify({ Action: 'run', Package: 'm/p', Test: 'TestOne' })}\n${JSON.stringify({ Action: 'pass', Package: 'm/p', Test: 'TestOne', Elapsed: 0.01 })}\n${JSON.stringify({ Action: 'run', Package: 'm/p', Test: 'TestTwo' })}\n${JSON.stringify({ Action: 'fail', Package: 'm/p', Test: 'TestTwo', Elapsed: 0.02 })}\n`, { tests: 2, pass: 1, fail: 1, skipped: 0, format: 'go-json' }],
  ];

  let ticketNum = 1;
  for (const [label, payload, expected] of samples) {
    ticketNum += 1;
    const script = join(root, `emit-${label}.cjs`);
    writeFileSync(script, `process.stdout.write(${JSON.stringify(payload)});`);
    const res = await runTestSuite(
      { cwd: root, command: `${quote(process.execPath)} ${quote(script)}`, env },
      { ...machine.ports, say: () => {}, stdout: { write() {} }, stderr: { write() {} } },
    );
    assert.equal(res.exitCode, 0, label);
    const receipt = JSON.parse(readFileSync(join(queue, `ticket-${ticketNum}.json`), 'utf8'));
    assert.equal(receipt.outcome, 'completed', label);
    assert.equal(receipt.counts?.tests, expected.tests, `${label} tests`);
    assert.equal(receipt.counts?.pass, expected.pass, `${label} pass`);
    assert.equal(receipt.counts?.fail, expected.fail, `${label} fail`);
    assert.equal(receipt.counts?.skipped, expected.skipped, `${label} skipped`);
    assert.equal(receipt.counts?.format, expected.format, `${label} format`);
  }
});
