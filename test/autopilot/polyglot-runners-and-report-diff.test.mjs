import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { chmodSync, mkdirSync, mkdtempSync, readFileSync, rmSync, statSync, symlinkSync, writeFileSync } from 'node:fs';
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

test('3561 parseTestSummaryOutput & extractTestCases support all 5 runners, pytest >=60s (#9), cargo ignored reasons (#18), and fail closed on incomplete/truncated streams (#4)', () => {
  // 1. node:test TAP v13 (nested subtests + SKIP + duration_ms + after-hook suite failure #1)
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
  assert.equal(parseTestSummaryOutput('TAP version 13\n# tests 2\n# pass 2\n'), null);
  assert.equal(parseTestSummaryOutput('TAP version 13\n1..2\nok 1 - a\nBail out! crashed\n'), null);

  // 2. Vitest (ANSI CLI output)
  const vitestOut = [
    '\x1b[32m Test Files \x1b[0m 2 passed (2)',
    '\x1b[32m      Tests \x1b[0m 10 passed | 1 failed | 2 skipped (13)',
    '   Duration  412ms',
  ].join('\n');
  assert.deepEqual(parseTestSummaryOutput(vitestOut), { total: 13, passed: 10, failed: 1, skipped: 2, format: 'vitest' });

  // 3. Pytest (CLI summary, verbose cases, AND >=60s duration format #9)
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
  assert.deepEqual(parseTestSummaryOutput('=== 12 passed, 1 failed in 75.32s (0:01:15) ==='), { total: 13, passed: 12, failed: 1, skipped: 0, format: 'pytest' });
  assert.deepEqual(parseTestSummaryOutput('12 passed in 75.32s (0:01:15)', 'pytest'), { total: 12, passed: 12, failed: 0, skipped: 0, format: 'pytest' });
  assert.deepEqual(parseTestSummaryOutput('=== no tests ran in 0.01s ==='), { total: 0, passed: 0, failed: 0, skipped: 0, format: 'pytest' });

  // 4. Cargo test (multiple binaries + ignored with reason #18; bare summary without header rejected in auto mode #15)
  const cargoOut = [
    'running 2 tests',
    'test alpha::ok_case ... ok',
    'test alpha::skip_case ... ignored, slow network test',
    'test result: ok. 1 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 0.01s',
    'running 2 tests',
    'test beta::pass_case ... ok',
    'test beta::bad_case ... FAILED',
    'test result: FAILED. 1 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.02s',
  ].join('\n');
  assert.deepEqual(parseTestSummaryOutput(cargoOut), { total: 4, passed: 2, failed: 1, skipped: 1, format: 'cargo' });
  const cargoCases = extractTestCases(cargoOut, 'cargo');
  assert.equal(cargoCases.length, 4);
  assert.deepEqual(cargoCases[1], { id: 'alpha::skip_case', status: 'skip', durationMs: null });
  assert.equal(parseTestSummaryOutput('running 3 tests\ntest a ... ok\n'), null, 'killed cargo run fails closed');
  assert.equal(parseTestSummaryOutput('test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out\n'), null, 'auto-detect requires running header');

  // 5. go test -json (#4: stream cut off between tests without terminal package event fails closed!)
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
  const truncatedBetweenTests = [
    JSON.stringify({ Action: 'run', Package: 'example/calc', Test: 'TestAdd' }),
    JSON.stringify({ Action: 'pass', Package: 'example/calc', Test: 'TestAdd', Elapsed: 0.01 }),
  ].join('\n') + '\n';
  assert.equal(parseTestSummaryOutput(truncatedBetweenTests), null, 'go-json missing package terminal event must fail closed (#4)');
  const buildFailGo = JSON.stringify({ Action: 'build-fail', Package: 'example/broken' }) + '\n';
  assert.deepEqual(extractTestCases(buildFailGo, 'go-json'), [{ id: 'example/broken::<build>', status: 'error', durationMs: null }]);
});

test('G3 parseJunitXml handles CDATA, entities, nested testsuites, suite-level errors/attributes (#2), and fails closed on malformed/unsafe XML', () => {
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

  // #2: Direct <error> under <testsuite> and errors=/failures= attributes > parsed testcase failures MUST NOT look all-pass!
  const suiteDirectError = parseJunitXml('<testsuite name="s"><error message="beforeAll crashed"/><testcase name="t1"/></testsuite>');
  assert.equal(suiteDirectError.ok, true);
  assert.equal(suiteDirectError.counts.failed, 1);
  assert.ok(suiteDirectError.cases.some(c => c.id === 's::<suite-error>' && c.status === 'error'));

  const suiteAttrError = parseJunitXml('<testsuite name="s" errors="1" failures="0"><testcase name="t1"/></testsuite>');
  assert.equal(suiteAttrError.ok, true);
  assert.equal(suiteAttrError.counts.failed, 1);
  assert.ok(suiteAttrError.cases.some(c => c.id === 's::<suite-error-count>' && c.status === 'error'));

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

test('G3 compareTestReports covers #1 TAP after-hook fail-closed, #2 JUnit suite errors, #3 strict shard parity, #4 truncated go-json, #17 vitest/pytest XML aliases, and #19 duplicate-ID multiset diff', () => {
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

  // 1. Clean diff + format aliases 'vitest' / 'pytest' (#17)
  const okDiff = compareTestReports({
    baseReport: baseXml, headReport: headCleanXml,
    baseMeta: { ...VALID_META, format: 'vitest' },
    headMeta: { ...VALID_META, format: 'pytest' },
    approvedRemovals: ['c::t3'],
  });
  assert.equal(okDiff.status, 'pass');
  assert.equal(okDiff.verdict, 'ALLOW');
  assert.deepEqual(okDiff.approvedRemovedIds, ['c::t3']);
  assert.deepEqual(okDiff.fixedIds, ['c::t4']);
  assert.deepEqual(okDiff.addedIds, ['c::t5']);

  // #1: TAP suite failing in after-hook while children pass (even with NO exitCode in meta!) MUST HOLD!
  const tapBasePass = [
    'TAP version 13',
    '# Subtest: suite',
    '    ok 1 - child',
    '    1..1',
    'ok 1 - suite',
    '  ---',
    "  type: 'suite'",
    '  ...',
    '1..1',
    '# tests 1', '# suites 1', '# pass 1', '# fail 0', '# cancelled 0', '# skipped 0', '# todo 0', '',
  ].join('\n');
  const tapHeadAfterHookFail = [
    'TAP version 13',
    '# Subtest: suite',
    '    ok 1 - child',
    '    1..1',
    'not ok 1 - suite',
    '  ---',
    "  type: 'suite'",
    '  ...',
    '1..1',
    '# tests 1', '# suites 1', '# pass 1', '# fail 1', '# cancelled 0', '# skipped 0', '# todo 0', '',
  ].join('\n');
  const afterHookDiff = compareTestReports({
    baseReport: tapBasePass, headReport: tapHeadAfterHookFail,
    baseMeta: VALID_META, headMeta: VALID_META,
  });
  assert.equal(afterHookDiff.verdict, 'HOLD', 'TAP after-hook failure must NEVER return ALLOW (#1)');
  assert.equal(afterHookDiff.status, 'fail');
  assert.ok(afterHookDiff.newlyFailingIds.includes('suite::<suite-hook>'));

  // #2: JUnit suite-level error in head MUST HOLD
  const junitSuiteErrDiff = compareTestReports({
    baseReport: '<testsuite name="s"><testcase name="t1"/></testsuite>',
    headReport: '<testsuite name="s" errors="1"><testcase name="t1"/></testsuite>',
    baseMeta: VALID_META, headMeta: VALID_META,
  });
  assert.equal(junitSuiteErrDiff.verdict, 'HOLD');
  assert.equal(junitSuiteErrDiff.status, 'fail');

  // #3: Partial-shard fail-open: missing completedShards OR one-sided shard meta MUST return unknown/HOLD!
  for (const [label, bMeta, hMeta] of [
    ['missing completedShards', { ...VALID_META, expectedShards: 4 }, { ...VALID_META, expectedShards: 4 }],
    ['one-sided shard meta', { ...VALID_META, expectedShards: 2, completedShards: 2 }, VALID_META],
    ['partial head shards', { ...VALID_META, expectedShards: 4, completedShards: 4 }, { ...VALID_META, expectedShards: 4, completedShards: 3 }],
  ]) {
    const res = compareTestReports({ baseReport: baseXml, headReport: baseXml, baseMeta: bMeta, headMeta: hMeta });
    assert.equal(res.status, 'unknown', `${label} must fail closed (#3)`);
    assert.equal(res.verdict, 'HOLD');
    assert.equal(res.reason, 'partial_shard_mismatch');
  }

  // #4: go test -json truncated between tests (no package terminal event) -> unknown/HOLD
  const goComplete = [
    JSON.stringify({ Action: 'run', Package: 'p', Test: 'TestA' }),
    JSON.stringify({ Action: 'pass', Package: 'p', Test: 'TestA', Elapsed: 0.01 }),
    JSON.stringify({ Action: 'pass', Package: 'p', Elapsed: 0.02 }),
  ].join('\n');
  const goTruncated = [
    JSON.stringify({ Action: 'run', Package: 'p', Test: 'TestA' }),
    JSON.stringify({ Action: 'pass', Package: 'p', Test: 'TestA', Elapsed: 0.01 }),
  ].join('\n');
  const goTruncDiff = compareTestReports({ baseReport: goComplete, headReport: goTruncated, baseMeta: VALID_META, headMeta: VALID_META });
  assert.equal(goTruncDiff.status, 'unknown');
  assert.equal(goTruncDiff.verdict, 'HOLD');

  // #19: Duplicate passing test IDs tracked as multiset — removing 1 of 2 catches missingIds!
  const dupBase = '<testsuite name="s"><testcase classname="c" name="dup"/><testcase classname="c" name="dup"/></testsuite>';
  const dupHead = '<testsuite name="s"><testcase classname="c" name="dup"/></testsuite>';
  const dupDiff = compareTestReports({ baseReport: dupBase, headReport: dupHead, baseMeta: VALID_META, headMeta: VALID_META });
  assert.equal(dupDiff.status, 'fail');
  assert.equal(dupDiff.verdict, 'HOLD');
  assert.deepEqual(dupDiff.missingIds, ['c::dup']);

  // Cache-key parity, zero tests, killed, non-zero without failure
  for (const field of CACHE_KEY_FIELDS) {
    const mismatched = compareTestReports({ baseReport: baseXml, headReport: baseXml, baseMeta: VALID_META, headMeta: { ...VALID_META, [field]: 'diff' } });
    assert.equal(mismatched.status, 'unknown');
    assert.deepEqual(mismatched.mismatches, [field]);
  }
  assert.equal(compareTestReports({ baseReport: '<testsuite name="e"/>', headReport: baseXml, baseMeta: VALID_META, headMeta: VALID_META }).reason, 'zero_collected_tests');
  assert.equal(compareTestReports({ baseReport: baseXml, headReport: baseXml, baseMeta: VALID_META, headMeta: { ...VALID_META, killed: true } }).reason, 'runner_killed');
  const clean1 = '<testsuite name="s"><testcase classname="c" name="t1"/></testsuite>';
  assert.equal(compareTestReports({ baseReport: clean1, headReport: clean1, baseMeta: VALID_META, headMeta: { ...VALID_META, exitCode: 137 } }).reason, 'runner_nonzero_without_failures');
});

test('G3 runBaseOwnedTestOracle catches weakened assertions, isolates relative symlinks (#5), uses strict allowlist env (#6), preserves exec bit & .git (#20), and rejects all-skip runs (#20)', async t => {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-oracle-wt-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));

  const baseRepo = join(scratch, 'base');
  const headWorktree = join(scratch, 'head');
  mkdirSync(join(baseRepo, 'src'), { recursive: true });
  mkdirSync(join(baseRepo, 'test'), { recursive: true });

  writeFileSync(join(baseRepo, 'src/tax.mjs'), 'export const computeTax = cents => Math.round(cents * 0.10);\n');
  writeFileSync(join(baseRepo, 'data.txt'), 'original-head-data\n');
  symlinkSync('data.txt', join(baseRepo, 'rel-link.txt'));
  writeFileSync(
    join(baseRepo, 'test/tax.test.mjs'),
    [
      "import test from 'node:test';",
      "import assert from 'node:assert/strict';",
      "import { writeFileSync } from 'node:fs';",
      "import { computeTax } from '../src/tax.mjs';",
      "test('computes exact 10 percent tax', () => {",
      "  // Attempt to write through relative symlink; verbatimSymlinks must keep writes inside temp copy!",
      "  writeFileSync('rel-link.txt', 'mutated-in-sandbox\\n');",
      '  assert.equal(computeTax(100), 10);',
      '});',
      '',
    ].join('\n'),
  );
  chmodSync(join(baseRepo, 'test/tax.test.mjs'), 0o755);
  execFileSync('git', ['init', '-q'], { cwd: baseRepo });
  execFileSync('git', ['add', '.'], { cwd: baseRepo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=t@example.com', 'commit', '-q', '-m', 'base'], { cwd: baseRepo });
  execFileSync('git', ['worktree', 'add', '-q', '-b', 'pr-head', headWorktree, 'HEAD'], { cwd: baseRepo });
  t.after(() => {
    try { execFileSync('git', ['worktree', 'remove', '--force', headWorktree], { cwd: baseRepo, stdio: 'ignore' }); } catch {}
  });

  // PR breaks implementation (5%) AND weakens assertion so head alone passes
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

  const cleanChildEnv = { PATH: process.env.PATH, HOME: scratch };
  const headAlone = execFileSync(process.execPath, ['--test', '--test-reporter=tap', 'test/tax.test.mjs'], { cwd: headWorktree, env: cleanChildEnv, encoding: 'utf8' });
  assert.match(headAlone, /# pass 1\b/);

  // 1. Oracle catches regression, NEVER mutates headTree or headTree/data.txt through rel-link.txt (#5)!
  const cmd = [process.execPath, '--test', '--test-reporter=tap', 'test/tax.test.mjs'];
  const held = await runBaseOwnedTestOracle({ baseTree: baseRepo, headTree: headWorktree, editedTestFiles: ['test/tax.test.mjs'], testCommand: cmd });
  assert.equal(held.status, 'fail');
  assert.equal(held.verdict, 'HOLD');
  assert.equal(held.reason, 'unlisted_base_test_regression');
  assert.equal(held.regressions[0].id, 'computes exact 10 percent tax');
  assert.equal(readFileSync(join(headWorktree, 'test/tax.test.mjs'), 'utf8'), weakenedHeadTest);
  assert.equal(readFileSync(join(headWorktree, 'data.txt'), 'utf8'), 'original-head-data\n', 'verbatimSymlinks prevents writes through relative symlinks into real headTree (#5)');

  // 2. #6 Strict allowlist env & #20 exec bit preserved on overlaid base file
  const dirtyOracleEnv = {
    PATH: process.env.PATH, HOME: scratch, GOPATH: '/opt/go', CARGO_HOME: '/opt/cargo',
    ANTHROPIC_AUTH_TOKEN: 'secret-1', CODEX_API_KEY: 'secret-2', AZURE_OPENAI_API_KEY: 'secret-3',
    NODE_AUTH_TOKEN: 'secret-4', HF_TOKEN: 'secret-5', AWS_ACCESS_KEY_ID: 'AKIA123',
    GOOGLE_APPLICATION_CREDENTIALS: '/tmp/gcp.json', SSH_AUTH_SOCK: '/tmp/ssh.sock',
    DATABASE_PASSWORD: 'dbpw', SLACK_BOT_TOKEN: 'xoxb-secret', PYTEST_ADDOPTS: '-k none',
  };
  let seenOracleEnv = null, seenExecMode = null;
  const allowRes = await runBaseOwnedTestOracle({
    baseTree: baseRepo, headTree: headWorktree, editedTestFiles: ['test/tax.test.mjs'],
    testCommand: 'custom', env: dirtyOracleEnv,
    runner: async ({ cwd, env }) => {
      seenOracleEnv = env;
      seenExecMode = statSync(join(cwd, 'test/tax.test.mjs')).mode & 0o111;
      return { exitCode: 0, stdout: 'TAP version 13\n1..1\nok 1 - ok\n' };
    },
  });
  assert.equal(allowRes.verdict, 'ALLOW');
  assert.equal(seenOracleEnv.GOPATH, '/opt/go');
  assert.equal(seenOracleEnv.CARGO_HOME, '/opt/cargo');
  for (const forbidden of [
    'ANTHROPIC_AUTH_TOKEN', 'CODEX_API_KEY', 'AZURE_OPENAI_API_KEY', 'NODE_AUTH_TOKEN',
    'HF_TOKEN', 'AWS_ACCESS_KEY_ID', 'GOOGLE_APPLICATION_CREDENTIALS', 'SSH_AUTH_SOCK',
    'DATABASE_PASSWORD', 'SLACK_BOT_TOKEN', 'PYTEST_ADDOPTS', 'NODE_TEST_CONTEXT',
  ]) {
    assert.equal(seenOracleEnv[forbidden], undefined, `${forbidden} must NOT leak to untrusted oracle code (#6)`);
  }
  assert.ok(seenExecMode !== 0, 'overlaid base file must preserve executable bit (#20)');

  // 3. #20 All-skip run in oracle MUST fail closed (verdict: 'HOLD', reason: 'oracle_zero_executed_tests')!
  const allSkip = await runBaseOwnedTestOracle({
    baseTree: baseRepo, headTree: headWorktree, editedTestFiles: ['test/tax.test.mjs'],
    testCommand: 'custom',
    runner: async () => ({ exitCode: 0, stdout: 'TAP version 13\n1..2\nok 1 - a # SKIP\nok 2 - b # SKIP\n' }),
  });
  assert.equal(allSkip.status, 'unknown');
  assert.equal(allSkip.verdict, 'HOLD');
  assert.equal(allSkip.reason, 'oracle_zero_executed_tests');

  // 4. Intended changes allowed & unsafe paths fail closed
  const intended = await runBaseOwnedTestOracle({
    baseTree: baseRepo, headTree: headWorktree, editedTestFiles: ['test/tax.test.mjs'],
    testCommand: cmd, intendedChanges: ['computes exact 10 percent tax'],
  });
  assert.equal(intended.verdict, 'ALLOW');
  assert.equal(intended.reason, 'intended_changes_only');

  symlinkSync(join(baseRepo, 'test/tax.test.mjs'), join(headWorktree, 'test/sym.test.mjs'));
  for (const unsafePath of ['../outside.test.mjs', 'test/sym.test.mjs']) {
    const res = await runBaseOwnedTestOracle({ baseTree: baseRepo, headTree: headWorktree, editedTestFiles: [unsafePath], testCommand: cmd });
    assert.equal(res.status, 'unknown');
    assert.equal(res.verdict, 'HOLD');
    assert.equal(res.reason, 'unsafe_test_path');
  }
});

test('test-suite-queue passes safe toolchain env without PYTEST_ADDOPTS (#14) and test-suite-recorder normalizes polyglot counts (#15) & fails closed on truncation (#16)', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-polyglot-queue-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const queue = join(root, 'queue'), home = join(root, 'home'), state = join(root, 'state');
  mkdirSync(queue); mkdirSync(home); mkdirSync(state);
  const machine = checkMachine({ taskset: null });
  writeFileSync(join(queue, 'capacity.json'), JSON.stringify(withCheckLifetime(calculateCheckCapacity({ checks: 1 }, machine.ports))));

  const env = {
    PATH: process.env.PATH, HOME: home, PDD_STATE_DIR: state, PDD_SUITE_QUEUE: queue,
    GOPATH: '/opt/go', GOMODCACHE: '/opt/gomodcache', CARGO_HOME: '/opt/cargo', RUSTUP_HOME: '/opt/rustup',
    VIRTUAL_ENV: '/opt/venv', UV_CACHE_DIR: '/opt/uv-cache',
    PYTEST_ADDOPTS: '-k only_one', GH_TOKEN: 'ghs_must_be_scrubbed', OPENAI_API_KEY: 'sk-must-be-scrubbed',
  };

  let capturedEnv = null;
  const envRes = await runTestSuite({ cwd: root, command: 'true', env }, {
    ...machine.ports, say: () => {},
    execute: async (_cmd, opts) => { capturedEnv = opts.env; opts.onChild(process.pid); return { exitCode: 0 }; },
  });
  assert.equal(envRes.exitCode, 0);
  for (const [k, v] of [['GOPATH', '/opt/go'], ['GOMODCACHE', '/opt/gomodcache'], ['CARGO_HOME', '/opt/cargo'], ['RUSTUP_HOME', '/opt/rustup'], ['VIRTUAL_ENV', '/opt/venv'], ['UV_CACHE_DIR', '/opt/uv-cache']]) {
    assert.equal(capturedEnv[k], v);
  }
  assert.equal(capturedEnv.PYTEST_ADDOPTS, undefined, 'PYTEST_ADDOPTS must NOT pass through (#14)');
  assert.equal(capturedEnv.GH_TOKEN, undefined);
  assert.equal(capturedEnv.OPENAI_API_KEY, undefined);

  const samples = [
    ['pytest', '=== 4 passed, 1 failed, 2 skipped in 75.32s (0:01:15) ===\n', { tests: 7, suites: 0, pass: 4, fail: 1, cancelled: 0, skipped: 2, todo: 0, format: 'pytest' }],
    ['vitest', ' Test Files  1 passed (1)\n      Tests  5 passed | 1 skipped (6)\n   Duration  120ms\n', { tests: 6, suites: 0, pass: 5, fail: 0, cancelled: 0, skipped: 1, todo: 0, format: 'vitest' }],
    ['cargo', 'running 3 tests\ntest a ... ok\ntest b ... ok\ntest c ... ignored, slow\ntest result: ok. 2 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 0.01s\n', { tests: 3, suites: 0, pass: 2, fail: 0, cancelled: 0, skipped: 1, todo: 0, format: 'cargo' }],
    ['go', [
      JSON.stringify({ Action: 'run', Package: 'm/p', Test: 'TestOne' }),
      JSON.stringify({ Action: 'pass', Package: 'm/p', Test: 'TestOne', Elapsed: 0.01 }),
      JSON.stringify({ Action: 'run', Package: 'm/p', Test: 'TestTwo' }),
      JSON.stringify({ Action: 'fail', Package: 'm/p', Test: 'TestTwo', Elapsed: 0.02 }),
      JSON.stringify({ Action: 'fail', Package: 'm/p', Elapsed: 0.03 }),
    ].join('\n') + '\n', { tests: 2, suites: 0, pass: 1, fail: 1, cancelled: 0, skipped: 0, todo: 0, format: 'go-json' }],
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
    assert.deepEqual(receipt.counts, expected, `${label} normalized counts (#15)`);
  }

  // #16: Overflowing >256 KiB of Go JSON lifecycle events returns counts: null (never wrong partial counts!)
  ticketNum += 1;
  const overflowScript = join(root, 'emit-go-overflow.cjs');
  writeFileSync(overflowScript, `for (let i = 0; i < 4000; i++) {
    process.stdout.write(JSON.stringify({ Action: 'run', Package: 'm/big', Test: 'TestLongCaseNameNumber_' + i }) + '\\n');
    process.stdout.write(JSON.stringify({ Action: 'pass', Package: 'm/big', Test: 'TestLongCaseNameNumber_' + i, Elapsed: 0.001 }) + '\\n');
  }
  process.stdout.write(JSON.stringify({ Action: 'pass', Package: 'm/big', Elapsed: 1.0 }) + '\\n');`);
  const overflowRes = await runTestSuite(
    { cwd: root, command: `${quote(process.execPath)} ${quote(overflowScript)}`, env },
    { ...machine.ports, say: () => {}, stdout: { write() {} }, stderr: { write() {} } },
  );
  assert.equal(overflowRes.exitCode, 0);
  const overflowReceipt = JSON.parse(readFileSync(join(queue, `ticket-${ticketNum}.json`), 'utf8'));
  assert.equal(overflowReceipt.counts, null, 'truncated Go JSON lifecycle buffer must return null instead of wrong partial counts (#16)');
});

test('#3561/#3634 runPolyglotBaseControl isolates Python formal test files into separate pytest subprocesses (prevents Z3 main_ctx deadlocks)', async t => {
  const { runPolyglotBaseControl } = await import('../../src/autopilot/core/live-evidence.mjs');
  const root = mkdtempSync(join(tmpdir(), 'pdd-py-formal-iso-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  writeFileSync(join(root, 'pyproject.toml'), '[tool.pytest.ini_options]\ntestpaths = ["tests_py"]\n');

  const calls = [];
  const res = await runPolyglotBaseControl({
    baseDir: root,
    changedFiles: [
      'src/ledger.py',
      'tests_py/test_unit.py',
      'tests_py/test_formal_a.py',
      'tests_py/formal/test_b.py',
    ],
    changedProdFiles: ['src/ledger.py'],
    execFn: async (bin, args) => {
      calls.push([bin, ...args]);
      const fail = args.includes('tests_py/formal/test_b.py');
      return { exitCode: fail ? 1 : 0, stdout: fail ? '1 failed in 0.1s\n' : '1 passed in 0.1s\n', stderr: '', killed: false, code: null };
    },
  });
  assert.equal(res.state, 'ran-and-failed-on-base');
  assert.deepEqual(res.isolatedFiles, ['tests_py/test_formal_a.py', 'tests_py/formal/test_b.py']);
  assert.equal(calls.length, 3);
  assert.equal(calls[0][0], 'pytest');
  assert.equal(calls[0][1], '-v');
  assert.match(calls[0][2], /^--junitxml=/);
  assert.equal(calls[0][3], '--');
  assert.equal(calls[0][4], 'tests_py/test_unit.py');
  assert.equal(calls[1][0], 'pytest');
  assert.equal(calls[1][1], '-v');
  assert.match(calls[1][2], /^--junitxml=/);
  assert.equal(calls[1][3], '--');
  assert.equal(calls[1][4], 'tests_py/test_formal_a.py');
  assert.equal(calls[2][0], 'pytest');
  assert.equal(calls[2][1], '-v');
  assert.match(calls[2][2], /^--junitxml=/);
  assert.equal(calls[2][3], '--');
  assert.equal(calls[2][4], 'tests_py/formal/test_b.py');
});
