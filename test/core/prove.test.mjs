import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import {
  detectHostCapabilities,
  isProductionSurfaceFile,
  matchCapabilities,
  matchVerifyPaths,
  parseVerifyConfig,
} from '../../src/core/verify-paths.mjs';
import {
  EXIT_FAILED,
  EXIT_NOT_PROVED,
  EXIT_PROVED,
  OUTCOME_FAILED,
  OUTCOME_NOT_PROVED,
  OUTCOME_PROVED,
  detectRepoTestCommand,
  runProve,
} from '../../src/core/prove.mjs';

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

test('verify-paths validates pdd.json verify schema, matches globs linearly, and probes open needs[] capabilities', t => {
  const cfg = parseVerifyConfig({
    verify: {
      test: 'node --test',
      paths: [
        { id: 'core-cli', name: 'Core CLI', when: ['src/cli/**/*.mjs'], run: 'node --test test/cli.test.mjs' },
        { id: 'ui-smoke', name: 'UI smoke', when: 'src/ui/**', run: 'npm run e2e', needs: ['browser', 'account:staging', 'custom:gpu'] },
      ],
    },
  });
  assert.equal(cfg.configured, true);
  assert.deepEqual(cfg.errors, []);
  assert.equal(cfg.paths.length, 2);

  const matched = matchVerifyPaths(cfg, ['src/cli/main.mjs', 'src/unmapped/worker.mjs', 'docs/readme.md', 'test/unit.test.mjs']);
  assert.deepEqual(matched.matched.map(r => r.id), ['core-cli']);
  assert.deepEqual(matched.changedSurfaces, ['src/cli/main.mjs', 'src/unmapped/worker.mjs']);
  assert.deepEqual(matched.unmappedSurfaces, ['src/unmapped/worker.mjs']);

  // Open capability probing honors explicit capabilities, PDD_CAPABILITIES env, and account:<name> config file.
  const fakeHome = mkdtempSync(join(tmpdir(), 'pdd-cap-home-'));
  t.after(() => rmSync(fakeHome, { recursive: true, force: true }));
  mkdirSync(join(fakeHome, '.config', 'pdd'), { recursive: true });
  writeFileSync(join(fakeHome, '.config', 'pdd', 'autopilot-test-env.json'), JSON.stringify({ staging: { token: 'ok' } }));

  const capState = detectHostCapabilities(['browser', 'account:staging', 'custom:gpu'], {
    env: { HOME: fakeHome, PDD_CAPABILITIES: 'custom:gpu,!browser' },
  });
  assert.equal(capState.checked['account:staging'], true);
  assert.equal(capState.checked['custom:gpu'], true);
  assert.equal(capState.checked.browser, false);
  assert.deepEqual(matchCapabilities(['browser', 'account:staging', 'custom:gpu'], capState), {
    satisfied: false,
    missing: ['browser'],
  });

  // Invalid verify schema reports crisp errors without throwing.
  const bad = parseVerifyConfig({
    verify: {
      test: '   ',
      paths: [
        { id: 'dup', when: ['src/**'], run: 'echo ok' },
        { id: 'dup', when: ['src/**'], run: 'echo ok' },
        { id: 'bad-glob', when: ['*a*a*a*a*a*a*a*a*a*a*a*a*'], run: 'echo ok' },
      ],
    },
  });
  assert.ok(bad.errors.length >= 3, JSON.stringify(bad.errors));
});

test('G1/G2 zero-flag prove emits Proved, Failed, and Not proved honestly across mapped, unmapped, missing-capability, and base-trust scenarios', t => {
  const repo = initGitRepo(t, 'pdd-prove-zero-');
  mkdirSync(join(repo, 'src', 'billing'), { recursive: true });
  mkdirSync(join(repo, 'src', 'ui'), { recursive: true });
  mkdirSync(join(repo, 'src', 'other'), { recursive: true });
  mkdirSync(join(repo, 'test'), { recursive: true });

  const nodeBin = JSON.stringify(process.execPath);
  writeFileSync(
    join(repo, 'package.json'),
    JSON.stringify({ name: 'prove-demo', type: 'module', scripts: { test: `${nodeBin} --test test/unit.test.mjs` } }, null, 2) + '\n',
  );
  writeFileSync(
    join(repo, 'pdd.json'),
    JSON.stringify({
      verify: {
        test: `${nodeBin} --test test/unit.test.mjs`,
        paths: [
          { id: 'billing', name: 'Billing recipe', when: ['src/billing/**/*.mjs'], run: `${nodeBin} -e "process.exit(0)"` },
          { id: 'ui-browser', name: 'Browser E2E', when: ['src/ui/**/*.mjs'], run: `${nodeBin} -e "process.exit(0)"`, needs: ['browser', 'custom:display'] },
        ],
      },
    }, null, 2) + '\n',
  );
  writeFileSync(join(repo, 'src', 'billing', 'calc.mjs'), 'export const sum = (a, b) => a + b;\n');
  writeFileSync(join(repo, 'src', 'ui', 'view.mjs'), 'export const render = () => "ok";\n');
  writeFileSync(join(repo, 'src', 'other', 'worker.mjs'), 'export const tick = () => 1;\n');
  writeFileSync(
    join(repo, 'test', 'unit.test.mjs'),
    "import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { sum } from '../src/billing/calc.mjs';\ntest('sum', () => assert.equal(sum(2, 3), 5));\n",
  );
  commitAll(repo, 'base');

  execFileSync('git', ['checkout', '-q', '-b', 'feat'], { cwd: repo });

  // 1. Mapped change -> Proved (exit 0) with structured provenance JSON receipt.
  writeFileSync(join(repo, 'src', 'billing', 'calc.mjs'), 'export const sum = (a, b) => Number(a) + Number(b);\n');
  const provedOut = makeSink(), provedErr = makeSink();
  const proved = runProve({ cwd: repo, json: true }, { stdout: provedOut, stderr: provedErr });
  assert.equal(proved.exitCode, EXIT_PROVED);
  assert.equal(proved.outcome, OUTCOME_PROVED);
  assert.equal(provedErr.text, '');
  const receipt = JSON.parse(provedOut.text);
  assert.equal(receipt.schema_version, 'pdd.prove.v1');
  assert.equal(receipt.mode, 'verify');
  assert.equal(receipt.outcome, 'Proved');
  assert.equal(receipt.baseRef, 'main');
  assert.equal(receipt.test.ok, true);
  assert.equal(receipt.paths.length, 1);
  assert.equal(receipt.paths[0].status, 'proved');
  assert.deepEqual(receipt.notProvedReasons, []);

  // 2. Unmapped production surface -> Not proved (exit 3), NEVER fakes Proved!
  writeFileSync(join(repo, 'src', 'other', 'worker.mjs'), 'export const tick = () => 2;\n');
  const unmappedOut = makeSink(), unmappedErr = makeSink();
  const unmapped = runProve({ cwd: repo, json: true }, { stdout: unmappedOut, stderr: unmappedErr });
  assert.equal(unmapped.exitCode, EXIT_NOT_PROVED);
  assert.equal(unmapped.outcome, OUTCOME_NOT_PROVED);
  assert.ok(unmapped.receipt.notProvedReasons.some(r => r.includes('src/other/worker.mjs')));

  // Revert unmapped file; edit UI surface whose recipe needs ['browser', 'custom:display'].
  execFileSync('git', ['checkout', '--', 'src/other/worker.mjs'], { cwd: repo });
  writeFileSync(join(repo, 'src', 'ui', 'view.mjs'), 'export const render = () => "v2";\n');

  // 3. Missing required capability -> Not proved (exit 3) with explicit missing capability reason.
  const noCap = runProve({ cwd: repo, json: true, capabilities: [] }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(noCap.exitCode, EXIT_NOT_PROVED);
  assert.equal(noCap.outcome, OUTCOME_NOT_PROVED);
  assert.equal(noCap.receipt.paths.find(p => p.id === 'ui-browser').status, 'not-proved');
  assert.deepEqual(noCap.receipt.paths.find(p => p.id === 'ui-browser').missingCapabilities, ['browser', 'custom:display']);

  // 4. Supplying required capabilities -> Proved (exit 0)!
  const withCap = runProve({ cwd: repo, json: true, capabilities: ['browser', 'custom:display'] }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(withCap.exitCode, EXIT_PROVED);
  assert.equal(withCap.outcome, OUTCOME_PROVED);

  // 5. Base-trust protection: weakening pdd.json on the branch CANNOT bypass base verify.paths!
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({ verify: { test: `${nodeBin} -e "process.exit(0)"`, paths: [{ id: 'ui-browser', when: ['src/ui/**'], run: `${nodeBin} -e "process.exit(0)"` }] } }) + '\n');
  const trusted = runProve({ cwd: repo, json: true, capabilities: [] }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(trusted.exitCode, EXIT_NOT_PROVED, 'must enforce merge-base verify.paths with needs:[browser, custom:display]');
  assert.match(trusted.receipt.configSource, /:pdd\.json$/);

  // 6. Failing test suite -> Failed (exit 1).
  writeFileSync(join(repo, 'src', 'billing', 'calc.mjs'), 'export const sum = (a, b) => a - b;\n');
  const failed = runProve({ cwd: repo, json: true, capabilities: ['browser', 'custom:display'] }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(failed.exitCode, EXIT_FAILED);
  assert.equal(failed.outcome, OUTCOME_FAILED);
  assert.equal(failed.receipt.test.ok, false);
});

test('G1 zero-flag prove marks branch-only verify.paths as Not proved when merge base has no verify config', t => {
  const repo = initGitRepo(t, 'pdd-prove-branch-cfg-');
  mkdirSync(join(repo, 'src'), { recursive: true });
  writeFileSync(join(repo, 'src', 'app.mjs'), 'export const v = 1;\n');
  commitAll(repo, 'base without pdd.json');

  execFileSync('git', ['checkout', '-q', '-b', 'add-verify'], { cwd: repo });
  const nodeBin = JSON.stringify(process.execPath);
  writeFileSync(
    join(repo, 'pdd.json'),
    JSON.stringify({ verify: { test: `${nodeBin} -e "process.exit(0)"`, paths: [{ id: 'app', when: ['src/**'], run: `${nodeBin} -e "process.exit(0)"` }] } }) + '\n',
  );
  writeFileSync(join(repo, 'src', 'app.mjs'), 'export const v = 2;\n');
  commitAll(repo, 'add verify.paths on branch');

  const res = runProve({ cwd: repo, json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(res.exitCode, EXIT_NOT_PROVED);
  assert.equal(res.outcome, OUTCOME_NOT_PROVED);
  assert.ok(res.receipt.notProvedReasons.some(r => r.includes('not yet trusted on merge base')));
});

test('G1 bug-contrast mode fixes all 5 brownfield bugs: colocated tests, offline --base, uncommitted overlay, scrubbed env + isolated --setup, and honest causal --expect', t => {
  const repo = initGitRepo(t, 'pdd-prove-bug-');
  mkdirSync(join(repo, 'src'), { recursive: true });

  // Buggy base commit (no network, no remote origin).
  writeFileSync(join(repo, 'src', 'math.mjs'), 'export const divide = (a, b) => a / b;\n');
  commitAll(repo, 'buggy base');

  execFileSync('git', ['checkout', '-q', '-b', 'fix-div-zero'], { cwd: repo });
  // Fix committed on branch.
  writeFileSync(
    join(repo, 'src', 'math.mjs'),
    'export const divide = (a, b) => { if (b === 0) throw new RangeError("ERR_DIVIDE_BY_ZERO"); return a / b; };\n',
  );
  commitAll(repo, 'fix divide by zero');

  // Uncommitted COLOCATED test file in src/ (Fixes #1 colocated, #2 offline --base, #3 uncommitted overlay!).
  writeFileSync(
    join(repo, 'src', 'math.test.mjs'),
    [
      "import test from 'node:test';",
      "import assert from 'node:assert/strict';",
      "import { readFileSync } from 'node:fs';",
      "import { divide } from './math.mjs';",
      "test('rejects division by zero and scrubs secrets', () => {",
      '  assert.equal(process.env.GH_TOKEN, undefined, "GH_TOKEN must be scrubbed");',
      '  assert.equal(process.env.OPENAI_API_KEY, undefined, "OPENAI_API_KEY must be scrubbed");',
      '  assert.equal(process.env.CODEX_THREAD_ID, undefined, "CODEX_THREAD_ID must be scrubbed");',
      '  assert.throws(() => divide(10, 0), /ERR_DIVIDE_BY_ZERO/, "expected ERR_DIVIDE_BY_ZERO");',
      '});',
      'void readFileSync;',
    ].join('\n') + '\n',
  );

  const nodeBin = JSON.stringify(process.execPath);
  const envWithSecrets = {
    ...process.env,
    GH_TOKEN: 'ghp_secret_must_be_scrubbed',
    OPENAI_API_KEY: 'sk-secret-must-be-scrubbed',
    CODEX_THREAD_ID: 'thread-secret',
  };

  // Fixes #1, #2, #3, #4 (scrubbed env + isolated --setup never mutating caller repo!) + #5 (causal --expect).
  const setupCmd = `${nodeBin} -e "require('node:fs').writeFileSync('.setup-marker', 'isolated')"`;
  const okOut = makeSink(), okErr = makeSink();
  const proved = runProve(
    {
      cwd: repo,
      base: 'main',
      test: `${nodeBin} --test src/math.test.mjs`,
      expect: 'ERR_DIVIDE_BY_ZERO',
      setup: setupCmd,
      json: true,
      env: envWithSecrets,
    },
    { stdout: okOut, stderr: okErr },
  );
  assert.equal(proved.exitCode, EXIT_PROVED, okErr.text || okOut.text);
  assert.equal(proved.outcome, OUTCOME_PROVED);
  assert.equal(proved.receipt.reason, 'proved');
  assert.deepEqual(proved.receipt.overlayPaths, ['src/math.test.mjs']);
  assert.equal(proved.receipt.base.ok, false);
  assert.equal(proved.receipt.base.expectedFound, true);
  assert.equal(proved.receipt.head.ok, true);
  assert.equal(existsSync(join(repo, '.setup-marker')), false, 'isolated --setup MUST NOT mutate caller checkout');

  // Fix #5a: Missing module / setup error on base -> Not proved (setup-error), NEVER Proved even if --expect matches!
  writeFileSync(
    join(repo, 'src', 'broken-import.test.mjs'),
    "import { nope } from './nonexistent-dep-xyz.mjs';\nconsole.log(nope);\n",
  );
  const setupFail = runProve(
    {
      cwd: repo,
      base: 'main',
      test: `${nodeBin} src/broken-import.test.mjs`,
      expect: 'ERR_MODULE_NOT_FOUND',
      json: true,
    },
    { stdout: makeSink(), stderr: makeSink() },
  );
  assert.equal(setupFail.exitCode, EXIT_NOT_PROVED);
  assert.equal(setupFail.outcome, OUTCOME_NOT_PROVED);
  assert.equal(setupFail.receipt.reason, 'setup-error');

  // Fix #5b: Base fails for WRONG reason (symptom absent from output) -> Not proved (wrong-reason).
  const wrongReason = runProve(
    {
      cwd: repo,
      base: 'main',
      test: `${nodeBin} --test src/math.test.mjs`,
      expect: 'COMPLETELY_DIFFERENT_SYMPTOM',
      json: true,
    },
    { stdout: makeSink(), stderr: makeSink() },
  );
  assert.equal(wrongReason.exitCode, EXIT_NOT_PROVED);
  assert.equal(wrongReason.outcome, OUTCOME_NOT_PROVED);
  assert.equal(wrongReason.receipt.reason, 'wrong-reason');

  // Fix #5c: Base passes -> Failed (base-passes).
  const basePasses = runProve(
    {
      cwd: repo,
      base: 'main',
      test: `${nodeBin} -e "process.exit(0)"`,
      expect: 'ERR_DIVIDE_BY_ZERO',
      json: true,
    },
    { stdout: makeSink(), stderr: makeSink() },
  );
  assert.equal(basePasses.exitCode, EXIT_FAILED);
  assert.equal(basePasses.outcome, OUTCOME_FAILED);
  assert.equal(basePasses.receipt.reason, 'base-passes');
});

test('G1/G2 polyglot prove works offline on real Python (pytest/pyproject.toml) and Go (go test/go.mod) repositories', t => {
  // 1. Python repo auto-detection (`pyproject.toml` -> `pytest`) + zero-flag verify.paths + bug-contrast.
  const pyRepo = initGitRepo(t, 'pdd-prove-py-');
  mkdirSync(join(pyRepo, 'pkg'), { recursive: true });
  mkdirSync(join(pyRepo, 'tests'), { recursive: true });
  writeFileSync(join(pyRepo, 'pyproject.toml'), '[project]\nname = "demo"\n[tool.pytest.ini_options]\npythonpath = ["."]\n');
  assert.equal(detectRepoTestCommand(pyRepo), 'pytest');
  writeFileSync(
    join(pyRepo, 'pdd.json'),
    JSON.stringify({ verify: { paths: [{ id: 'py-pkg', when: ['pkg/**/*.py'], run: 'python3 -m unittest discover -s tests' }] } }) + '\n',
  );
  writeFileSync(join(pyRepo, 'pkg', '__init__.py'), '');
  writeFileSync(join(pyRepo, 'pkg', 'tax.py'), 'def calc(cents):\n    return cents\n');
  writeFileSync(
    join(pyRepo, 'tests', 'test_tax.py'),
    'import unittest\nfrom pkg.tax import calc\nclass T(unittest.TestCase):\n    def test_calc(self):\n        self.assertEqual(calc(100), 100)\n',
  );
  commitAll(pyRepo, 'py base');

  execFileSync('git', ['checkout', '-q', '-b', 'fix-tax'], { cwd: pyRepo });
  writeFileSync(join(pyRepo, 'pkg', 'tax.py'), 'def calc(cents):\n    if cents < 0:\n        raise ValueError("NEGATIVE_CENTS")\n    return cents\n');
  writeFileSync(
    join(pyRepo, 'tests', 'test_tax.py'),
    'import unittest\nfrom pkg.tax import calc\nclass T(unittest.TestCase):\n    def test_neg(self):\n        with self.assertRaisesRegex(ValueError, "NEGATIVE_CENTS"):\n            calc(-1)\n',
  );

  const pyContrast = runProve(
    { cwd: pyRepo, base: 'main', test: 'python3 -m unittest tests/test_tax.py', expect: 'ValueError not raised', json: true },
    { stdout: makeSink(), stderr: makeSink() },
  );
  assert.equal(pyContrast.exitCode, EXIT_PROVED, JSON.stringify(pyContrast.receipt));
  assert.equal(pyContrast.outcome, OUTCOME_PROVED);

  const pyZero = runProve({ cwd: pyRepo, json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(pyZero.exitCode, EXIT_PROVED, JSON.stringify(pyZero.receipt));
  assert.equal(pyZero.receipt.test.command, 'pytest');

  // 2. Go repo auto-detection (`go.mod` -> `go test ./...`) + colocated `*_test.go` bug-contrast + zero-flag prove.
  const goRepo = initGitRepo(t, 'pdd-prove-go-');
  writeFileSync(join(goRepo, 'go.mod'), 'module example.com/demo\n\ngo 1.21\n');
  assert.equal(detectRepoTestCommand(goRepo), 'go test ./...');
  writeFileSync(
    join(goRepo, 'pdd.json'),
    JSON.stringify({ verify: { paths: [{ id: 'go-pkg', when: ['**/*.go'], run: 'go test ./...' }] } }) + '\n',
  );
  writeFileSync(join(goRepo, 'calc.go'), 'package demo\nfunc Add(a, b int) int { return a - b }\n');
  commitAll(goRepo, 'go buggy base');

  execFileSync('git', ['checkout', '-q', '-b', 'fix-add'], { cwd: goRepo });
  writeFileSync(join(goRepo, 'calc.go'), 'package demo\nfunc Add(a, b int) int { return a + b }\n');
  // Uncommitted colocated Go test file!
  writeFileSync(
    join(goRepo, 'calc_test.go'),
    'package demo\nimport "testing"\nfunc TestAdd(t *testing.T) { if got := Add(2, 3); got != 5 { t.Fatalf("WANT_FIVE got %d", got) } }\n',
  );

  const goContrast = runProve(
    { cwd: goRepo, base: 'main', test: 'go test ./...', expect: 'WANT_FIVE', json: true },
    { stdout: makeSink(), stderr: makeSink() },
  );
  assert.equal(goContrast.exitCode, EXIT_PROVED, JSON.stringify(goContrast.receipt));
  assert.equal(goContrast.outcome, OUTCOME_PROVED);
  assert.deepEqual(goContrast.receipt.overlayPaths, ['calc_test.go']);

  const goZero = runProve({ cwd: goRepo, json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(goZero.exitCode, EXIT_PROVED, JSON.stringify(goZero.receipt));
  assert.equal(goZero.receipt.test.command, 'go test ./...');
  assert.equal(readFileSync(join(goRepo, 'calc.go'), 'utf8').includes('a + b'), true);
});

test('Astra #1-#8 regressions: fail-closed bad base, uncommitted pdd.json self-auth block, symlink/dangling overlay refusal, deleted-test parity & zero checkout mutation, Go [build failed] & signal setup-error, broad env scrubbing, negative capability override, and .svg/.github surfaces', t => {
  const nodeBin = JSON.stringify(process.execPath);

  // #7 Negative capability override: { browser: false } MUST remove 'browser' even when PDD_CAPABILITIES lists it!
  const negCap = detectHostCapabilities(['browser', 'docker'], {
    env: { PDD_CAPABILITIES: 'browser,docker' },
    capabilities: { browser: false },
  });
  assert.equal(negCap.checked.browser, false);
  assert.deepEqual(matchCapabilities(['browser', 'docker'], negCap), { satisfied: false, missing: ['browser'] });

  // #8 .svg UI assets and .github/ workflows MUST NOT be silently excluded as non-surfaces!
  assert.equal(isProductionSurfaceFile('ui/checkout.ui.svg'), true);
  assert.equal(isProductionSurfaceFile('.github/workflows/ci.yml'), true);
  assert.equal(isProductionSurfaceFile('pkg/__pycache__/mod.cpython-314.pyc'), false);
  assert.equal(isProductionSurfaceFile('.pytest_cache/v/cache/lastfailed'), false);
  assert.equal(isProductionSurfaceFile('node_modules/pkg/index.js'), false);
  assert.equal(isProductionSurfaceFile('.DS_Store'), false);

  // #1 + #2: Unresolvable base ref -> Not proved (exit 3); uncommitted pdd.json on main (baseSha === headSha) CANNOT self-authorize!
  const repo = initGitRepo(t, 'pdd-prove-astra-trust-');
  mkdirSync(join(repo, 'src'), { recursive: true });
  writeFileSync(join(repo, 'src', 'app.mjs'), 'export const v = 1;\n');
  commitAll(repo, 'base without pdd.json');

  const badBase = runProve({ cwd: repo, base: 'refs/heads/nonexistent-ref', json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(badBase.exitCode, EXIT_NOT_PROVED);
  assert.equal(badBase.outcome, OUTCOME_NOT_PROVED);

  // Still on `main` (`baseSha === headSha`) with uncommitted pdd.json + src edit -> MUST be Not proved!
  writeFileSync(
    join(repo, 'pdd.json'),
    JSON.stringify({ verify: { test: `${nodeBin} -e "process.exit(0)"`, paths: [{ id: 'app', when: ['src/**'], run: `${nodeBin} -e "process.exit(0)"` }] } }) + '\n',
  );
  writeFileSync(join(repo, 'src', 'app.mjs'), 'export const v = 2;\n');
  const selfAuth = runProve({ cwd: repo, json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(selfAuth.exitCode, EXIT_NOT_PROVED, 'uncommitted pdd.json when baseSha===headSha MUST NOT self-authorize');
  assert.ok(selfAuth.receipt.notProvedReasons.some(r => r.includes('not yet trusted on merge base')));

  // #4a Deleted failing test parity + #4b Zero caller checkout mutation without --setup + #6 Broader env scrubbing!
  const parityRepo = initGitRepo(t, 'pdd-prove-parity-');
  mkdirSync(join(parityRepo, 'test'), { recursive: true });
  writeFileSync(join(parityRepo, 'test', 'failing.test.mjs'), "import test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('fails', () => assert.fail('DELIBERATE_FAIL'));\n");
  writeFileSync(
    join(parityRepo, 'test', 'side-effect.test.mjs'),
    [
      "import test from 'node:test';",
      "import assert from 'node:assert/strict';",
      "import { writeFileSync } from 'node:fs';",
      "test('writes file and verifies scrubbed env', () => {",
      "  writeFileSync('side-effect-marker.tmp', 'isolated');",
      '  for (const k of ["GH_CUSTOM", "GITHUB_ACTOR", "CLAUDE_CODE_USE_BEDROCK", "ANTHROPIC_BASE_URL", "OPENAI_ORG_ID", "CODEX_HOME", "HERDR_SOCKET", "PDD_CUSTOM", "AWS_ACCESS_KEY_ID", "STRIPE_API_KEY", "DB_PASSWORD", "CUSTOM_SECRET", "AUTH_TOKEN"]) {',
      '    assert.equal(process.env[k], undefined, `env ${k} must be scrubbed`);',
      '  }',
      '});',
    ].join('\n') + '\n',
  );
  commitAll(parityRepo, 'base with failing test');
  execFileSync('git', ['checkout', '-q', '-b', 'delete-failing-test'], { cwd: parityRepo });
  // Deleting the failing test on head MUST mirror into baseWorktree -> base ALSO passes -> Failed (base-passes), NEVER Proved!
  rmSync(join(parityRepo, 'test', 'failing.test.mjs'));
  const delCheat = runProve(
    {
      cwd: parityRepo,
      base: 'main',
      test: `${nodeBin} --test test/*.test.mjs`,
      expect: 'DELIBERATE_FAIL',
      json: true,
      env: {
        ...process.env,
        GH_CUSTOM: 'x', GITHUB_ACTOR: 'x', CLAUDE_CODE_USE_BEDROCK: '1', ANTHROPIC_BASE_URL: 'x',
        OPENAI_ORG_ID: 'x', CODEX_HOME: '/tmp/x', HERDR_SOCKET: '/tmp/x', PDD_CUSTOM: 'x',
        AWS_ACCESS_KEY_ID: 'x', STRIPE_API_KEY: 'x', DB_PASSWORD: 'x', CUSTOM_SECRET: 'x', AUTH_TOKEN: 'x',
      },
    },
    { stdout: makeSink(), stderr: makeSink() },
  );
  assert.equal(delCheat.exitCode, EXIT_FAILED, JSON.stringify(delCheat.receipt));
  assert.equal(delCheat.receipt.reason, 'base-passes', 'deleting a failing test must mirror deletion into base worktree');
  assert.equal(existsSync(join(parityRepo, 'side-effect-marker.tmp')), false, 'head test without --setup MUST NOT mutate caller checkout');

  // #5a Signalled base process -> setup-error (Not proved, exit 3), NEVER causal proof!
  const sigRepo = initGitRepo(t, 'pdd-prove-signal-');
  writeFileSync(join(sigRepo, 'app.mjs'), 'export const crash = true;\n');
  commitAll(sigRepo, 'base crashes');
  execFileSync('git', ['checkout', '-q', '-b', 'fix-crash'], { cwd: sigRepo });
  writeFileSync(join(sigRepo, 'app.mjs'), 'export const crash = false;\n');
  writeFileSync(join(sigRepo, 'app.test.mjs'), "import { crash } from './app.mjs';\nif (crash) { console.error('EXPECTED_MSG'); process.kill(process.pid, 'SIGKILL'); }\n");
  const sigRes = runProve(
    { cwd: sigRepo, base: 'main', test: `${nodeBin} app.test.mjs`, expect: 'EXPECTED_MSG', json: true },
    { stdout: makeSink(), stderr: makeSink() },
  );
  assert.equal(sigRes.exitCode, EXIT_NOT_PROVED, JSON.stringify(sigRes.receipt));
  assert.equal(sigRes.receipt.reason, 'setup-error');

  // #5b Go `FAIL pkg [build failed]` mid-line -> setup-error (Not proved, exit 3), NEVER causal proof!
  const goBuildRepo = initGitRepo(t, 'pdd-prove-go-build-');
  writeFileSync(join(goBuildRepo, 'go.mod'), 'module example.com/b\n\ngo 1.21\n');
  writeFileSync(join(goBuildRepo, 'calc.go'), 'package b\nfunc Add(a, b int) int { return a + b }\n');
  commitAll(goBuildRepo, 'go base missing NewFunc');
  execFileSync('git', ['checkout', '-q', '-b', 'add-newfunc'], { cwd: goBuildRepo });
  writeFileSync(join(goBuildRepo, 'calc.go'), 'package b\nfunc Add(a, b int) int { return a + b }\nfunc NewFunc() int { return 7 }\n');
  writeFileSync(join(goBuildRepo, 'calc_test.go'), 'package b\nimport "testing"\nfunc TestNew(t *testing.T) { if NewFunc() != 7 { t.Fatal("bad") } }\n');
  const goBuildFail = runProve(
    { cwd: goBuildRepo, base: 'main', test: 'go test ./...', expect: 'build failed', json: true },
    { stdout: makeSink(), stderr: makeSink() },
  );
  assert.equal(goBuildFail.exitCode, EXIT_NOT_PROVED, JSON.stringify(goBuildFail.receipt));
  assert.equal(goBuildFail.receipt.reason, 'setup-error');

  // #3 Overlay symlink traversal / dangling destination symlink -> refused (`setup-error`, NEVER writes outside)!
  const outsideDir = mkdtempSync(join(tmpdir(), 'pdd-prove-outside-'));
  t.after(() => rmSync(outsideDir, { recursive: true, force: true }));
  const symRepo = initGitRepo(t, 'pdd-prove-sym-');
  mkdirSync(join(symRepo, 'test'), { recursive: true });
  writeFileSync(join(symRepo, 'test', 'ok.test.mjs'), 'export const x = 1;\n');
  // Commit a dangling symlink in base at test/dangling.test.mjs -> outsideDir/escaped.txt
  symlinkSync(join(outsideDir, 'escaped.txt'), join(symRepo, 'test', 'dangling.test.mjs'));
  commitAll(symRepo, 'base with dangling symlink');
  execFileSync('git', ['checkout', '-q', '-b', 'replace-symlink'], { cwd: symRepo });
  rmSync(join(symRepo, 'test', 'dangling.test.mjs'));
  writeFileSync(join(symRepo, 'test', 'dangling.test.mjs'), 'console.log("pwned");\n');
  const symRes = runProve(
    { cwd: symRepo, base: 'main', test: `${nodeBin} -e "process.exit(0)"`, expect: 'x', json: true },
    { stdout: makeSink(), stderr: makeSink() },
  );
  assert.equal(symRes.exitCode, EXIT_NOT_PROVED, JSON.stringify(symRes.receipt));
  assert.equal(symRes.receipt.reason, 'setup-error');
  assert.equal(existsSync(join(outsideDir, 'escaped.txt')), false, 'dangling symlink destination MUST NEVER be written through');
});
