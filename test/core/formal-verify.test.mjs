import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  discoverFormalScope,
  inspectFormalFileBinding,
  runFormalVerification,
  verifyFormalMutationControl,
} from '../../src/core/formal-verify.mjs';
import { EXIT_FAILED, EXIT_NOT_PROVED, EXIT_PROVED, OUTCOME_FAILED, OUTCOME_NOT_PROVED, OUTCOME_PROVED, runProve } from '../../src/core/prove.mjs';
import { collectLiveEvidenceContract } from '../../src/autopilot/core/live-evidence.mjs';
import { evaluateEvidenceContract } from '../../src/autopilot/gates/evidence-contract.mjs';

const REPO_ROOT = fileURLToPath(new URL('../../', import.meta.url));
const HAS_PYTHON3 = spawnSync('python3', ['--version'], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }).status === 0;
const HAS_PYTEST = spawnSync('pytest', ['--version'], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }).status === 0;
const HAS_GO = spawnSync('go', ['version'], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }).status === 0;

function installVenvPytestShim(repoDir) {
  // Real Python3 runner shim in `.venv/bin/pytest` that executes real test_* functions with PYTHONPATH,
  // emits pytest -v lines, and writes real JUnit XML when `--junitxml=` is passed (used when host pytest is absent).
  const binDir = join(repoDir, '.venv', 'bin');
  mkdirSync(binDir, { recursive: true });
  writeFileSync(join(binDir, 'pytest'), [
    '#!/usr/bin/env python3',
    'import importlib.util, os, sys, traceback',
    'from xml.sax.saxutils import escape',
    'junit = None',
    'files = []',
    'for a in sys.argv[1:]:',
    '    if a.startswith("--junitxml="): junit = a.split("=", 1)[1]',
    '    elif a.startswith("-"): continue',
    '    else: files.append(a)',
    'passed = failed = 0',
    'xml_cases = []',
    'for f in files:',
    '    spec = importlib.util.spec_from_file_location("m", f)',
    '    mod = importlib.util.module_from_spec(spec)',
    '    spec.loader.exec_module(mod)',
    '    for name in sorted(dir(mod)):',
    '        if not name.startswith("test_"): continue',
    '        fn = getattr(mod, name)',
    '        if not callable(fn): continue',
    '        try:',
    '            fn()',
    '            passed += 1',
    '            print(f"{f}::{name} PASSED")',
    '            xml_cases.append(f\'<testcase classname="{escape(f)}" name="{escape(name)}" time="0.001"/>\')',
    '        except Exception as exc:',
    '            failed += 1',
    '            print(f"{f}::{name} FAILED")',
    '            traceback.print_exc()',
    '            xml_cases.append(f\'<testcase classname="{escape(f)}" name="{escape(name)}" time="0.001"><failure message="{escape(str(exc))}"/></testcase>\')',
    'if junit:',
    '    with open(junit, "w", encoding="utf-8") as fh:',
    '        fh.write(f\'<?xml version="1.0" encoding="utf-8"?><testsuite name="pytest" tests="{passed + failed}" failures="{failed}" errors="0" skipped="0">{" ".join(xml_cases)}</testsuite>\')',
    'parts = []',
    'if failed: parts.append(f"{failed} failed")',
    'if passed: parts.append(f"{passed} passed")',
    'summary = ", ".join(parts) or "no tests ran"',
    'print(f"=== {summary} in 0.01s ===")',
    'sys.exit(1 if failed else 0)',
  ].join('\n') + '\n', { mode: 0o755 });
}

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

function gitSha(dir, ref = 'HEAD') {
  return execFileSync('git', ['rev-parse', ref], { cwd: dir, encoding: 'utf8' }).trim();
}

// ---------------------------------------------------------------------------
// Test A: Fake standalone Z3/math spec model (zero production imports)
// ---------------------------------------------------------------------------
test('Test A: standalone spec model without production imports classifies as proved_spec_model and refuses proved_solver_code in pdd prove AND collectLiveEvidenceContract', async t => {
  const repo = initGitRepo(t, 'pdd-formal-test-a-');
  const nodeBin = JSON.stringify(process.execPath);
  mkdirSync(join(repo, 'src'), { recursive: true });
  mkdirSync(join(repo, 'test'), { recursive: true });

  writeFileSync(join(repo, 'package.json'), JSON.stringify({ name: 'ledger-demo', type: 'module', scripts: { test: `${nodeBin} --test test/ledger.test.mjs` } }, null, 2) + '\n');
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({
    verify: {
      test: `${nodeBin} --test test/ledger.test.mjs`,
      paths: [{ id: 'ledger', when: ['src/ledger.mjs'], run: `${nodeBin} --test test/ledger.test.mjs` }],
    },
  }, null, 2) + '\n');
  writeFileSync(join(repo, 'src', 'ledger.mjs'), 'export const credit = (bal, amt) => bal + amt;\n');
  writeFileSync(join(repo, 'test', 'ledger.test.mjs'), "import test from 'node:test'; import assert from 'node:assert/strict'; import { credit } from '../src/ledger.mjs'; test('credit', () => assert.equal(credit(10, 5), 15));\n");
  commitAll(repo, 'base');
  const baseSha = gitSha(repo, 'main');

  execFileSync('git', ['checkout', '-q', '-b', 'feat-spec-only'], { cwd: repo });
  writeFileSync(join(repo, 'src', 'ledger.mjs'), 'export const credit = (bal, amt) => (amt < 0 ? bal : bal + amt);\n');
  // Standalone math model WITH a commented-out import attempt (comment stripping must defeat spoofing!).
  writeFileSync(join(repo, 'test', 'ledger.formal.test.mjs'), [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "// import { credit } from '../src/ledger.mjs';",
    "/* import '../src/ledger.mjs'; */",
    "test('standalone tautology model', () => {",
    '  for (let x = 0; x < 50; x++) assert.ok(x + 1 > x);',
    '});',
  ].join('\n') + '\n');
  commitAll(repo, 'add disconnected spec model');
  const headSha = gitSha(repo, 'HEAD');

  // 1. Static binding inspection rejects commented-out imports -> proved_spec_model!
  const binding = inspectFormalFileBinding({ root: repo, filePath: 'test/ledger.formal.test.mjs', targetModules: ['src/ledger.mjs'] });
  assert.equal(binding.codeBound, false);
  assert.deepEqual(binding.importedProductionModules, []);
  assert.equal(binding.tier, 'proved_spec_model');
  assert.equal(binding.satisfiesCodeVerification, false);

  // 2. Real `pdd prove` MUST NOT return Proved; classifies as proved_spec_model (Not proved, exit 3).
  const out = makeSink(), err = makeSink();
  const proveRes = await runProve({ cwd: repo, base: 'main', json: true }, { stdout: out, stderr: err });
  assert.equal(proveRes.exitCode, EXIT_NOT_PROVED, out.text || err.text);
  assert.equal(proveRes.outcome, OUTCOME_NOT_PROVED);
  assert.equal(proveRes.receipt.formal.tier, 'proved_spec_model');
  assert.equal(proveRes.receipt.formal.satisfiesCodeVerification, false);
  assert.match(proveRes.receipt.formal.summary, /Formal: proved_spec_model/);
  assert.ok(proveRes.receipt.notProvedReasons.some(r => r.includes('formal-spec-model-only')));

  // 3. Refusal when claiming proved_solver_code directly.
  const refused = runFormalVerification({
    root: repo,
    touchedFiles: ['src/ledger.mjs', 'test/ledger.formal.test.mjs'],
    claimedTier: 'proved_solver_code',
  });
  assert.equal(refused.ok, false);
  assert.equal(refused.state, 'failed');
  assert.ok(refused.errors.some(e => e.includes('formal-spec-model-refused')));

  // 4. Real `collectLiveEvidenceContract` + `evaluateEvidenceContract` MUST HOLD when proved_solver_code is claimed!
  const live = await collectLiveEvidenceContract({
    repo: 'acme/ledger',
    job: {
      head: headSha,
      issue: 42,
      title: 'Credit invariant',
      body: 'Clamp negative credits.',
      evidence: { formal: { state: 'proved_solver_code' } },
    },
    headTree: repo,
    baseTip: baseSha,
    changedFiles: ['src/ledger.mjs', 'test/ledger.formal.test.mjs'],
    allTouchedFiles: ['src/ledger.mjs', 'test/ledger.formal.test.mjs'],
  });
  assert.equal(live.formalVerification.tier, 'proved_spec_model');
  assert.equal(live.contractInput.requireCodeBoundFormal, true);
  const verdict = evaluateEvidenceContract({
    ...live.contractInput,
    requireFrozenAcs: false,
    requireBaseOracle: false,
    requireGapCheck: false,
  });
  assert.equal(verdict.decision, 'HOLD');
  assert.equal(verdict.checks.formalProofBinding.ok, false);
  assert.equal(verdict.checks.formalProofBinding.tier, 'proved_spec_model');
});

// ---------------------------------------------------------------------------
// Test B: Real zero-dep code-bound formal/property test (JS + Python pytest)
// ---------------------------------------------------------------------------
test('Test B (JS): real zero-dep seeded PRNG code-bound formal test passes pdd prove, auto-links on prod edit, and kills mutation control', async t => {
  const repo = initGitRepo(t, 'pdd-formal-test-b-js-');
  const nodeBin = JSON.stringify(process.execPath);
  mkdirSync(join(repo, 'src'), { recursive: true });
  mkdirSync(join(repo, 'test'), { recursive: true });

  writeFileSync(join(repo, 'package.json'), JSON.stringify({ name: 'calc-demo', type: 'module', scripts: { test: `${nodeBin} --test test/calc.test.mjs` } }, null, 2) + '\n');
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({
    verify: {
      test: `${nodeBin} --test test/calc.test.mjs`,
      paths: [{ id: 'calc', when: ['src/calc.mjs'], run: `${nodeBin} --test test/calc.test.mjs` }],
    },
  }, null, 2) + '\n');
  const origCalc = 'export const add = (a, b) => a + b;\nexport const clamp = (v, lo, hi) => Math.min(hi, Math.max(lo, v));\n';
  writeFileSync(join(repo, 'src', 'calc.mjs'), origCalc);
  writeFileSync(join(repo, 'test', 'calc.test.mjs'), "import test from 'node:test'; import assert from 'node:assert/strict'; import { add } from '../src/calc.mjs'; test('add', () => assert.equal(add(1, 2), 3));\n");
  commitAll(repo, 'base');

  execFileSync('git', ['checkout', '-q', '-b', 'feat-formal-js'], { cwd: repo });
  writeFileSync(join(repo, 'src', 'calc.mjs'), 'export const add = (a, b) => Number(a) + Number(b);\nexport const clamp = (v, lo, hi) => Math.min(hi, Math.max(lo, v));\n');
  writeFileSync(join(repo, 'test', 'calc.formal.test.mjs'), [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { add, clamp } from '../src/calc.mjs';",
    'function mulberry32(seed) {',
    '  let a = seed >>> 0;',
    '  return () => { a = (a + 0x6d2b79f5) | 0; let t = Math.imul(a ^ (a >>> 15), 1 | a); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };',
    '}',
    "test('zero-install PRNG invariants: commutativity and clamp bounds over 200 worlds', () => {",
    '  const rng = mulberry32(0x2026);',
    '  for (let i = 0; i < 200; i++) {',
    '    const a = Math.floor(rng() * 1000) - 500;',
    '    const b = Math.floor(rng() * 1000) - 500;',
    '    assert.equal(add(a, b), add(b, a));',
    '    assert.equal(add(a, 0), a);',
    '    const lo = Math.min(a, b), hi = Math.max(a, b), v = Math.floor(rng() * 2000) - 1000;',
    '    const c = clamp(v, lo, hi);',
    '    assert.ok(c >= lo && c <= hi);',
    '  }',
    '});',
  ].join('\n') + '\n');
  commitAll(repo, 'add code-bound PRNG formal test');

  // 1. Real `pdd prove` (human mode + JSON mode) passes cleanly with Formal: bounded (code-bound)!
  const humanOut = makeSink(), humanErr = makeSink();
  const proveHuman = await runProve({ cwd: repo, base: 'main', json: false }, { stdout: humanOut, stderr: humanErr });
  assert.equal(proveHuman.exitCode, EXIT_PROVED, humanOut.text || humanErr.text);
  assert.equal(proveHuman.outcome, OUTCOME_PROVED);
  assert.match(humanOut.text, /Formal: bounded \(1 passed, code-bound\)/);
  assert.equal(proveHuman.receipt.formal.tier, 'bounded');
  assert.equal(proveHuman.receipt.formal.satisfiesCodeVerification, true);
  assert.deepEqual(proveHuman.receipt.formal.files[0].importedProductionModules, ['src/calc.mjs']);

  // 2. Real formal mutation control: injecting 1-line bug kills mutation AND never mutates caller checkout!
  const beforeCalc = readFileSync(join(repo, 'src', 'calc.mjs'), 'utf8');
  const killed = verifyFormalMutationControl({
    root: repo,
    targetFile: 'src/calc.mjs',
    mutatedContent: 'export const add = (a, b) => Number(a) - Number(b);\nexport const clamp = (v, lo, hi) => Math.min(hi, Math.max(lo, v));\n',
    formalFiles: ['test/calc.formal.test.mjs'],
  });
  assert.equal(killed.executed, true);
  assert.equal(killed.failedOnMutation, true);
  assert.equal(killed.syntaxOnlyCrash, false);
  assert.equal(readFileSync(join(repo, 'src', 'calc.mjs'), 'utf8'), beforeCalc, 'mutation control must NEVER modify caller checkout');

  // 3. Syntax-only crash NEVER counts as valid mutation control!
  const synCrash = verifyFormalMutationControl({
    root: repo,
    targetFile: 'src/calc.mjs',
    mutatedContent: 'export const add = (a, b => ;\n',
    formalFiles: ['test/calc.formal.test.mjs'],
  });
  assert.equal(synCrash.failedOnMutation, false);
  assert.equal(synCrash.syntaxOnlyCrash, true);

  // 4. Linked formal auto-discovery: editing ONLY src/calc.mjs with a bug fails pdd prove automatically!
  execFileSync('git', ['checkout', '-q', 'main'], { cwd: repo });
  execFileSync('git', ['merge', '-q', '--ff-only', 'feat-formal-js'], { cwd: repo });
  execFileSync('git', ['checkout', '-q', '-b', 'break-clamp'], { cwd: repo });
  writeFileSync(join(repo, 'src', 'calc.mjs'), 'export const add = (a, b) => Number(a) + Number(b);\nexport const clamp = (v, lo, hi) => v;\n');
  const broken = await runProve({ cwd: repo, base: 'main', json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(broken.exitCode, EXIT_FAILED);
  assert.equal(broken.outcome, OUTCOME_FAILED);
  assert.equal(broken.receipt.formal.state, 'failed');
  assert.equal(broken.receipt.formal.files[0].file, 'test/calc.formal.test.mjs');
});

test('Test B (Python live): real zero-dep Python formal test passes pdd prove with PYTHONPATH=src + JUnit XML, kills mutation, and rejects fake Python spec model', { skip: !HAS_PYTHON3 }, async t => {
  const repo = initGitRepo(t, 'pdd-formal-test-b-py-');
  mkdirSync(join(repo, 'src'), { recursive: true });
  mkdirSync(join(repo, 'tests'), { recursive: true });
  if (!HAS_PYTEST) installVenvPytestShim(repo);
  const pyTestCmd = HAS_PYTEST ? 'PYTHONPATH=src pytest tests/test_calc.py' : 'PYTHONPATH=src .venv/bin/pytest tests/test_calc.py';

  writeFileSync(join(repo, 'pyproject.toml'), '[project]\nname = "pycalc"\n[tool.pytest.ini_options]\ntestpaths = ["tests"]\n');
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({
    verify: {
      test: pyTestCmd,
      paths: [{ id: 'py-calc', when: ['src/calc.py'], run: pyTestCmd }],
    },
  }, null, 2) + '\n');
  writeFileSync(join(repo, '.gitignore'), '.venv/\n__pycache__/\n');
  writeFileSync(join(repo, 'src', 'calc.py'), 'def add(a: int, b: int) -> int:\n    return a + b\n\ndef clamp(v: int, lo: int, hi: int) -> int:\n    return min(hi, max(lo, v))\n');
  writeFileSync(join(repo, 'tests', 'test_calc.py'), 'from calc import add\n\ndef test_add():\n    assert add(2, 3) == 5\n');
  commitAll(repo, 'base python repo');

  execFileSync('git', ['checkout', '-q', '-b', 'feat-py-formal'], { cwd: repo });
  writeFileSync(join(repo, 'src', 'calc.py'), 'def add(a: int, b: int) -> int:\n    return int(a) + int(b)\n\ndef clamp(v: int, lo: int, hi: int) -> int:\n    return min(hi, max(lo, v))\n');
  writeFileSync(join(repo, 'tests', 'test_formal_calc.py'), [
    'import random',
    'from calc import add, clamp',
    '',
    'def test_formal_prng_invariants():',
    '    rng = random.Random(2026)',
    '    for _ in range(200):',
    '        a = rng.randint(-500, 500)',
    '        b = rng.randint(-500, 500)',
    '        assert add(a, b) == add(b, a)',
    '        assert add(a, 0) == a',
    '        lo, hi = min(a, b), max(a, b)',
    '        c = clamp(rng.randint(-1000, 1000), lo, hi)',
    '        assert lo <= c <= hi',
  ].join('\n') + '\n');
  commitAll(repo, 'add code-bound python formal test');

  // Real live pytest run via pdd prove!
  const out = makeSink(), err = makeSink();
  const proved = await runProve({ cwd: repo, base: 'main', json: true }, { stdout: out, stderr: err });
  assert.equal(proved.exitCode, EXIT_PROVED, out.text || err.text);
  assert.equal(proved.outcome, OUTCOME_PROVED);
  assert.equal(proved.receipt.formal.tier, 'bounded');
  assert.equal(proved.receipt.formal.satisfiesCodeVerification, true);
  assert.equal(proved.receipt.formal.files[0].runnerKind, 'pytest');
  assert.equal(proved.receipt.formal.files[0].passed, 1);
  assert.deepEqual(proved.receipt.formal.files[0].importedProductionModules, ['src/calc.py']);

  // Real Python mutation control (even when stale __pycache__/*.pyc exists from the exact same second with identical file length)!
  if (HAS_PYTEST) {
    const startSec = Math.floor(Date.now() / 1000);
    while (Math.floor(Date.now() / 1000) === startSec) { /* align to fresh second boundary */ }
    writeFileSync(join(repo, 'src', 'calc.py'), 'def add(a: int, b: int) -> int:\n    return int(a) + int(b)\n\ndef clamp(v: int, lo: int, hi: int) -> int:\n    return min(hi, max(lo, v))\n');
    execFileSync('pytest', ['-q', 'tests/test_formal_calc.py'], { cwd: repo, env: { ...process.env, PYTHONPATH: 'src' } });
  }
  const killed = verifyFormalMutationControl({
    root: repo,
    targetFile: 'src/calc.py',
    mutatedContent: 'def add(a: int, b: int) -> int:\n    return int(a) - int(b)\n\ndef clamp(v: int, lo: int, hi: int) -> int:\n    return min(hi, max(lo, v))\n',
    formalFiles: ['tests/test_formal_calc.py'],
  });
  assert.equal(killed.executed, true);
  assert.equal(killed.failedOnMutation, true, killed.summary);
  assert.equal(killed.syntaxOnlyCrash, false);

  // Fake standalone Python spec model (commented-out import + docstring) MUST classify as proved_spec_model!
  writeFileSync(join(repo, 'tests', 'test_formal_fake.py'), [
    '"""from calc import add"""',
    '# from calc import clamp',
    'def test_standalone_tautology():',
    '    for x in range(50):',
    '        assert x + 1 > x',
  ].join('\n') + '\n');
  const fakeProve = await runProve({ cwd: repo, base: 'main', json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(fakeProve.exitCode, EXIT_NOT_PROVED);
  assert.equal(fakeProve.receipt.formal.tier, 'proved_spec_model');
  assert.equal(fakeProve.receipt.formal.satisfiesCodeVerification, false);
});

// ---------------------------------------------------------------------------
// Test C: Pure docs/UI PR with zero invariants -> Formal: not-applicable (exit 0)
// ---------------------------------------------------------------------------
test('Test C: docs/UI PR with no invariants passes pdd prove cleanly with Formal: not-applicable and zero busywork', async t => {
  const repo = initGitRepo(t, 'pdd-formal-test-c-');
  const nodeBin = JSON.stringify(process.execPath);
  mkdirSync(join(repo, 'docs'), { recursive: true });
  mkdirSync(join(repo, 'user_stories'), { recursive: true });

  writeFileSync(join(repo, 'package.json'), JSON.stringify({ name: 'docs-demo', scripts: { test: `${nodeBin} -e "process.exit(0)"` } }, null, 2) + '\n');
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({ verify: { test: `${nodeBin} -e "process.exit(0)"`, paths: [] } }, null, 2) + '\n');
  writeFileSync(join(repo, 'docs', 'guide.md'), '# Guide\n\nWelcome.\n');
  commitAll(repo, 'base');

  execFileSync('git', ['checkout', '-q', '-b', 'docs-update'], { cwd: repo });
  writeFileSync(join(repo, 'docs', 'guide.md'), '# Guide\n\nUpdated copy.\n');
  commitAll(repo, 'update docs');

  const out = makeSink(), err = makeSink();
  const res = await runProve({ cwd: repo, base: 'main', json: false }, { stdout: out, stderr: err });
  assert.equal(res.exitCode, EXIT_PROVED, out.text || err.text);
  assert.equal(res.outcome, OUTCOME_PROVED);
  assert.equal(res.receipt.formal.applicable, false);
  assert.equal(res.receipt.formal.state, 'not-applicable');
  assert.equal(res.receipt.formal.summary, 'Formal: not-applicable');
  assert.match(out.text, /Formal: not-applicable/);

  // Story with explicit `## Rules to check` and 0 formal files surfaces honest non-blocking advisory without failing exit 0!
  writeFileSync(join(repo, 'user_stories', 'ledger.md'), '# Ledger\n\n## Rules to check\n- Balance never drops below zero.\n\n## Acceptance criteria\n1. Reject negative balance.\n');
  const scope = discoverFormalScope({ root: repo, touchedFiles: ['user_stories/ledger.md'] });
  assert.equal(scope.applicable, true);
  assert.equal(scope.invariantRules.length, 1);
  const missingRes = runFormalVerification({ root: repo, touchedFiles: ['user_stories/ledger.md'] });
  assert.equal(missingRes.ok, true);
  assert.equal(missingRes.state, 'missing');
  assert.match(missingRes.summary, /Formal: missing \(advisory: 1 invariant rule/);
});

// ---------------------------------------------------------------------------
// Test E: Security / Merge-base trust for verify.formal_command & symlink refusal
// ---------------------------------------------------------------------------
test('Test E: untrusted PR-added verify.formal_command is NEVER executed, while merge-base trusted verify.formal_command runs cleanly', async t => {
  const repo = initGitRepo(t, 'pdd-formal-test-e-');
  const nodeBin = JSON.stringify(process.execPath);
  mkdirSync(join(repo, 'src'), { recursive: true });
  writeFileSync(join(repo, 'package.json'), JSON.stringify({ name: 'sec-demo', scripts: { test: `${nodeBin} -e "process.exit(0)"` } }, null, 2) + '\n');
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({
    verify: {
      test: `${nodeBin} -e "process.exit(0)"`,
      paths: [{ id: 'app', when: ['src/**'], run: `${nodeBin} -e "process.exit(0)"` }],
    },
  }, null, 2) + '\n');
  writeFileSync(join(repo, 'src', 'app.mjs'), 'export const x = 1;\n');
  commitAll(repo, 'base without formal_command');

  // Attacker PR injects verify.formal_command and lint.mutation_command on branch!
  execFileSync('git', ['checkout', '-q', '-b', 'pr-untrusted-cmd'], { cwd: repo });
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({
    verify: {
      test: `${nodeBin} -e "process.exit(0)"`,
      formal_command: `${nodeBin} -e "require('node:fs').writeFileSync('.pwned-formal', '1')"`,
      mutation_command: `${nodeBin} -e "require('node:fs').writeFileSync('.pwned-mut', '1')"`,
      paths: [{ id: 'app', when: ['src/**'], run: `${nodeBin} -e "process.exit(0)"` }],
    },
    lint: {
      mutation_command: `${nodeBin} -e "require('node:fs').writeFileSync('.pwned-lint-mut', '1')"`,
    },
  }, null, 2) + '\n');
  writeFileSync(join(repo, 'src', 'app.mjs'), 'export const x = 2;\n');
  commitAll(repo, 'untrusted formal_command edit');

  const untrusted = await runProve({ cwd: repo, base: 'main', json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(untrusted.exitCode, EXIT_NOT_PROVED);
  assert.equal(existsSync(join(repo, '.pwned-formal')), false, 'untrusted PR verify.formal_command MUST NEVER execute');
  assert.equal(existsSync(join(repo, '.pwned-mut')), false, 'untrusted PR verify.mutation_command MUST NEVER execute');
  assert.equal(existsSync(join(repo, '.pwned-lint-mut')), false, 'untrusted PR lint.mutation_command MUST NEVER execute');

  // Now commit verify.formal_command on merge-base `main` -> trusted execution works with PDD_FORMAL_FILE!
  execFileSync('git', ['checkout', '-q', 'main'], { cwd: repo });
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({
    verify: {
      test: `${nodeBin} -e "process.exit(0)"`,
      formal_command: `${nodeBin} -e "require('node:fs').writeFileSync('.trusted-formal-ran', process.env.PDD_FORMAL_FILE || 'global')"`,
      paths: [{ id: 'app', when: ['src/**'], run: `${nodeBin} -e "process.exit(0)"` }],
    },
  }, null, 2) + '\n');
  commitAll(repo, 'trust formal_command on base');

  execFileSync('git', ['checkout', '-q', '-b', 'feat-trusted-formal'], { cwd: repo });
  writeFileSync(join(repo, 'src', 'app.mjs'), 'export const x = 3;\n');
  commitAll(repo, 'change app');

  const trusted = await runProve({ cwd: repo, base: 'main', json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(trusted.exitCode, EXIT_PROVED, JSON.stringify(trusted.receipt));
  assert.equal(existsSync(join(repo, '.trusted-formal-ran')), true, 'merge-base trusted verify.formal_command executes');
  assert.equal(trusted.receipt.formal.tier, 'bounded');

  // Symlinked formal file and symlinked mutation target are strictly refused.
  const outside = mkdtempSync(join(tmpdir(), 'pdd-formal-outside-'));
  t.after(() => rmSync(outside, { recursive: true, force: true }));
  writeFileSync(join(outside, 'secret.mjs'), 'export const s = 1;\n');
  mkdirSync(join(repo, 'test'), { recursive: true });
  symlinkSync(join(outside, 'secret.mjs'), join(repo, 'test', 'evil.formal.test.mjs'));
  symlinkSync(join(outside, 'secret.mjs'), join(repo, 'src', 'evil.mjs'));
  assert.equal(inspectFormalFileBinding({ root: repo, filePath: 'test/evil.formal.test.mjs' }).codeBound, false);
  const symMut = verifyFormalMutationControl({ root: repo, targetFile: 'src/evil.mjs', mutatedContent: 'x' });
  assert.equal(symMut.executed, false);
  assert.match(symMut.summary, /symlink/i);
});

// ---------------------------------------------------------------------------
// Go & Rust code-binding static inspection (+ real `go test` when installed)
// ---------------------------------------------------------------------------
test('polyglot static code-binding inspection across Go (cross-pkg & same-pkg symbols), Rust crates, and all 15 real pdd formal tests', t => {
  // 1. Go repo: same-package symbol reference = code-bound; same-package tautology with 0 symbol refs = proved_spec_model!
  const goRepo = initGitRepo(t, 'pdd-formal-go-');
  mkdirSync(join(goRepo, 'pkg', 'mathx'), { recursive: true });
  mkdirSync(join(goRepo, 'pkg', 'specx'), { recursive: true });
  writeFileSync(join(goRepo, 'go.mod'), 'module example.com/mathx\n\ngo 1.22\n');
  writeFileSync(join(goRepo, 'pkg', 'mathx', 'add.go'), 'package mathx\n\nfunc Add(a, b int) int { return a + b }\n');
  writeFileSync(join(goRepo, 'pkg', 'mathx', 'add_formal_test.go'), 'package mathx\n\nimport "testing"\n\nfunc TestFormalAdd(t *testing.T) {\n\tfor i := 0; i < 50; i++ {\n\t\tif Add(i, 1) != Add(1, i) { t.Fatal("bad") }\n\t}\n}\n');
  writeFileSync(join(goRepo, 'pkg', 'specx', 'prod.go'), 'package specx\n\nfunc Mul(a, b int) int { return a * b }\n');
  writeFileSync(join(goRepo, 'pkg', 'specx', 'fake_formal_test.go'), 'package specx\n\nimport "testing"\n\n// Mul(1, 2)\nfunc TestFake(t *testing.T) {\n\tfor i := 0; i < 50; i++ {\n\t\tif i+1 <= i { t.Fatal("bad") }\n\t}\n}\n');
  commitAll(goRepo, 'go repo');

  const goBound = inspectFormalFileBinding({ root: goRepo, filePath: 'pkg/mathx/add_formal_test.go' });
  assert.equal(goBound.codeBound, true);
  assert.deepEqual(goBound.importedProductionModules, ['pkg/mathx/add.go']);

  const goFake = inspectFormalFileBinding({ root: goRepo, filePath: 'pkg/specx/fake_formal_test.go' });
  assert.equal(goFake.codeBound, false);
  assert.equal(goFake.tier, 'proved_spec_model');

  if (HAS_GO) {
    const goRes = runFormalVerification({ root: goRepo, touchedFiles: ['pkg/mathx/add.go', 'pkg/mathx/add_formal_test.go'] });
    assert.equal(goRes.ok, true, JSON.stringify(goRes));
    assert.equal(goRes.tier, 'bounded');
    assert.equal(goRes.files[0].runnerKind, 'go');
    assert.equal(goRes.files[0].passed, 1);
  }

  // 2. Rust repo: crate use = code-bound; standalone test without crate use = proved_spec_model!
  const rsRepo = initGitRepo(t, 'pdd-formal-rs-');
  mkdirSync(join(rsRepo, 'src'), { recursive: true });
  mkdirSync(join(rsRepo, 'tests'), { recursive: true });
  writeFileSync(join(rsRepo, 'Cargo.toml'), '[package]\nname = "my-ledger"\nversion = "0.1.0"\n');
  writeFileSync(join(rsRepo, 'src', 'lib.rs'), 'pub fn add(a: i32, b: i32) -> i32 { a + b }\n');
  writeFileSync(join(rsRepo, 'tests', 'formal_ledger.rs'), 'use my_ledger::add;\n#[test]\nfn formal_add() { assert_eq!(add(1, 2), 3); }\n');
  writeFileSync(join(rsRepo, 'tests', 'formal_fake.rs'), '// use my_ledger::add;\n#[test]\nfn fake() { assert!(2 > 1); }\n');
  commitAll(rsRepo, 'rust repo');

  const rsBound = inspectFormalFileBinding({ root: rsRepo, filePath: 'tests/formal_ledger.rs' });
  assert.equal(rsBound.codeBound, true);
  assert.deepEqual(rsBound.importedProductionModules, ['src/lib.rs']);

  const rsFake = inspectFormalFileBinding({ root: rsRepo, filePath: 'tests/formal_fake.rs' });
  assert.equal(rsFake.codeBound, false);
  assert.equal(rsFake.tier, 'proved_spec_model');

  // 3. Real pdd repo check: ALL existing `test/*.formal.test.mjs` files resolve real production imports!
  const pddFormals = readdirSync(join(REPO_ROOT, 'test')).filter(n => n.endsWith('.formal.test.mjs')).sort();
  assert.ok(pddFormals.length >= 15, `expected >=15 existing formal tests in pdd repo, found ${pddFormals.length}`);
  for (const name of pddFormals) {
    const b = inspectFormalFileBinding({ root: REPO_ROOT, filePath: `test/${name}` });
    assert.equal(b.codeBound, true, `real pdd formal test test/${name} must resolve production imports`);
    assert.ok(b.importedProductionModules.length > 0, `test/${name} importedProductionModules non-empty`);
  }
});

// ---------------------------------------------------------------------------
// Adversarial Security & Spoof Regression Tests (P0-1, P0-3, P0-4, P0-5, P1-2, P1-7)
// ---------------------------------------------------------------------------
test('Adversarial P0-1/P0-3/P0-4/P0-5/P1-2/P1-7: blocks tracked .venv RCE, tampered verify scripts, arg injection, string/lifetime/import-type spoofs, and import-error mutations', async t => {
  const { buildRunnerInvocation, resolvePytestBinary, parsePytestVerboseReport, parseVitestVerboseReport } = await import('../../src/core/polyglot-runners.mjs');
  const { detectShadowBinaries } = await import('../../src/core/lint/test-inventory.mjs');

  // P0-1: Git-tracked `.venv/bin/pytest` in an untrusted PR MUST be refused by resolvePytestBinary,
  // flagged by detectShadowBinaries, and NEVER executed by pdd prove!
  const venvRepo = initGitRepo(t, 'pdd-formal-p01-venv-');
  const nodeBin = JSON.stringify(process.execPath);
  writeFileSync(join(venvRepo, 'package.json'), JSON.stringify({ name: 'node-app', scripts: { test: `${nodeBin} -e "process.exit(0)"` } }) + '\n');
  writeFileSync(join(venvRepo, 'src-base.mjs'), 'export const x = 1;\n');
  commitAll(venvRepo, 'base node repo');
  execFileSync('git', ['checkout', '-q', '-b', 'pr-evil-venv'], { cwd: venvRepo });
  const rceMarker = join(venvRepo, 'rce-pwned.txt');
  mkdirSync(join(venvRepo, '.venv', 'bin'), { recursive: true });
  mkdirSync(join(venvRepo, 'tests'), { recursive: true });
  writeFileSync(join(venvRepo, '.venv', 'bin', 'pytest'), `#!/bin/sh\necho PWNED > ${JSON.stringify(rceMarker)}\nexit 0\n`, { mode: 0o755 });
  writeFileSync(join(venvRepo, 'tests', 'test_formal_evil.py'), 'def test_x():\n    assert True\n');
  commitAll(venvRepo, 'commit tracked .venv/bin/pytest');

  assert.equal(resolvePytestBinary(venvRepo), 'pytest', 'git-tracked .venv/bin/pytest MUST be refused');
  const hits = detectShadowBinaries(venvRepo, { touchedFiles: ['.venv/bin/pytest'], baseSha: 'main' });
  assert.ok(hits.some(h => h.path === '.venv/bin/pytest'), 'detectShadowBinaries MUST flag tracked .venv/bin/pytest');
  const venvProve = await runProve({ cwd: venvRepo, base: 'main', json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(venvProve.exitCode, EXIT_FAILED);
  assert.equal(existsSync(rceMarker), false, 'PR-tracked .venv/bin/pytest MUST NEVER execute during pdd prove');

  // P0-3: Untrusted PR edit to script referenced by merge-base verify.formal_command OR package.json script MUST NOT execute!
  const scriptRepo = initGitRepo(t, 'pdd-formal-p03-script-');
  mkdirSync(join(scriptRepo, 'tools'), { recursive: true });
  writeFileSync(join(scriptRepo, 'package.json'), JSON.stringify({ name: 's-app', scripts: { test: `${nodeBin} -e "process.exit(0)"` } }) + '\n');
  writeFileSync(join(scriptRepo, 'tools', 'formal.mjs'), 'console.log("ok");\n');
  writeFileSync(join(scriptRepo, 'pdd.json'), JSON.stringify({ verify: { test: 'npm test', formal_command: `${nodeBin} tools/formal.mjs` } }) + '\n');
  commitAll(scriptRepo, 'base with merge-base verify.formal_command');
  execFileSync('git', ['checkout', '-q', '-b', 'pr-tamper-script'], { cwd: scriptRepo });
  const scriptMarker = join(scriptRepo, 'script-pwned.txt');
  writeFileSync(join(scriptRepo, 'tools', 'formal.mjs'), `import { writeFileSync } from 'node:fs'; writeFileSync(${JSON.stringify(scriptMarker)}, 'pwned');\n`);
  commitAll(scriptRepo, 'tamper tools/formal.mjs');
  const tamperRes = await runProve({ cwd: scriptRepo, base: 'main', json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(tamperRes.exitCode, EXIT_NOT_PROVED);
  assert.equal(existsSync(scriptMarker), false, 'PR-tampered verify-referenced script MUST NEVER execute');
  assert.ok(tamperRes.receipt.notProvedReasons.some(r => r.includes('tools/formal.mjs')));

  // P0-4 & P1-7: Leading-dash operands get `--` + `./` prefix, npx uses `--no-install`, and parsers handle parametrized pytest & vitest file headers!
  const pyInv = buildRunnerInvocation('pytest', { files: ['-o=addopts=evil_formal_test.py'], junitPath: '/tmp/j.xml' });
  assert.equal(pyInv.args.at(-2), '--');
  assert.equal(pyInv.args.at(-1), './-o=addopts=evil_formal_test.py');
  const vitInv = buildRunnerInvocation('vitest', { files: ['--config=evil.formal.test.ts'], junitPath: '/tmp/v.xml' });
  assert.equal(vitInv.args[0], '--no-install');
  assert.equal(vitInv.args.at(-2), '--');
  assert.equal(vitInv.args.at(-1), './--config=evil.formal.test.ts');
  const nodeInv = buildRunnerInvocation('node:test', { files: ['--import=evil.formal.test.mjs'] });
  assert.equal(nodeInv.args[0], '--test-reporter=tap');
  assert.equal(nodeInv.args[1], '--');
  assert.equal(nodeInv.args[2], './--import=evil.formal.test.mjs');
  const pyParam = parsePytestVerboseReport('tests/test_a.py::test_fn[hello world] PASSED [100%]\n====== 1 passed in 0.02s ======\n');
  assert.equal(pyParam.ok, true);
  assert.equal(pyParam.cases.length, 1);
  assert.equal(pyParam.cases[0].id, 'tests/test_a.py::test_fn[hello world]');
  const vitVerbose = parseVitestVerboseReport(' ✓ test/a.test.ts (1 test) 4ms\n   ✓ adds numbers 2ms\n\n Test Files  1 passed (1)\n      Tests  1 passed (1)\n   Duration  12ms\n');
  assert.equal(vitVerbose.ok, true);
  assert.equal(vitVerbose.cases.length, 1, 'vitest file header line must not double-count as a test case');
  assert.equal(vitVerbose.cases[0].id, 'adds numbers');

  // P0-5: String-literal, TS `import type`, Python backslash-continued string, Go backtick raw string, and Rust lifetime/string spoofs ALL fail closed!
  const spoofRepo = initGitRepo(t, 'pdd-formal-p05-spoofs-');
  mkdirSync(join(spoofRepo, 'src'), { recursive: true });
  mkdirSync(join(spoofRepo, 'test'), { recursive: true });
  mkdirSync(join(spoofRepo, 'tests'), { recursive: true });
  mkdirSync(join(spoofRepo, 'pkg', 'specx'), { recursive: true });
  writeFileSync(join(spoofRepo, 'src', 'ledger.mjs'), 'export const credit = x => x + 1;\n');
  writeFileSync(join(spoofRepo, 'src', 'ledger.ts'), 'export interface Account { balance: number }\nexport const credit = (x: number) => x + 1;\n');
  writeFileSync(join(spoofRepo, 'src', 'calc.py'), 'def add(a, b):\n    return a + b\n');
  writeFileSync(join(spoofRepo, 'go.mod'), 'module example.com/spoof\n\ngo 1.22\n');
  writeFileSync(join(spoofRepo, 'pkg', 'specx', 'prod.go'), 'package specx\n\nvar i int\nfunc Mul(a, b int) int { return a * b }\n');
  writeFileSync(join(spoofRepo, 'Cargo.toml'), '[package]\nname = "my-ledger"\nversion = "0.1.0"\n');
  writeFileSync(join(spoofRepo, 'src', 'lib.rs'), 'pub fn add(a: i32, b: i32) -> i32 { a + b }\n');

  writeFileSync(join(spoofRepo, 'test', 'js-str.formal.test.mjs'), 'const a = "require(\'../src/ledger.mjs\')";\nconst b = "import(\'../src/ledger.mjs\')";\nconst c = `\nimport { credit } from \'../src/ledger.mjs\';\n`;\nconst solver = "crosshair";\n');
  writeFileSync(join(spoofRepo, 'test', 'ts-type.formal.test.ts'), "import type { Account } from '../src/ledger.ts';\nconst x: Account = { balance: 1 };\nexport { x };\n");
  writeFileSync(join(spoofRepo, 'tests', 'test_formal_py_spoof.py'), 'x = "importlib.import_module(\'calc\')"\ns = "line1 \\\nfrom calc import add"\n');
  writeFileSync(join(spoofRepo, 'pkg', 'specx', 'spoof_formal_test.go'), 'package specx\n\nimport "testing"\n\nconst raw = `\nimport "example.com/spoof/pkg/specx"\n`\n\nfunc TestSpoof(t *testing.T) {\n\tfor i := 0; i < 10; i++ { _ = i }\n}\n');
  writeFileSync(join(spoofRepo, 'tests', 'formal_rs_spoof.rs'), 'const S: &str = "\nuse my_ledger::add;\n";\nfn f<\'a, \'b>(x: &\'a str, _y: &\'b str) -> &\'a str {\n    // use my_ledger::add;\n    x\n}\n');
  commitAll(spoofRepo, 'spoof fixtures');

  const jsSpoof = inspectFormalFileBinding({ root: spoofRepo, filePath: 'test/js-str.formal.test.mjs' });
  assert.equal(jsSpoof.codeBound, false, 'JS string/template spoofs MUST NOT satisfy code binding');
  assert.equal(jsSpoof.hasCodeBoundSolver, false, 'string literal "crosshair" MUST NOT spoof solver evidence');
  const tsSpoof = inspectFormalFileBinding({ root: spoofRepo, filePath: 'test/ts-type.formal.test.ts' });
  assert.equal(tsSpoof.codeBound, false, 'TS import type MUST NOT satisfy runtime code binding');
  const pySpoof = inspectFormalFileBinding({ root: spoofRepo, filePath: 'tests/test_formal_py_spoof.py' });
  assert.equal(pySpoof.codeBound, false, 'Python string & backslash-continued spoofs MUST NOT satisfy code binding');
  const goSpoof = inspectFormalFileBinding({ root: spoofRepo, filePath: 'pkg/specx/spoof_formal_test.go' });
  assert.equal(goSpoof.codeBound, false, 'Go backtick raw string & 1-char var i MUST NOT satisfy code binding');
  const rsSpoof = inspectFormalFileBinding({ root: spoofRepo, filePath: 'tests/formal_rs_spoof.rs' });
  assert.equal(rsSpoof.codeBound, false, 'Rust multiline string & lifetime-bracketed comment MUST NOT satisfy code binding');

  // P1-2: Mutation control rejects broken-import crashes & directory targets without throwing!
  writeFileSync(join(spoofRepo, 'test', 'real.formal.test.mjs'), "import test from 'node:test'; import assert from 'node:assert/strict'; import { credit } from '../src/ledger.mjs'; test('c', () => assert.equal(credit(1), 2));\n");
  const importErrMut = verifyFormalMutationControl({
    root: spoofRepo,
    targetFile: 'src/ledger.mjs',
    mutatedContent: "import { nope } from './does-not-exist-xyz.mjs';\nexport const credit = x => x + nope;\n",
    formalFiles: ['test/real.formal.test.mjs'],
  });
  assert.equal(importErrMut.failedOnMutation, false, 'ERR_MODULE_NOT_FOUND crash MUST NOT count as killing a mutation');
  assert.equal(importErrMut.syntaxOnlyCrash, true);
  const dirTargetMut = verifyFormalMutationControl({
    root: spoofRepo,
    targetFile: 'src',
    mutatedContent: 'x',
    formalFiles: ['test/real.formal.test.mjs'],
  });
  assert.equal(dirTargetMut.executed, false);
});
