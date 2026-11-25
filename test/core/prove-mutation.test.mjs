import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawn, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  evaluateMutationOutcome,
  generateGuardMutations,
  runProveMutationCheck,
  selectGuardMutations,
} from '../../src/core/prove-mutation.mjs';
import { EXIT_NOT_PROVED, EXIT_PROVED, EXIT_USAGE, OUTCOME_NOT_PROVED, OUTCOME_PROVED, runProve } from '../../src/core/prove.mjs';

const BIN_PATH = fileURLToPath(new URL('../../bin/pdd.mjs', import.meta.url));
const HAS_PYTHON3 = spawnSync('python3', ['--version'], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }).status === 0;
const HAS_PYTEST = spawnSync('pytest', ['--version'], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }).status === 0;

function installVenvPytestShim(repoDir) {
  const binDir = join(repoDir, '.venv', 'bin');
  mkdirSync(binDir, { recursive: true });
  writeFileSync(join(binDir, 'pytest'), [
    '#!/usr/bin/env python3',
    'import importlib.util, sys, traceback',
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
    'print(f"=== {(\", \".join(parts) or \"no tests ran\")} in 0.01s ===")',
    'sys.exit(1 if failed else 0)',
  ].join('\n') + '\n', { mode: 0o755 });
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

function makeSink() {
  let text = '';
  return { write(s) { text += String(s); }, get text() { return text; } };
}

test('selectGuardMutations prioritizes formal-covered guards, caps at 3, spreads across files, and deduplicates lines', () => {
  const { selected } = selectGuardMutations({
    maxMutations: 3,
    formalCoveredLines: { 'src/a.mjs': [2, 8], 'src/b.mjs': [4] },
    candidates: [
      { file: 'src/a.mjs', line: 12, kind: 'comparison-flip', description: 'uncov', original: 'a', mutated: 'b', mutatedContent: 'x' },
      { file: 'src/a.mjs', line: 8, kind: 'return-flip', description: 'ret', original: 'a', mutated: 'b', mutatedContent: 'x' },
      { file: 'src/a.mjs', line: 2, kind: 'comparison-flip', description: 'cmpA', original: 'a', mutated: 'b', mutatedContent: 'x' },
      { file: 'src/a.mjs', line: 2, kind: 'guard-negate', description: 'dupLine', original: 'a', mutated: 'b', mutatedContent: 'x' },
      { file: 'src/b.mjs', line: 4, kind: 'comparison-flip', description: 'cmpB', original: 'a', mutated: 'b', mutatedContent: 'x' },
    ],
  });
  assert.equal(selected.length, 3);
  assert.deepEqual(selected.map(m => `${m.file}:${m.line}`), ['src/a.mjs:2', 'src/b.mjs:4', 'src/a.mjs:8']);
  assert.ok(selected.every(m => m.formalCovered === true));
});

test('evaluateMutationOutcome ignores syntax-only crashes and fails with Not proved on surviving formal-covered guard', () => {
  const res = evaluateMutationOutcome({
    formalFiles: ['test/guard.formal.test.mjs'],
    results: [
      { id: 'M1', file: 'src/g.mjs', line: 5, kind: 'comparison-flip', description: 'Flip `<` to `>=`', original: 'if (x < 0)', mutated: 'if (x >= 0)', formalCovered: true, executed: true, failedOnMutation: false, syntaxOnlyCrash: false, exitCode: 0, summary: 'passed' },
      { id: 'M2', file: 'src/g.mjs', line: 9, kind: 'guard-negate', description: 'Bad syntax', original: 'if (y)', mutated: 'if (!(y)', formalCovered: true, executed: true, failedOnMutation: false, syntaxOnlyCrash: true, exitCode: 1, summary: 'SyntaxError' },
    ],
  });
  assert.equal(res.status, 'not-proved');
  assert.equal(res.ok, false);
  assert.equal(res.killed, 0);
  assert.equal(res.survived, 1);
  assert.equal(res.syntaxErrors, 1);
  assert.equal(res.killRate, 0);
  assert.equal(res.isolated, true);
  assert.equal(res.workingTreeMutated, false);
  assert.ok(res.notProvedReasons.some(r => r.includes('[mutation-survived]') && r.includes('src/g.mjs:5')));

  // All syntax errors with 0 real assertions -> Not proved (never Proved)!
  const onlySyntax = evaluateMutationOutcome({
    formalFiles: ['test/guard.formal.test.mjs'],
    results: [
      { id: 'M1', file: 'src/g.mjs', line: 5, kind: 'guard-negate', description: 'Bad', original: 'a', mutated: 'b', formalCovered: true, executed: true, failedOnMutation: false, syntaxOnlyCrash: true, exitCode: 1, summary: 'SyntaxError' },
    ],
  });
  assert.equal(onlySyntax.status, 'not-proved');
  assert.equal(onlySyntax.ok, false);
  assert.equal(onlySyntax.killed, 0);
});

test('generateGuardMutations never mutates strings or comments in JS and uses real AST in Python', t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-mut-gen-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  mkdirSync(join(dir, 'src'), { recursive: true });

  writeFileSync(join(dir, 'src', 'guard.mjs'), [
    'export function check(x) {',
    '  const note = "if (x < 0) return false;";',
    '  // if (x > 10) return false;',
    '  if (x < 0) return false;',
    '  return true;',
    '}',
  ].join('\n') + '\n');
  const jsRes = generateGuardMutations({
    root: dir,
    diffLinesByFile: { 'src/guard.mjs': [2, 3, 4, 5] },
    targetFiles: ['src/guard.mjs'],
  });
  assert.deepEqual(jsRes.candidates.map(c => c.line), [4, 5], 'string literal and comment lines MUST NOT be mutated');
  assert.equal(jsRes.candidates[0].kind, 'comparison-flip');
  assert.match(jsRes.candidates[0].mutated, /x >= 0/);

  if (HAS_PYTHON3) {
    writeFileSync(join(dir, 'src', 'guard.py'), [
      'def check(x: int) -> bool:',
      '    msg = "if x < 0: return False"',
      '    # if x > 10: return False',
      '    if x < 0:',
      '        return False',
      '    return True',
    ].join('\n') + '\n');
    const pyRes = generateGuardMutations({
      root: dir,
      diffLinesByFile: { 'src/guard.py': [2, 3, 4, 5, 6] },
      targetFiles: ['src/guard.py'],
    });
    assert.deepEqual(pyRes.candidates.map(c => c.line), [4, 5, 6]);
    assert.equal(pyRes.candidates[0].kind, 'comparison-flip');
    assert.match(pyRes.candidates[0].mutated, /x >= 0/);
  }
});

test('AC3/AC4/AC5/AC6 (JS live): pdd prove --mutation-check returns Proved when formal kills guard mutations, Not proved when a guard survives, and leaves zero working-tree changes', t => {
  const repo = initGitRepo(t, 'pdd-prove-mut-js-');
  const nodeBin = JSON.stringify(process.execPath);
  mkdirSync(join(repo, 'src'), { recursive: true });
  mkdirSync(join(repo, 'test'), { recursive: true });

  writeFileSync(join(repo, 'package.json'), JSON.stringify({ name: 'mut-js', type: 'module', scripts: { test: `${nodeBin} --test test/*.test.mjs` } }, null, 2) + '\n');
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({
    verify: {
      test: `${nodeBin} --test test/*.test.mjs`,
      paths: [{ id: 'auth', when: ['src/**/*.mjs'], run: `${nodeBin} --test test/*.test.mjs` }],
    },
  }, null, 2) + '\n');
  writeFileSync(join(repo, 'src', 'quota.mjs'), 'export function allow(used, limit) {\n  return used <= limit;\n}\n');
  writeFileSync(join(repo, 'test', 'quota.test.mjs'), "import test from 'node:test'; import assert from 'node:assert/strict'; import { allow } from '../src/quota.mjs'; test('allow', () => assert.equal(allow(1, 5), true));\n");
  commitAll(repo, 'base');

  execFileSync('git', ['checkout', '-q', '-b', 'feat-quota-guards'], { cwd: repo });
  const prodBody = [
    'export function allow(used, limit) {',
    '  if (limit < 0) return false;',
    '  if (used > limit) return false;',
    '  return true;',
    '}',
  ].join('\n') + '\n';
  writeFileSync(join(repo, 'src', 'quota.mjs'), prodBody);

  // 1. Strong formal test -> ALL mutations killed -> Proved (exit 0)!
  writeFileSync(join(repo, 'test', 'quota.formal.test.mjs'), [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { allow } from '../src/quota.mjs';",
    "test('formal quota guards', () => {",
    '  for (let limit = -5; limit <= 10; limit++) {',
    '    for (let used = 0; used <= 12; used++) {',
    '      const expected = limit >= 0 && used <= limit;',
    '      assert.equal(allow(used, limit), expected);',
    '    }',
    '  }',
    '});',
  ].join('\n') + '\n');
  commitAll(repo, 'strong formal test');

  const killedCli = spawnSync(process.execPath, [BIN_PATH, 'prove', '--coverage', '--mutation-check', '--base', 'main', '--json'], {
    cwd: repo,
    encoding: 'utf8',
    timeout: 30_000,
  });
  assert.equal(killedCli.status, EXIT_PROVED, `stderr: ${killedCli.stderr}\nstdout: ${killedCli.stdout}`);
  const killedReceipt = JSON.parse(killedCli.stdout);
  assert.equal(killedReceipt.outcome, OUTCOME_PROVED);
  assert.equal(killedReceipt.mutation.status, 'proved');
  assert.equal(killedReceipt.mutation.ok, true);
  assert.ok(killedReceipt.mutation.attempted >= 1 && killedReceipt.mutation.attempted <= 3);
  assert.equal(killedReceipt.mutation.killed, killedReceipt.mutation.attempted);
  assert.equal(killedReceipt.mutation.survived, 0);
  assert.equal(killedReceipt.mutation.killRate, 100);
  assert.equal(killedReceipt.coverage.status, 'ok');
  assert.equal(readFileSync(join(repo, 'src', 'quota.mjs'), 'utf8'), prodBody);
  assert.equal(execFileSync('git', ['status', '--porcelain'], { cwd: repo, encoding: 'utf8' }), '');

  // 2. Weak formal test (calls allow(), hits guards, but only checks typeof === 'boolean') -> surviving mutation -> Not proved (exit 3)!
  writeFileSync(join(repo, 'test', 'quota.formal.test.mjs'), [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { allow } from '../src/quota.mjs';",
    "test('weak formal test', () => {",
    '  for (let i = 0; i < 10; i++) {',
    '    assert.equal(typeof allow(i, 5), "boolean");',
    '  }',
    '});',
  ].join('\n') + '\n');
  commitAll(repo, 'weaken formal assertions');

  const survivedCli = spawnSync(process.execPath, [BIN_PATH, 'prove', '--mutation-check', '--base', 'main', '--json'], {
    cwd: repo,
    encoding: 'utf8',
    timeout: 30_000,
  });
  assert.equal(survivedCli.status, EXIT_NOT_PROVED, `stderr: ${survivedCli.stderr}\nstdout: ${survivedCli.stdout}`);
  const survivedReceipt = JSON.parse(survivedCli.stdout);
  assert.equal(survivedReceipt.outcome, OUTCOME_NOT_PROVED);
  assert.equal(survivedReceipt.mutation.status, 'not-proved');
  assert.ok(survivedReceipt.mutation.survived >= 1);
  assert.ok(survivedReceipt.notProvedReasons.some(r => r.includes('[mutation-survived]')));
  assert.equal(readFileSync(join(repo, 'src', 'quota.mjs'), 'utf8'), prodBody);
  assert.equal(execFileSync('git', ['status', '--porcelain'], { cwd: repo, encoding: 'utf8' }), '');

  // AC6: Combining --mutation-check with --test exits 2!
  const badCombo = spawnSync(process.execPath, [BIN_PATH, 'prove', '--mutation-check', '--base', 'main', '--test', 'npm test', '--expect', 'ERR'], {
    cwd: repo,
    encoding: 'utf8',
    timeout: 10_000,
  });
  assert.equal(badCombo.status, EXIT_USAGE);
  assert.equal(badCombo.stdout, '');
});

test('AC3/AC4/AC5 (Python live): pdd prove --mutation-check catches both killed (Proved) and surviving (Not proved) AST guard mutations', { skip: !HAS_PYTHON3 }, t => {
  const repo = initGitRepo(t, 'pdd-prove-mut-py-');
  mkdirSync(join(repo, 'src'), { recursive: true });
  mkdirSync(join(repo, 'tests'), { recursive: true });
  if (!HAS_PYTEST) installVenvPytestShim(repo);
  const pyTestCmd = HAS_PYTEST ? 'PYTHONPATH=src pytest tests/test_balance.py' : 'PYTHONPATH=src .venv/bin/pytest tests/test_balance.py';

  writeFileSync(join(repo, '.gitignore'), '.venv/\n__pycache__/\n');
  writeFileSync(join(repo, 'pyproject.toml'), '[project]\nname = "pybal"\n[tool.pytest.ini_options]\ntestpaths = ["tests"]\n');
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({
    verify: {
      test: pyTestCmd,
      paths: [{ id: 'py-bal', when: ['src/balance.py'], run: pyTestCmd }],
    },
  }, null, 2) + '\n');
  writeFileSync(join(repo, 'src', 'balance.py'), 'def can_withdraw(bal: int, amt: int) -> bool:\n    return bal >= amt\n');
  writeFileSync(join(repo, 'tests', 'test_balance.py'), 'from balance import can_withdraw\n\ndef test_basic():\n    assert can_withdraw(10, 5) is True\n');
  commitAll(repo, 'py base');

  execFileSync('git', ['checkout', '-q', '-b', 'feat-py-mut'], { cwd: repo });
  const pyBody = [
    'def can_withdraw(bal: int, amt: int) -> bool:',
    '    if amt <= 0:',
    '        return False',
    '    if amt > bal:',
    '        return False',
    '    return True',
  ].join('\n') + '\n';
  writeFileSync(join(repo, 'src', 'balance.py'), pyBody);
  writeFileSync(join(repo, 'tests', 'test_formal_balance.py'), [
    'from balance import can_withdraw',
    '',
    'def test_formal_withdraw_grid():',
    '    for bal in range(0, 8):',
    '        for amt in range(-2, 10):',
    '            expected = (amt > 0) and (amt <= bal)',
    '            assert can_withdraw(bal, amt) is expected',
  ].join('\n') + '\n');
  commitAll(repo, 'py strong formal');

  const killed = runProve({ cwd: repo, base: 'main', mutationCheck: true, json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(killed.exitCode, EXIT_PROVED, JSON.stringify(killed.receipt));
  assert.equal(killed.receipt.mutation.status, 'proved');
  assert.ok(killed.receipt.mutation.killed >= 1);
  assert.equal(killed.receipt.mutation.survived, 0);
  assert.equal(readFileSync(join(repo, 'src', 'balance.py'), 'utf8'), pyBody);
  assert.equal(execFileSync('git', ['status', '--porcelain'], { cwd: repo, encoding: 'utf8' }), '');

  // Weak formal test -> surviving mutation -> Not proved (exit 3)!
  writeFileSync(join(repo, 'tests', 'test_formal_balance.py'), [
    'from balance import can_withdraw',
    '',
    'def test_formal_weak():',
    '    for amt in range(1, 5):',
    '        assert isinstance(can_withdraw(10, amt), bool)',
  ].join('\n') + '\n');
  commitAll(repo, 'py weak formal');

  const survived = runProve({ cwd: repo, base: 'main', mutationCheck: true, json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(survived.exitCode, EXIT_NOT_PROVED, JSON.stringify(survived.receipt));
  assert.equal(survived.receipt.mutation.status, 'not-proved');
  assert.ok(survived.receipt.mutation.survived >= 1);
  assert.equal(readFileSync(join(repo, 'src', 'balance.py'), 'utf8'), pyBody);
  assert.equal(execFileSync('git', ['status', '--porcelain'], { cwd: repo, encoding: 'utf8' }), '');
});

test('AC5: interrupting pdd prove --mutation-check mid-flight with SIGINT leaves zero workspace pollution', async t => {
  const repo = initGitRepo(t, 'pdd-prove-mut-sigint-');
  const nodeBin = JSON.stringify(process.execPath);
  mkdirSync(join(repo, 'src'), { recursive: true });
  mkdirSync(join(repo, 'test'), { recursive: true });

  writeFileSync(join(repo, 'package.json'), JSON.stringify({ name: 'sig-demo', type: 'module', scripts: { test: `${nodeBin} -e "process.exit(0)"` } }, null, 2) + '\n');
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({
    verify: {
      test: `${nodeBin} -e "process.exit(0)"`,
      paths: [{ id: 'sig', when: ['src/**/*.mjs'], run: `${nodeBin} -e "process.exit(0)"` }],
    },
  }, null, 2) + '\n');
  writeFileSync(join(repo, 'src', 'gate.mjs'), 'export const open = x => x > 0;\n');
  commitAll(repo, 'base');

  execFileSync('git', ['checkout', '-q', '-b', 'feat-sig'], { cwd: repo });
  const gateBody = 'export function open(x) {\n  if (x <= 0) return false;\n  return true;\n}\n';
  writeFileSync(join(repo, 'src', 'gate.mjs'), gateBody);
  // Slow formal test during mutation so we can send SIGINT mid-execution.
  writeFileSync(join(repo, 'test', 'gate.formal.test.mjs'), [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { open } from '../src/gate.mjs';",
    "test('slow formal', async () => {",
    '  await new Promise(r => setTimeout(r, 400));',
    '  assert.equal(open(1), true);',
    '  assert.equal(open(0), false);',
    '});',
  ].join('\n') + '\n');
  commitAll(repo, 'add slow formal test');

  const child = spawn(process.execPath, [BIN_PATH, 'prove', '--mutation-check', '--base', 'main'], {
    cwd: repo,
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  await new Promise(resolve => {
    setTimeout(() => {
      try { child.kill('SIGINT'); } catch {}
    }, 650);
    child.on('exit', () => resolve());
  });

  assert.equal(readFileSync(join(repo, 'src', 'gate.mjs'), 'utf8'), gateBody, 'production file MUST stay byte-identical on SIGINT');
  assert.equal(execFileSync('git', ['status', '--porcelain'], { cwd: repo, encoding: 'utf8' }), '', 'working tree MUST remain completely clean after SIGINT');
});

test('Finding 1: SIGTERM and process-group SIGINT mid-mutation exit promptly on signal without swallowing, leaking temp dirs, or misclassifying as survived', async t => {
  const repo = initGitRepo(t, 'pdd-prove-mut-sig-prompt-');
  const nodeBin = JSON.stringify(process.execPath);
  mkdirSync(join(repo, 'src'), { recursive: true });
  mkdirSync(join(repo, 'test'), { recursive: true });
  writeFileSync(join(repo, 'package.json'), JSON.stringify({ name: 'sig-prompt', type: 'module', scripts: { test: `${nodeBin} -e "process.exit(0)"` } }, null, 2) + '\n');
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({
    verify: {
      test: `${nodeBin} -e "process.exit(0)"`,
      paths: [{ id: 'sig', when: ['src/**/*.mjs'], run: `${nodeBin} -e "process.exit(0)"` }],
    },
  }, null, 2) + '\n');
  writeFileSync(join(repo, 'src', 'gate.mjs'), 'export const open = x => x > 0;\n');
  commitAll(repo, 'base');

  execFileSync('git', ['checkout', '-q', '-b', 'feat-sig-prompt'], { cwd: repo });
  const gateBody = [
    'export function open(x) {',
    '  if (x < 0) return false;',
    '  if (x === 0) return false;',
    '  if (x > 100) return false;',
    '  return true;',
    '}',
  ].join('\n') + '\n';
  writeFileSync(join(repo, 'src', 'gate.mjs'), gateBody);
  // Slow formal test (~2s per run -> 3 mutations would take >6s if signal were swallowed!)
  writeFileSync(join(repo, 'test', 'gate.formal.test.mjs'), [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { open } from '../src/gate.mjs';",
    "test('slow formal', async () => {",
    '  await new Promise(r => setTimeout(r, 1500));',
    '  assert.equal(open(1), true);',
    '  assert.equal(open(-1), false);',
    '  assert.equal(open(0), false);',
    '  assert.equal(open(200), false);',
    '});',
  ].join('\n') + '\n');
  commitAll(repo, 'add slow 3-guard formal test');

  for (const mode of ['SIGTERM-direct', 'SIGINT-pgroup']) {
    const isolatedTmp = mkdtempSync(join(tmpdir(), `pdd-mut-sig-tmp-${mode}-`));
    t.after(() => rmSync(isolatedTmp, { recursive: true, force: true }));
    const started = Date.now();
    const child = spawn(process.execPath, [BIN_PATH, 'prove', '--mutation-check', '--base', 'main', '--json'], {
      cwd: repo,
      env: { ...process.env, TMPDIR: isolatedTmp },
      detached: mode === 'SIGINT-pgroup',
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    let out = '';
    child.stdout.on('data', d => { out += d; });
    const exitInfo = await new Promise(resolve => {
      const timer = setTimeout(() => {
        try {
          if (mode === 'SIGINT-pgroup') process.kill(-child.pid, 'SIGINT');
          else child.kill('SIGTERM');
        } catch {}
      }, 900);
      child.on('exit', (code, signal) => {
        clearTimeout(timer);
        resolve({ code, signal, elapsedMs: Date.now() - started });
      });
    });

    const expectedSig = mode === 'SIGINT-pgroup' ? 'SIGINT' : 'SIGTERM';
    assert.equal(exitInfo.signal, expectedSig, `${mode} MUST terminate with ${expectedSig}, got ${JSON.stringify(exitInfo)} stdout=${out}`);
    assert.equal(exitInfo.code, null, `${mode} MUST not exit 0 or 3 after signal`);
    assert.ok(exitInfo.elapsedMs < 4000, `${mode} MUST exit promptly instead of running remaining mutations (${exitInfo.elapsedMs}ms)`);
    assert.equal(out.includes('mutation-survived'), false, `${mode} MUST NEVER misclassify signal-killed run as survived`);
    const leaked = readdirSync(isolatedTmp).filter(n => n.startsWith('pdd-prove-') || n.startsWith('pdd-formal-run-'));
    assert.deepEqual(leaked, [], `${mode} MUST leave zero leaked temp directories`);
    assert.equal(readFileSync(join(repo, 'src', 'gate.mjs'), 'utf8'), gateBody);
    assert.equal(execFileSync('git', ['status', '--porcelain'], { cwd: repo, encoding: 'utf8' }), '');
  }
});

test('Finding 2: multiline if continuation-line edits in JS and Python generate formal-covered guard mutations', t => {
  // 1. JS multiline `if (\n a < 0\n || b > 10\n)` where ONLY line 4 (`|| b > 10`) changed
  const jsRepo = initGitRepo(t, 'pdd-mut-multi-js-');
  const nodeBin = JSON.stringify(process.execPath);
  mkdirSync(join(jsRepo, 'src'), { recursive: true });
  mkdirSync(join(jsRepo, 'test'), { recursive: true });
  writeFileSync(join(jsRepo, 'package.json'), JSON.stringify({ name: 'multi-js', type: 'module', scripts: { test: `${nodeBin} --test test/*.test.mjs` } }, null, 2) + '\n');
  writeFileSync(join(jsRepo, 'pdd.json'), JSON.stringify({
    verify: {
      test: `${nodeBin} --test test/*.test.mjs`,
      paths: [{ id: 'core', when: ['src/**/*.mjs'], run: `${nodeBin} --test test/*.test.mjs` }],
    },
  }, null, 2) + '\n');
  writeFileSync(join(jsRepo, 'src', 'multi.mjs'), [
    'export function allow(a, b) {',
    '  if (',
    '    a < 0',
    '    || b > 100',
    '  ) {',
    '    return false;',
    '  }',
    '  return true;',
    '}',
  ].join('\n') + '\n');
  writeFileSync(join(jsRepo, 'test', 'multi.formal.test.mjs'), [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { allow } from '../src/multi.mjs';",
    "test('formal allow guard', () => {",
    '  assert.equal(typeof allow(-1, 0), "boolean");',
    '  assert.equal(typeof allow(1, 5), "boolean");',
    '});',
  ].join('\n') + '\n');
  commitAll(jsRepo, 'base');

  execFileSync('git', ['checkout', '-q', '-b', 'feat-multi-js'], { cwd: jsRepo });
  writeFileSync(join(jsRepo, 'src', 'multi.mjs'), [
    'export function allow(a, b) {',
    '  if (',
    '    a < 0',
    '    || b > 10',
    '  ) {',
    '    return false;',
    '  }',
    '  return true;',
    '}',
  ].join('\n') + '\n');
  commitAll(jsRepo, 'tighten continuation line b > 10');

  const jsWeak = runProve({ cwd: jsRepo, base: 'main', mutationCheck: true, json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(jsWeak.exitCode, EXIT_NOT_PROVED, JSON.stringify(jsWeak.receipt));
  assert.equal(jsWeak.receipt.mutation.status, 'not-proved');
  assert.equal(jsWeak.receipt.mutation.attempted, 1);
  assert.equal(jsWeak.receipt.mutation.survived, 1);
  assert.equal(jsWeak.receipt.mutation.mutations[0].line, 4);
  assert.equal(jsWeak.receipt.mutation.mutations[0].formalCovered, true);

  // Strengthen JS formal test -> kills multiline continuation-line mutation -> Proved (exit 0)
  writeFileSync(join(jsRepo, 'test', 'multi.formal.test.mjs'), [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { allow } from '../src/multi.mjs';",
    "test('formal allow guard', () => {",
    '  assert.equal(allow(-1, 0), false);',
    '  assert.equal(allow(1, 5), true);',
    '  assert.equal(allow(1, 11), false);',
    '});',
  ].join('\n') + '\n');
  commitAll(jsRepo, 'strengthen js multiline formal test');

  const jsStrong = runProve({ cwd: jsRepo, base: 'main', mutationCheck: true, json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(jsStrong.exitCode, EXIT_PROVED, JSON.stringify(jsStrong.receipt));
  assert.equal(jsStrong.receipt.mutation.status, 'proved');
  assert.equal(jsStrong.receipt.mutation.killed, 1);
  assert.equal(jsStrong.receipt.mutation.mutations[0].line, 4);

  // 2. Python multiline `if (\n a < 0\n or b > 10\n):` where ONLY line 4 (`or b > 10`) changed
  if (HAS_PYTHON3) {
    const pyRepo = initGitRepo(t, 'pdd-mut-multi-py-');
    mkdirSync(join(pyRepo, 'src'), { recursive: true });
    mkdirSync(join(pyRepo, 'tests'), { recursive: true });
    if (!HAS_PYTEST) installVenvPytestShim(pyRepo);
    const pyTestCmd = HAS_PYTEST ? 'PYTHONPATH=src pytest tests/test_formal_multi.py' : 'PYTHONPATH=src .venv/bin/pytest tests/test_formal_multi.py';
    writeFileSync(join(pyRepo, '.gitignore'), '.venv/\n__pycache__/\n');
    writeFileSync(join(pyRepo, 'pdd.json'), JSON.stringify({
      verify: {
        test: pyTestCmd,
        paths: [{ id: 'py', when: ['src/**/*.py'], run: pyTestCmd }],
      },
    }, null, 2) + '\n');
    writeFileSync(join(pyRepo, 'src', 'multi.py'), [
      'def allow(a: int, b: int) -> bool:',
      '    if (',
      '        a < 0',
      '        or b > 100',
      '    ):',
      '        return False',
      '    return True',
    ].join('\n') + '\n');
    writeFileSync(join(pyRepo, 'tests', 'test_formal_multi.py'), [
      'from multi import allow',
      'def test_allow_guard():',
      '    assert isinstance(allow(-1, 0), bool)',
      '    assert isinstance(allow(1, 5), bool)',
    ].join('\n') + '\n');
    commitAll(pyRepo, 'py base');

    execFileSync('git', ['checkout', '-q', '-b', 'feat-multi-py'], { cwd: pyRepo });
    writeFileSync(join(pyRepo, 'src', 'multi.py'), [
      'def allow(a: int, b: int) -> bool:',
      '    if (',
      '        a < 0',
      '        or b > 10',
      '    ):',
      '        return False',
      '    return True',
    ].join('\n') + '\n');
    commitAll(pyRepo, 'tighten py continuation line b > 10');

    const pyWeak = runProve({ cwd: pyRepo, base: 'main', mutationCheck: true, json: true }, { stdout: makeSink(), stderr: makeSink() });
    assert.equal(pyWeak.exitCode, EXIT_NOT_PROVED, JSON.stringify(pyWeak.receipt));
    assert.equal(pyWeak.receipt.mutation.status, 'not-proved');
    assert.equal(pyWeak.receipt.mutation.attempted, 1);
    assert.equal(pyWeak.receipt.mutation.survived, 1);
    assert.equal(pyWeak.receipt.mutation.mutations[0].line, 4);
    assert.equal(pyWeak.receipt.mutation.mutations[0].formalCovered, true);

    writeFileSync(join(pyRepo, 'tests', 'test_formal_multi.py'), [
      'from multi import allow',
      'def test_allow_guard():',
      '    assert allow(-1, 0) is False',
      '    assert allow(1, 5) is True',
      '    assert allow(1, 11) is False',
    ].join('\n') + '\n');
    commitAll(pyRepo, 'strengthen py multiline formal test');

    const pyStrong = runProve({ cwd: pyRepo, base: 'main', mutationCheck: true, json: true }, { stdout: makeSink(), stderr: makeSink() });
    assert.equal(pyStrong.exitCode, EXIT_PROVED, JSON.stringify(pyStrong.receipt));
    assert.equal(pyStrong.receipt.mutation.status, 'proved');
    assert.equal(pyStrong.receipt.mutation.killed, 1);
    assert.equal(pyStrong.receipt.mutation.mutations[0].line, 4);
  }
});

test('Finding 3: top-level JS guard throwing RangeError during module import counts as killed, not survived', t => {
  const repo = initGitRepo(t, 'pdd-mut-toplevel-throw-');
  const nodeBin = JSON.stringify(process.execPath);
  mkdirSync(join(repo, 'src'), { recursive: true });
  mkdirSync(join(repo, 'test'), { recursive: true });
  writeFileSync(join(repo, 'package.json'), JSON.stringify({ name: 'tl-throw', type: 'module', scripts: { test: `${nodeBin} --test test/*.test.mjs` } }, null, 2) + '\n');
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({
    verify: {
      test: `${nodeBin} --test test/*.test.mjs`,
      paths: [{ id: 'cfg', when: ['src/**/*.mjs'], run: `${nodeBin} --test test/*.test.mjs` }],
    },
  }, null, 2) + '\n');
  writeFileSync(join(repo, 'src', 'config.mjs'), 'export const MAX_LIMIT = 100;\n');
  writeFileSync(join(repo, 'test', 'config.formal.test.mjs'), [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { MAX_LIMIT } from '../src/config.mjs';",
    "test('config limit valid', () => assert.ok(MAX_LIMIT >= 10));",
  ].join('\n') + '\n');
  commitAll(repo, 'base');

  execFileSync('git', ['checkout', '-q', '-b', 'feat-tl-guard'], { cwd: repo });
  writeFileSync(join(repo, 'src', 'config.mjs'), [
    'export const MAX_LIMIT = 100;',
    'if (MAX_LIMIT < 10) {',
    '  throw new RangeError("CONFIG_TOO_SMALL");',
    '}',
  ].join('\n') + '\n');
  commitAll(repo, 'add module-load guard');

  const res = runProve({ cwd: repo, base: 'main', mutationCheck: true, json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(res.exitCode, EXIT_PROVED, JSON.stringify(res.receipt));
  assert.equal(res.receipt.mutation.status, 'proved');
  assert.equal(res.receipt.mutation.killed, 1);
  assert.equal(res.receipt.mutation.survived, 0);
  assert.equal(res.receipt.mutation.mutations[0].outcome, 'killed');
});

test('Reviewer P1 #1 & P2 #5: multiline JS guard-negate preserves exact offsets after // Prompt headers and quote-bearing regexes; fatal SIGKILL never classifies as survived', t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-mut-offset-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  mkdirSync(join(dir, 'src'), { recursive: true });
  writeFileSync(join(dir, 'src', 'header_guard.mjs'), [
    '// Prompt: prompts/cli/header-guard.prompt.md',
    '',
    '// Regex with quotes must not desync lexer',
    'const Q = /^[\'"]|[\'"]$/g;',
    'export function check(a, b) {',
    '  if (',
    '    a.replace(Q, "")',
    '  ) {',
    '    return true;',
    '  }',
    '  return Boolean(b);',
    '}',
  ].join('\n') + '\n');

  const gen = generateGuardMutations({
    root: dir,
    diffLinesByFile: { 'src/header_guard.mjs': [6, 7] },
    targetFiles: ['src/header_guard.mjs'],
  });
  assert.ok(gen.candidates.length >= 1, JSON.stringify(gen));
  assert.equal(gen.candidates[0].kind, 'guard-negate');
  assert.match(gen.candidates[0].mutatedContent, /if \(\!\(\s*\n\s*a\.replace\(Q, ""\)\s*\n\s*\)\) \{/);

  // Fatal non-interrupt child signal (SIGKILL) MUST classify as outcome: 'error' (Not proved), NEVER 'survived'!
  const repo = initGitRepo(t, 'pdd-mut-sigkill-');
  mkdirSync(join(repo, 'src'), { recursive: true });
  mkdirSync(join(repo, 'test'), { recursive: true });
  writeFileSync(join(repo, 'src', 'g.mjs'), 'export const f = x => x;\n');
  writeFileSync(join(repo, 'test', 'g.formal.test.mjs'), "import { f } from '../src/g.mjs'; console.log(f(1));\n");
  commitAll(repo, 'base');
  const baseSha = execFileSync('git', ['rev-parse', 'HEAD'], { cwd: repo, encoding: 'utf8' }).trim();
  writeFileSync(join(repo, 'src', 'g.mjs'), 'export function f(x) {\n  if (x < 0) return false;\n  return true;\n}\n');

  const sigkillRes = runProveMutationCheck(
    {
      root: repo,
      baseSha,
      touchedFiles: ['src/g.mjs'],
      formalResult: { applicable: true, ok: true, state: 'bounded', tier: 'bounded', errors: [], files: [{ file: 'test/g.formal.test.mjs', importedProductionModules: ['src/g.mjs'] }] },
      formalCoverageFiles: { 'src/g.mjs': { executedLines: [2] } },
    },
    { spawnSync: () => ({ status: null, signal: 'SIGKILL', stdout: '', stderr: '', error: null }) },
  );
  assert.equal(sigkillRes.status, 'not-proved');
  assert.equal(sigkillRes.survived, 0, 'SIGKILL MUST NEVER classify as survived');
  assert.equal(sigkillRes.errorsCount, 1);
  assert.equal(sigkillRes.mutations[0].outcome, 'error');
});
