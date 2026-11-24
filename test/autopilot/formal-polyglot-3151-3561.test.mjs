import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawn, spawnSync } from 'node:child_process';
import { appendFileSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { calculateAutopilotMetrics } from '../../src/metrics-model.mjs';
import { readAutopilotMetricsState } from '../../src/autopilot-metrics.mjs';
import { openPullRequest, runCompiledCodeTestCheck, shouldRunCompiledCodeTest } from '../../src/autopilot-core.mjs';
import { proseSha256 } from '../../src/runtime-seam.mjs';
import {
  collectLiveEvidenceContract,
  runPolyglotBaseControl,
  runRefactorEquivalenceCheck,
} from '../../src/autopilot/core/live-evidence.mjs';
import { evaluateEvidenceContract } from '../../src/autopilot/gates/evidence-contract.mjs';
import { coreWorld } from '../helpers/core-world.mjs';

const REPO_ROOT = fileURLToPath(new URL('../../', import.meta.url));
const PDD_BIN = join(REPO_ROOT, 'bin', 'pdd.mjs');
const HAS_PYTHON3 = spawnSync('python3', ['--version'], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }).status === 0;
const HAS_PYTEST = spawnSync('pytest', ['--version'], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }).status === 0;

function makePytestShimScript() {
  return [
    '#!/usr/bin/env python3',
    'import importlib.util, sys, traceback',
    'files = [a for a in sys.argv[1:] if not a.startswith("-")]',
    'passed = failed = 0',
    'for f in files:',
    '    spec = importlib.util.spec_from_file_location("m", f)',
    '    mod = importlib.util.module_from_spec(spec)',
    '    spec.loader.exec_module(mod)',
    '    for name in sorted(dir(mod)):',
    '        if not name.startswith("test_"): continue',
    '        fn = getattr(mod, name)',
    '        if not callable(fn): continue',
    '        try:',
    '            fn(); passed += 1; print(f"{f}::{name} PASSED")',
    '        except Exception:',
    '            failed += 1; print(f"{f}::{name} FAILED"); traceback.print_exc()',
    'parts = ([f"{failed} failed"] if failed else []) + ([f"{passed} passed"] if passed else [])',
    'summary = ", ".join(parts) or "no tests ran"',
    'print(f"=== {summary} in 0.01s ===")',
    'sys.exit(1 if failed else 0)',
  ].join('\n') + '\n';
}

const writeIn = (cwd, rel, text) => {
  mkdirSync(join(cwd, rel, '..'), { recursive: true });
  writeFileSync(join(cwd, rel), text);
};

function seed(w, files) {
  const dir = join(w.dir, `seed-${Math.random().toString(36).slice(2)}`);
  w.git(w.dir, 'clone', '-q', w.remote, dir);
  for (const [path, text] of Object.entries(files)) writeIn(dir, path, text);
  w.git(dir, 'add', '.');
  w.git(dir, 'commit', '-qm', 'base');
  w.git(dir, 'push', '-q', 'origin', 'HEAD:main');
}

const mergeNote = pr => pr.comments.map(c => c.body).find(body => body.includes('<!-- pdd:autopilot-core:merge:')) ?? '';

function execReplayCommand(job) {
  const command = job.args.at(-3);
  return new Promise(done => {
    const child = spawn('/bin/bash', ['-c', command], {
      cwd: job.cwd,
      detached: true,
      env: { PATH: process.env.PATH, HOME: process.env.HOME, CI: 'true', LANG: 'C' },
    });
    let out = '';
    child.stdout.on('data', chunk => { out += chunk; });
    child.stderr.on('data', chunk => { out += chunk; });
    const timer = setTimeout(() => { try { process.kill(-child.pid, 'SIGKILL'); } catch {} }, 60_000);
    child.on('close', status => { clearTimeout(timer); done({ status, out }); });
  });
}

// ---------------------------------------------------------------------------
// Part 0: Skill, job-rules, workRules(), and RESULT_RULES alignment
// ---------------------------------------------------------------------------
test('Part 0: formal.md, SKILL.md, job-rules.md, workRules(), and RESULT_RULES align on zero-install triggers and JSON formal field', async t => {
  const formalMd = readFileSync(join(REPO_ROOT, 'skills/pdd/references/formal.md'), 'utf8');
  const skillMd = readFileSync(join(REPO_ROOT, 'skills/pdd/SKILL.md'), 'utf8');
  const jobRulesMd = readFileSync(join(REPO_ROOT, 'src/autopilot/job-rules.md'), 'utf8');

  assert.match(formalMd, /zero-install/i);
  assert.match(formalMd, /mulberry32/i);
  assert.match(formalMd, /not-applicable/);
  assert.match(formalMd, /verify\.formal_command/);
  assert.ok(skillMd.trimEnd().split('\n').length <= 75, 'SKILL.md stays compact with zero bloat');
  assert.doesNotMatch(skillMd, /only for invariant-heavy work/i);
  assert.match(skillMd, /not-applicable/);

  // Blind Read-Only Reviewer section in job-rules.md explicitly covers formal verification and spec-model claims.
  const reviewerSection = jobRulesMd.slice(jobRulesMd.indexOf('## For the Blind Read-Only Reviewer'));
  assert.match(reviewerSection, /formal\/property coverage/i);
  assert.match(reviewerSection, /proved_solver_code/);

  // Autopilot core buildPrompt (`workRules` + `RESULT_RULES`) wires `"formal"` and zero-install rules.
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17, { title: 'Add discount rules', body: 'Enforce discount bounds.' });
  await w.tick();
  const buildInput = w.job(17, 'build').input;
  assert.match(buildInput, /"formal":\{"state":"proved_solver_code\|bounded\|proved_spec_model\|not-applicable"/);
  assert.match(buildInput, /zero-install deterministic seeded PRNG/i);
  assert.match(buildInput, /not-applicable/);
});

// ---------------------------------------------------------------------------
// Part 1: All 5 live formal state & metrics bugs (#3151)
// ---------------------------------------------------------------------------
test('Part 1 Bug 1 & Bug 5: POSITIVE.formal downgrades unchecked proved_solver_code to not-run, and 0-file proved_solver_code/proved fails closed', async t => {
  // Bug 5: Claiming formal=proved_solver_code or formal=proved with 0 formal files fails closed!
  for (const bogus of ['proved_solver_code', 'proved']) {
    const w = await coreWorld(t, { settings: { runs: 1 } });
    seed(w, { 'src/a.mjs': 'export const a = 1;\n' });
    w.issue(17, { title: 'Update a', body: 'Return 2.' });
    await w.tick();
    const cwd = w.job(17, 'build').cwd;
    writeIn(cwd, 'src/a.mjs', 'export const a = 2;\n');
    const line = `Evidence: runtime=not-run; vectors=not-run; formal=${bogus}; tests=pass (1/1)`;
    w.build(17, { body: `Fixes #17\n\nRuntime: not run (no prompt changed)\n${line}`, result: { promptChanged: false, evidence: line } });
    await w.tick();
    const repair = w.job(17, 'repair');
    assert.ok(repair, `0-file formal=${bogus} must trigger repair immediately`);
    assert.match(repair.input, new RegExp(`formal=${bogus}, but zero formal test files were changed or verified`));
    assert.deepEqual(w.github.merges, []);
  }

  // Bug 1: POSITIVE.formal includes proved_solver_code -> unchecked proved_solver_code downgrades to not-run!
  const w = await coreWorld(t, { settings: { runs: 1 } });
  const files = {
    'src/calc.mjs': 'export const add = (a, b) => a + b;\n',
    'test/calc.formal.test.mjs': "import test from 'node:test'; import { add } from '../src/calc.mjs'; test('f', () => { if (add(1, 1) !== 2) throw new Error('x'); });\n",
  };
  seed(w, files);
  w.issue(17);
  await w.tick();
  writeIn(w.job(17, 'build').cwd, 'test/calc.formal.test.mjs', `${files['test/calc.formal.test.mjs']}\n`);
  const evLine = 'Evidence: runtime=not-run; vectors=not-run; formal=proved_solver_code; tests=pass (1/1)';
  const { pr } = w.build(17, { body: `Fixes #17\n\nRuntime: not run (no prompt changed)\n${evLine}`, result: { promptChanged: false, evidence: evLine } });
  await w.tick();
  w.review(17, 'PASS');
  w.suite(17, 0);
  await w.tick();
  // Fail vectors runner 3 times -> triggers 1 repair, then after repair fails 3 times -> merges with formal=not-run (NEVER repeating proved_solver_code!).
  for (let i = 0; i < 3; i++) {
    const job = w.job(17, 'vectors');
    appendFileSync(job.log, 'runner crash\n');
    w.finish(17, 'vectors', { code: 1 });
    await w.tick();
  }
  assert.match(w.job(17, 'repair')?.input ?? '', /The Evidence line says formal=proved_solver_code, but Autopilot could not check it/);
  w.build(17, { role: 'repair', write: false });
  await w.tick();
  w.review(17, 'PASS');
  w.suite(17, 0);
  await w.tick();
  for (let i = 0; i < 3; i++) {
    const job = w.job(17, 'vectors');
    appendFileSync(job.log, 'runner crash\n');
    w.finish(17, 'vectors', { code: 1 });
    await w.tick();
  }
  await w.tick();
  assert.deepEqual(w.github.merges, [pr.number]);
  const note = mergeNote(pr);
  assert.match(note, /formal=not-run \(Autopilot could not check:/);
  assert.doesNotMatch(note, /formal=proved_solver_code/);
});

test('Part 1 Bug 2: metrics-model.mjs & autopilot-metrics.mjs count proved_solver_code as pass while never counting proved_spec_model as pass', t => {
  const report = calculateAutopilotMetrics({
    runs: [
      { repo: 'acme/app', issue: 1, startedAt: '2026-11-17T10:00:00Z', at: '2026-11-17T10:15:00Z', status: 'merged', pr: 11, gates: { formal: 'proved_solver_code', suite: 'pass', review: 'pass', ci: 'pass' }, promptChanged: true },
      { repo: 'acme/app', issue: 2, startedAt: '2026-11-17T11:00:00Z', at: '2026-11-17T11:15:00Z', status: 'merged', pr: 12, gates: { formal: 'proved_spec_model', suite: 'pass', review: 'pass', ci: 'pass' }, promptChanged: true },
      { repo: 'acme/app', issue: 3, startedAt: '2026-11-17T12:00:00Z', at: '2026-11-17T12:15:00Z', status: 'merged', pr: 13, gates: { formal: 'bounded', suite: 'pass', review: 'pass', ci: 'pass' }, promptChanged: true },
    ],
    repos: ['acme/app'],
    now: '2026-11-17T15:00:00Z',
    timezone: 'UTC',
    view: 'full',
  });
  // Issues #1 (proved_solver_code) and #3 (bounded) count as pass (2/2 applicable); #2 (proved_spec_model) stays na (NOT counted as pass!).
  assert.equal(report.stages.gates.formal.passed, 2);
  assert.equal(report.stages.gates.formal.applicable, 2);
  assert.equal(report.stages.promptChecks.formal.passed, 2);
  assert.equal(report.stages.promptChecks.formal.total, 2);

  // Verify readAutopilotMetricsState infers promptChanged=true for proved_solver_code and excludes proved_spec_model!
  const stateDir = mkdtempSync(join(tmpdir(), 'pdd-metrics-3151-'));
  t.after(() => rmSync(stateDir, { recursive: true, force: true }));
  const apDir = join(stateDir, 'autopilot');
  const coreDir = join(apDir, 'acme-core');
  mkdirSync(coreDir, { recursive: true });
  writeFileSync(join(apDir, 'acme.json'), JSON.stringify({ repo: 'acme/app', enabled: true }));
  const t1 = Date.parse('2026-11-17T10:00:00Z');
  const t2 = Date.parse('2026-11-17T11:00:00Z');
  writeFileSync(join(coreDir, 'history.jsonl'), [
    JSON.stringify({ issue: 10, pr: 101, outcome: 'merged', at: t1, evidence: { formal: { state: 'proved_solver_code', passed: 2, total: 2 } } }),
    JSON.stringify({ issue: 11, pr: 102, outcome: 'merged', at: t2, evidence: { formal: { state: 'proved_spec_model', passed: 1, total: 1 } } }),
  ].join('\n') + '\n');

  const st = readAutopilotMetricsState({ stateDir, now: () => Date.parse('2026-11-17T12:00:00Z') });
  const r10 = st.runs.find(r => r.issue === 10);
  const r11 = st.runs.find(r => r.issue === 11);
  assert.equal(r10.promptChanged, true, 'proved_solver_code counts in hasPromptCheck');
  assert.deepEqual(r10.gateCounts?.formal, { passed: 2, total: 2 });
  assert.equal(r11.promptChanged, undefined, 'proved_spec_model never counts as code-proved prompt check');
  assert.equal(r11.gateCounts?.formal, undefined, 'proved_spec_model never records passing formal gateCounts');
});

test('Part 1 Bug 3 & Bug 4: openPullRequest preserves proved_solver_code & proved_spec_model without stomping; syncStampedReplayEvidence & engineEvidenceReds respect honest proved_spec_model', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  seed(w, {
    'src/calc.mjs': 'export const add = (a, b) => a + b;\n',
    'test/calc.formal.test.mjs': "import test from 'node:test'; import assert from 'node:assert/strict'; import { add } from '../src/calc.mjs'; test('f', () => assert.equal(add(1, 2), 3));\n",
  });
  w.issue(17);
  await w.tick();
  const build = w.job(17, 'build');
  writeIn(build.cwd, 'src/calc.mjs', 'export const add = (a, b) => Number(a) + Number(b);\n');
  w.git(build.cwd, 'add', '.');
  w.git(build.cwd, 'commit', '-qm', 'update calc');
  const head = w.git(build.cwd, 'rev-parse', 'HEAD').trim();
  w.git(build.cwd, 'push', '-q', 'origin', `HEAD:${build.branch}`);

  const { root: _drop, ...portsWithoutRoot } = w.ports();
  // Bug 3a: openPullRequest with passing vecDone.formal having tier='proved_solver_code' MUST preserve proved_solver_code!
  const solverStamp = await openPullRequest(
    { state: w.state, settings: w.settings, budget: { state: 'normal', used: 0, allowed: 1000 } },
    { issue: 17, branch: build.branch, head, worktree: build.cwd, vectors: { head, state: 'done', result: { formal: { state: 'pass', tier: 'proved_solver_code', tests: 2, pass: 2 } } } },
    { head, title: 'Solver proof', summary: 'Code-bound solver.', tests: { state: 'pass', passed: 1, total: 1 }, formal: { state: 'proved_solver_code' }, runtime: { state: 'not-run', cause: 'none' }, ports: portsWithoutRoot },
  );
  assert.match(solverStamp.body, /formal=proved_solver_code\b/, 'openPullRequest must NOT stomp proved_solver_code to bounded');

  // Bug 3b: openPullRequest with passing vecDone.formal having tier='proved_spec_model' MUST stamp proved_spec_model (NEVER upgrade to bounded)!
  const specStamp = await openPullRequest(
    { state: w.state, settings: w.settings, budget: { state: 'normal', used: 0, allowed: 1000 } },
    { issue: 17, branch: build.branch, head, worktree: build.cwd, pr: solverStamp.pr, vectors: { head, state: 'done', result: { formal: { state: 'pass', tier: 'proved_spec_model', tests: 1, pass: 1 } } } },
    { pr: solverStamp.pr, head, title: 'Spec model', summary: 'Disconnected spec.', tests: { state: 'pass', passed: 1, total: 1 }, formal: { state: 'bounded' }, runtime: { state: 'not-run', cause: 'none' }, ports: portsWithoutRoot },
  );
  assert.match(specStamp.body, /formal=proved_spec_model\b/, 'openPullRequest must NOT upgrade disconnected proved_spec_model to bounded');

  // Bug 4: Live replay with honest `formal=proved_spec_model` is respected (no RED telling agent to lie, no overwrite to bounded)!
  const w2 = await coreWorld(t, { settings: { runs: 1 } });
  const specFiles = {
    'test/spec.formal.test.mjs': "import test from 'node:test'; import assert from 'node:assert/strict'; test('standalone math', () => assert.ok(2 + 2 === 4));\n",
  };
  seed(w2, specFiles);
  w2.issue(17);
  await w2.tick();
  writeIn(w2.job(17, 'build').cwd, 'test/spec.formal.test.mjs', `${specFiles['test/spec.formal.test.mjs']}\n`);
  const specEv = 'Evidence: runtime=not-run; vectors=not-run; formal=proved_spec_model; tests=pass (1/1)';
  const { pr: pr2 } = w2.build(17, { body: `Fixes #17\n\nRuntime: not run (no prompt changed)\n${specEv}`, result: { promptChanged: false, evidence: specEv, formal: { state: 'proved_spec_model' } } });
  await w2.tick();
  w2.review(17, 'PASS');
  w2.suite(17, 0);
  await w2.tick();
  const vecJob = w2.job(17, 'vectors');
  const run = await execReplayCommand(vecJob);
  appendFileSync(vecJob.log, run.out);
  w2.finish(17, 'vectors', { code: run.status });
  await w2.tick();
  await w2.tick();
  assert.equal(w2.job(17, 'repair'), undefined, w2.job(17, 'repair')?.input);
  assert.deepEqual(w2.github.merges, [pr2.number]);
  assert.match(pr2.body, /formal=proved_spec_model\b/, 'syncStampedReplayEvidence must NEVER rewrite honest proved_spec_model to bounded');
});

// ---------------------------------------------------------------------------
// Part 2: Polyglot pytest (--junitxml + .venv + PYTHONPATH=src), vitest (--reporter=junit), replayPlan
// ---------------------------------------------------------------------------
test('Part 2: runPolyglotBaseControl passes vitest --reporter=junit and pytest -v --junitxml with PYTHONPATH=src and symlink-safe .venv resolution', async t => {
  // 1. Vitest: passes --reporter=junit --outputFile=<tmp> and parses real JUnit XML!
  const vDir = mkdtempSync(join(tmpdir(), 'pdd-vitest-junit-'));
  t.after(() => rmSync(vDir, { recursive: true, force: true }));
  writeFileSync(join(vDir, 'package.json'), JSON.stringify({ devDependencies: { vitest: '^2.0.0' } }));
  const vRes = await runPolyglotBaseControl({
    baseDir: vDir,
    changedFiles: ['src/app.ts', 'src/app.test.ts'],
    changedProdFiles: ['src/app.ts'],
    execFn: async (bin, args, opts) => {
      assert.equal(bin, 'npx');
      assert.equal(args[0], '--no-install');
      assert.equal(args[1], 'vitest');
      assert.equal(args[2], 'run');
      assert.equal(args[3], '--reporter=junit');
      assert.equal(opts.env.GH_TOKEN, undefined, 'runPolyglotBaseControl must scrub GH_TOKEN from child env');
      assert.equal(opts.env.OPENAI_API_KEY, undefined, 'runPolyglotBaseControl must scrub OPENAI_API_KEY from child env');
      const outArg = args.find(a => a.startsWith('--outputFile='));
      assert.ok(outArg, 'vitest must pass --outputFile=<tmp>');
      const outFile = outArg.slice('--outputFile='.length);
      writeFileSync(outFile, '<testsuites><testsuite name="app"><testcase classname="app" name="fails on base"><failure message="boom"/></testcase></testsuite></testsuites>');
      return { exitCode: 1, stdout: '', stderr: '', killed: false, code: null };
    },
    env: { ...process.env, GH_TOKEN: 'ghp_secret_leak_test', OPENAI_API_KEY: 'sk-secret-leak-test' },
  });
  assert.equal(vRes.state, 'ran-and-failed-on-base');
  assert.equal(vRes.runnerKind, 'vitest');
  assert.equal(vRes.report?.format, 'junit');
  assert.equal(vRes.cases.length, 1);
  assert.equal(vRes.cases[0].status, 'fail');

  // 2. Pytest: prefers non-symlink .venv/bin/pytest, refuses symlinked .venv, sets PYTHONPATH=src!
  const pyDir = mkdtempSync(join(tmpdir(), 'pdd-py-venv-'));
  t.after(() => rmSync(pyDir, { recursive: true, force: true }));
  mkdirSync(join(pyDir, 'src'), { recursive: true });
  mkdirSync(join(pyDir, '.venv', 'bin'), { recursive: true });
  writeFileSync(join(pyDir, 'pyproject.toml'), '[tool.pytest.ini_options]\n');
  writeFileSync(join(pyDir, '.venv', 'bin', 'pytest'), '#!/bin/sh\nexit 0\n', { mode: 0o755 });
  let seenBin = null, seenEnv = null;
  const pyRes = await runPolyglotBaseControl({
    baseDir: pyDir,
    changedFiles: ['src/mod.py', 'tests/test_mod.py'],
    changedProdFiles: ['src/mod.py'],
    execFn: async (bin, args, opts) => {
      seenBin = bin;
      seenEnv = opts.env;
      const xmlArg = args.find(a => a.startsWith('--junitxml='));
      assert.ok(xmlArg);
      writeFileSync(xmlArg.slice('--junitxml='.length), '<testsuite tests="1" failures="1"><testcase classname="test_mod" name="test_bug"><failure/></testcase></testsuite>');
      return { exitCode: 1, stdout: 'tests/test_mod.py::test_bug FAILED\n1 failed in 0.02s\n', stderr: '', killed: false, code: null };
    },
  });
  assert.equal(seenBin, join(pyDir, '.venv', 'bin', 'pytest'));
  assert.match(seenEnv.PYTHONPATH ?? '', /^src(?:[:;]|$)/);
  assert.equal(pyRes.state, 'ran-and-failed-on-base');
  assert.equal(pyRes.report?.format, 'junit');

  // Symlinked .venv must be refused (falls back to 'pytest').
  const symPyDir = mkdtempSync(join(tmpdir(), 'pdd-py-symvenv-'));
  t.after(() => rmSync(symPyDir, { recursive: true, force: true }));
  writeFileSync(join(symPyDir, 'pyproject.toml'), '[tool.pytest.ini_options]\n');
  symlinkSync(join(pyDir, '.venv'), join(symPyDir, '.venv'));
  let symSeenBin = null;
  await runPolyglotBaseControl({
    baseDir: symPyDir,
    changedFiles: ['src/mod.py', 'tests/test_mod.py'],
    changedProdFiles: ['src/mod.py'],
    execFn: async bin => { symSeenBin = bin; return { exitCode: 1, stdout: '1 failed in 0.01s\n', stderr: '', killed: false, code: null }; },
  });
  assert.equal(symSeenBin, 'pytest', 'symlinked .venv MUST be refused');
});

test('Part 2 (Live Python pytest in vectorsState): replayPlan executes real Python formal test via pytest without rejecting as non-JS', { skip: !HAS_PYTHON3 }, async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  const pyShimDir = HAS_PYTEST ? null : mkdtempSync(join(tmpdir(), 'pdd-py-shim-'));
  if (pyShimDir) {
    t.after(() => rmSync(pyShimDir, { recursive: true, force: true }));
    writeFileSync(join(pyShimDir, 'pytest'), makePytestShimScript(), { mode: 0o755 });
  }
  seed(w, {
    'pyproject.toml': '[tool.pytest.ini_options]\ntestpaths = ["tests"]\n',
    'src/math_py.py': 'def add(a, b):\n    return a + b\n',
    'tests/test_formal_math.py': 'from math_py import add\n\ndef test_comm():\n    for i in range(20):\n        assert add(i, 3) == add(3, i)\n',
  });
  const pyTickEnv = pyShimDir ? { ...process.env, PATH: `${pyShimDir}:${process.env.PATH}` } : process.env;
  w.issue(17, { title: 'Add formal invariant for math_py', body: 'Extend test_formal_math.py.' });
  await w.tick({ env: pyTickEnv });
  writeIn(w.job(17, 'build').cwd, 'tests/test_formal_math.py', 'from math_py import add\n\ndef test_comm():\n    for i in range(40):\n        assert add(i, 3) == add(3, i)\n');
  const ev = 'Evidence: runtime=not-run; vectors=not-run; formal=bounded; tests=pass (1/1)';
  const { pr } = w.build(17, { body: `Fixes #17\n\nRuntime: not run (no prompt changed)\n${ev}`, result: { promptChanged: false, evidence: ev } });
  await w.tick({ env: pyTickEnv });
  w.review(17, 'PASS');
  w.suite(17, 0);
  await w.tick({ env: pyTickEnv });

  const vecJob = w.job(17, 'vectors');
  assert.ok(vecJob, 'vectorsState launched polyglot pytest replay job');
  assert.match(vecJob.args.at(-3), /pytest.*-v.*test_formal_math\.py/);
  const run = await new Promise(done => {
    const child = spawn('/bin/bash', ['-c', vecJob.args.at(-3)], {
      cwd: vecJob.cwd,
      detached: true,
      env: { PATH: pyShimDir ? `${pyShimDir}:${process.env.PATH}` : process.env.PATH, HOME: process.env.HOME, CI: 'true', LANG: 'C' },
    });
    let out = '';
    child.stdout.on('data', chunk => { out += chunk; });
    child.stderr.on('data', chunk => { out += chunk; });
    const timer = setTimeout(() => { try { process.kill(-child.pid, 'SIGKILL'); } catch {} }, 60_000);
    child.on('close', status => { clearTimeout(timer); done({ status, out }); });
  });
  appendFileSync(vecJob.log, run.out);
  w.finish(17, 'vectors', { code: run.status });
  await w.tick({ env: pyTickEnv });
  await w.tick({ env: pyTickEnv });
  assert.equal(w.job(17, 'repair'), undefined, w.job(17, 'repair')?.input);
  assert.deepEqual(w.github.merges, [pr.number]);
  assert.match(mergeNote(pr), /Formal tests \(Autopilot's run at [0-9a-f]{7}\): pass \(1\/1\)/);
});

// ---------------------------------------------------------------------------
// Part 4 Test D: Pure Path `b` refactor equivalence (real baseTree vs headTree)
// ---------------------------------------------------------------------------
test('Test D: Path b pure-refactor equivalence verifies untouched base tests on base & head and HOLDS on behavioral regression', async t => {
  const baseDir = mkdtempSync(join(tmpdir(), 'pdd-ref-base-'));
  const headGoodDir = mkdtempSync(join(tmpdir(), 'pdd-ref-head-good-'));
  const headBadDir = mkdtempSync(join(tmpdir(), 'pdd-ref-head-bad-'));
  t.after(() => {
    rmSync(baseDir, { recursive: true, force: true });
    rmSync(headGoodDir, { recursive: true, force: true });
    rmSync(headBadDir, { recursive: true, force: true });
  });

  const pkg = JSON.stringify({ name: 'ref-demo', type: 'module', scripts: { test: 'node --test' } }) + '\n';
  const untouchedTest = [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { totalCents } from '../src/pricing.mjs';",
    "test('totalCents sums positive prices', () => {",
    '  assert.equal(totalCents([100, 250, 50]), 400);',
    '  assert.equal(totalCents([]), 0);',
    '});',
  ].join('\n') + '\n';

  for (const dir of [baseDir, headGoodDir, headBadDir]) {
    writeIn(dir, 'package.json', pkg);
    writeIn(dir, 'test/pricing.test.mjs', untouchedTest);
  }
  writeIn(baseDir, 'src/pricing.mjs', 'export function totalCents(items) { let s = 0; for (const x of items) s += x; return s; }\n');
  // Equivalent structural refactor (reduce instead of loop).
  writeIn(headGoodDir, 'src/pricing.mjs', 'export const totalCents = items => items.reduce((acc, x) => acc + x, 0);\n');
  // Subtle behavioral regression (+1 off-by-one).
  writeIn(headBadDir, 'src/pricing.mjs', 'export const totalCents = items => items.reduce((acc, x) => acc + x, 1);\n');

  const okEquiv = await runRefactorEquivalenceCheck({
    baseTree: baseDir,
    headTree: headGoodDir,
    changedFiles: ['src/pricing.mjs'],
  });
  assert.equal(okEquiv.applicable, true);
  assert.equal(okEquiv.status, 'pass');
  assert.equal(okEquiv.verdict, 'ALLOW');
  assert.deepEqual(okEquiv.untouchedTests, ['test/pricing.test.mjs']);

  const badEquiv = await runRefactorEquivalenceCheck({
    baseTree: baseDir,
    headTree: headBadDir,
    changedFiles: ['src/pricing.mjs'],
  });
  assert.equal(badEquiv.applicable, true);
  assert.equal(badEquiv.status, 'fail');
  assert.equal(badEquiv.verdict, 'HOLD');
  assert.ok(badEquiv.reportDiff?.newlyFailingIds.length > 0);

  // Also verify collectLiveEvidenceContract + evaluateEvidenceContract HOLDS when isPathBPureRefactor hits regression!
  const liveHold = await collectLiveEvidenceContract({
    repo: 'acme/pricing',
    job: { head: 'a'.repeat(40), issue: 5, title: 'Refactor pricing', body: 'Pure refactor.' },
    headTree: headBadDir,
    baseTree: baseDir,
    changedFiles: ['src/pricing.mjs'],
    isPathBPureRefactor: true,
  });
  assert.equal(liveHold.refactorEquivalence.verdict, 'HOLD');
  const contractHold = evaluateEvidenceContract({
    ...liveHold.contractInput,
    requireFrozenAcs: false,
    requireBaseOracle: false,
    requireGapCheck: false,
  });
  assert.equal(contractHold.decision, 'HOLD');
});

// ---------------------------------------------------------------------------
// Part 4: Auto `pdd test --target code` CLI subprocess hook (0 AI calls)
// ---------------------------------------------------------------------------
test('Part 4: auto pdd test --target code detects CLI-implemented prompt and executes real CLI subprocess (pass & fail, 0 AI calls)', async t => {
  const repo = mkdtempSync(join(tmpdir(), 'pdd-target-code-auto-'));
  t.after(() => rmSync(repo, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q', '-b', 'main'], { cwd: repo });
  execFileSync('git', ['config', 'user.name', 'Test'], { cwd: repo });
  execFileSync('git', ['config', 'user.email', 'test@example.com'], { cwd: repo });

  const iface = {
    status: 'approved',
    prose_sha256: '',
    entries: [{
      operation: 'greet',
      implementation: { kind: 'cli', command: `${process.execPath} bin/greet.mjs` },
      input_schema: {
        type: 'object',
        additionalProperties: false,
        required: ['argv'],
        properties: { argv: { type: 'array', items: { type: 'string' } } },
      },
      result_schema: {
        type: 'object',
        additionalProperties: false,
        required: ['exit_code', 'stdout', 'stderr'],
        properties: {
          exit_code: { type: 'integer' },
          stdout: { type: 'string' },
          stderr: { type: 'string' },
        },
      },
      errors: [],
    }],
    calls: [],
    resources: [],
    limits: { max_steps: 2, max_model_calls: 2 },
    conventions: [
      { path: '/entries/0/input_schema', convention: 'cli' },
      { path: '/entries/0/result_schema', convention: 'cli' },
    ],
  };
  const renderPrompt = () => `# Greet CLI\n\nOwn \`bin/greet.mjs\`: print \`hello <name>\\n\` and exit 0.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(iface)}\n\`\`\`\n</details>\n`;
  iface.prose_sha256 = proseSha256(renderPrompt());
  writeIn(repo, 'prompts/greet.prompt.md', renderPrompt());
  writeIn(repo, 'bin/greet.mjs', '// Prompt: prompts/greet.prompt.md\n\nprocess.stdout.write(`hello ${process.argv[2] ?? "world"}\\n`);\n');
  writeIn(repo, 'user_stories/greet.md', '# Greet CLI\n\n## Acceptance criteria\n\n1. Greets the named user.\n');
  writeIn(repo, 'tests/greet.json', JSON.stringify({
    entry_path: 'prompts/greet.prompt.md',
    steps: [{
      id: 's1',
      op: 'greet',
      input: { argv: ['Ada'] },
      checks: {
        1: [
          ['result', '/exit_code', '=', 0],
          ['result', '/stdout', '=', 'hello Ada\n'],
        ],
      },
    }],
  }, null, 2) + '\n');
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['commit', '-qm', 'cli prompt + impl'], { cwd: repo });

  assert.equal(shouldRunCompiledCodeTest({ root: repo, changedFiles: ['bin/greet.mjs'] }), true);
  assert.equal(shouldRunCompiledCodeTest({ root: repo, changedFiles: ['README.md'] }), false);

  const passRes = await runCompiledCodeTestCheck(
    { pdd: PDD_BIN },
    { issue: 1 },
    { headTree: repo, changedFiles: ['bin/greet.mjs'] },
  );
  assert.equal(passRes.applicable, true);
  assert.equal(passRes.state, 'pass', JSON.stringify(passRes));
  assert.equal(passRes.exitCode, 0);
  assert.equal(existsSync(join(repo, '.pdd/code-test/latest.json')), true);

  // Now break bin/greet.mjs -> auto --target code catches the failure with 0 AI calls!
  writeIn(repo, 'bin/greet.mjs', '// Prompt: prompts/greet.prompt.md\n\nprocess.stdout.write("wrong\\n");\n');
  const failRes = await runCompiledCodeTestCheck(
    { pdd: PDD_BIN },
    { issue: 1 },
    { headTree: repo, changedFiles: ['bin/greet.mjs'] },
  );
  assert.equal(failRes.applicable, true);
  assert.equal(failRes.state, 'fail', JSON.stringify(failRes));
  assert.ok(failRes.failedStories.some(s => s.includes('user_stories/greet.md')));
});

// ---------------------------------------------------------------------------
// Adversarial Autopilot Regressions (P0-2, P0-6, P0-7, P0-8, P1-3)
// ---------------------------------------------------------------------------
test('Adversarial P0-2/P0-6/P0-7/P0-8/P1-3: scrubs secrets, blocks syncStampedReplayEvidence laundering, fails closed on base crash & code-test error, and keeps proved_spec_model out of gateCounts', async t => {
  // P0-2 & P0-7: runRefactorEquivalenceCheck scrubs secrets AND fails closed when base crashes or report fails to parse!
  const baseDir = mkdtempSync(join(tmpdir(), 'pdd-ref-p07-base-'));
  const headDir = mkdtempSync(join(tmpdir(), 'pdd-ref-p07-head-'));
  t.after(() => { rmSync(baseDir, { recursive: true, force: true }); rmSync(headDir, { recursive: true, force: true }); });
  writeIn(baseDir, 'package.json', JSON.stringify({ name: 'x', type: 'module', scripts: { test: 'node --test' } }));
  writeIn(headDir, 'package.json', JSON.stringify({ name: 'x', type: 'module', scripts: { test: 'node --test' } }));
  writeIn(baseDir, 'test/a.test.mjs', "import test from 'node:test'; test('a', () => {});\n");
  writeIn(headDir, 'test/a.test.mjs', "import test from 'node:test'; test('a', () => {});\n");
  let callNum = 0;
  const baseCrashRes = await runRefactorEquivalenceCheck({
    baseTree: baseDir,
    headTree: headDir,
    changedFiles: ['src/a.mjs'],
    env: { ...process.env, GH_TOKEN: 'ghp_secret_leak_test', AWS_SECRET_ACCESS_KEY: 'aws_secret_leak_test' },
    execFn: async (_bin, _args, opts) => {
      assert.equal(opts.env.GH_TOKEN, undefined, 'runRefactorEquivalenceCheck must scrub GH_TOKEN');
      assert.equal(opts.env.AWS_SECRET_ACCESS_KEY, undefined, 'runRefactorEquivalenceCheck must scrub AWS_SECRET_ACCESS_KEY');
      callNum += 1;
      if (callNum === 1) return { exitCode: 1, stdout: '', stderr: 'Error [ERR_MODULE_NOT_FOUND]: missing dep', killed: false, code: null };
      return { exitCode: 0, stdout: 'TAP version 13\nok 1 - a\n1..1\n# tests 1\n# pass 1\n# fail 0\n', stderr: '', killed: false, code: null };
    },
  });
  assert.equal(baseCrashRes.verdict, 'HOLD', 'base crash in runRefactorEquivalenceCheck MUST fail closed (HOLD), never ALLOW');
  assert.match(baseCrashRes.reason, /refactor_base_failed/);

  // P0-6: Stamped PR in a repo with production code that adds a disconnected spec model and claims `formal=proved_solver_code`
  // MUST NOT be laundered into `proved_spec_model` and auto-merged by syncStampedReplayEvidence!
  const w = await coreWorld(t, { settings: { runs: 1 } });
  seed(w, {
    'src/calc.mjs': 'export const add = (a, b) => a + b;\n',
    'test/fake.formal.test.mjs': "import test from 'node:test'; import assert from 'node:assert/strict'; test('tautology', () => assert.equal(1 + 1, 2));\n",
  });
  w.issue(17);
  await w.tick();
  const build = w.job(17, 'build');
  writeIn(build.cwd, 'test/fake.formal.test.mjs', "import test from 'node:test'; import assert from 'node:assert/strict'; test('tautology2', () => assert.equal(2 + 2, 4));\n");
  // Omit PR number so Autopilot stamps the PR (setting job.stampedHead = head)!
  w.build(17, {
    openPr: false,
    result: {
      title: 'Claim solver code on fake spec',
      summary: 'Adds fake formal test.',
      promptChanged: false,
      tests: { state: 'pass', passed: 1, total: 1 },
      formal: { state: 'proved_solver_code' },
      runtime: { state: 'not-run', cause: 'no prompt changed' },
    },
  });
  await w.tick();
  w.review(17, 'PASS');
  w.suite(17, 0);
  await w.tick();
  const vecJob = w.job(17, 'vectors');
  assert.ok(vecJob, 'vectors job launched');
  const vecOut = await execReplayCommand(vecJob);
  appendFileSync(vecJob.log, vecOut.out);
  w.finish(17, 'vectors', { code: vecOut.status });
  await w.tick();
  assert.deepEqual(w.github.merges, [], 'false proved_solver_code claim on disconnected spec model MUST NOT auto-merge');
  assert.match(w.job(17, 'repair')?.input ?? '', /do not import production code|proved_spec_model/, 'must send repair RED instead of laundering claim');

  // P1-3: `proved_spec_model` in history + evDoc.vectors.kinds.formal MUST NEVER leak into gateCounts.formal or pass!
  const mState = mkdtempSync(join(tmpdir(), 'pdd-metrics-p13-'));
  t.after(() => rmSync(mState, { recursive: true, force: true }));
  const mCore = join(mState, 'autopilot', 'acme-core');
  mkdirSync(join(mCore, 'logs'), { recursive: true });
  writeFileSync(join(mState, 'autopilot', 'acme.json'), JSON.stringify({ repo: 'acme/app', enabled: true }));
  const headSha = 'a'.repeat(40);
  writeFileSync(join(mCore, 'logs', `22-evidence-${headSha}.json`), JSON.stringify({
    issue: 22, head: headSha,
    evidence: { formal: { state: 'proved_spec_model' } },
    vectors: { kinds: { formal: { state: 'pass', tier: 'proved_spec_model', codeBound: false, pass: 3, tests: 3 } } },
  }));
  writeFileSync(join(mCore, 'history.jsonl'), JSON.stringify({
    issue: 22, pr: 220, head: headSha, outcome: 'merged', at: Date.parse('2026-11-17T10:00:00Z'),
    evidence: { formal: { state: 'proved_spec_model' } },
  }) + '\n');
  const parsed = readAutopilotMetricsState({ stateDir: mState, now: () => Date.parse('2026-11-17T12:00:00Z') });
  const r22 = parsed.runs.find(r => r.issue === 22);
  assert.equal(r22.gates.formal, 'proved_spec_model');
  assert.equal(r22.gateCounts?.formal, undefined, 'evDoc.vectors.kinds.formal must NEVER leak counts into gateCounts.formal for proved_spec_model');
});
