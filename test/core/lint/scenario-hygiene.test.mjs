import '../../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  DEFAULT_SCENARIO_MAX_STEPS,
  DEFAULT_SCENARIO_MAX_WORLD_BYTES,
  computeDefaultScenarioCallCap,
  evaluateScenarioHygiene,
} from '../../../src/core/lint/scenario-hygiene.mjs';
import { lintRepoProject, runLocalLint } from '../../../src/repo-hygiene-lint.mjs';

const BIN_PDD = fileURLToPath(new URL('../../../bin/pdd.mjs', import.meta.url));
const SCENARIO_PATH = fileURLToPath(new URL('../../runtime/scenario-size-hygiene.json', import.meta.url));

function makeSteps(count, extraChecks = []) {
  return Array.from({ length: count }, (_, idx) => ({
    id: `s${idx + 1}`,
    op: 'step',
    input: { n: idx + 1 },
    checks: { '1': [['result', '/ok', '=', true], ...extraChecks] },
  }));
}

function initTempRepo(t, { steps = 15, initialWorld = { balance: 100 }, seeds = undefined, pddConfig = null } = {}) {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-scenario-hygiene-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));
  const repo = join(scratch, 'repo');
  mkdirSync(join(repo, 'prompts'), { recursive: true });
  mkdirSync(join(repo, 'user_stories'), { recursive: true });
  mkdirSync(join(repo, 'tests'), { recursive: true });

  execFileSync('git', ['init', '-q', '-b', 'main'], { cwd: repo });
  execFileSync('git', ['config', 'user.name', 'Test'], { cwd: repo });
  execFileSync('git', ['config', 'user.email', 'test@example.com'], { cwd: repo });

  writeFileSync(
    join(repo, 'prompts', 'ledger.prompt.md'),
    '# Ledger\n\nApply one `step({ n })` transition and return `{ ok: true }`.\n\n## Dependencies\n\nNone.\n',
  );
  writeFileSync(
    join(repo, 'user_stories', 'ledger.md'),
    '# Run ledger step\n\nAs a ledger operator, I want each step to return ok, so that balances stay consistent.\n\n## Acceptance criteria\n\n1. Calling step returns ok true.\n',
  );
  const scenarioDoc = {
    entry_path: 'prompts/ledger.prompt.md',
    initial_world: initialWorld,
    ...(seeds !== undefined ? { seeds } : {}),
    steps: makeSteps(steps),
  };
  writeFileSync(join(repo, 'tests', 'ledger.json'), `${JSON.stringify(scenarioDoc, null, 2)}\n`);
  if (pddConfig !== null) {
    writeFileSync(join(repo, 'pdd.json'), `${JSON.stringify(pddConfig, null, 2)}\n`);
  }
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['commit', '-q', '-m', 'init'], { cwd: repo });
  return { repo, home: join(scratch, 'home') };
}

function runCli(args, cwd, home) {
  mkdirSync(home, { recursive: true });
  return spawnSync(process.execPath, [BIN_PDD, ...args], {
    cwd,
    encoding: 'utf8',
    env: { ...process.env, HOME: home, PDD_STATE_DIR: join(home, 'state') },
    timeout: 20_000,
  });
}

test('vector replay: test/runtime/scenario-size-hygiene.json matches real evaluateScenarioHygiene 1-to-1', () => {
  const scenario = JSON.parse(readFileSync(SCENARIO_PATH, 'utf8'));
  assert.equal(scenario.steps.length, 4);

  for (const step of scenario.steps) {
    const res = evaluateScenarioHygiene(step.input.doc, step.input.options);
    if (step.id === 'oversized-16-steps') {
      assert.equal(res.oversized, true);
      assert.equal(res.metrics.steps, 16);
      assert.equal(res.finding.code, 'scenario-oversized');
      assert.equal(res.finding.defaultSeverity, 'warn');
      assert.match(res.finding.detail, /16 scenario steps \(limit: 15\)/);
      assert.match(res.finding.fix, /tests\/ledger\.<focus>\.json/);
    } else if (step.id === 'healthy-15-steps') {
      assert.equal(res.oversized, false);
      assert.equal(res.metrics.steps, 15);
      assert.equal(res.finding, null);
    } else if (step.id === 'oversized-state-bytes') {
      assert.equal(res.oversized, true);
      assert.ok(res.metrics.state_bytes > 32);
      assert.equal(res.finding.code, 'scenario-oversized');
      assert.equal(res.finding.defaultSeverity, 'warn');
      assert.match(res.finding.detail, /limit: 32/);
    } else if (step.id === 'custom-max-steps-10') {
      assert.equal(res.oversized, true);
      assert.equal(res.metrics.steps, 12);
      assert.equal(res.finding.code, 'scenario-oversized');
      assert.equal(res.finding.defaultSeverity, 'warn');
      assert.match(res.finding.detail, /12 scenario steps \(limit: 10\)/);
    }
  }
});

test('AC1 & AC2: pdd lint warns non-blocking on 16-step scenario and stays silent on 15-step scenario', t => {
  const over = initTempRepo(t, { steps: 16 });
  const rOver = runCli(['lint'], over.repo, over.home);
  assert.equal(rOver.status, 0, `expected non-blocking exit 0, got ${rOver.status}: ${rOver.stderr}`);
  assert.equal(rOver.stderr, '');
  assert.match(rOver.stdout, /\[scenario-oversized\]/);
  assert.match(rOver.stdout, /16 scenario steps \(limit: 15\)/);
  assert.match(rOver.stdout, /tests\/ledger\.<focus>\.json/);

  const rOverLocal = runCli(['lint', '--local'], over.repo, over.home);
  assert.equal(rOverLocal.status, 0, `expected non-blocking --local exit 0, got ${rOverLocal.status}: ${rOverLocal.stderr}`);
  assert.match(rOverLocal.stdout + rOverLocal.stderr, /\[scenario-oversized\]/);

  const healthy = initTempRepo(t, { steps: 15, initialWorld: { balance: 100, note: 'small' } });
  const rHealthy = runCli(['lint'], healthy.repo, healthy.home);
  assert.equal(rHealthy.status, 0, rHealthy.stderr);
  assert.doesNotMatch(rHealthy.stdout + rHealthy.stderr, /scenario-oversized/);
  assert.match(rHealthy.stdout, /Local lint: 0 errors, 0 warnings\./);
});

test('AC3: pdd lint warns non-blocking when serialized initial_world + seeds exceed 16,384 bytes', t => {
  const bigRepo = initTempRepo(t, {
    steps: 8,
    initialWorld: { ledger_blob: 'a'.repeat(12000) },
    seeds: { base_seed: { extra: 'b'.repeat(8000) } },
  });
  const res = runCli(['lint', '--json'], bigRepo.repo, bigRepo.home);
  assert.equal(res.status, 0, res.stderr);
  const payload = JSON.parse(res.stdout);
  assert.equal(payload.ok, true);
  const finding = payload.findings.find(f => f.code === 'scenario-oversized');
  assert.ok(finding, 'expected scenario-oversized finding');
  assert.equal(finding.severity, 'warn');
  assert.match(finding.message, /serialized state bytes \(limit: 16384\)/);
});

test('AC4 & AC5: pdd.json configures lint.scenario limits, off suppression, error elevation, and invalid config refusal', t => {
  // Custom max_steps: 10 catches a 12-step scenario
  const strict = initTempRepo(t, {
    steps: 12,
    pddConfig: { lint: { scenario: { max_steps: 10 } } },
  });
  const rStrict = runCli(['lint'], strict.repo, strict.home);
  assert.equal(rStrict.status, 0);
  assert.match(rStrict.stdout, /12 scenario steps \(limit: 10\)/);

  // Disabling rule suppresses warning
  const off = initTempRepo(t, {
    steps: 12,
    pddConfig: { lint: { scenario: { max_steps: 10 }, rules: { 'scenario-oversized': 'off' } } },
  });
  const rOff = runCli(['lint'], off.repo, off.home);
  assert.equal(rOff.status, 0);
  assert.doesNotMatch(rOff.stdout + rOff.stderr, /scenario-oversized/);

  // Elevating rule to "error" fails with exit 1
  const errRepo = initTempRepo(t, {
    steps: 16,
    pddConfig: { lint: { rules: { 'scenario-oversized': 'error' } } },
  });
  const rErr = runCli(['lint'], errRepo.repo, errRepo.home);
  assert.equal(rErr.status, 1);
  assert.match(rErr.stderr, /Error: scenario hygiene: tests\/ledger\.json:1 \[scenario-oversized\]/);

  // Invalid numeric limit fails config validation with lint-config-invalid
  const bad = initTempRepo(t, {
    steps: 4,
    pddConfig: { lint: { scenario: { max_steps: 0 } } },
  });
  const rBad = runCli(['lint'], bad.repo, bad.home);
  assert.equal(rBad.status, 1);
  assert.match(rBad.stderr, /\[lint-config-invalid\]/);
});

test('merge-base trust rejects untrusted working-tree relaxation of lint.scenario thresholds in --diff', t => {
  const fx = initTempRepo(t, {
    steps: 12,
    pddConfig: { lint: { scenario: { max_steps: 10 }, rules: { 'scenario-oversized': 'error' } } },
  });
  // Working-tree attempt to relax max_steps from 10 to 50 on a branch must be ignored and flagged.
  writeFileSync(
    join(fx.repo, 'pdd.json'),
    `${JSON.stringify({ lint: { scenario: { max_steps: 50 }, rules: { 'scenario-oversized': 'error' } } }, null, 2)}\n`,
  );
  writeFileSync(
    join(fx.repo, 'tests', 'ledger.json'),
    `${JSON.stringify({ entry_path: 'prompts/ledger.prompt.md', initial_world: { balance: 101 }, steps: makeSteps(12) }, null, 2)}\n`,
  );
  const out = [];
  const err = [];
  const code = runLocalLint(
    { cwd: fx.repo, diff: 'main' },
    { stdout: { write: s => out.push(s) }, stderr: { write: s => err.push(s) } },
  );
  assert.equal(code, 1);
  assert.match(err.join(''), /\[scenario-oversized\]/);
  assert.match(out.join(''), /\[lint-config-untrusted\]/);
  assert.match(out.join(''), /lint\.scenario\.max_steps/);
});

test('lower-bound positive calls checks exceeding default per-request cap emit scenario-oversized without false positives on simulation declarations', () => {
  assert.equal(DEFAULT_SCENARIO_MAX_STEPS, 15);
  assert.equal(DEFAULT_SCENARIO_MAX_WORLD_BYTES, 16384);
  assert.equal(computeDefaultScenarioCallCap({ initial_world: { a: 1 }, steps: makeSteps(15) }), 81);

  // Declaring 16 simulation ports on a 4-step scenario does NOT trigger false positives
  const manyDeclaredPorts = {
    entry_path: 'prompts/ledger.prompt.md',
    initial_world: { ok: true },
    simulation: Object.fromEntries(Array.from({ length: 16 }, (_, i) => [`p.op${i}`, { action: 'port.write', world_pointer: '/ok' }])),
    steps: makeSteps(4),
  };
  assert.equal(evaluateScenarioHygiene(manyDeclaredPorts).oversized, false);

  // Explicitly asserting 8 positive calls per step across 10 steps (min 90 > cap 56) DOES warn
  const heavyChecks = Array.from({ length: 8 }, (_, i) => ['calls', `p.op${i}`, '=', 1]);
  const heavyDoc = {
    entry_path: 'prompts/ledger.prompt.md',
    initial_world: { ok: true },
    steps: makeSteps(10, heavyChecks),
  };
  const evaluated = evaluateScenarioHygiene(heavyDoc, { path: 'tests/heavy.json' });
  assert.equal(evaluated.oversized, true);
  assert.equal(evaluated.metrics.min_estimated_calls, 90);
  assert.equal(evaluated.metrics.default_call_cap, 56);
  assert.match(evaluated.finding.detail, /minimum 90 estimated calls exceeding default per-request cap 56/);

  // Short JSON array-form 5-tuple calls checks ([criterion, "calls", path, op, value]) also count!
  const arrayTupleSteps = Array.from({ length: 10 }, (_, idx) => ({
    id: `a${idx + 1}`,
    op: 'step',
    input: { n: idx + 1 },
    checks: Array.from({ length: 8 }, (_, i) => ['1', 'calls', `p.op${i}`, '=', 1]),
  }));
  const arrayEvaluated = evaluateScenarioHygiene(
    { entry_path: 'prompts/ledger.prompt.md', initial_world: { ok: true }, steps: arrayTupleSteps },
    { path: 'tests/heavy-array.json' },
  );
  assert.equal(arrayEvaluated.oversized, true);
  assert.equal(arrayEvaluated.metrics.min_estimated_calls, 90);
  assert.equal(arrayEvaluated.metrics.default_call_cap, 56);
});

test('lintRepoProject scopes scenario-oversized cleanly and does not leak non-scenario JSON', t => {
  const fx = initTempRepo(t, { steps: 16 });
  mkdirSync(join(fx.repo, 'tests', 'fixtures'), { recursive: true });
  writeFileSync(
    join(fx.repo, 'tests', 'fixtures', 'big.json'),
    JSON.stringify({ steps: makeSteps(50) }),
  );
  execFileSync('git', ['add', '.'], { cwd: fx.repo });
  const res = lintRepoProject({ root: fx.repo });
  const oversized = res.findings.filter(f => f.code === 'scenario-oversized');
  assert.equal(oversized.length, 1);
  assert.equal(oversized[0].path, 'tests/ledger.json');
});
