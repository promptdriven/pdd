import '../../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  FORMAL_EXPORT_RESULT_SCHEMA,
  FORMAL_VECTORS_SCHEMA,
  convertItfTrace,
  exportFormalVectors,
  formatCompanionOutputPaths,
  normalizeItfValue,
} from '../../../src/core/lint/vector-export.mjs';
import { parseExactScenarioJson } from '../../../src/scenario-compile.mjs';

const BIN_PDD = fileURLToPath(new URL('../../../bin/pdd.mjs', import.meta.url));
const SCENARIO_PATH = fileURLToPath(new URL('../../runtime/formal-vector-export.json', import.meta.url));

function initTempRepo(t) {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-vector-export-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));
  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  mkdirSync(join(repo, 'prompts'), { recursive: true });
  mkdirSync(join(repo, 'user_stories'), { recursive: true });
  mkdirSync(join(repo, 'tests'), { recursive: true });
  mkdirSync(home, { recursive: true });

  execFileSync('git', ['init', '-q', '-b', 'main'], { cwd: repo });
  execFileSync('git', ['config', 'user.name', 'Test'], { cwd: repo });
  execFileSync('git', ['config', 'user.email', 'test@example.com'], { cwd: repo });

  writeFileSync(
    join(repo, 'prompts', 'option-grant.prompt.md'),
    '# Option grant\n\nProcess `issue({ shares, strike_cents })` and `withdraw({ amount })` and save via `ledger.save`.\n\n## Dependencies\n\nNone.\n',
  );
  writeFileSync(
    join(repo, 'user_stories', 'option-grant.md'),
    '# Issue option grant\n\nAs an equity administrator, I want option grant boundaries validated, so that pool limits hold.\n\n## Acceptance criteria\n\n1. Issuing a valid grant returns active status.\n2. Issuing zero shares fails with pool_exhausted and zero saves.\n',
  );
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['commit', '-q', '-m', 'init'], { cwd: repo });
  return { scratch, repo, home };
}

function runCli(args, { cwd, home, input = undefined }) {
  return spawnSync(process.execPath, [BIN_PDD, ...args], {
    cwd,
    input,
    encoding: 'utf8',
    env: { ...process.env, HOME: home, PDD_STATE_DIR: join(home, 'state') },
    timeout: 20_000,
  });
}

test('vector replay: test/runtime/formal-vector-export.json matches real exportFormalVectors 1-to-1', () => {
  const scenario = JSON.parse(readFileSync(SCENARIO_PATH, 'utf8'));
  assert.equal(scenario.steps.length, 6);

  for (const step of scenario.steps) {
    const res = exportFormalVectors(step.input.inputDoc, step.input.options);
    if (step.id === 'export-boundary-cases') {
      assert.equal(res.ok, true);
      assert.equal(res.files.length, 1);
      assert.equal(res.files[0].path, 'tests/option-grant.formal.json');
      assert.equal(res.files[0].step_count, 2);
      assert.equal(res.files[0].doc.entry_path, 'prompts/option-grant.prompt.md');
      assert.equal(res.files[0].doc.steps[0].input.strike_cents, 4200);
      assert.equal(res.files[0].doc.steps[1].error, 'pool_exhausted');
    } else if (step.id === 'export-quint-itf-trace') {
      assert.equal(res.ok, true);
      assert.equal(res.files[0].step_count, 1);
      assert.equal(res.files[0].doc.initial_world.balance, 100);
      assert.equal(res.files[0].doc.steps[0].op, 'withdraw');
      assert.equal(res.files[0].doc.steps[0].input.amount, 25);
    } else if (step.id === 'refuse-exceeding-max-steps') {
      assert.equal(res.ok, false);
      assert.equal(res.refusal.code, 'max-steps-exceeded');
    } else if (step.id === 'split-exceeding-max-steps') {
      assert.equal(res.ok, true);
      assert.equal(res.files.length, 2);
      assert.equal(res.files[0].path, 'tests/ledger.formal-01.json');
      assert.equal(res.files[0].step_count, 2);
      assert.equal(res.files[1].path, 'tests/ledger.formal-02.json');
      assert.equal(res.files[1].step_count, 1);
    } else if (step.id === 'refuse-missing-checks') {
      assert.equal(res.ok, false);
      assert.equal(res.refusal.code, 'missing-checks');
    } else if (step.id === 'refuse-invalid-pointer') {
      assert.equal(res.ok, false);
      assert.equal(res.refusal.code, 'invalid-pointer');
    }
  }
});

test('AC1: pdd vector export dry-run preserves exact BigInt 9007199254740993, writes zero files, and works via stdin', t => {
  const { repo, home } = initTempRepo(t);
  const rawSpec = `{
  "schema_version": "${FORMAL_VECTORS_SCHEMA}",
  "entry_path": "prompts/option-grant.prompt.md",
  "default_op": "issue",
  "cases": [
    {
      "id": "boundary-large-int",
      "criterion": "1",
      "input": { "shares": 10, "grant_seq": 9007199254740993 },
      "expect": { "/grant_seq": 9007199254740993, "/status": "active" }
    },
    {
      "id": "boundary-zero-shares",
      "criterion": "2",
      "input": { "shares": 0 },
      "error": "pool_exhausted",
      "checks": [["calls", "ledger.save", "=", 0]]
    }
  ]
}\n`;
  const inputFile = join(repo, 'formal-cases.json');
  writeFileSync(inputFile, rawSpec);

  const outPath = 'tests/option-grant.formal.json';
  const dry = runCli(['vector', 'export', 'formal-cases.json', '--out', outPath], { cwd: repo, home });
  assert.equal(dry.status, 0, dry.stderr);
  assert.equal(existsSync(join(repo, outPath)), false, 'dry-run without --write must write zero files');
  assert.match(dry.stdout, /9007199254740993/, 'raw output must preserve exact BigInt digits');
  const parsed = parseExactScenarioJson(dry.stdout);
  assert.equal(parsed.steps[0].input.grant_seq, 9007199254740993n);
  assert.equal(parsed.steps[0].checks['1'][0][3], 9007199254740993n);
  assert.equal(parsed.steps[1].error, 'pool_exhausted');

  // Piped stdin mode (omitting INPUT) and explicit `-- -` both produce identical Short JSON previews
  const stdinRes = runCli(['vector', 'export', '--json'], { cwd: repo, home, input: rawSpec });
  assert.equal(stdinRes.status, 0, stdinRes.stderr);
  const jsonOut = parseExactScenarioJson(stdinRes.stdout);
  assert.equal(jsonOut.schema_version, FORMAL_EXPORT_RESULT_SCHEMA);
  assert.equal(jsonOut.ok, true);
  assert.equal(jsonOut.written, false);
  assert.equal(jsonOut.files[0].doc.steps[0].input.grant_seq, 9007199254740993n);

  const dashRes = runCli(['vector', 'export', '--json', '--', '-'], { cwd: repo, home, input: rawSpec });
  assert.equal(dashRes.status, 0, dashRes.stderr);
  assert.equal(dashRes.stdout, stdinRes.stdout);
});

test('AC2: pdd vector export converts Quint ITF traces with #bigint, #tup, #set, #map into pdd lint-clean Short JSON', t => {
  const { repo, home } = initTempRepo(t);
  assert.deepEqual(normalizeItfValue({ '#tup': [1, { '#set': [2, 3] }] }), [1, [2, 3]]);
  assert.deepEqual(normalizeItfValue({ '#map': [['k', { '#bigint': '9007199254740993' }]] }), { k: 9007199254740993n });

  const itf = {
    '#meta': { format: 'ITF' },
    vars: ['balance', 'action', 'input', 'result'],
    states: [
      { '#meta': { index: 0 }, balance: { '#bigint': '100' } },
      {
        '#meta': { index: 1 },
        balance: { '#bigint': '75' },
        action: 'withdraw',
        input: { amount: { '#bigint': '25' } },
        result: { balance: { '#bigint': '75' } },
      },
    ],
  };
  const conv = convertItfTrace(itf, { entryPath: 'prompts/option-grant.prompt.md', defaultOp: 'withdraw' });
  assert.equal(conv.ok, true);

  const res = runCli(
    ['vector', 'export', '--entry', 'prompts/option-grant.prompt.md', '--op', 'withdraw', '--out', 'tests/option-grant.itf.json', '--write'],
    { cwd: repo, home, input: JSON.stringify(itf) },
  );
  assert.equal(res.status, 0, res.stderr);
  assert.equal(existsSync(join(repo, 'tests', 'option-grant.itf.json')), true);

  // Verify the written companion vector is pdd lint-clean (0 errors, 0 warnings)!
  execFileSync('git', ['add', 'tests/option-grant.itf.json'], { cwd: repo });
  const lint = runCli(['lint', 'tests/option-grant.itf.json'], { cwd: repo, home });
  assert.equal(lint.status, 0, lint.stderr);
  assert.doesNotMatch(lint.stdout + lint.stderr, /scenario-oversized|compact-scenario-compile/);
});

test('AC3: 20 cases refuse without --split and split into pdd lint-clean 15+5 companion vectors with --split --write', t => {
  const { repo, home } = initTempRepo(t);
  assert.deepEqual(formatCompanionOutputPaths('tests/ledger.formal.json', 1), ['tests/ledger.formal.json']);
  assert.deepEqual(formatCompanionOutputPaths('tests/ledger.formal.json', 2), ['tests/ledger.formal-01.json', 'tests/ledger.formal-02.json']);

  const cases20 = Array.from({ length: 20 }, (_, i) => ({
    id: `cell-${i + 1}`,
    criterion: i % 2 === 0 ? '1' : '2',
    input: { shares: i + 1, strike_cents: 100 },
    expect: { '/status': 'active', '/shares': i + 1 },
  }));
  const spec = {
    schema_version: FORMAL_VECTORS_SCHEMA,
    entry_path: 'prompts/option-grant.prompt.md',
    default_op: 'issue',
    cases: cases20,
  };

  // Without --split: refuses fail-closed with max-steps-exceeded and exit 1
  const refused = runCli(['vector', 'export', '--out', 'tests/option-grant.formal.json', '--write'], {
    cwd: repo,
    home,
    input: JSON.stringify(spec),
  });
  assert.equal(refused.status, 1);
  assert.match(refused.stderr, /max-steps-exceeded/);
  assert.equal(existsSync(join(repo, 'tests', 'option-grant.formal.json')), false);

  // With --split --write: writes -01 (15 steps) and -02 (5 steps), both 100% pdd lint-clean!
  const splitRes = runCli(['vector', 'export', '--split', '--out', 'tests/option-grant.formal.json', '--write'], {
    cwd: repo,
    home,
    input: JSON.stringify(spec),
  });
  assert.equal(splitRes.status, 0, splitRes.stderr);
  const p1 = join(repo, 'tests', 'option-grant.formal-01.json');
  const p2 = join(repo, 'tests', 'option-grant.formal-02.json');
  assert.equal(existsSync(p1), true);
  assert.equal(existsSync(p2), true);
  assert.equal(JSON.parse(readFileSync(p1, 'utf8')).steps.length, 15);
  assert.equal(JSON.parse(readFileSync(p2, 'utf8')).steps.length, 5);

  execFileSync('git', ['add', 'tests/option-grant.formal-01.json', 'tests/option-grant.formal-02.json'], { cwd: repo });
  const lint = runCli(['lint'], { cwd: repo, home });
  assert.equal(lint.status, 0, lint.stderr);
  assert.match(lint.stdout, /Local lint: 0 errors, 0 warnings\./);
});

test('AC4 & safety: refuses missing checks, invalid pointers, patch-null-deletes-key, missing --out, traversal, and symlink targets without writing', t => {
  const { scratch, repo, home } = initTempRepo(t);
  const validSpec = JSON.stringify({
    schema_version: FORMAL_VECTORS_SCHEMA,
    entry_path: 'prompts/option-grant.prompt.md',
    default_op: 'issue',
    cases: [{ id: 'c1', input: { shares: 1 }, expect: { '/status': 'active' } }],
  });

  // Zero checks -> exit 1
  const noChecks = runCli(['vector', 'export', '--out', 'tests/a.json', '--write'], {
    cwd: repo,
    home,
    input: JSON.stringify({ entry_path: 'prompts/option-grant.prompt.md', default_op: 'issue', cases: [{ id: 'c1', input: {} }] }),
  });
  assert.equal(noChecks.status, 1);
  assert.match(noChecks.stderr, /missing-checks/);
  assert.equal(existsSync(join(repo, 'tests', 'a.json')), false);

  // Malformed pointer -> exit 1
  const badPtr = runCli(['vector', 'export', '--out', 'tests/b.json', '--write'], {
    cwd: repo,
    home,
    input: JSON.stringify({ entry_path: 'prompts/option-grant.prompt.md', default_op: 'issue', cases: [{ id: 'c1', input: {}, expect: { bad: 1 } }] }),
  });
  assert.equal(badPtr.status, 1);
  assert.match(badPtr.stderr, /invalid-pointer/);
  assert.equal(existsSync(join(repo, 'tests', 'b.json')), false);

  // Explicit null in patch -> refuses fail-closed so exported Short JSON never emits patch-null-deletes-key warning
  const patchNull = exportFormalVectors({
    schema_version: FORMAL_VECTORS_SCHEMA,
    entry_path: 'prompts/option-grant.prompt.md',
    default_op: 'issue',
    seeds: { base: { a: 1 } },
    cases: [{ id: 'c1', from: 'base', patch: { a: null }, expect: { '/ok': true } }],
  });
  assert.equal(patchNull.ok, false);
  assert.equal(patchNull.refusal.code, 'patch-null-deletes-key');

  // --write without --out -> exit 2
  const noOut = runCli(['vector', 'export', '--write'], { cwd: repo, home, input: validSpec });
  assert.equal(noOut.status, 2);

  // Path traversal escaping repo -> exit 2
  const escapeRes = runCli(['vector', 'export', '--out', '../escaped.json', '--write'], { cwd: repo, home, input: validSpec });
  assert.equal(escapeRes.status, 2);
  assert.equal(existsSync(join(scratch, 'escaped.json')), false);

  // Symlink target refused -> exit 2
  const outside = join(scratch, 'outside.json');
  writeFileSync(outside, 'untouched');
  symlinkSync(outside, join(repo, 'tests', 'sym.json'));
  const symRes = runCli(['vector', 'export', '--out', 'tests/sym.json', '--write'], { cwd: repo, home, input: validSpec });
  assert.equal(symRes.status, 2);
  assert.equal(readFileSync(outside, 'utf8'), 'untouched');
});
