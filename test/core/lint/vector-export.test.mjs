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
  runVectorExport,
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
  const writtenItfPath = join(repo, 'tests', 'option-grant.itf.json');
  assert.equal(existsSync(writtenItfPath), true);
  const writtenItf = parseExactScenarioJson(readFileSync(writtenItfPath, 'utf8'));
  assert.equal(writtenItf.initial_world.balance, 100);
  assert.equal(writtenItf.steps[0].op, 'withdraw');
  assert.equal(writtenItf.steps[0].input.amount, 25);
  assert.deepEqual(writtenItf.steps[0].checks['1'], [['result', '/balance', '=', 75]]);

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

test('regression: --write allows ancestor directory matching target basename and refuses non-directory ancestor', t => {
  const { repo, home } = initTempRepo(t);
  const validSpec = JSON.stringify({
    schema_version: FORMAL_VECTORS_SCHEMA,
    entry_path: 'prompts/option-grant.prompt.md',
    default_op: 'issue',
    cases: [{ id: 'c1', input: { shares: 1 }, expect: { '/status': 'active' } }],
  });

  // Ancestor directory shares the same basename as the target file (tests/same.json/same.json).
  mkdirSync(join(repo, 'tests', 'same.json'), { recursive: true });
  const sameRes = runCli(['vector', 'export', '--out', 'tests/same.json/same.json', '--write'], { cwd: repo, home, input: validSpec });
  assert.equal(sameRes.status, 0, sameRes.stderr);
  assert.equal(existsSync(join(repo, 'tests', 'same.json', 'same.json')), true);

  // Ancestor path is a regular file rather than a directory -> exit 2 fail-closed.
  writeFileSync(join(repo, 'tests', 'blocking-file.json'), 'not a dir');
  const blockedRes = runCli(['vector', 'export', '--out', 'tests/blocking-file.json/child.json', '--write'], { cwd: repo, home, input: validSpec });
  assert.equal(blockedRes.status, 2);
  assert.match(blockedRes.stderr, /not a directory/i);
});

test('regression: CLI --criterion overrides spec default_criterion while omitted --criterion preserves spec default_criterion', t => {
  const { repo, home } = initTempRepo(t);
  const specWithDefault2 = JSON.stringify({
    schema_version: FORMAL_VECTORS_SCHEMA,
    entry_path: 'prompts/option-grant.prompt.md',
    default_op: 'issue',
    default_criterion: '2',
    cases: [{ id: 'c1', input: { shares: 1 }, expect: { '/status': 'active' } }],
  });

  // Omitted --criterion preserves spec.default_criterion ("2").
  const preserved = runCli(['vector', 'export', '--json'], { cwd: repo, home, input: specWithDefault2 });
  assert.equal(preserved.status, 0, preserved.stderr);
  assert.deepEqual(Object.keys(JSON.parse(preserved.stdout).files[0].doc.steps[0].checks), ['2']);

  // Explicit --criterion 1 overrides spec.default_criterion ("2").
  const overridden = runCli(['vector', 'export', '--criterion', '1', '--json'], { cwd: repo, home, input: specWithDefault2 });
  assert.equal(overridden.status, 0, overridden.stderr);
  assert.deepEqual(Object.keys(JSON.parse(overridden.stdout).files[0].doc.steps[0].checks), ['1']);

  // Blank CLI --criterion is rejected at argument parsing (exit 2), while invalid spec default_criterion fails closed (exit 1).
  const blankCli = runCli(['vector', 'export', '--criterion', '', '--json'], { cwd: repo, home, input: specWithDefault2 });
  assert.equal(blankCli.status, 2);

  const invalidLib = exportFormalVectors(JSON.parse(specWithDefault2), { defaultCriterion: '' });
  assert.equal(invalidLib.ok, false);
  assert.equal(invalidLib.refusal.code, 'invalid-criterion');

  const invalidSpec = runCli(['vector', 'export', '--json'], {
    cwd: repo,
    home,
    input: JSON.stringify({ ...JSON.parse(specWithDefault2), default_criterion: 0 }),
  });
  assert.equal(invalidSpec.status, 1);
  assert.equal(JSON.parse(invalidSpec.stdout).refusal.code, 'invalid-criterion');
});

test('regression: story_path refuses ancestor symlink, patch/set without from are preserved & validated, invalid optionals fail closed, and ports/json errors behave consistently', t => {
  const { scratch, repo, home } = initTempRepo(t);

  // 1. Ancestor symlink under repo for story_path must never be read via readSafeUtf8.
  const outsideDir = join(scratch, 'outside-stories');
  mkdirSync(outsideDir, { recursive: true });
  writeFileSync(join(outsideDir, 'secret.md'), '# Secret\n\n## Acceptance criteria\n\n1. Only one criterion.\n');
  symlinkSync(outsideDir, join(repo, 'linked-stories'));
  // If secret.md were read, criterion "2" would fail story-criterion-mismatch; because ancestor symlink is ignored, export succeeds.
  const symStorySpec = JSON.stringify({
    schema_version: FORMAL_VECTORS_SCHEMA,
    story_path: 'linked-stories/secret.md',
    entry_path: 'prompts/option-grant.prompt.md',
    default_op: 'issue',
    cases: [{ id: 'c1', criterion: '2', input: { shares: 1 }, expect: { '/status': 'active' } }],
  });
  const symStoryRes = runCli(['vector', 'export', '--json'], { cwd: repo, home, input: symStorySpec });
  assert.equal(symStoryRes.status, 0, symStoryRes.stderr);

  // 2. patch & set without from are preserved and validated (including patch-null-deletes-key).
  const withInputPatch = exportFormalVectors({
    schema_version: FORMAL_VECTORS_SCHEMA,
    entry_path: 'prompts/option-grant.prompt.md',
    default_op: 'issue',
    cases: [{ id: 'c1', input: { a: 1 }, patch: { b: 2 }, set: { '/c': null }, expect: { '/ok': true } }],
  });
  assert.equal(withInputPatch.ok, true);
  assert.deepEqual(withInputPatch.files[0].doc.steps[0].patch, { b: 2 });
  assert.deepEqual(withInputPatch.files[0].doc.steps[0].set, { '/c': null });

  const inputPatchNull = exportFormalVectors({
    schema_version: FORMAL_VECTORS_SCHEMA,
    entry_path: 'prompts/option-grant.prompt.md',
    default_op: 'issue',
    cases: [{ id: 'c1', input: { a: 1 }, patch: { a: null }, expect: { '/ok': true } }],
  });
  assert.equal(inputPatchNull.ok, false);
  assert.equal(inputPatchNull.refusal.code, 'patch-null-deletes-key');

  // 3. Explicit invalid optional fields fail closed instead of silently falling back.
  assert.equal(exportFormalVectors({
    entry_path: 'prompts/option-grant.prompt.md',
    default_op: 'issue',
    cases: [{ id: 'c1', entry_path: 123, input: {}, expect: { '/ok': true } }],
  }).refusal.code, 'invalid-case');
  assert.equal(exportFormalVectors({
    entry_path: 'prompts/option-grant.prompt.md',
    default_op: 'issue',
    cases: [{ id: 'c1', op: '   ', input: {}, expect: { '/ok': true } }],
  }).refusal.code, 'invalid-case');
  assert.equal(exportFormalVectors({
    entry_path: 'prompts/option-grant.prompt.md',
    story_path: 42,
    default_op: 'issue',
    cases: [{ id: 'c1', input: {}, expect: { '/ok': true } }],
  }).refusal.code, 'invalid-document');
  assert.equal(convertItfTrace({
    '#meta': { format: 'ITF' },
    states: [
      { '#meta': { index: 0 }, balance: 10 },
      { '#meta': { index: 1 }, action: 'withdraw', input: 123, balance: 5 },
    ],
  }, { entryPath: 'prompts/option-grant.prompt.md' }).refusal.code, 'invalid-itf');

  // 4. Injected ports.stdin works even when process.stdin may be a TTY, and --json emits structured refusal on syntax error.
  const outBuf = [];
  const errBuf = [];
  const validSpec = JSON.stringify({
    schema_version: FORMAL_VECTORS_SCHEMA,
    entry_path: 'prompts/option-grant.prompt.md',
    default_op: 'issue',
    cases: [{ id: 'c1', input: { shares: 1 }, expect: { '/status': 'active' } }],
  });
  const portExit = runVectorExport(
    { cwd: repo, json: true },
    {
      stdin: { readText: () => validSpec },
      stdout: { write: s => outBuf.push(s) },
      stderr: { write: s => errBuf.push(s) },
    },
  );
  assert.equal(portExit, 0, errBuf.join(''));
  assert.equal(JSON.parse(outBuf.join('')).ok, true);

  // Interactive TTY stdin without inputPath must return usage exit 2 immediately without reading fd 0.
  const ttyOut = [];
  const ttyErr = [];
  const ttyExit = runVectorExport(
    { cwd: repo },
    {
      stdin: { isTTY: true },
      stdout: { write: s => ttyOut.push(s) },
      stderr: { write: s => ttyErr.push(s) },
    },
  );
  assert.equal(ttyExit, 2);
  assert.equal(ttyOut.join(''), '');
  assert.match(ttyErr.join(''), /Provide an input JSON path/i);

  const badJsonCli = runCli(['vector', 'export', '--json'], { cwd: repo, home, input: '{broken json' });
  assert.equal(badJsonCli.status, 1);
  const badJsonPayload = JSON.parse(badJsonCli.stdout);
  assert.equal(badJsonPayload.schema_version, FORMAL_EXPORT_RESULT_SCHEMA);
  assert.equal(badJsonPayload.ok, false);
  assert.equal(badJsonPayload.refusal.code, 'invalid-json');
});
