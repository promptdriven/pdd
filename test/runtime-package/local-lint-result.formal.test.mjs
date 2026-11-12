import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { readRunResults, resultLines, usableResult } from '../../src/workflow-results.mjs';

// Oracle authority: approved local-lint-result Story, Rules to check; the
// workflow-results prompt's saved-local-layout-record/named-result-evidence.
// These are synthetic canonical records, not evidence of CLI persistence.
const START = Date.parse('2026-11-12T12:00:00.000Z');
const LOCAL = '20261112-120002-locl';
const HOSTED = '20261112-120001-host';
const SHA = 'a'.repeat(64);
const REASON = { code: 'local-only', message: 'checked SVG layout only; prompts not checked' };
const INCOMPLETE = 'Local lint result not saved (the local save did not finish). partial (local-only).';
// Every required summary field gets an independent mismatch witness. The
// malformed JSON and unreadable directory cases are separate failure modes.
const SUMMARY_FIELDS = ['batch', 'repo', 'exit_code', 'state', 'lint_state', 'reason', 'local_only', 'local_scope', 'summary_line', 'warnings', 'problems', 'rows', 'report_url'];
const SUMMARY_STATES = ['complete', 'missing', 'malformed', 'unreadable', ...SUMMARY_FIELDS.map(field => `mismatched:${field}`)];
const SCOPES = [
  { tests: [], prompts: ['prompts/example.prompt.md'] },
  { tests: ['tests/example.json'], prompts: ['prompts/example.prompt.md'] },
];

function fixture() {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'pdd-local-formal-'));
  const root = path.join(dir, 'repo');
  const foreign = path.join(dir, 'foreign');
  const state = path.join(dir, 'state');
  for (const folder of [root, foreign, path.join(state, 'batches')]) fs.mkdirSync(folder, { recursive: true });
  return { dir, root, foreign, state, env: { PDD_STATE_DIR: state } };
}

function snapshot(dir) {
  const values = [];
  function visit(name) {
    const item = path.join(dir, name);
    const stat = fs.lstatSync(item, { bigint: true });
    const identity = [name, String(stat.mode), String(stat.mtimeNs)];
    if (stat.isDirectory()) {
      values.push([...identity, 'directory']);
      for (const child of fs.readdirSync(item).sort()) visit(path.join(name, child));
    } else if (stat.isSymbolicLink()) {
      values.push([...identity, 'link', fs.readlinkSync(item)]);
    } else {
      values.push([...identity, createHash('sha256').update(fs.readFileSync(item)).digest('hex')]);
    }
  }
  visit('');
  return values;
}

function localRecord(root, at, scope, exit) {
  const warnings = scope.tests.length ? ['One local layout warning.'] : [];
  const problems = exit === 4 ? [{ code: 'missing-interface', path: 'prompts/example.prompt.md', message: 'Runtime interface missing.', section: 'Runtime interface' }] : [];
  const summary = `partial: checked SVG layout only; prompts not checked (local-only). ${warnings.length} warnings. 0 AI calls. No checks were sent.`;
  const batch = {
    version: 1, batch: LOCAL, root, created_at: new Date(at).toISOString(),
    intent: 'lint-only', local_only: true, source_sha256: null,
    local_scope: structuredClone(scope), summary_line: summary, exit_code: exit,
    warnings, problems, rows: [],
    lint: { state: 'partial', lint_state: 'partial', reason: structuredClone(REASON), request_ids: [] },
  };
  const saved = {
    batch: LOCAL, repo: root, exit_code: exit, state: 'partial', lint_state: 'partial',
    reason: structuredClone(REASON), local_only: true, local_scope: structuredClone(scope),
    summary_line: summary, warnings, problems, rows: [], report_url: null,
  };
  return { batch, saved };
}

function save(f, record, completion) {
  const folder = path.join(f.state, 'batches', record.batch.batch);
  fs.mkdirSync(folder, { recursive: true });
  fs.writeFileSync(path.join(folder, 'batch.json'), JSON.stringify(record.batch));
  if (completion === 'missing') return;
  if (completion === 'unreadable') {
    fs.mkdirSync(path.join(folder, 'summary.json'));
    return;
  }
  const summary = structuredClone(record.saved);
  if (completion.startsWith('mismatched:')) {
    const field = completion.slice('mismatched:'.length);
    const mutations = {
      batch: '20261112-120003-else', repo: '/a-different-repository',
      exit_code: summary.exit_code === 0 ? 4 : 0, state: 'passed', lint_state: 'passed',
      reason: { code: 'local-only', message: 'A different reason.' }, local_only: false,
      local_scope: { tests: ['tests/different.json'], prompts: ['prompts/different.prompt.md'] },
      summary_line: 'Different partial summary.', warnings: ['Different warning.'],
      problems: [{ code: 'different', path: 'prompts/different.prompt.md', message: 'Different finding.' }],
      rows: [{ test: 'tests/different.json', state: 'passed' }], report_url: 'https://example.invalid/report',
    };
    summary[field] = mutations[field];
  }
  const content = completion === 'malformed' ? '{invalid JSON' : JSON.stringify(summary);
  fs.writeFileSync(path.join(folder, 'summary.json'), content);
}

function hosted(f) {
  const row = { test: 'tests/hosted.json', story: 'user_stories/hosted.md', state: 'passed', request_ids: ['hosted-request'] };
  const batch = {
    version: 1, batch: HOSTED, root: f.root, created_at: new Date(START + 1).toISOString(),
    intent: 'lint-only', source_sha256: SHA, rows: [row],
    lint: { state: 'passed', lint_state: 'passed', request_ids: ['hosted-request'] },
  };
  const saved = { batch: HOSTED, repo: f.root, rows: [row], summary_line: 'Lint: 1 of 1 tests pass. 0 AI calls.' };
  save(f, { batch, saved }, 'complete');
}

async function readUnchanged(f) {
  const before = snapshot(f.dir);
  const calls = { capture: 0, git: 0 };
  const result = await readRunResults({ root: f.root, since: START }, {
    env: f.env,
    capture: () => { calls.capture++; return { sha256: SHA }; },
    git: () => { calls.git++; return ''; },
  });
  assert.deepEqual(snapshot(f.dir), before, 'formal reader must not change any file, directory or timestamp');
  return { result: result.filter(row => row.kind === 'pdd lint'), calls };
}

function assertLocal(result, record, completion, label) {
  assert.equal(result.batch, LOCAL, `${label}: local candidate must remain selected`);
  assert.equal(result.kind, 'pdd lint', label);
  assert.equal(result.at, Date.parse(record.batch.created_at), label);
  assert.equal(result.state, 'partial', label);
  assert.equal(result.localOnly, true, label);
  assert.deepEqual(result.localScope, record.batch.local_scope, label);
  assert.deepEqual(result.tests, record.batch.local_scope.tests, label);
  assert.deepEqual(result.reason, REASON, label);
  assert.deepEqual(result.states, [], label);
  assert.deepEqual(result.requests, [], label);
  assert.deepEqual(result.warnings, record.batch.warnings, label);
  assert.deepEqual(result.problems, record.batch.problems, label);
  assert.equal(result.exitCode, completion === 'complete' ? record.batch.exit_code : 2, label);
  assert.equal(result.summary, completion === 'complete' ? record.batch.summary_line : INCOMPLETE, label);
  assert.equal(usableResult(result), false, `${label}: empty local evidence cannot authorize full proof`);
  assert.notEqual(result.source, 'current', `${label}: null source cannot establish currentness`);
  assert.ok(!result.engine && !result.model, `${label}: no engine or model may be invented`);
  assert.ok(!result.reports?.length, `${label}: no server report may be invented`);
  const text = resultLines([result], { kinds: ['pdd lint'] }).join('\n');
  assert.ok(text.includes(result.summary), `${label}: summary remains visible`);
  assert.doesNotMatch(text, /0 of 0 tests pass|Lint: 1 of 1 tests pass/, label);
  for (const fact of [...record.batch.warnings, ...record.batch.problems.map(p => p.message), ...record.batch.local_scope.prompts, ...record.batch.local_scope.tests]) {
    assert.ok(text.includes(fact), `${label}: missing displayed fact ${fact}`);
  }
  if (!record.batch.local_scope.tests.length) assert.match(text, /repository scan/i, label);
}

test('formal bounded local completion, since boundary, root, scope and exit policy (408 inputs)', async () => {
  let checked = 0;
  for (const completion of SUMMARY_STATES) for (const delta of [-1, 0, 1])
    for (const sameRoot of [true, false]) for (const scope of SCOPES) for (const exit of [0, 4]) {
      const f = fixture();
      const label = JSON.stringify({ completion, delta, sameRoot, scope, exit });
      try {
        const record = localRecord(sameRoot ? f.root : f.foreign, START + delta, scope, exit);
        save(f, record, completion);
        const { result } = await readUnchanged(f);
        const eligible = sameRoot && delta >= 0;
        assert.equal(result.length, eligible ? 1 : 0, `${label}: formal root/time admission`);
        if (eligible) assertLocal(result[0], record, completion, label);
        checked++;
      } finally { fs.rmSync(f.dir, { recursive: true, force: true }); }
    }
  assert.equal(checked, 408);
  console.log(`FORMAL local-admission: ${checked} exhaustive inputs passed`);
});

test('formal bounded newer local cannot reveal older hosted pass (136 inputs)', async () => {
  let checked = 0;
  for (const completion of SUMMARY_STATES) for (const sameRoot of [true, false])
    for (const scope of SCOPES) for (const exit of [0, 4]) {
      const f = fixture();
      const label = JSON.stringify({ completion, sameRoot, scope, exit, olderHosted: true });
      try {
        hosted(f);
        const record = localRecord(sameRoot ? f.root : f.foreign, START + 2, scope, exit);
        save(f, record, completion);
        const { result } = await readUnchanged(f);
        assert.equal(result.length, 1, label);
        if (sameRoot) assertLocal(result[0], record, completion, label);
        else {
          assert.equal(result[0].batch, HOSTED, `${label}: foreign candidate must not displace eligible hosted evidence`);
          assert.equal(usableResult(result[0]), true, `${label}: existing hosted route remains usable`);
        }
        checked++;
      } finally { fs.rmSync(f.dir, { recursive: true, force: true }); }
    }
  assert.equal(checked, 136);
  console.log(`FORMAL local-supersession: ${checked} exhaustive inputs passed`);
});

test('formal bounded result eligibility guards preserve native and prove routes (576 inputs)', () => {
  let checked = 0;
  for (const kind of ['pdd lint', 'pdd test', 'native evidence', 'pdd workflow prove'])
    for (const localOnly of [false, true]) for (const state of [undefined, 'partial', 'current', 'stale'])
      for (const states of [[], [{ state: 'passed' }], [{ state: 'partial' }]])
        for (const stage of ['current', 'pr1']) for (const proof of ['none', 'pdd-observed', 'qualified-external']) {
          const result = { kind, localOnly, state, states, assessment: { identity: { stage }, storyNativeProof: proof } };
          // Ordered oracle from named-result-evidence, never from production.
          const partial = kind === 'pdd lint' && localOnly || state === 'partial' || states.some(row => row.state === 'partial');
          const expected = partial ? false : kind === 'native evidence'
            ? stage !== 'pr1' && ['pdd-observed', 'qualified-external'].includes(proof)
            : kind === 'pdd workflow prove' ? state === 'current' : true;
          assert.equal(usableResult(result), expected, `formal eligibility counterexample: ${JSON.stringify(result)}`);
          checked++;
        }
  assert.equal(checked, 576);
  console.log(`FORMAL eligibility: ${checked} exhaustive inputs passed`);
});
