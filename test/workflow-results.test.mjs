import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, mkdtempSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { readRunResults, resultLines, noResultLine, usableResult } from '../src/workflow-results.mjs';
import { validateProofRecord } from '../src/workflow-prove.mjs';

function folders(t) {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-results-'))); t.after(() => rmSync(base, { recursive: true, force: true }));
  const root = join(base, 'worktree'), state = join(base, 'state'), runDir = join(base, 'run');
  for (const dir of [root, state, runDir]) mkdirSync(dir);
  const batch = (name, value, summary) => {
    const folder = join(state, 'batches', name); mkdirSync(folder, { recursive: true });
    writeFileSync(join(folder, 'batch.json'), JSON.stringify({ version: 1, batch: name, root, rows: [{ test: 'tests/a.json', state: 'passed' }], ...value }));
    if (summary) writeFileSync(join(folder, 'summary.json'), JSON.stringify(summary));
  };
  return { root, state, runDir, batch, env: { PDD_STATE_DIR: state, HOME: base } };
}
const since = Date.parse('2026-11-03T10:00:00Z');

test('2904: reads the newest check and lint of this worktree since the run started, with source, engine and model', t => {
  const f = folders(t);
  f.batch('20261103-110000-aaaa', { intent: 'check', created_at: '2026-11-03T11:00:00Z', source_sha256: 'a'.repeat(64) }, { summary_line: 'Prompt tests: ✗ older' });
  f.batch('20261103-120000-bbbb', { intent: 'check', created_at: '2026-11-03T12:00:00Z', source_sha256: 'b'.repeat(64), rows: [{ test: 'tests/a.json', engine_sha: '0123456789abcdef', requested_model: 'm' }] }, { summary_line: 'Prompt tests: ✓ 2 of 2 criteria' });
  f.batch('20261103-130000-cccc', { intent: 'check', created_at: '2026-11-03T13:00:00Z', root: '/elsewhere' }, { summary_line: 'Prompt tests: ✓ foreign' });
  f.batch('20261103-090000-dddd', { intent: 'check', created_at: '2026-11-03T09:00:00Z' }, { summary_line: 'Prompt tests: ✓ before the run' });
  f.batch('20261103-113000-eeee', { intent: 'lint-only', created_at: '2026-11-03T11:30:00Z', lint: { state: null }, rows: [{ test: 'tests/a.json', state: 'unknown' }] });
  const captured = [];
  const results = readRunResults({ root: f.root, since }, { env: f.env, capture: (root, selection) => { captured.push([root, selection]); return { sha256: 'b'.repeat(64) }; } });
  assert.deepEqual(captured, [[f.root, { tests: ['tests/a.json'], appMap: null }]]);
  assert.deepEqual(resultLines(results), [
    'pdd result: pdd test (batch 20261103-120000-bbbb, 2026-11-03T12:00:00Z, source current, engine 0123456789ab, model m): Prompt tests: ✓ 2 of 2 criteria',
    'pdd result: pdd lint (batch 20261103-113000-eeee, 2026-11-03T11:30:00Z): Lint: result unknown (the lint did not finish).']);
});

const phase = extra => ({ exitCode: null, signal: '', timedOut: false, outputLimited: false, stdoutTail: [], stderrTail: [], expectedFound: false, error: '', setupError: '', observedError: '', ...extra });
const proof = (runId, headSha, baseSha) => ({ v: 2, origin: 'pdd.workflow-prove.v2', runId, baseSha, headSha, test: 'node --test test/a.test.mjs', expect: 'defect-x',
  paths: ['test/a.test.mjs'], base: phase({ exitCode: 1, expectedFound: true, observedError: 'defect-x' }), head: phase({ exitCode: 0 }), outcome: 'proved', cleanupError: '', setupError: '', interruptSignal: '' });
const HEAD = 'c'.repeat(40), BASE = 'b'.repeat(40);

test('2904: a prove record counts only when it is valid, this run\'s, made in this run and for the current head and base', t => {
  const f = folders(t), file = join(f.runDir, 'old-code-proof.json'), git = (root, args) => args[0] === 'rev-parse' ? HEAD : BASE;
  const read = (extra = {}) => readRunResults({ root: f.root, runDir: f.runDir, runId: 'run-1', since, baseBranch: 'main', ...extra }, { env: f.env, git });
  assert.deepEqual(read(), [], 'no file, no result');
  assert.equal(validateProofRecord(proof('run-1', HEAD, BASE)), true);
  for (const record of [{ runId: 'run-1', outcome: 'proved', headSha: HEAD }, proof('other', HEAD, BASE), { ...proof('run-1', HEAD, BASE), outcome: 'old-passes' }]) {
    writeFileSync(file, JSON.stringify(record));
    const [result] = read();
    assert.deepEqual([result.state, result.summary], ['unavailable', 'Old-code proof: unavailable.']);
    assert.equal(usableResult(result), false);
  }
  writeFileSync(file, JSON.stringify(proof('run-1', 'd'.repeat(40), BASE)));
  assert.equal(read()[0].summary, 'Old-code proof: stale (base or head changed; rerun pdd workflow prove).');
  writeFileSync(file, JSON.stringify(proof('run-1', HEAD, 'e'.repeat(40))));
  assert.equal(read()[0].state, 'stale', 'a changed base is stale too');
  writeFileSync(file, JSON.stringify(proof('run-1', HEAD, BASE)));
  assert.equal(read({ since: Date.now() + 3600000 })[0].summary, 'Old-code proof: stale (saved before this run started; rerun pdd workflow prove).');
  const [current] = read();
  assert.equal(current.state, 'current'); assert.equal(usableResult(current), true);
  assert.match(resultLines([current])[0], /^pdd result: pdd workflow prove \(\d{4}-\d\d-\d\dT[\d:]+Z, head ccccccc\): Old-code proof: ✓ `node --test test\/a\.test\.mjs`: old-code exit `1`; output contains `defect-x`; new-code exit `0`\.$/);
  assert.equal(readRunResults({ root: f.root, runDir: f.runDir, runId: 'run-1', since }, { env: f.env, git: () => '' })[0].summary, 'Old-code proof: unavailable.');
  // A base that cannot be read is never current.
  assert.deepEqual(['main', null].map(baseBranch => readRunResults({ root: f.root, runDir: f.runDir, runId: 'run-1', since, baseBranch }, { env: f.env, git: (root, args) => args[0] === 'rev-parse' ? HEAD : '' })[0].summary),
    ['Old-code proof: unavailable.', 'Old-code proof: unavailable.']);
});

test('2904: test and lint results keep pdd\'s saved request ids and report links, with no agent summary', t => {
  const f = folders(t);
  f.batch('20261103-120000-bbbb', { intent: 'check', created_at: '2026-11-03T12:00:00Z', rows: [
    { test: 'tests/a.json', request_ids: ['11111111-1111-4111-8111-111111111111'], report_url: 'https://rt.example.test/r/actual-report' },
    { test: 'tests/b.json', request_ids: ['22222222-2222-4222-8222-222222222222'], report_url: 'not a link' }] }, { summary_line: 'Prompt tests: ✓ 2 of 2 criteria' });
  f.batch('20261103-113000-eeee', { intent: 'lint-only', created_at: '2026-11-03T11:30:00Z', lint: { state: 'passed', request_ids: ['33333333-3333-4333-8333-333333333333'] } });
  const results = readRunResults({ root: f.root, since }, { env: f.env, capture: () => { throw Error('no capture'); } });
  assert.deepEqual(results[0].requests, ['11111111-1111-4111-8111-111111111111', '22222222-2222-4222-8222-222222222222']);
  assert.deepEqual(results[0].reports, ['https://rt.example.test/r/actual-report']);
  assert.deepEqual(results[1].requests, ['33333333-3333-4333-8333-333333333333']);
  assert.deepEqual(resultLines(results), [
    'pdd result: pdd test (batch 20261103-120000-bbbb, 2026-11-03T12:00:00Z, source unknown, requests 11111111-1111-4111-8111-111111111111 22222222-2222-4222-8222-222222222222): Prompt tests: ✓ 2 of 2 criteria; Report: https://rt.example.test/r/actual-report (report links expire after 7 days)',
    'pdd result: pdd lint (batch 20261103-113000-eeee, 2026-11-03T11:30:00Z, request 33333333-3333-4333-8333-333333333333): Lint: 1 of 1 tests pass. 0 AI calls.']);
});

test('2904: says pdd:no-verdict when there is no result', () => {
  assert.deepEqual(resultLines([]), [noResultLine()]);
  assert.equal(noResultLine(['pdd test', 'pdd lint']), 'pdd result: none. pdd has no pdd test or pdd lint result of its own for this run (pdd:no-verdict).');
  assert.deepEqual(resultLines([{ kind: 'pdd workflow prove', at: 0, state: 'current', summary: 'x' }], { kinds: ['pdd test'] }), ['pdd result: none. pdd has no pdd test result of its own for this run (pdd:no-verdict).']);
});

// #2904: the step reader and the PR renderer judge a proof with one rule, so they give the same line for every probe.
test('2904: the step reader and the PR renderer give the same proof line for the same probe files', async t => {
  const { preparePrEvidence } = await import('../src/workflow-pr-evidence.mjs');
  const { utimesSync } = await import('node:fs');
  const started = Date.parse('2026-11-03T10:00:00Z'), after = new Date('2026-11-03T11:00:00Z'), before = new Date('2026-11-03T09:00:00Z');
  const probes = [
    ['malformed', { runId: 'run-1', outcome: 'proved', headSha: HEAD }, after, BASE, 'Old-code proof: unavailable.'],
    ['another run', proof('other', HEAD, BASE), after, BASE, 'Old-code proof: unavailable.'],
    ['inconsistent outcome', { ...proof('run-1', HEAD, BASE), outcome: 'old-passes' }, after, BASE, 'Old-code proof: unavailable.'],
    ['older head', proof('run-1', 'd'.repeat(40), BASE), after, BASE, 'Old-code proof: stale (base or head changed; rerun pdd workflow prove).'],
    ['changed base', proof('run-1', HEAD, 'e'.repeat(40)), after, BASE, 'Old-code proof: stale (base or head changed; rerun pdd workflow prove).'],
    ['saved before the run', proof('run-1', HEAD, BASE), before, BASE, 'Old-code proof: stale (saved before this run started; rerun pdd workflow prove).'],
    ['base unreadable', proof('run-1', HEAD, BASE), after, '', 'Old-code proof: unavailable.'],
    ['current', proof('run-1', HEAD, BASE), after, BASE, /^Old-code proof: ✓ /]];
  for (const [name, record, time, base, expected] of probes) {
    const f = folders(t), file = join(f.runDir, 'old-code-proof.json');
    writeFileSync(file, JSON.stringify(record)); utimesSync(file, time, time);
    const [step] = readRunResults({ root: f.root, runDir: f.runDir, runId: 'run-1', since: started, baseBranch: 'main' }, { env: f.env, git: (root, args) => args[0] === 'rev-parse' ? HEAD : base });
    const pr = await preparePrEvidence({ run: { runId: 'run-1', startedAt: started, runDir: f.runDir, root: f.root, baseBranch: 'main', number: 7, workflow: 'bug', steps: [] }, isCode: true },
      { currentHead: async () => base ? { headSha: HEAD, baseSha: base, error: '' } : { headSha: '', baseSha: '', error: 'Current Git head unavailable.' } });
    assert.equal(step.summary, pr.lines[0], name);
    if (typeof expected === 'string') assert.equal(step.summary, expected, name); else assert.match(step.summary, expected, name);
    assert.equal(usableResult(step), name === 'current', name);
  }
});

test('2904: a 51-row batch keeps every request id and report link in the record; the line names how many it does not show', t => {
  const f = folders(t), id = i => `${String(i).padStart(8, '0')}-1111-4111-8111-111111111111`;
  f.batch('20261103-120000-bbbb', { intent: 'check', created_at: '2026-11-03T12:00:00Z',
    rows: Array.from({ length: 51 }, (_, i) => ({ test: `tests/t${i}.json`, request_ids: [id(i)], report_url: `https://rt.example.test/r/report-${i}` })) }, { summary_line: 'Prompt tests: ✓ 51 of 51 criteria' });
  const [result] = readRunResults({ root: f.root, since }, { env: f.env, capture: () => { throw Error('no capture'); } });
  assert.equal(result.requests.length, 51); assert.equal(result.requests.at(-1), id(50));
  assert.equal(result.reports.length, 51); assert.equal(result.reports.at(-1), 'https://rt.example.test/r/report-50');
  const [line] = resultLines([result]);
  assert.ok(line.includes(id(9)) && !line.includes(id(10)));
  assert.ok(line.includes('report-9 ') && !line.includes('report-10 '));
  assert.ok(line.endsWith('; 41 more requests and 41 more reports not shown (all in the run record)'), line.slice(-120));
});

test('2904: a cached row shows the build and model from its cache identity, marked as cached; direct values win', t => {
  const f = folders(t);
  f.batch('20261103-120000-bbbb', { intent: 'check', created_at: '2026-11-03T12:00:00Z',
    rows: [{ test: 'tests/a.json', state: 'passed', cached: true, engine_sha: null, requested_model: 'unknown', cache_identity: { engine_sha: 'fedcba9876543210', requested_model: 'cached-model' } }] }, { summary_line: 'Prompt tests: ✓ 1 of 1 criteria' });
  const [result] = readRunResults({ root: f.root, since }, { env: f.env, capture: () => { throw Error('no capture'); } });
  assert.deepEqual([result.engine, result.engineCached, result.model, result.modelCached], ['fedcba987654', true, 'cached-model', true]);
  assert.equal(resultLines([result])[0], 'pdd result: pdd test (batch 20261103-120000-bbbb, 2026-11-03T12:00:00Z, source unknown, engine fedcba987654 (cached), model cached-model (cached)): Prompt tests: ✓ 1 of 1 criteria');
  f.batch('20261103-130000-cccc', { intent: 'check', created_at: '2026-11-03T13:00:00Z',
    rows: [{ test: 'tests/a.json', cache_identity: { engine_sha: 'fedcba9876543210', requested_model: 'cached-model' } }, { test: 'tests/b.json', engine_sha: '0123456789abcdef', requested_model: 'live-model' }, { test: 'tests/c.json', cache_identity: 'not an object' }] }, { summary_line: 'Prompt tests: ✓ 2 of 2 criteria' });
  const [mixed] = readRunResults({ root: f.root, since }, { env: f.env, capture: () => { throw Error('no capture'); } });
  assert.deepEqual([mixed.engine, mixed.engineCached, mixed.model, mixed.modelCached], ['0123456789ab', undefined, 'live-model', undefined]);
});
