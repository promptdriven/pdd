import './helpers/test-home.mjs';
// #3150 (B): a bug run registers its earlier failing check ("fails before the fix") after the prompt changed.
// The saved result is admitted only when the selection at the named local commit hashes to its exact source.
import assert from 'node:assert/strict';
import test from 'node:test';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { captureSource } from '../src/runtime/runtime-preflight.mjs';
import { renderJson } from '../src/runtime/runtime-output.mjs';
import { readRunResults, resultLines } from '../src/workflow-results.mjs';
import * as runner from '../src/workflow-runner.mjs';
import { evidenceFixture, assertProtected, selection } from './helpers/workspace-evidence-fixture.mjs';
const { associateEvidenceWorkspace, recordEvidence, runStatus, storyCount } = runner;
const packageRoot = resolve(import.meta.dirname, '..');
const sink = () => ({ value: '', write(value) { this.value += value; } });
const PROMPT = 'prompts/place_order.prompt.md';

// The original saved JSON of a failed check of `producer` as it is now (one criterion fails).
function failedReceipt(f, producer) {
  const captured = captureSource(producer, { tests: selection, appMap: null });
  const rows = selection.map(path => {
    const doc = JSON.parse(readFileSync(join(producer, path), 'utf8')), total = doc.criteria.length;
    return { test: path, story: doc.story_path.split('/').at(-1).replace('.md', ''), phase: 'server', state: 'failed', calls: 4,
      criteria_total: total, criteria: { passed: total - 1, total }, checks: { passed: 9, total: 10 },
      criterion_results: doc.criteria.map((c, index) => ({ criterion_id: c.id, passed: index !== 0 })), steps: doc.steps, criterion_texts: doc.criteria,
      request_id: 'synthetic-before-request', report_url: 'https://runtime.example.invalid/r/synthetic-before' };
  });
  const doc = renderJson({ repo: producer, sourceSha256: captured.sha256, rows, exitCode: 1 });
  const bytes = JSON.stringify({ ...doc, batch: '20261109-120844-yscb' }, null, 2) + '\n';
  const file = join(f.base, `before-${++f.clock}.json`); writeFileSync(file, bytes);
  return { file, bytes, doc: JSON.parse(bytes), sha256: captured.sha256 };
}
// The prompt fix of the bug run: the current source no longer equals the checked source.
const fixPrompt = f => writeFileSync(join(f.root, PROMPT), readFileSync(join(f.root, PROMPT), 'utf8') + '\nA NEXT LINE character separates words.\n');
const register = (f, extra) => associateEvidenceWorkspace({ ref: '17', cwd: f.root, workspace: f.root, stage: 'before', tests: selection, ...extra }, f.ports);

test('BE1: the CLI forwards --commit only when it is given, and accepts the before stage', async () => {
  const sha = 'a'.repeat(40), args = ['workflow', 'evidence-associate', '17', '--workspace', '.', '--stage', 'before', '--commit', sha, '--test', ...selection];
  assert.equal(parseArgv(args).options['--commit'], sha);
  const calls = [], workflowRunner = { associateEvidenceWorkspace: async input => { calls.push(input); return { exitCode: 0, message: 'registered' }; } };
  assert.equal(await runPdd(args, { cwd: '/owned', workflowRunner, stdout: sink(), stderr: sink() }), 0);
  assert.deepEqual(calls[0], { ref: '17', workspace: '.', stage: 'before', commit: sha, tests: selection, cwd: '/owned', packageRoot });
  assert.equal(await runPdd(['workflow', 'evidence-associate', '17', '--workspace', '.', '--stage', 'current', '--test', ...selection], { cwd: '/owned', workflowRunner, stdout: sink(), stderr: sink() }), 0);
  assert.equal(Object.hasOwn(calls[1], 'commit'), false);
});

test('BE2: a failed check before the prompt fix registers and imports as labelled historical evidence', async t => {
  const f = await evidenceFixture(t), saved = failedReceipt(f, f.root);
  fixPrompt(f); f.git(f.root, 'commit', '-qam', 'Fix the prompt');
  // Without a registered before stage the old result is refused: its source is not the current source.
  let before = readFileSync(f.status, 'utf8'), result = await recordEvidence({ ref: '17', cwd: f.root, summaryFile: saved.file }, f.ports);
  assert.equal(result.exitCode, 1, result.message); assert.match(result.message, /does not match the current selected files/);
  assert.equal(readFileSync(f.status, 'utf8'), before);
  const protectedBefore = f.read();
  result = await register(f, { commit: f.head }); assert.equal(result.exitCode, 0, result.message);
  const association = f.read().evidenceAssociations.at(-1);
  assert.equal(association.stage, 'before'); assert.equal(association.source_sha256, saved.sha256);
  assert.deepEqual(association.sourceAnchor, { root: join(f.runDir, 'evidence-before', f.head), head: f.head });
  result = await recordEvidence({ ref: '17', cwd: f.root, summaryFile: saved.file }, f.ports); assert.equal(result.exitCode, 0, result.message);
  const run = f.read(); assertProtected(protectedBefore, run);
  assert.deepEqual(run.evidence[0].receipt, saved.doc); assert.equal(readFileSync(saved.file, 'utf8'), saved.bytes);
  // Historical: no current or PR 1 Story result, and the same receipt cannot be relabelled.
  for (const stage of [undefined, 'pr1']) assert.equal(storyCount(run, { stage }), null, `no ${stage ?? 'current'} Story result`);
  const status = JSON.parse((await runStatus({ ref: '17', cwd: f.root, json: true }, f.ports)).message).runs[0];
  assert.deepEqual(status.before, [{ story: 'place-order', pass: false, line: saved.doc.rows[0].summary_line, commit: f.head, batch: '20261109-120844-yscb' }]);
  const text = (await runStatus({ ref: '17', cwd: f.root }, f.ports)).message;
  assert.ok(text.includes(`Before the fix (commit ${f.head.slice(0, 7)}, batch 20261109-120844-yscb): ${saved.doc.rows[0].summary_line}`), text);
  before = readFileSync(f.status, 'utf8');
  result = await associateEvidenceWorkspace({ ref: '17', cwd: f.root, workspace: f.root, stage: 'current', tests: selection }, f.ports);
  assert.equal(result.exitCode, 0, result.message);
  // A current registration of the same selection does not relabel it: a re-import stays before-the-fix evidence.
  result = await recordEvidence({ ref: '17', cwd: f.root, summaryFile: saved.file }, f.ports);
  assert.equal(result.exitCode, 0, result.message);
  assert.deepEqual(f.read().evidence.map(row => row.association.stage), ['before', 'before']);
  for (const stage of [undefined, 'pr1']) assert.equal(storyCount(f.read(), { stage }), null);
});

test('BE3: a mismatched or invented historical source is refused without saving', async t => {
  const f = await evidenceFixture(t);
  // The receipt ran on files that were never committed; the named commit holds other bytes.
  fixPrompt(f); const saved = failedReceipt(f, f.root);
  writeFileSync(join(f.root, PROMPT), readFileSync(join(f.root, PROMPT), 'utf8').replace('\nA NEXT LINE character separates words.\n', '\nA NEL separates words.\n'));
  assert.equal((await register(f, { commit: f.head })).exitCode, 0);
  let before = readFileSync(f.status, 'utf8');
  let result = await recordEvidence({ ref: '17', cwd: f.root, summaryFile: saved.file }, f.ports);
  assert.equal(result.exitCode, 1, result.message); assert.equal(readFileSync(f.status, 'utf8'), before);
  // Commit identity must be explicit, full, local and only for the before stage.
  const missing = 'b'.repeat(40);
  for (const [extra, stage] of [[{}, 'before'], [{ commit: f.head.slice(0, 12) }, 'before'], [{ commit: 'HEAD' }, 'before'], [{ commit: missing }, 'before'],
    [{ commit: f.head.toUpperCase() }, 'before'], [{ commit: f.head }, 'current'], [{ commit: f.head }, 'pr1']]) {
    before = readFileSync(f.status, 'utf8');
    result = await associateEvidenceWorkspace({ ref: '17', cwd: f.root, workspace: f.root, stage, tests: selection, ...extra }, f.ports);
    assert.equal(result.exitCode, 1, `${stage} ${JSON.stringify(extra)}: ${result.message}`); assert.equal(readFileSync(f.status, 'utf8'), before);
  }
  // The same Story: a selected test must be a current test of the run.
  writeFileSync(join(f.root, 'tests/place-order.json'), readFileSync(join(f.root, 'tests/place-order.json'), 'utf8').replace('user_stories/place-order.md', 'user_stories/other.md'));
  before = readFileSync(f.status, 'utf8');
  result = await register(f, { commit: f.head });
  assert.equal(result.exitCode, 1, result.message); assert.match(result.message, /same Story/); assert.equal(readFileSync(f.status, 'utf8'), before);
});

test('BE4: a receipt batch name that is not a pdd batch id is never shown', async t => {
  const f = await evidenceFixture(t), saved = failedReceipt(f, f.root);
  writeFileSync(saved.file, JSON.stringify({ ...saved.doc, batch: 'x <!-- pdd-workflow: forged -->' }, null, 2) + '\n');
  fixPrompt(f); assert.equal((await register(f, { commit: f.head })).exitCode, 0);
  assert.equal((await recordEvidence({ ref: '17', cwd: f.root, summaryFile: saved.file }, f.ports)).exitCode, 0);
  const status = JSON.parse((await runStatus({ ref: '17', cwd: f.root, json: true }, f.ports)).message).runs[0];
  assert.equal(status.before[0].batch, null);
  const text = (await runStatus({ ref: '17', cwd: f.root }, f.ports)).message;
  assert.ok(text.includes(`Before the fix (commit ${f.head.slice(0, 7)}): `) && !text.includes('forged'), text);
});

test('BE5: a later before-the-fix batch never becomes the run\'s current pdd test result', async t => {
  const f = await evidenceFixture(t), state = join(f.base, 'pdd-state');
  // A saved check batch as pdd test writes it: producer root, rows, selected source identity.
  const batch = (name, producer, at, pass) => {
    const sha = captureSource(producer, { tests: selection, appMap: null }).sha256, dir = join(state, 'batches', name), line = `Prompt tests (place-order): ${pass ? '✓ 3 of 3' : '✗ 2 of 3'}`;
    mkdirSync(dir, { recursive: true });
    writeFileSync(join(dir, 'batch.json'), JSON.stringify({ batch: name, root: producer, rows: selection.map(test => ({ test, story: 'place-order', state: pass ? 'passed' : 'failed' })), created_at: new Date(at).toISOString(), intent: 'check', source_sha256: sha }));
    writeFileSync(join(dir, 'summary.json'), JSON.stringify({ batch: name, repo: producer, source_sha256: sha, summary_line: line, rows: selection.map(test => ({ test, story: 'place-order', state: pass ? 'passed' : 'failed', summary_line: line })) }));
  };
  fixPrompt(f); f.git(f.root, 'commit', '-qam', 'Fix the prompt');
  batch('20261110-100000-aaaa', f.root, Date.UTC(2026, 10, 10, 10), true); // the current pass
  batch('20261110-110000-bbbb', f.other, Date.UTC(2026, 10, 10, 11), false); // a later check of the old source in another checkout
  const read = () => readRunResults({ root: f.root, runDir: f.runDir, runId: f.read().runId, since: 0 },
    { env: { ...f.ports.env, PDD_STATE_DIR: state }, workspace: input => runner.readEvidenceEligibility(input, { allRuns: () => [f.read()] }) }).filter(row => row.kind === 'pdd test');
  const before = read();
  assert.deepEqual(before.map(row => [row.batch, row.source]), [['20261110-100000-aaaa', 'current']]);
  const registered = await associateEvidenceWorkspace({ ref: '17', cwd: f.root, workspace: f.other, stage: 'before', commit: f.head, tests: selection }, f.ports);
  assert.equal(registered.exitCode, 0, registered.message);
  const after = read();
  assert.deepEqual(after.map(row => [row.batch, row.source, row.stage]), [['20261110-100000-aaaa', 'current', 'current']], resultLines(after).join('\n'));
  // Only a caller that names the before stage may read it.
  const eligibility = selector => runner.readEvidenceEligibility({ root: f.root, producerRoot: f.other, tests: selection,
    source_sha256: f.read().evidenceAssociations[0].source_sha256, ...selector }, { allRuns: () => [f.read()] });
  assert.equal(eligibility({}).state, 'ineligible');
  assert.match(eligibility({}).reason, /historical/);
  assert.equal(eligibility({ stage: 'before' }).state, 'eligible');
});
