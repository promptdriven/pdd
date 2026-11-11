import './helpers/test-home.mjs';
// #3150 (B): a bug run registers its earlier failing check ("fails before the fix") after the prompt changed.
// The saved result is admitted only when the selection at the named local commit hashes to its exact source.
import assert from 'node:assert/strict';
import test from 'node:test';
import { readFileSync, writeFileSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { captureSource } from '../src/runtime-preflight.mjs';
import { renderJson } from '../src/runtime-output.mjs';
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
