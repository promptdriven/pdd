import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, mkdtempSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { readRunResults, resultLines, noResultLine } from '../src/workflow-results.mjs';

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

test('2904: reads this run\'s prove record only, and says pdd:no-verdict when there is no result', t => {
  const f = folders(t);
  assert.deepEqual(readRunResults({ root: f.root, runDir: f.runDir, runId: 'run-1', since }, { env: f.env }), []);
  assert.deepEqual(resultLines([]), [noResultLine()]);
  assert.equal(noResultLine(['pdd test', 'pdd lint']), 'pdd result: none. pdd has no pdd test or pdd lint result of its own for this run (pdd:no-verdict).');
  writeFileSync(join(f.runDir, 'old-code-proof.json'), JSON.stringify({ runId: 'other', outcome: 'proved' }));
  assert.deepEqual(readRunResults({ root: f.root, runDir: f.runDir, runId: 'run-1', since }, { env: f.env }), []);
  writeFileSync(join(f.runDir, 'old-code-proof.json'), JSON.stringify({ runId: 'run-1', outcome: 'proved', headSha: 'c'.repeat(40) }));
  const [proof] = readRunResults({ root: f.root, runDir: f.runDir, runId: 'run-1', since }, { env: f.env });
  assert.equal(proof.kind, 'pdd workflow prove');
  assert.match(resultLines([proof])[0], /^pdd result: pdd workflow prove \(\d{4}-\d\d-\d\dT[\d:]+Z, head ccccccc\): Old-code proof: proved$/);
  assert.deepEqual(resultLines([proof], { kinds: ['pdd test'] }), ['pdd result: none. pdd has no pdd test result of its own for this run (pdd:no-verdict).']);
});
