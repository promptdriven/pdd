import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { exitCodeFor } from '../src/runtime-seam.mjs';

const variants = [
  { state: 'passed' }, { state: 'failed' }, { state: 'refused' },
  { state: 'not_run' }, { state: 'unknown' }, { state: 'queued' },
  { state: 'running' }, { state: 'not_run', busy: true }
];
function* sequences(length, prefix = []) {
  if (!length) { yield prefix; return; }
  for (const variant of variants) yield* sequences(length - 1, [...prefix, variant]);
}
function* partitions(length, prefix = []) {
  if (prefix.length === length) { yield prefix; return; }
  const maximum = prefix.length ? Math.max(...prefix) + 1 : 0;
  for (let label = 0; label <= maximum; label++) yield* partitions(length, [...prefix, label]);
}

const exitRank = { passed: 0, failed: 1, refused: 2, not_run: 3, unknown: 4, queued: 4, running: 4 };
const codes = [0, 1, 4, 5, 3];
function checkExit(rows, label) {
  const rank = Math.max(0, ...rows.map(row => exitRank[row.state]));
  for (const interrupted of [false, true]) for (const lintUnknown of [false, true]) {
    assert.equal(exitCodeFor(rows, { interrupted, lintUnknown }), interrupted || lintUnknown || !rows.length ? 3 : codes[rank], `${label}: unchanged exit precedence`);
  }
}

test('NO-VERDICT bounded proof (host exit mapping): unchanged exit precedence across every Story partition and stale-busy control', t => {
  checkExit([{ state: 'refused', story: 'refused-witness' }], 'refused is not a judged failure');
  let configurations = 0;
  for (let length = 0; length <= 4; length++) {
    for (const sequence of sequences(length)) for (const labels of partitions(length)) {
      const rows = sequence.map((variant, index) => ({ ...variant, story: `story-${labels[index]}` }));
      checkExit(rows, JSON.stringify(rows));
      configurations++;
    }
  }
  assert.equal(configurations, 64137);
  let controls = 0;
  for (const state of ['refused', 'unknown']) {
    const stale = { state, busy: true, story: 'stale' };
    for (const companion of [null, { state: 'not_run', busy: true, story: 'other' }, { state: 'passed', story: 'other' }]) {
      for (const rows of companion ? [[stale, companion], [companion, stale]] : [[stale]]) {
        checkExit(rows, `stale busy ${state}`);
        controls++;
      }
    }
  }
  assert.equal(controls, 10);
  t.diagnostic(`${configurations} exhaustive configurations + ${controls} stale-busy controls; 4 exit-option combinations each`);
});
