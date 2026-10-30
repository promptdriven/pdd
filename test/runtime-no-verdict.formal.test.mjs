import test from 'node:test';
import assert from 'node:assert/strict';
import { summaryLine, storyLines, exitCodeFor } from '../src/runtime-output.mjs';

// Approved check-no-verdict Story: finite state-order proof, not a prose check.
// Enumerate all ordered sequences of 0..4 rows over the seven states plus
// confirmed busy/not_run, and ALL identity partitions (restricted-growth labels).
// Four rows allow duplicate rows, overlapping failed/inconclusive Stories and
// multiple independent Stories. Identity names and titles are fixed representatives.
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

// Requirement oracle uses a truth table of evidence classes and their rank.
// A busy flag on refused/unknown is stale metadata, never busy evidence.
function expectedMark(rows) {
  const evidence = new Set(rows.map(row => row.state));
  const candidates = [[0, 'no verdict ·']];
  if (rows.length && rows.every(row => row.state === 'not_run' && row.busy === true)) candidates.push([1, 'busy ·']);
  if (evidence.has('queued') || evidence.has('running')) candidates.push([2, 'running ·']);
  if (rows.length && evidence.size === 1 && evidence.has('passed')) candidates.push([3, '✓']);
  if (evidence.has('failed')) candidates.push([4, '✗']);
  return candidates.sort((a, b) => b[0] - a[0])[0][1];
}
const exitRank = { passed: 0, failed: 1, refused: 2, not_run: 3, unknown: 4, queued: 4, running: 4 };
const codes = [0, 1, 4, 5, 3];
const markOf = line => {
  const match = line.match(/: (✗|✓|running ·|busy ·|no verdict ·) /u);
  assert.ok(match, `summary has a recognized mark: ${line}`);
  return match[1];
};
function checkRows(rows, label) {
  const mark = markOf(summaryLine(rows));
  assert.equal(mark, expectedMark(rows), label);
  assert.equal(mark === '✗', rows.some(row => row.state === 'failed'), `${label}: cross iff judged failure`);
  const identities = [...new Set(rows.map(row => row.story))];
  const lines = storyLines(rows);
  assert.deepEqual(lines.map(([story]) => story), identities, `${label}: one line per identity, first-seen order`);
  for (const [story, line] of lines) {
    const own = rows.filter(row => row.story === story);
    assert.equal(markOf(line), expectedMark(own), `${label}: Story ${story}`);
    assert.equal(markOf(line), markOf(summaryLine(own)), `${label}: Story/overall rule equivalence`);
  }
  const rank = Math.max(0, ...rows.map(row => exitRank[row.state]));
  for (const interrupted of [false, true]) for (const lintUnknown of [false, true]) {
    assert.equal(exitCodeFor(rows, { interrupted, lintUnknown }), interrupted || lintUnknown ? 3 : codes[rank], `${label}: unchanged exit precedence`);
  }
}

test('NO-VERDICT bounded proof: state marks, every Story partition and unchanged exit precedence', t => {
  // Lead with the semantic bug witness so the old-code control detects a false
  // judged-failure mark, rather than stopping at the empty-batch vocabulary.
  checkRows([{ state: 'refused', story: 'refused-witness' }], 'refused is not a judged failure');
  let configurations = 0;
  for (let length = 0; length <= 4; length++) {
    for (const sequence of sequences(length)) for (const labels of partitions(length)) {
      const rows = sequence.map((variant, index) => ({ ...variant, story: `story-${labels[index]}` }));
      checkRows(rows, JSON.stringify(rows));
      configurations++;
    }
  }
  assert.equal(configurations, 64137);
  // Adversarial stale metadata controls: busy cannot mask refused or unknown,
  // alone, with true busy rows, or with passed rows, in either row order.
  let controls = 0;
  for (const state of ['refused', 'unknown']) {
    const stale = { state, busy: true, story: 'stale' };
    for (const companion of [null, { state: 'not_run', busy: true, story: 'other' }, { state: 'passed', story: 'other' }]) {
      for (const rows of companion ? [[stale, companion], [companion, stale]] : [[stale]]) {
        checkRows(rows, `stale busy ${state}`);
        assert.equal(markOf(summaryLine(rows)), 'no verdict ·');
        controls++;
      }
    }
  }
  assert.equal(controls, 10);
  t.diagnostic(`${configurations} exhaustive configurations + ${controls} stale-busy controls; 4 exit-option combinations each`);
});
