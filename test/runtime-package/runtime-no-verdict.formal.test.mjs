import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { summaryLine, storyLines } from '../../src/runtime/runtime-output.mjs';

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

function expectedMark(rows) {
  const evidence = new Set(rows.map(row => row.state));
  const candidates = [[0, 'no verdict ·']];
  if (rows.some(row => row.state === 'not_run' && row.busy === true) &&
      rows.every(row => row.state === 'passed' || (row.state === 'not_run' && row.busy === true))) candidates.push([1, 'busy ·']);
  if (evidence.has('queued') || evidence.has('running')) candidates.push([2, 'running ·']);
  if (rows.length && evidence.size === 1 && evidence.has('passed')) candidates.push([3, '✓']);
  if (evidence.has('failed')) candidates.push([4, '✗']);
  return candidates.sort((a, b) => b[0] - a[0])[0][1];
}
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
}

test('NO-VERDICT bounded proof (runtime output): state marks and every Story partition', t => {
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
  t.diagnostic(`${configurations} exhaustive configurations + ${controls} stale-busy controls`);
});
