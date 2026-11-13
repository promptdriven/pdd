import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { PROMPT_TESTS_LABEL } from '../src/prompt-tests-words.mjs';
import { summaryLine } from '../src/runtime-seam.mjs';

const states = ['passed', 'failed', 'queued', 'running', 'refused', 'not_run', 'unknown'];
const choices = states.flatMap(state => [false, true].map(busy => ({ state, busy, story: 'one' })));
function expected(rows) {
  if (rows.some(row => row.state === 'failed')) return '✗';
  if (rows.length && rows.every(row => row.state === 'passed')) return '✓';
  if (rows.some(row => ['queued', 'running'].includes(row.state))) return 'running ·';
  if (rows.some(row => row.state === 'not_run' && row.busy) && rows.every(row => row.state === 'passed' || (row.state === 'not_run' && row.busy))) return 'busy ·';
  return 'no verdict ·';
}
test('bounded Story rule (host seam): summary mark precedence and Prompt tests label for zero, one and two rows', () => {
  for (const rows of [[], ...choices.map(x => [x]), ...choices.flatMap(x => choices.map(y => [x, y]))]) {
    for (const story of [null, 'one']) {
      const line = summaryLine(rows, story);
      assert.ok(line.startsWith(PROMPT_TESTS_LABEL), line);
      assert.ok(line.includes(`: ${expected(rows)} `), JSON.stringify({ rows, story, line }));
    }
  }
});
