import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { summaryLine } from '../src/runtime/runtime-output.mjs';

const states = ['passed', 'failed', 'queued', 'running', 'refused', 'not_run', 'unknown'];
const choices = states.flatMap(state => [false, true].map(busy => ({ state, busy, story: 'one' })));
function expected(rows) {
  if (rows.some(row => row.state === 'failed')) return '✗';
  if (rows.length && rows.every(row => row.state === 'passed')) return '✓';
  if (rows.some(row => ['queued', 'running'].includes(row.state))) return 'running ·';
  if (rows.some(row => row.state === 'not_run' && row.busy) && rows.every(row => row.state === 'passed' || (row.state === 'not_run' && row.busy))) return 'busy ·';
  return 'no verdict ·';
}
test('bounded Story rule: summary mark precedence for zero, one and two rows', () => {
  for (const rows of [[], ...choices.map(x => [x]), ...choices.flatMap(x => choices.map(y => [x, y]))]) {
    for (const story of [null, 'one']) assert.ok(summaryLine(rows, story).includes(`: ${expected(rows)} `), JSON.stringify({ rows, story, line: summaryLine(rows, story) }));
  }
});
