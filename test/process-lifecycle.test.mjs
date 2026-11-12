// Generated from prompts/cli/process-lifecycle.prompt.md (sha256: de04fa68ad1a4008e5a1558f65bb0a37d627643318e5d30ca12102d60edaa091).
import test from 'node:test';
import assert from 'node:assert/strict';
import { descendants, parseProcessTable, terminateCaptured } from '../src/process-lifecycle.mjs';

const rows = parseProcessTable([
  '  10  1  10  20 Mon Nov 11 10:00:00 2026 node wrapper spec.json',
  '  11 10  11  20 Mon Nov 11 10:00:01 2026 node helper /run',
  '  12 11  11  20 Mon Nov 11 10:00:02 2026 node child /run',
  '  13  1  13  20 Mon Nov 11 10:00:03 2026 node unrelated'
].join('\n'));

test('captures descendants while their wrapper still links them', () => {
  assert.deepEqual(descendants(rows, [rows[0]]).map(row => row.pid), [10, 11, 12]);
});

test('rechecks start identity before every signal and leaves PID reuse alone', async () => {
  const signals = [], reused = { ...rows[1], start: 'Mon Nov 11 11:00:01 2026' };
  const result = await terminateCaptured([rows[1]], { list: async () => [reused], signal: (...args) => signals.push(args), sleep: async () => {}, grace: 1, poll: 1 });
  assert.equal(result.confirmed, true); assert.deepEqual(signals, []);
});

test('keeps a same-start process with changed command for retry', async () => {
  const signals = [], changed = { ...rows[1], args: 'node helper changed' };
  const result = await terminateCaptured([rows[1]], { list: async () => [changed], signal: (...args) => signals.push(args), sleep: async () => {}, grace: 1, poll: 1 });
  assert.equal(result.confirmed, false); assert.deepEqual(signals, []);
});
