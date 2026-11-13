// Generated from prompts/cli/process-lifecycle.prompt.md (sha256: 633979f76a75c5eafe13c915d6c0982e6f71ea2125afa24fb03a8bf80be6da83).
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

test('re-reads a target immediately before TERM and leaves a reused PID alone', async () => {
  const signals = [], reused = { ...rows[1], start: 'Mon Nov 11 11:00:01 2026' };
  let calls = 0;
  const result = await terminateCaptured([rows[1]], { list: async () => ++calls === 2 ? [reused] : [rows[1]],
    signal: (...args) => signals.push(args), sleep: async () => {}, grace: 1, poll: 1 });
  assert.equal(calls, 2); assert.equal(result.confirmed, true); assert.deepEqual(signals, []);
});

test('re-reads a target immediately before KILL and leaves a reused PID alone', async () => {
  const signals = [], reused = { ...rows[1], start: 'Mon Nov 11 11:00:01 2026' };
  let calls = 0;
  const result = await terminateCaptured([rows[1]], { list: async () => ++calls === 4 ? [reused] : [rows[1]],
    signal: (...args) => signals.push(args), sleep: async () => {}, grace: 1, poll: 1 });
  assert.equal(calls, 4); assert.equal(result.confirmed, true); assert.deepEqual(signals, [[rows[1].pid, 'SIGTERM']]);
});

test('keeps cleanup uncertain when a pre-KILL inventory is missing or incomplete', async t => {
  await t.test('missing inventory', async () => {
    let calls = 0; const signals = [];
    const result = await terminateCaptured([rows[1]], { list: async () => ++calls === 4 ? null : [rows[1]],
      signal: (...args) => signals.push(args), sleep: async () => {}, grace: 1, poll: 1 });
    assert.equal(result.confirmed, false); assert.equal(result.remaining, 1);
    assert.deepEqual(signals, [[rows[1].pid, 'SIGTERM']]);
  });
  await t.test('incomplete inventory', async () => {
    let calls = 0; const signals = [], incomplete = [rows[1]];
    Object.defineProperty(incomplete, 'incomplete', { value: true });
    const result = await terminateCaptured([rows[1]], { list: async () => ++calls === 4 ? incomplete : [rows[1]],
      signal: (...args) => signals.push(args), sleep: async () => {}, grace: 1, poll: 1 });
    assert.equal(result.confirmed, false); assert.equal(result.remaining, 1);
    assert.deepEqual(signals, [[rows[1].pid, 'SIGTERM']]);
  });
});

test('keeps a same-start process with a changed command when it changes before TERM or KILL', async t => {
  const changed = { ...rows[1], args: 'node helper changed' };
  await t.test('before TERM', async () => {
    let calls = 0; const signals = [];
    const result = await terminateCaptured([rows[1]], { list: async () => ++calls === 2 ? [changed] : [rows[1]],
      signal: (...args) => signals.push(args), sleep: async () => {}, grace: 1, poll: 1 });
    assert.equal(result.confirmed, false); assert.equal(result.remaining, 1); assert.deepEqual(signals, []);
  });
  await t.test('before KILL', async () => {
    let calls = 0; const signals = [];
    const result = await terminateCaptured([rows[1]], { list: async () => ++calls === 4 ? [changed] : [rows[1]],
      signal: (...args) => signals.push(args), sleep: async () => {}, grace: 1, poll: 1 });
    assert.equal(result.confirmed, false); assert.equal(result.remaining, 1); assert.deepEqual(signals, [[rows[1].pid, 'SIGTERM']]);
  });
});

test('keeps a same-start process with changed command for retry', async () => {
  const signals = [], changed = { ...rows[1], args: 'node helper changed' };
  const result = await terminateCaptured([rows[1]], { list: async () => [changed], signal: (...args) => signals.push(args), sleep: async () => {}, grace: 1, poll: 1 });
  assert.equal(result.confirmed, false); assert.deepEqual(signals, []);
});

test('signals a captured child process group (-pgid) with SIGTERM then SIGKILL, even after its leader exited, and skips reused leader PIDs', async t => {
  const leader = rows[1], stubbornGrandchild = { pid: 19, ppid: 1, pgid: leader.pgid, rss: 20, start: 'Mon Nov 11 10:00:05 2026', args: 'node value.mjs stubborn' };
  await t.test('leader exited leaving a SIGTERM-ignoring grandchild in the group', async () => {
    let active = [stubbornGrandchild]; const signals = [];
    const result = await terminateCaptured([leader], { list: async () => active,
      signal: (target, sig) => { signals.push([target, sig]); if (target === -leader.pgid && sig === 'SIGKILL') active = []; },
      sleep: async () => {}, grace: 1, poll: 1 });
    assert.deepEqual(result, { confirmed: true, stopped: 1, killed: 1, remaining: 0 });
    assert.deepEqual(signals, [[-leader.pgid, 'SIGTERM'], [-leader.pgid, 'SIGKILL']]);
  });
  await t.test('reused leader PID is never group-signalled', async () => {
    const reusedLeader = { ...leader, start: 'Mon Nov 11 11:30:00 2026', args: 'node other-tenant' };
    const signals = [];
    const result = await terminateCaptured([leader], { list: async () => [reusedLeader],
      signal: (...args) => signals.push(args), sleep: async () => {}, grace: 1, poll: 1 });
    assert.equal(result.confirmed, true);
    assert.deepEqual(signals, []);
  });
});
