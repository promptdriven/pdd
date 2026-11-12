import test from 'node:test';
import assert from 'node:assert/strict';
import { EventEmitter } from 'node:events';
import { PassThrough } from 'node:stream';
import { setImmediate } from 'node:timers/promises';
import { readCodexRateLimitsReply } from '../src/codex-limits.mjs';

// A fake app-server child. `answer(row)` returns the text lines to write for one request.
function fakeChild(answer, { closeOnKill = true } = {}) {
  const child = new EventEmitter();
  child.stdin = new PassThrough(); child.stdout = new PassThrough(); child.stderr = new PassThrough();
  child.exitCode = null; child.signalCode = null;
  const sent = [], signals = [];
  child.kill = signal => { signals.push(signal); if (closeOnKill) queueMicrotask(() => child.emit('close', 0)); return true; };
  child.stdin.on('data', bytes => {
    for (const line of bytes.toString().trim().split('\n')) {
      const row = JSON.parse(line); sent.push(row);
      queueMicrotask(() => { for (const text of answer(row, child) ?? []) child.stdout.write(text); });
    }
  });
  return { child, sent, signals };
}
const ok = result => row => row.method === 'initialize' ? [JSON.stringify({ id: 1, result: {} }) + '\n']
  : row.method === 'account/rateLimits/read' ? [JSON.stringify({ id: 2, result }) + '\n'] : [];

test('the transport returns the raw read reply and sends only the three read-only methods', async () => {
  const reply = { rateLimits: { primary: { usedPercent: 5, windowDurationMins: 300, resetsAt: 1800000000 } }, accountId: 'acct-fake' };
  const f = fakeChild(ok(reply));
  let spawned;
  const result = await readCodexRateLimitsReply({ command: '/fake/codex', cwd: '/fake/home', env: { CODEX_HOME: '/fake/home' } },
    { spawn: (command, args, options) => { spawned = { command, args, cwd: options.cwd, env: options.env, shell: options.shell }; return f.child; } });
  assert.deepEqual(result, { ok: true, reply });
  assert.deepEqual(spawned, { command: '/fake/codex', args: ['app-server', '--listen', 'stdio://'], cwd: '/fake/home', env: { CODEX_HOME: '/fake/home' }, shell: false });
  assert.deepEqual(f.sent.map(row => row.method), ['initialize', 'initialized', 'account/rateLimits/read']);
  assert.deepEqual(f.sent[0].params, { clientInfo: { name: 'pdd_health', title: 'PDD health', version: '1' } });
  assert.equal('params' in f.sent[2], false);
  assert.deepEqual(f.signals, ['SIGTERM']);
});

test('a caller can name its own client', async () => {
  const f = fakeChild(ok({}));
  const clientInfo = { name: 'pdd_accounts', title: 'PDD accounts', version: '1' };
  await readCodexRateLimitsReply({ clientInfo }, { spawn: () => f.child });
  assert.deepEqual(f.sent[0].params, { clientInfo });
});

test('each failure gives one safe reason and never the raw text', async () => {
  const cases = [
    ['spawn', () => { throw new Error('fake-private spawn'); }],
    ['spawn', () => { const f = fakeChild(() => []); queueMicrotask(() => f.child.emit('error', new Error('fake-private'))); return f.child; }],
    ['exit', () => fakeChild((row, child) => { child.emit('close', 1); return []; }).child],
    ['error', () => fakeChild(row => [JSON.stringify({ id: 1, error: { message: 'fake-private' } }) + '\n']).child],
    ['protocol', () => fakeChild(row => [JSON.stringify({ id: 1, result: [] }) + '\n']).child],
    ['protocol', () => fakeChild(row => ['not json fake-private\n']).child],
    ['protocol', () => fakeChild(row => ['[1]\n']).child],
    ['error', () => fakeChild(row => row.method === 'initialize' ? [JSON.stringify({ id: 1, result: {} }) + '\n']
      : row.method === 'account/rateLimits/read' ? [JSON.stringify({ id: 2, error: { message: 'fake-private' } }) + '\n'] : []).child],
    ['output', () => fakeChild((row, child) => { child.stderr.write('x'.repeat(1024 * 1024 + 1)); return []; }).child],
  ];
  for (const [reason, spawn] of cases) {
    const result = await readCodexRateLimitsReply({}, { spawn });
    assert.deepEqual(result, { ok: false, reason }, reason);
    assert.equal(JSON.stringify(result).includes('fake-private'), false);
  }
});

test('no reply in 10 seconds is a timeout', async t => {
  t.mock.timers.enable({ apis: ['setTimeout'] });
  const f = fakeChild(() => []);
  const pending = readCodexRateLimitsReply({}, { spawn: () => f.child });
  await setImmediate();
  t.mock.timers.tick(9_999);
  assert.deepEqual(f.signals, []);
  t.mock.timers.tick(1);
  assert.deepEqual(await pending, { ok: false, reason: 'timeout' });
  assert.deepEqual(f.signals, ['SIGTERM']);
});
