import test from 'node:test';
import assert from 'node:assert/strict';
import { EventEmitter } from 'node:events';
import { PassThrough } from 'node:stream';
import { existsSync, mkdtempSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { setImmediate, setTimeout as delay } from 'node:timers/promises';
import { readCodexLimits, parseCodexLimits } from '../src/codex-limits.mjs';
const window = (usedPercent, resetsAt = 1800000000) => ({ usedPercent, resetsAt });
const limits = (primary, secondary = null) => ({ rateLimits: { primary, secondary } });

test('Codex limit normalization handles both windows and explicit reached types without retaining private fields', () => {
  assert.deepEqual(parseCodexLimits(limits(window(99))), { state: 'healthy', resetAt: null, usedPercent: 99 });
  assert.deepEqual(parseCodexLimits(limits(window(100), window(110, 1800000300))), { state: 'limited', resetAt: 1800000300000, usedPercent: 110 });
  assert.deepEqual(parseCodexLimits(limits(window(20), window(100, null))), { state: 'limited', resetAt: null, usedPercent: 100 });
  assert.deepEqual(parseCodexLimits({ rateLimits: { primary: null, secondary: null, rateLimitReachedType: 'usageLimit' }, token: 'synthetic-private' }), { state: 'limited', resetAt: null, usedPercent: null });
  assert.equal(parseCodexLimits({ rateLimits: { primary: window(1) }, rateLimitsByLimitId: { codex: { primary: window(100) } } }).state, 'limited');
  for (const row of [null, {}, limits({ usedPercent: '100' }), limits(window(-1)), limits(window(NaN)), limits(window(100, -1)), limits(window(100, 9e12))])
    assert.deepEqual(parseCodexLimits(row), { state: 'unknown', resetAt: null, usedPercent: null });
});

function fakeServer(reply, { earlyExit = false, badInitialize = false, flood = false, closeOnKill = true } = {}) {
  const calls = [], process = new EventEmitter();
  process.stdin = new PassThrough(); process.stdout = new PassThrough(); process.stderr = new PassThrough();
  const signals = [];
  process.kill = signal => { signals.push(signal); if (closeOnKill) queueMicrotask(() => process.emit('close', 0)); return true; };
  process.stdin.on('data', bytes => {
    for (const line of bytes.toString().trim().split('\n')) {
      const row = JSON.parse(line); calls.push(row);
      queueMicrotask(() => {
        if (earlyExit) { process.emit('close', 1); return; }
        if (flood) { process.stderr.write('x'.repeat(1024 * 1024 + 1)); return; }
        if (row.method === 'initialize') process.stdout.write(JSON.stringify({ id: 1, ...(badInitialize ? { error: { message: 'synthetic-private' } } : { result: {} }) }) + '\n');
        if (row.method === 'account/rateLimits/read') {
          const text = JSON.stringify({ id: 2, result: reply }) + '\n';
          process.stdout.write(text.slice(0, 12)); process.stdout.write(text.slice(12));
        }
      });
    }
  });
  return { calls, process, signals, killed: () => signals.length };
}

test('read-only app-server handshake sends exactly three allowed methods, binds profile and closes child', async () => {
  const f = fakeServer({ ...limits(window(100)), secret: 'synthetic-private', rateLimitResetCredits: { availableCount: 10 } });
  const env = { HOME: '/synthetic', CODEX_HOME: '/synthetic/profile' };
  const result = await readCodexLimits({ command: '/synthetic/codex', cwd: '/checkout', env }, { spawn: (command, args, options) => {
    assert.equal(command, '/synthetic/codex'); assert.deepEqual(args, ['app-server', '--listen', 'stdio://']); assert.equal(options.env, env); return f.process;
  } });
  assert.equal(result.state, 'limited'); assert.equal(f.killed(), 1);
  assert.deepEqual(f.calls.map(row => row.method), ['initialize', 'initialized', 'account/rateLimits/read']);
  assert.equal(JSON.stringify(result).includes('synthetic-private'), false);
});

test('bounded transport refuses startup error, early exit, invalid handshake and excess output', async () => {
  for (const options of [{ earlyExit: true }, { badInitialize: true }, { flood: true }]) {
    const f = fakeServer({}, options);
    assert.equal((await readCodexLimits({}, { spawn: () => f.process })).state, 'unknown');
    assert.equal(f.killed(), options.earlyExit ? 0 : 1);
  }
  assert.equal((await readCodexLimits({}, { spawn: () => { throw Error('synthetic-private'); } })).state, 'unknown');
});

test('transport escalates after 500 milliseconds and still waits for close', async t => {
  t.mock.timers.enable({ apis: ['setTimeout'] });
  const f = fakeServer(limits(window(4)), { closeOnKill: false });
  let settled = false;
  const pending = readCodexLimits({}, { spawn: () => f.process }).then(value => { settled = true; return value; });
  try {
    await setImmediate();
    assert.deepEqual(f.signals, ['SIGTERM']);
    t.mock.timers.tick(499);
    assert.deepEqual(f.signals, ['SIGTERM']);
    t.mock.timers.tick(1);
    assert.deepEqual(f.signals, ['SIGTERM', 'SIGKILL']);
    assert.equal(settled, false);
  } finally {
    f.process.emit('close', 0);
    await pending;
  }
  assert.deepEqual(await pending, { state: 'healthy', resetAt: null, usedPercent: 4 });
  t.mock.timers.tick(10_000);
  assert.deepEqual(f.signals, ['SIGTERM', 'SIGKILL']);
});

test('transport waits for child close before returning a response or failure', async () => {
  for (const options of [{}, { badInitialize: true }, { flood: true }]) {
    const f = fakeServer(limits(window(4)), { ...options, closeOnKill: false });
    let settled = false;
    const pending = readCodexLimits({}, { spawn: () => f.process }).then(value => { settled = true; return value; });
    try {
      await setImmediate();
      assert.equal(f.killed(), 1);
      assert.equal(settled, false, 'result must wait for child close');
    } finally {
      f.process.emit('close', 0);
      await pending;
    }
    assert.deepEqual(await pending, options.badInitialize || options.flood
      ? { state: 'unknown', resetAt: null, usedPercent: null }
      : { state: 'healthy', resetAt: null, usedPercent: 4 });
  }
});

for (const row of [
  { name: 'response', options: {}, expected: { state: 'healthy', resetAt: null, usedPercent: 4 } },
  { name: 'protocol failure', options: { badInitialize: true }, expected: { state: 'unknown', resetAt: null, usedPercent: null } },
  { name: 'exited child with inherited pipes', options: { badInitialize: true }, exited: true, expected: { state: 'unknown', resetAt: null, usedPercent: null } },
]) {
  test(`transport bounds cleanup after ${row.name}`, async t => {
    t.mock.timers.enable({ apis: ['setTimeout'] });
    const f = fakeServer(limits(window(4)), { ...row.options, closeOnKill: false });
    let settled = false, unrefs = 0;
    f.process.unref = () => { unrefs++; };
    const pending = readCodexLimits({}, { spawn: () => f.process }).then(value => { settled = true; return value; });
    try {
      await setImmediate();
      if (row.exited) { f.process.exitCode = 0; f.process.emit('exit', 0); }
      t.mock.timers.tick(999);
      await setImmediate();
      assert.equal(settled, false);
      assert.equal(f.process.stdout.destroyed, false);
      t.mock.timers.tick(1);
      await setImmediate();
      assert.equal(settled, true, 'cleanup must finish without child close');
      assert.deepEqual(await pending, row.expected);
      assert.deepEqual([f.process.stdin, f.process.stdout, f.process.stderr].map(stream => stream.destroyed), [true, true, true]);
      assert.equal(unrefs, 1);
      assert.deepEqual(f.signals, row.exited ? ['SIGTERM'] : ['SIGTERM', 'SIGKILL']);
      const signals = [...f.signals];
      t.mock.timers.tick(10_000);
      assert.deepEqual(f.signals, signals);
    } finally {
      f.process.emit('close', 0);
      await pending;
    }
  });
}

test('transport bounds cleanup after the exchange times out', async t => {
  t.mock.timers.enable({ apis: ['setTimeout'] });
  const f = fakeServer({}, { closeOnKill: false });
  f.process.stdin.removeAllListeners('data');
  let settled = false;
  const pending = readCodexLimits({}, { spawn: () => f.process }).then(value => { settled = true; return value; });
  try {
    t.mock.timers.tick(9_999);
    assert.deepEqual(f.signals, []);
    t.mock.timers.tick(1);
    assert.deepEqual(f.signals, ['SIGTERM']);
    t.mock.timers.tick(1_000);
    await setImmediate();
    assert.equal(settled, true, 'timeout cleanup must finish without child close');
    assert.deepEqual(await pending, { state: 'unknown', resetAt: null, usedPercent: null });
    assert.deepEqual(f.signals, ['SIGTERM', 'SIGKILL']);
  } finally {
    f.process.emit('close', 0);
    await pending;
  }
});

test('native transport finishes while a descendant holds inherited output pipes', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-health-inherited-'));
  const ready = join(dir, 'ready'), release = join(dir, 'release'), stopped = join(dir, 'stopped');
  const file = join(dir, 'codex'), descendant = join(dir, 'descendant.cjs');
  t.after(async () => {
    writeFileSync(release, 'release');
    const deadline = performance.now() + 5_000;
    while (existsSync(ready) && !existsSync(stopped) && performance.now() < deadline) await delay(10);
    assert.equal(existsSync(ready) && !existsSync(stopped), false, 'owned descendant must stop');
    rmSync(dir, { recursive: true, force: true });
  });
  writeFileSync(descendant, `
const fs = require('node:fs');
const stop = () => {
  clearInterval(hold); clearTimeout(safety);
  fs.writeFileSync(${JSON.stringify(stopped)}, 'stopped');
};
const hold = setInterval(() => { if (fs.existsSync(${JSON.stringify(release)})) stop(); }, 10);
const safety = setTimeout(stop, 15000);
fs.writeFileSync(${JSON.stringify(ready)}, 'ready');
process.send('ready');
`);
  writeFileSync(file, `#!${process.execPath}
const { spawn } = require('node:child_process');
const child = spawn(process.execPath, [${JSON.stringify(descendant)}], { stdio: ['ignore', 'inherit', 'inherit', 'ipc'] });
child.once('message', () => {
  child.disconnect(); child.unref();
  process.stdout.write('null\\n');
  process.stdin.destroy();
});
`, { mode: 0o755 });
  const pending = readCodexLimits({ command: file, cwd: dir, env: { HOME: dir, XDG_CONFIG_HOME: dir, PATH: process.env.PATH } });
  let deadline;
  try {
    const result = await Promise.race([pending, new Promise(resolve => { deadline = setTimeout(() => resolve('pending'), 5_000); })]);
    assert.deepEqual(result, { state: 'unknown', resetAt: null, usedPercent: null }, 'inherited pipes must not block the health result');
    assert.equal(existsSync(ready), true);
    assert.equal(existsSync(stopped), false);
  } finally {
    clearTimeout(deadline);
    writeFileSync(release, 'release');
    await pending;
  }
});

test('native fake app-server process reads limits without creating a thread or a turn', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-health-protocol-')); t.after(() => rmSync(dir, { recursive: true, force: true }));
  const file = join(dir, 'codex');
  writeFileSync(file, `#!${process.execPath}\nconst readline=require('node:readline');\nif (process.argv.slice(2).join(' ') !== 'app-server --listen stdio://') process.exitCode=2;\nreadline.createInterface({input:process.stdin}).on('line', text=>{ const row=JSON.parse(text); if (row.method==='initialize') console.log(JSON.stringify({id:1,result:{}})); else if (row.method==='initialized') {} else if (row.method==='account/rateLimits/read') console.log(JSON.stringify({id:2,result:${JSON.stringify(limits(window(100)))}})); else {process.exitCode=3;process.stdin.destroy();} });\n`, { mode: 0o755 });
  const result = await readCodexLimits({ command: file, cwd: dir, env: { HOME: dir, PATH: process.env.PATH } });
  assert.equal(result.state, 'limited'); assert.equal(result.resetAt, 1800000000000);
});

test('#3252 weekly stop line stops secondary window at 97% by default while primary stops at 100%, and spendControlReached stops immediately', async () => {
  assert.deepEqual(parseCodexLimits(limits(window(99), window(96.9, 1800000600))), { state: 'healthy', resetAt: null, usedPercent: 99 });
  assert.deepEqual(parseCodexLimits(limits(window(40), window(97, 1800000600))), { state: 'limited', resetAt: 1800000600000, usedPercent: 97 });
  assert.deepEqual(parseCodexLimits(limits(window(40), window(98.5, 1800000900))), { state: 'limited', resetAt: 1800000900000, usedPercent: 98.5 });
  assert.deepEqual(parseCodexLimits(limits(window(40), window(96, 1800000600)), { weeklyStopPercent: 95 }), { state: 'limited', resetAt: 1800000600000, usedPercent: 96 });
  assert.deepEqual(parseCodexLimits({ rateLimits: { primary: window(10), secondary: window(20, 1800000300), spendControlReached: true } }), { state: 'limited', resetAt: 1800000300000, usedPercent: 20 });
  assert.deepEqual(parseCodexLimits({ rateLimits: { primary: window(10, null), secondary: window(20, null), spendControlReached: true } }), { state: 'limited', resetAt: null, usedPercent: 20 });

  const f = fakeServer(limits(window(12), window(97, 1800001200)));
  const viaTransport = await readCodexLimits({ weeklyStopPercent: 97 }, { spawn: () => f.process });
  assert.deepEqual(viaTransport, { state: 'limited', resetAt: 1800001200000, usedPercent: 97 });

  // OpenAI Pro accounts report their 7-day weekly window in primary (windowDurationMins: 10080) with secondary: null.
  assert.deepEqual(parseCodexLimits({
    rateLimits: {
      planType: 'pro',
      primary: { usedPercent: 97, windowDurationMins: 10080, resetsAt: 1795218173 },
      secondary: null,
      credits: { hasCredits: true },
    },
  }), { state: 'limited', resetAt: 1795218173000, usedPercent: 97 });
  assert.deepEqual(parseCodexLimits({
    rateLimits: {
      planType: 'pro',
      primary: { usedPercent: 96, windowDurationMins: 10080, resetsAt: 1795218173 },
      secondary: null,
      credits: { hasCredits: true },
    },
  }), { state: 'healthy', resetAt: null, usedPercent: 96 });
  assert.deepEqual(parseCodexLimits({
    rateLimits: {
      planType: 'pro',
      primary: { usedPercent: 97, resetsAt: 1795218173 },
      secondary: null,
      credits: { hasCredits: true },
    },
  }), { state: 'limited', resetAt: 1795218173000, usedPercent: 97 });
  assert.deepEqual(parseCodexLimits({
    rateLimits: {
      planType: 'team',
      primary: { usedPercent: 98, windowDurationMins: 300, resetsAt: 1795000000 },
      secondary: { usedPercent: 60, windowDurationMins: 10080, resetsAt: 1795218173 },
    },
  }), { state: 'healthy', resetAt: null, usedPercent: 98 });
});
