import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { launcher } from './helpers/environment-launcher-fixture.mjs';
import { environmentHealthy } from '../src/autopilot-environment.mjs';

test('standalone retry checks the supplied checkout volume', async () => {
  const seen = [];
  const ports = { platform: 'linux', cpuCount: () => 4, load: () => 1,
    memory: () => ({ available: 20, total: 100 }), readFile: () => 'some avg10=0.00 total=0',
    suiteAvailable: async () => true,
    statfs: cwd => { seen.push(cwd); return { bavail: cwd === '/checkout' ? 2 : 0, blocks: 20, bsize: 1024 ** 3 }; } };
  assert.equal(await environmentHealthy({ cwd: '/checkout', env: {} }, ports), true);
  assert.deepEqual(seen, ['/checkout']);
});

// #3048 AC8: the timer's working volume can differ from the checkout volume.
test('due validation reuses the tick checkout observation and retains retry restrictions', async t => {
  const f = await launcher(t); await f.start(); f.prompts.length = 0;
  delete f.ports.machineHealth;
  delete f.ports.environmentHealthy;
  const nativeDisks = [], observations = [], tools = [], queues = [];
  assert.notEqual(f.cwd, process.cwd());
  t.mock.method(fs, 'statfsSync', cwd => {
    nativeDisks.push(cwd);
    return { bavail: cwd === f.cwd ? 2 : 0, blocks: 20, bsize: 1024 ** 3 };
  });
  syncBuiltinESMExports();
  t.after(() => { t.mock.restoreAll(); syncBuiltinESMExports(); });
  const resources = { cpuCount: 4, load: 1, memory: { available: 20, total: 100 },
    pressure: { io: 0, memory: 0 }, disk: { available: 2 * 1024 ** 3, total: 20 * 1024 ** 3 } };
  let current, toolPresent, queue;
  f.ports.machineResources = async input => { observations.push(input); return structuredClone(current); };
  f.ports.platform = 'linux';
  f.ports.toolPresent = async tool => { tools.push(tool); return toolPresent; };
  f.ports.readDir = path => { queues.push(path); return queue ? ['ticket-1.json'] : []; };
  f.ports.readFile = () => JSON.stringify({ ticket: 1, pid: 101, cwd: f.cwd, state: 'waiting', queuedAt: 1, startedAt: null, finishedAt: null });
  f.ports.alive = () => true;
  for (const row of [
    { name: 'healthy checkout', expected: 1 },
    { name: 'full CPU load', load: 4, expected: 0 },
    { name: 'I/O pressure', pressure: { io: 10, memory: 0 }, expected: 0 },
    { name: 'memory pressure', pressure: { io: 0, memory: 10 }, expected: 0 },
    { name: 'missing tool', tool: false, expected: 0 },
    { name: 'suite waiter', queue: true, expected: 0 },
    { name: 'recovered checkout', expected: 1 },
  ]) {
    current = { ...resources, load: row.load ?? resources.load, pressure: row.pressure ?? resources.pressure };
    toolPresent = row.tool !== false; queue = row.queue; f.prompts.length = 0;
    f.environmentWaits = [{ number: 12, at: f.time - 60_000, nextAt: f.time, attempts: 0, area: 0, step: 'verify', reason: 'missing tool: node' }];
    await f.tick();
    assert.equal(JSON.parse(readFileSync(f.stateFile(), 'utf8')).health.paused, false, row.name);
    assert.equal(f.rules().filter(rule => rule.kind === 'environment-ready').length, row.expected, row.name);
    f.time += 30 * 60_000;
  }
  assert.deepEqual(observations, Array.from({ length: 7 }, () => ({ cwd: f.cwd })));
  assert.deepEqual(nativeDisks, [], 'retry must not perform a second native disk read');
  assert.deepEqual(tools, ['node', 'node', 'node', 'node']);
  assert.equal(queues.length, 3);
});

// #3048 AC1: malformed protocol input must normalize at the native child boundary.
for (const frame of [null, [], 'synthetic-private', 0, false]) {
  for (const phase of ['initialize', 'account/rateLimits/read']) {
    test(`native account transport returns unknown and stops its child for ${JSON.stringify(frame)} at ${phase}`, t => {
      const dir = mkdtempSync(join(tmpdir(), 'pdd-health-frame-'));
      t.after(() => rmSync(dir, { recursive: true, force: true }));
      const file = join(dir, 'codex'), stopped = join(dir, 'stopped');
      writeFileSync(file, `#!${process.execPath}
const fs = require('node:fs');
const reader = require('node:readline').createInterface({ input: process.stdin });
const keepAlive = setInterval(() => {}, 1000);
process.stdin.on('end', () => clearInterval(keepAlive));
process.on('SIGTERM', () => {
  fs.writeFileSync(${JSON.stringify(stopped)}, 'stopped');
  clearInterval(keepAlive); reader.close(); process.stdin.destroy();
});
reader.on('line', text => {
  const row = JSON.parse(text);
  if (row.method === ${JSON.stringify(phase)}) {
    console.log(${JSON.stringify(JSON.stringify(frame))});
    // A later valid reply cannot erase the preceding protocol error.
    console.log(JSON.stringify({ id: ${phase === 'initialize' ? 1 : 2}, result: ${phase === 'initialize' ? '{}' : '{ rateLimits: { primary: { usedPercent: 4, resetsAt: null } } }'} }));
  }
  else if (row.method === 'initialize') console.log(JSON.stringify({ id: 1, result: {} }));
  else if (row.method === 'account/rateLimits/read') console.log(JSON.stringify({ id: 2, result: { rateLimits: { primary: { usedPercent: 4, resetsAt: null } } } }));
});
`, { mode: 0o755 });
      const code = `import { readCodexLimits } from ${JSON.stringify(new URL('../src/codex-limits.mjs', import.meta.url).href)};
console.log(JSON.stringify(await readCodexLimits({ command: ${JSON.stringify(file)}, cwd: ${JSON.stringify(dir)} })));`;
      const reply = spawnSync(process.execPath, ['--input-type=module', '-e', code], { cwd: dir, encoding: 'utf8', timeout: 15_000 });
      assert.equal(reply.error, undefined, 'transport must finish within its bound');
      assert.equal(reply.status, 0, 'malformed frame must not crash the consumer');
      assert.deepEqual(JSON.parse(reply.stdout), { state: 'unknown', resetAt: null, usedPercent: null });
      assert.equal(reply.stderr, '', 'transport must not expose raw protocol diagnostics');
      assert.equal(readFileSync(stopped, 'utf8'), 'stopped');
    });
  }
}
