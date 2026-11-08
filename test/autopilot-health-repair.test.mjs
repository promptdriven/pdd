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
      const code = `import { spawn } from 'node:child_process';
import { readCodexLimits } from ${JSON.stringify(new URL('../src/codex-limits.mjs', import.meta.url).href)};
let child, close;
const closed = new Promise(resolve => { close = resolve; });
const result = await readCodexLimits({ command: ${JSON.stringify(file)}, cwd: ${JSON.stringify(dir)} }, {
  spawn: (...args) => { child = spawn(...args); child.once('close', (code, signal) => close({ code, signal })); return child; }
});
const termination = await Promise.race([closed, new Promise(resolve => setTimeout(() => resolve(null), 3000).unref())]);
if (!termination) child.kill('SIGKILL');
console.log(JSON.stringify({ result, termination }));`;
      const reply = spawnSync(process.execPath, ['--input-type=module', '-e', code], { cwd: dir, encoding: 'utf8', timeout: 15_000 });
      assert.equal(reply.error, undefined, 'transport must finish within its bound');
      assert.equal(reply.status, 0, 'malformed frame must not crash the consumer');
      const { result, termination } = JSON.parse(reply.stdout);
      assert.deepEqual(result, { state: 'unknown', resetAt: null, usedPercent: null });
      assert.deepEqual(termination, { code: 0, signal: null }, 'child must close after SIGTERM');
      assert.equal(reply.stderr, '', 'transport must not expose raw protocol diagnostics');
      assert.equal(readFileSync(stopped, 'utf8'), 'stopped');
    });
  }
}


test('native account transport escalates when the child ignores SIGTERM', t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-health-escalation-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const file = join(dir, 'codex');
  writeFileSync(file, `#!${process.execPath}
process.on('SIGTERM', () => {});
setInterval(() => {}, 1000);
process.stdin.once('data', () => console.log('[]'));
`, { mode: 0o755 });
  const code = `import { spawn } from 'node:child_process';
import { readCodexLimits } from ${JSON.stringify(new URL('../src/codex-limits.mjs', import.meta.url).href)};
let child, close;
const closed = new Promise(resolve => { close = resolve; });
const result = await readCodexLimits({ command: ${JSON.stringify(file)}, cwd: ${JSON.stringify(dir)} }, {
  spawn: (...args) => { child = spawn(...args); child.once('close', (code, signal) => close({ code, signal })); return child; }
});
const termination = await Promise.race([closed, new Promise(resolve => setTimeout(() => resolve(null), 3000).unref())]);
if (!termination) child.kill('SIGKILL');
console.log(JSON.stringify({ result, termination }));`;
  const reply = spawnSync(process.execPath, ['--input-type=module', '-e', code], { cwd: dir, encoding: 'utf8', timeout: 15_000 });
  assert.equal(reply.error, undefined, 'transport and child cleanup must finish within the bound');
  assert.equal(reply.status, 0);
  assert.equal(reply.stderr, '');
  assert.deepEqual(JSON.parse(reply.stdout), {
    result: { state: 'unknown', resetAt: null, usedPercent: null },
    termination: { code: null, signal: 'SIGKILL' },
  });
});

// Release integration: #3048 and #3067 must use the same tick sample.
test('release: one machine observation controls health and check capacity', async t => {
  const f = await launcher(t); await f.start(); delete f.ports.machineHealth;
  let reads = 0;
  const resources = {cpuCount:48,load:0,memory:{available:32*1024**3,total:64*1024**3},
    pressure:{io:0,memory:0},disk:{available:8*1024**3,total:64*1024**3},
    check:{cpuIds:Array.from({length:48},(_,i)=>i+4),platform:'linux',battery:false,virtualized:true,taskset:'/fake/taskset'}};
  f.ports.machineResources = async input => { reads++; assert.deepEqual(input,{cwd:f.cwd}); return resources; };
  for (const name of ['cores','memory','load','battery','virtualized','taskset'])
    f.ports.checkCapacityPorts[name] = () => assert.fail('duplicate native observation');
  await f.tick();
  const state = JSON.parse(readFileSync(f.stateFile(),'utf8'));
  assert.equal(reads,1);
  assert.equal(state.health.paused,false);
  assert.deepEqual([state.checkCapacity.cores,state.checkCapacity.checks,state.checkCapacity.coresPerCheck],[48,4,12]);
  assert.deepEqual(state.checkCapacity.cpuIds,resources.check.cpuIds);
});
