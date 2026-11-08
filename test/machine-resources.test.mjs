import test from 'node:test';
import assert from 'node:assert/strict';
import { readMachineResources } from '../src/machine-resources.mjs';
import { machineHealth, environmentHealthy } from '../src/autopilot-environment.mjs';
const GiB = 1024 ** 3;
const resources = { cpuCount: 4, load: 1, memory: { available: GiB, total: 10 * GiB }, pressure: { io: 0, memory: 0 }, disk: { available: GiB, total: 20 * GiB } };

test('shared machine port reports bytes, available disk blocks and Linux available memory', async () => {
  const seen = [];
  const actual = await readMachineResources({ cwd: '/checkout' }, { platform: 'linux', cpuCount: () => 4, load: () => 1,
    readFile: path => path.endsWith('meminfo') ? 'MemTotal: 10485760 kB\nMemAvailable: 1048576 kB\n' : 'some avg10=0.00 avg60=0.00 total=0',
    statfs: path => { seen.push(path); return { bavail: 262144, bfree: 999999, blocks: 5242880, bsize: 4096 }; } });
  assert.deepEqual(actual, resources); assert.deepEqual(seen, ['/checkout']);
});

test('unknown individual observations stay unknown without hiding other metrics', async () => {
  const row = await readMachineResources({ cwd: '/checkout' }, { platform: 'linux', cpuCount: () => 8, load: () => NaN,
    readFile: () => { throw Error('unavailable'); }, statfs: () => { throw Error('unavailable'); } });
  assert.equal(row.cpuCount, 8); assert.equal(row.load, null);
  assert.deepEqual(row.memory, { available: null, total: null }); assert.deepEqual(row.disk, { available: null, total: null });
  assert.deepEqual(row.pressure, { io: null, memory: null });
});

test('bounded resource admission: exact memory, absolute disk and relative disk boundaries', async () => {
  let checked = 0;
  for (const memoryPercent of [0, 9, 10, 11, 100]) for (const diskTotal of [10 * GiB, 20 * GiB, 40 * GiB])
    for (const diskFree of [0, GiB - 1, GiB, GiB + 1, 2 * GiB]) {
      const row = structuredClone(resources); row.memory = { available: memoryPercent, total: 100 }; row.disk = { available: diskFree, total: diskTotal };
      const expected = memoryPercent >= 10 && diskFree >= GiB && diskFree >= diskTotal * 0.05;
      assert.equal((await machineHealth({ cwd: '/checkout' }, { machineResources: async () => row })).healthy, expected,
        JSON.stringify({ memoryPercent, diskTotal, diskFree })); checked++;
    }
  assert.equal(checked, 75);
});

test('health and validation retry share the same machine port and memory decision', async () => {
  let calls = [];
  const ports = { platform: 'linux', machineResources: async input => { calls.push(input); return resources; }, suiteAvailable: async () => true };
  assert.equal((await machineHealth({ cwd: '/checkout' }, ports)).healthy, true);
  assert.equal(await environmentHealthy({}, { ...ports, cwd: '/checkout' }), true);
  assert.deepEqual(calls, [{ cwd: '/checkout' }, { cwd: '/checkout' }]);
  for (const memory of [null, { available: -1, total: 100 }, { available: 101, total: 100 }, { available: 1, total: 0 }, { available: 9, total: 100 }]) {
    const machineResources = async () => ({ ...resources, memory });
    assert.equal((await machineHealth({}, { machineResources })).healthy, false);
    assert.equal(await environmentHealthy({}, { ...ports, machineResources }), false);
  }
});

test('non-Linux fallback uses injected OS memory and no proc files', async () => {
  const row = await readMachineResources({ cwd: '/checkout' }, { platform: 'darwin', cpuCount: () => 2, load: () => 0,
    memory: () => ({ available: 20, total: 100 }), readFile: () => assert.fail('proc read'), statfs: () => ({ bavail: 10, blocks: 100, bsize: 4096 }) });
  assert.deepEqual(row.memory, { available: 20, total: 100 }); assert.deepEqual(row.pressure, { io: null, memory: null });
});
