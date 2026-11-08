import test from 'node:test';
import assert from 'node:assert/strict';
import { environmentHealthy } from '../src/autopilot-environment.mjs';
const good = { cpuCount: () => 4, load: () => 1, memory: () => ({ available: 20, total: 100 }), platform: 'linux',
  readFile: () => 'some avg10=0.00 avg60=0.00 total=0', suiteAvailable: async () => true };
const check = (ports = {}, reason = '') => environmentHealthy({ env: {}, reason }, { ...good, ...ports });
test('load, available memory and I/O/memory pressure enforce exact health limits', async () => {
  assert.equal(await check(), true);
  for (const ports of [{ load: () => 4 }, { load: () => NaN }, { cpuCount: () => 0 }, { memory: () => ({ available: 9, total: 100 }) },
    { readFile: () => 'some avg10=10.00 total=0' }, { readFile: () => '' }, { readFile: () => { throw Error('EACCES'); } },
    { readFile: path => path.endsWith('/memory') ? 'some avg10=11 total=0' : good.readFile() }]) assert.equal(await check(ports), false);
  assert.equal(await check({ memory: () => ({ available: 10, total: 100 }) }), true);
});
test('a missing tool retries only after that named executable is present', async () => {
  const tools = [];
  assert.equal(await check({ toolPresent: async tool => { tools.push(tool); return false; } }, 'missing tool: node'), false);
  assert.equal(await check({ toolPresent: async tool => { tools.push(tool); return true; } }, 'missing tool: node'), true);
  assert.deepEqual(tools, ['node', 'node']);
  assert.equal(await check({}, 'missing tool'), false);
});
test('shared suite queue permits capacity, blocks waiters/full/malformed/unreadable ownership and needs no installation', async () => {
  let rows = [];
  const readFile = path => path.startsWith('/proc/') ? good.readFile() : JSON.stringify(rows.find(row => path.endsWith(`ticket-${row.ticket}.json`)));
  const p = { ...good, suiteAvailable: undefined, readFile, readDir: () => rows.map(row => `ticket-${row.ticket}.json`) };
  const run = env => environmentHealthy({ env: env ?? { PDD_SUITE_QUEUE: '/synthetic/queue' } }, p);
  const row = (ticket, state) => ({ ticket, pid: 100 + ticket, cwd: '/project', state, queuedAt: 1, startedAt: null, finishedAt: null });
  assert.equal(await run(), true);
  rows = [row(1, 'running'), row(2, 'running')]; assert.equal(await run(), true);
  rows.push(row(3, 'running')); assert.equal(await run(), false);
  rows = [row(1, 'waiting')]; assert.equal(await run(), false);
  rows = [row(1, 'finished')]; assert.equal(await run(), true);
  rows = [{ ...row(1, 'running'), pid: null }]; assert.equal(await run(), false);
  p.readDir = () => { throw Object.assign(Error('not installed'), { code: 'ENOENT' }); }; assert.equal(await run(), true);
  p.readDir = () => { throw Object.assign(Error('unreadable'), { code: 'EACCES' }); }; assert.equal(await run(), false);
  assert.equal(await run({ PDD_SUITE_QUEUE: 'relative' }), false);
});
