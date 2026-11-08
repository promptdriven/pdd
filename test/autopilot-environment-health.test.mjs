import test from 'node:test';
import assert from 'node:assert/strict';
import { environmentHealthy } from '../src/autopilot-environment.mjs';
const good = { statfs: () => ({ bavail: 2, blocks: 10, bsize: 1024 ** 3 }), cpuCount: () => 4, load: () => 1, memory: () => ({ available: 20, total: 100 }), platform: 'linux',
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
  const p = { ...good, suiteAvailable: undefined, alive: () => true, readFile, readDir: () => rows.map(row => `ticket-${row.ticket}.json`) };
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

function queueHealth(rows, alive) {
  const p = { ...good, suiteAvailable: undefined, alive,
    readDir: () => rows.map(row => `ticket-${row.ticket}.json`),
    readFile: path => path.startsWith('/proc/') ? good.readFile() : JSON.stringify(rows.find(row => path.endsWith(`ticket-${row.ticket}.json`))) };
  return environmentHealthy({ env: { PDD_SUITE_QUEUE: '/synthetic/queue' } }, p);
}
const ticket = (number, state, extra = {}) => ({ ticket: number, pid: 100 + number, childPid: 200 + number,
  cwd: '/project', state, queuedAt: 1, startedAt: 2, finishedAt: null, ...extra });

test('confirmed-dead waiting owners release effective capacity without rewriting tickets', async () => {
  const rows = [ticket(1, 'waiting')], before = structuredClone(rows), probes = [];
  assert.equal(await queueHealth(rows, pid => { probes.push(pid); return false; }), true,
    'dead waiting owners must not block environment recovery');
  assert.deepEqual(probes, [101]);
  assert.deepEqual(rows, before);
  assert.equal(await queueHealth(rows, () => true), false, 'live waiting owners keep FIFO priority');
  assert.equal(await queueHealth(rows, () => { throw Object.assign(Error('unknown'), { code: 'EPERM' }); }), false);
});

test('dead running owners release capacity only with confirmed-dead descendant groups', async () => {
  const rows = [1, 2, 3].map(n => ticket(n, 'running')), before = structuredClone(rows), probes = [];
  assert.equal(await queueHealth(rows, pid => { probes.push(pid); return false; }), true,
    'dead owners and descendant groups must not block environment recovery');
  assert.deepEqual(probes, [101, -201, 102, -202, 103, -203]);
  assert.deepEqual(rows, before);
  assert.equal(await queueHealth(rows, pid => pid < 0), false, 'live descendants retain all slots');
  assert.equal(await queueHealth(rows, pid => pid < 0 ? undefined : false), false, 'unknown descendants retain all slots');
  assert.equal(await queueHealth(rows, pid => { if (pid < 0) throw Object.assign(Error('unknown'), { code: 'EPERM' }); return false; }), false);
  for (const childPid of [undefined, null, 0, -2, '201'])
    assert.equal(await queueHealth(rows.map(row => ({ ...row, childPid })), () => false), false, 'invalid descendant ownership stays blocked');
  assert.equal(await queueHealth(rows, pid => pid > 0), false, 'a live runner keeps its slot');
});

test('native killed suite runner and group leave read-only usable queue capacity', async t => {
  const { mkdtempSync, writeFileSync, readFileSync, rmSync } = await import('node:fs');
  const { tmpdir } = await import('node:os');
  const { join } = await import('node:path');
  const { spawn } = await import('node:child_process');
  const { once } = await import('node:events');
  const root = mkdtempSync(join(tmpdir(), 'pdd-recovery-queue-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const child = spawn(process.execPath, ['-e', 'setInterval(() => {}, 1000)'], { detached: true, stdio: 'ignore' });
  t.after(() => { try { process.kill(-child.pid, 'SIGKILL'); } catch (error) { if (error.code !== 'ESRCH') throw error; } });
  const closed = once(child, 'close'); await once(child, 'spawn'); child.kill('SIGTERM'); await closed;
  for (const pid of [child.pid, -child.pid]) assert.throws(() => process.kill(pid, 0), { code: 'ESRCH' });
  const p = { statfs: good.statfs, cpuCount: good.cpuCount, load: good.load, memory: good.memory, platform: 'darwin' };
  for (const state of ['waiting', 'running']) {
    const records = [1, 2, 3].map(n => [join(root, `ticket-${n}.json`), JSON.stringify(ticket(n, state, { pid: child.pid, childPid: child.pid }))]);
    for (const [file, bytes] of records) writeFileSync(file, bytes);
    assert.equal(await environmentHealthy({ env: { PDD_SUITE_QUEUE: root } }, p), true, `native dead ${state} ownership must release capacity`);
    for (const [file, bytes] of records) assert.equal(readFileSync(file, 'utf8'), bytes, 'preflight cannot rewrite records');
  }
});

for (const [checks,running] of [[1,1],[5,3]]) test(`release: retry preflight uses ${checks} shared slots with ${running} busy`, async t => {
  const {mkdtempSync,writeFileSync,rmSync} = await import('node:fs');
  const {tmpdir} = await import('node:os');
  const {join} = await import('node:path');
  const {configureCheckCapacity} = await import('../src/test-suite-queue.mjs');
  const {checkMachine} = await import('./helpers/check-machine.mjs');
  const root=mkdtempSync(join(tmpdir(),'pdd-retry-capacity-'));
  t.after(()=>rmSync(root,{recursive:true,force:true}));
  const env={PDD_SUITE_QUEUE:root};
  await configureCheckCapacity({env,checks},checkMachine({count:64}).ports);
  for(let i=1;i<=running;i++) writeFileSync(join(root,`ticket-${i}.json`),JSON.stringify({ticket:i,pid:100+i,childPid:200+i,cwd:root,state:'running',queuedAt:1,startedAt:2,finishedAt:null}));
  const machineResources=async()=>({cpuCount:64,load:0,memory:{available:2*1024**3,total:10*1024**3},pressure:{io:0,memory:0},disk:{available:4*1024**3,total:20*1024**3}});
  assert.equal(await environmentHealthy({env,cwd:root},{machineResources,alive:()=>true}),running<checks);
});
