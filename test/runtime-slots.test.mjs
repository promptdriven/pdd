import test from 'node:test';
import assert from 'node:assert/strict';
import { chmodSync, mkdirSync, readFileSync, readdirSync, statSync, writeFileSync } from 'node:fs';
import { spawn } from 'node:child_process';
import { join } from 'node:path';
import { acquireRuntimeSlot, recordRuntimeRequest, releaseRuntimeSlot, listRuntimeJobs, runJobs } from '../src/runtime-slots.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { harbor, fakeRuntime, sink, temp, root } from './runtime-fake.mjs';

const origin = 'http://localhost:453';
const options = stateDir => ({ stateDir, origin });
const folder = stateDir => join(stateDir, 'slots', 'localhost%3A453');
function seed(stateDir, row) { mkdirSync(folder(stateDir), { recursive: true }); writeFileSync(join(folder(stateDir), `${row.id}.json`), JSON.stringify(row)); }
const record = (id, extra = {}) => ({ id, state: 'active', pid: process.pid, kind: 'check', started_at: 0, request_ids: ['run-a'], ...extra });
const child = (args, { cwd, env }) => new Promise((done, fail) => {
  const p = spawn(process.execPath, args, { cwd, env: { ...process.env, ...env }, stdio: ['ignore', 'pipe', 'pipe'] });
  let stdout = '', stderr = ''; p.stdout.on('data', b => stdout += b); p.stderr.on('data', b => stderr += b);
  p.on('error', fail); p.on('close', code => done({ code, stdout, stderr }));
});

test('slots: native reservation permissions, unique append and confirmed release', async t => {
  const stateDir = join(temp(t), 'state');
  const reservation = await acquireRuntimeSlot({ ...options(stateDir), limit: 1, kind: 'lint' });
  assert.equal(statSync(folder(stateDir)).mode & 0o777, 0o700);
  assert.equal(statSync(join(reservation.directory, `${reservation.id}.json`)).mode & 0o777, 0o600);
  await recordRuntimeRequest(reservation, 'a'); await recordRuntimeRequest(reservation, 'a'); await recordRuntimeRequest(reservation, 'b');
  await releaseRuntimeSlot(reservation, { ended: false });
  assert.deepEqual((await listRuntimeJobs(options(stateDir))).jobs[0].request_ids, ['a', 'b']);
  await releaseRuntimeSlot(reservation, { ended: true });
  assert.deepEqual(await listRuntimeJobs(options(stateDir)), { jobs: [] });
});

test('slots: dead owners retain running, unknown and unreadable jobs until the 30-minute boundary', async t => {
  for (const state of ['running', 'unknown', 'error', 'ended']) for (const age of [1_799_999, 1_800_000]) {
    const stateDir = join(temp(t), 'state'); seed(stateDir, record('old', { pid: 777, started_at: 0, request_ids: [`run-${state}-${age}`] }));
    let now = age;
    const found = await acquireRuntimeSlot({ ...options(stateDir), limit: 1, kind: 'try', deadline: age + 1 }, {
      now: () => now, isAlive: pid => pid !== 777, readRun: async () => { if (state === 'error') throw Error('unreadable'); return state; }, sleep: async ms => { now += ms; },
    });
    const allowed = state === 'ended' || age >= 1_800_000;
    assert.equal(!!found, allowed, `${state}/${age}`);
    const jobs = (await listRuntimeJobs(options(stateDir))).jobs;
    assert.equal(jobs.some(row => row.id === 'old'), !allowed);
    if (found) await releaseRuntimeSlot(found, { ended: true });
  }
});

test('slots: all recorded IDs must end; unsent dead records can be reclaimed', async t => {
  for (const ids of [[], ['ended', 'running'], ['ended', 'ended-again']]) {
    const stateDir = join(temp(t), 'state'); seed(stateDir, record('dead', { pid: 777, request_ids: ids })); let now = 10;
    const lease = await acquireRuntimeSlot({ ...options(stateDir), kind: 'check', limit: 1, deadline: 11 }, {
      isAlive: pid => pid !== 777, now: () => now, sleep: async ms => now += ms, readRun: async id => id.startsWith('ended') ? 'ended' : 'running',
    });
    assert.equal(!!lease, !ids.includes('running'));
  }
});

test('slots: FIFO ties ignore enumeration order; dead waiters disappear; one ticket persists through contention', async t => {
  const stateDir = join(temp(t), 'state');
  seed(stateDir, record('wait-b', { state: 'waiting', started_at: 20, request_ids: [] }));
  seed(stateDir, record('wait-a', { state: 'waiting', started_at: 20, request_ids: [] }));
  seed(stateDir, record('dead', { state: 'waiting', pid: 777, started_at: 1, request_ids: [] }));
  const { unlinkSync } = await import('node:fs');
  let rounds = 0, now = 20; const lines = [];
  const lease = await acquireRuntimeSlot({ ...options(stateDir), kind: 'try', limit: 1, deadline: 1000 }, {
    now: () => now, randomUUID: () => 'wait-c', isAlive: pid => pid !== 777, say: text => lines.push(text),
    sleep: async ms => {
      const jobs = (await listRuntimeJobs(options(stateDir))).jobs;
      assert.equal(jobs.filter(row => row.id === 'wait-c').length, 1);
      assert.equal(jobs.some(row => row.id === 'dead'), false);
      const expected = rounds++ === 0 ? 'wait-a' : 'wait-b';
      assert.equal(jobs.filter(row => row.state === 'waiting')[0].id, expected);
      unlinkSync(join(folder(stateDir), `${expected}.json`)); now += ms;
    },
  });
  assert.equal(lease.id, 'wait-c'); assert.equal(rounds, 2);
  assert.ok(lines.some(text => /2 ahead/.test(text))); assert.ok(lines.some(text => /1 ahead/.test(text)));
});

test('slots: interruption and deadline remove only the caller ticket', async t => {
  for (const interrupt of [false, true]) {
    const stateDir = join(temp(t), 'state'); seed(stateDir, record('busy'));
    let now = 100, stopped = false;
    const lease = await acquireRuntimeSlot({ ...options(stateDir), kind: 'lint', limit: 1, deadline: 200 }, {
      now: () => now, interrupted: () => stopped, sleep: async ms => { now += ms; if (interrupt) stopped = true; },
    });
    assert.equal(lease, null); assert.deepEqual((await listRuntimeJobs(options(stateDir))).jobs.map(row => row.id), ['busy']);
  }
});

test('jobs: replay every unchanged runtime-jobs vector against the public listing boundary', async () => {
  const scenario = JSON.parse(readFileSync(new URL('./runtime/runtime-jobs.json', import.meta.url)));
  const world = structuredClone(scenario.initial_world); let calls = 0;
  const pointer = (value, path) => path.split('/').slice(1).reduce((obj, key) => obj[key.replace(/~1/g, '/').replace(/~0/g, '~')], value);
  for (const step of scenario.steps) {
    assert.equal(step.operation, 'listRuntimeJobs');
    const result = await listRuntimeJobs(step.input, { files: { listRecords: async args => {
      calls++; world.reads.push(args); return structuredClone(scenario.simulation['files.listRecords'].result_template);
    } } });
    for (const check of step.checks) {
      assert.equal(check.op, 'equals');
      const got = check.target === 'result' ? pointer(result, check.path) : check.target === 'world' ? pointer(world, check.path) : calls;
      assert.deepEqual(got, check.value, `${step.step_id}/${check.criterion_id}/${check.target}${check.path}`);
    }
  }
});

test('jobs: real CLI outside Git, no auth or runtime calls; errors never look empty', async t => {
  const sandbox = temp(t), stateDir = join(sandbox, 'state'), gh = join(sandbox, 'gh');
  writeFileSync(gh, `#!/bin/sh\necho forbidden >&2\nexit 77\n`); chmodSync(gh, 0o700);
  const fake = await fakeRuntime(t, () => { assert.fail('jobs contacted runtime'); });
  const env = { PATH: sandbox, PDD_STATE_DIR: stateDir, PDD_RUNTIME_URL: fake.origin };
  const guard = join(sandbox, 'no-effects.mjs');
  writeFileSync(guard, `import http from 'node:http'; import https from 'node:https'; import net from 'node:net'; import child from 'node:child_process'; import {syncBuiltinESMExports} from 'node:module';
const stop=()=>{throw Error('Forbidden jobs side effect');}; globalThis.fetch=stop; process.kill=stop;
for(const mod of [http,https]){mod.request=stop;mod.get=stop;}net.connect=stop;net.createConnection=stop;
for(const key of ['spawn','spawnSync','exec','execFile','execSync','execFileSync','fork'])child[key]=stop;syncBuiltinESMExports();`);
  const argv = ['--import', guard, join(root, 'bin/pdd.mjs'), 'jobs'];
  const empty = await child(argv, { cwd: sandbox, env });
  assert.equal(empty.code, 0); assert.equal(empty.stderr, ''); assert.ok(empty.stdout.trim());
  seed(stateDir, record('wait', { state: 'waiting', pid: 222, kind: 'try', started_at: 20, request_ids: [] }));
  seed(stateDir, record('active', { pid: 111, kind: 'lint', started_at: 10, request_ids: ['req-one'] }));
  // Use this fake's host folder, since jobs uses the configured runtime host.
  const { renameSync } = await import('node:fs'); renameSync(folder(stateDir), join(stateDir, 'slots', encodeURIComponent(new URL(fake.origin).host)));
  const shown = await child(argv, { cwd: sandbox, env });
  assert.equal(shown.code, 0); assert.ok(shown.stdout.indexOf('111') < shown.stdout.indexOf('222')); assert.match(shown.stdout, /req-one/);
  const out = sink(), err = sink();
  assert.equal(await runJobs({ env }, { stdout: out, stderr: err, files: { listRecords: () => { throw Error('permission denied'); } } }), 5);
  assert.equal(out.text, ''); assert.match(err.text, /permission denied/);
  const broken = join(stateDir, 'slots', encodeURIComponent(new URL(fake.origin).host), 'broken.json'); writeFileSync(broken, '{');
  const bad = await child(argv, { cwd: sandbox, env });
  assert.equal(bad.code, 5); assert.equal(bad.stdout, ''); assert.ok(bad.stderr);
});

test('jobs: router, catalog, help and completion expose the local no-option command', async () => {
  let called = 0; const out = sink(), err = sink();
  assert.equal(await runPdd(['jobs'], { stdout: out, stderr: err, env: {}, runtimeSlots: { runJobs: async () => { called++; return 0; } } }), 0);
  assert.equal(called, 1);
  assert.equal(await runPdd(['jobs', '--json'], { stdout: out, stderr: err }), 2);
  for (const argv of [['--help'], ['completion', 'bash'], ['completion', 'zsh']]) {
    const stdout = sink(); assert.equal(await runPdd(argv, { stdout, stderr: sink() }), 0); assert.match(stdout.text, /jobs/);
  }
});

test('slots: ten real CLI checks across repositories share a limit of three and all finish', { timeout: 45_000 }, async t => {
  const setup = harbor(t), second = harbor(t); let peak = 0, active = 0; const jobs = new Map();
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.method === 'POST') {
      const id = e.request.requestId; jobs.set(id, { command: e.command }); active++; peak = Math.max(peak, active);
      return { status: 202, json: f.job(id, e.command, 'queued') };
    }
    const id = e.url.split('/').at(-1), job = jobs.get(id);
    assert.ok(job, `unknown job ${id}`);
    if (!job.ended) { active--; job.ended = true; }
    return { status: 200, json: job.command === 'lint' ? f.lint(id) : f.check(id) };
  });
  const gh = join(setup.sandbox, 'gh'); writeFileSync(gh, '#!/bin/sh\nif [ "$1" = auth ]; then echo fixture-token; else echo "octo 4242"; fi\n'); chmodSync(gh, 0o700);
  const env = { HOME: setup.home, PATH: `${setup.sandbox}:${process.env.PATH}`, PDD_STATE_DIR: setup.state, PDD_MAX_JOBS: '3', PDD_RUNTIME_URL: fake.origin };
  const results = await Promise.all(Array.from({ length: 10 }, (_, i) => child([join(root, 'bin/pdd.mjs'), 'check', 'place-order', '--json'], { cwd: i % 2 ? second.repo : setup.repo, env })));
  for (const result of results) { assert.equal(result.code, 0, result.stdout + result.stderr); assert.equal(JSON.parse(result.stdout).rows[0].state, 'passed'); }
  assert.equal(peak, 3); assert.equal(active, 0); assert.equal(fake.posts.filter(e => e.command === 'check').length, 10);
  assert.equal((await listRuntimeJobs({ stateDir: setup.state, origin: fake.origin })).jobs.length, 0);
});

test('slots: an actual exited producer does not free its posted lease until its job is confirmed ended', async t => {
  const sandbox = temp(t), stateDir = join(sandbox, 'state');
  const code = `const m = await import(${JSON.stringify(new URL('../src/runtime-slots.mjs', import.meta.url).href)}); const r = await m.acquireRuntimeSlot({stateDir:${JSON.stringify(stateDir)},origin:${JSON.stringify(origin)},kind:'check',limit:1}); await m.recordRuntimeRequest(r,'live-runtime-job'); process.stdout.write(String(process.pid)+'\\n');`;
  const produced = await child(['--input-type=module', '-e', code], { cwd: sandbox, env: { FORCE_COLOR: '3' } }); assert.equal(produced.code, 0, produced.stderr);
  const owner = Number(produced.stdout.trim()); assert.ok(owner > 1);
  let now = Date.now();
  const waiting = await acquireRuntimeSlot({ ...options(stateDir), kind: 'lint', limit: 1, deadline: now + 1 }, { now: () => now, sleep: async ms => now += ms, readRun: async () => 'running' });
  assert.equal(waiting, null); assert.equal((await listRuntimeJobs(options(stateDir))).jobs[0].pid, owner);
  now += 15_000;
  const ended = await acquireRuntimeSlot({ ...options(stateDir), kind: 'try', limit: 1 }, { now: () => now, readRun: async () => 'ended' });
  assert.ok(ended); await releaseRuntimeSlot(ended, { ended: true });
});

test('slots: simultaneous native claimants safely reclaim dead unique claims', { timeout: 20_000 }, async t => {
  const sandbox = temp(t), stateDir = join(sandbox, 'state'), log = join(sandbox, 'events');
  mkdirSync(folder(stateDir), { recursive: true });
  for (let i = 0; i < 3; i++) writeFileSync(join(folder(stateDir), `.claim-dead-${i}.lock`), JSON.stringify({ id: `dead-${i}`, pid: 2147483647, number: 1, choosing: false }));
  const source = `import {appendFileSync} from 'node:fs'; const m=await import(${JSON.stringify(new URL('../src/runtime-slots.mjs', import.meta.url).href)}); const r=await m.acquireRuntimeSlot({stateDir:${JSON.stringify(stateDir)},origin:${JSON.stringify(origin)},kind:'check',limit:3,deadline:Date.now()+15000}); if(!r)process.exit(2); appendFileSync(${JSON.stringify(log)},JSON.stringify({event:'enter',id:r.id})+'\\n'); await new Promise(done=>setTimeout(done,20)); appendFileSync(${JSON.stringify(log)},JSON.stringify({event:'exit',id:r.id})+'\\n'); await m.releaseRuntimeSlot(r,{ended:true});`;
  const started = performance.now();
  const results = await Promise.all(Array.from({ length: 12 }, () => child(['--input-type=module', '-e', source], { cwd: sandbox, env: {} })));
  for (const result of results) assert.equal(result.code, 0, result.stderr);
  const elapsed = performance.now() - started; t.diagnostic(`12 contenders, limit 3, 20 ms hold: ${Math.round(elapsed)} ms`);
  assert.ok(elapsed < 15_000);
  const active = new Set(); let peak = 0, entered = 0;
  for (const line of readFileSync(log, 'utf8').trim().split('\n')) {
    const event = JSON.parse(line);
    if (event.event === 'enter') { active.add(event.id); entered++; peak = Math.max(peak, active.size); } else active.delete(event.id);
    assert.ok(active.size <= 3);
  }
  assert.equal(entered, 12); assert.equal(active.size, 0); assert.ok(peak >= 1);
  assert.equal(readdirSync(folder(stateDir)).filter(name => name.endsWith('.lock')).length, 0);
});

test('slots: blocked request registration stops at cancellation or the caller deadline', async () => {
  for (const interrupt of [false, true]) {
    let now = 0, stopped = false, writes = 0;
    const result = await recordRuntimeRequest({ id: 'lease', directory: '/state' }, 'request', {
      deadline: 10, now: () => now, interrupted: () => stopped,
      sleep: async ms => { now += ms; if (interrupt) stopped = true; },
      files: { exclusiveCreate: async () => false, writeAtomic: () => { writes++; }, unlink: () => {}, listRecords: () => ({ jobs: [] }) },
    });
    assert.equal(result, false); assert.equal(writes, 0); assert.equal(now, 10);
  }
});

test('jobs: age comes from the injected clock and snapshot read errors retain their code', async () => {
  const stdout = sink(), stderr = sink();
  assert.equal(await runJobs({ env: { PDD_STATE_DIR: '/state', PDD_RUNTIME_URL: origin } }, {
    stdout, stderr, now: () => 10_000, files: { listRecords: () => ({ jobs: [record('one', { started_at: 1000 })] }) },
  }), 0);
  assert.match(stdout.text, /9 s/); assert.equal(stderr.text, '');
  await assert.rejects(listRuntimeJobs(options('/state'), { files: { listRecords: () => { throw Error('denied'); } } }), { code: 'local-state-unavailable' });
});
