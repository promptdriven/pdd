import test from 'node:test';
import assert from 'node:assert/strict';
import { reviewerLease, repositoryMachines } from '../src/autopilot-reviewer.mjs';
import { createGithubRepoFake } from './helpers/github-repo-fake.mjs';
const repository = 'acme/widgets', minute = 60000;
function fixture() {
  const f = { time: Date.parse('2026-11-07T12:00:00Z') };
  f.github = createGithubRepoFake({ repository, issues: 0, now: () => f.time });
  f.ports = { now: () => f.time, execFile: (_file, args, options) => f.github.gh(args, options) };
  f.identity = i => ({ machine: `machine-${i}`, coordinatorId: `coordinator-${i}`, login: 'acme' });
  f.acquire = i => reviewerLease({ repository, identity: f.identity(i), acquire: true }, f.ports);
  f.read = i => reviewerLease({ repository, identity: f.identity(i) }, f.ports);
  return f;
}

test('lease acquisition and expiry races accept one holder; renewal is cheap and preserves generation', async () => {
  const f = fixture();
  const raced = await Promise.all([0, 1, 2, 3].map(f.acquire));
  assert.equal(raced.filter(x => x.held).length, 1);
  const holder = raced.findIndex(x => x.held), lease = raced[holder].lease;
  assert.deepEqual((await Promise.all([0, 1, 2, 3].map(f.read))).map(x => x.held), [0, 1, 2, 3].map(i => i === holder));
  const mark = f.github.mark();
  await f.acquire(holder);
  assert.equal(f.github.since(mark).calls.filter(x => x.method !== 'GET').length, 0);
  f.time += 30 * minute;
  const renewed = await f.acquire(holder);
  assert.equal(renewed.held, true);
  assert.equal(renewed.lease.generation, lease.generation);
  assert.equal(Date.parse(renewed.lease.lastSeen), f.time);
  f.github.beforeRest = call => { if (call.method === 'GET' && call.endpoint.includes('/contents/')) { f.time += 90 * minute; f.github.beforeRest = null; } };
  assert.equal((await f.read(holder)).held, false, 'a delayed read cannot extend authority past expiry');
  const taken = await Promise.all([0, 1, 2, 3].map(f.acquire));
  assert.equal(taken.filter(x => x.held).length, 1);
  assert.notEqual(taken.find(x => x.held).lease.generation, lease.generation);
});

test('lease reads never write and malformed, future, unavailable and refused observations fail closed', async () => {
  const f = fixture();
  assert.equal((await f.read(0)).state, 'absent');
  assert.equal(f.github.calls.filter(x => x.method !== 'GET').length, 0);
  const owned = await f.acquire(0);
  const branch = 'pdd/autopilot-reviewer';
  const saved = f.github.contents.get(branch);
  for (const value of [{}, { ...owned.lease, lastSeen: new Date(f.time + minute).toISOString(), expiresAt: new Date(f.time + 91 * minute).toISOString() }]) {
    f.github.contents.set(branch, { ...saved, content: Buffer.from(JSON.stringify(value)).toString('base64') });
    assert.equal((await f.acquire(1)).state, 'unknown');
  }
  f.github.contents.set(branch, saved);
  f.github.failRead = call => call.endpoint.includes('/contents/');
  assert.equal((await f.acquire(1)).held, false);
  f.github.failRead = null;
  f.time += 91 * minute;
  f.github.failRest = call => call.method === 'PUT';
  assert.equal((await f.acquire(1)).held, false);
});

test('a stopped identity cannot renew and a lost write response cannot grant authority', async () => {
  const f = fixture();
  await f.acquire(0); f.time += 30 * minute;
  const mark = f.github.mark();
  assert.equal((await reviewerLease({ repository, identity: { ...f.identity(0), enabled: false }, acquire: true }, f.ports)).held, true);
  assert.equal(f.github.since(mark).calls.filter(x => x.method !== 'GET').length, 0);
  f.time += 91 * minute;
  const ports = { ...f.ports, execFile: async (file, args, options) => {
    const result = await f.ports.execFile(file, args, options);
    if (args.includes('PUT')) throw Error('response lost');
    return result;
  } };
  assert.equal((await reviewerLease({ repository, identity: f.identity(1), acquire: true }, ports)).held, false);
  assert.equal((await f.read(1)).held, true, 'the next live observation can establish ownership');
});

test('fleet identity is machine plus coordinator; expired evidence and duplicate issues are excluded', async () => {
  const f = fixture(), { lease } = await f.acquire(0);
  const own = { ...f.identity(1), machine: 'machine-0', active: true, issue: 'https://github.com/acme/widgets/issues/2', lastSeen: new Date(f.time).toISOString() };
  const view = repositoryMachines({ lease, claims: [own, own, { ...f.identity(2), active: false, issue: 'expired' }] }, f.time);
  assert.equal(view.machines.length, 2);
  assert.deepEqual(view.machines[1].issues, [own.issue]);
  assert.deepEqual(view.sharedLogins, ['acme']);
  assert.equal(repositoryMachines({ lease, claims: [] }, f.time + 90 * minute).reviewer, null);
});
