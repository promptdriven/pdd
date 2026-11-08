import test from 'node:test';
import assert from 'node:assert/strict';
import { githubFloorGuard, githubLedger, githubMachineEntries, nativeGithubCounter } from '../src/github-calls.mjs';
import { commandGithubFloor, createDependencyReadPorts } from '../src/issue-dependencies-github.mjs';
import { githubAppWorld } from './helpers/github-app-world.mjs';

const now = Date.parse('2026-11-07T12:00:00Z');
const identity = 'app:1234:installation:9876';
const entry = { at: now, api: 'rest', purpose: 'setup', status: 200, resource: 'core', limit: 15000, remaining: 5, resetAt: now + 3600000 };

for (const who of ['personal', 'App']) for (const resource of ['core', 'graphql']) {
  for (const [name, changes, blocked] of [
    ['low', {}, true], ['high', { remaining: 14000 }, false], ['at floor', { remaining: 1000 }, false],
    ['expired', { resetAt: now }, false], ['future', { at: now + 1 }, false],
  ]) test(`${who} ${resource} floor starts from selected ${name} entries`, () => {
    const selected = [{ ...entry, resource, ...(who === 'App' ? { identity } : {}), ...changes }];
    const guard = githubFloorGuard({ floor: 1000, entries: selected, now: () => now });
    assert.equal(guard.blocked(resource), blocked);
    assert.equal(guard.stopped, blocked);
  });
}

test('App floor expires and follows later replies without losing the stopped marker', () => {
  let time = now;
  const guard = githubFloorGuard({ entries: [{ ...entry, identity }], now: () => time });
  assert.equal(guard.blocked(), true);
  time = entry.resetAt;
  assert.equal(guard.blocked(), false);
  assert.equal(guard.stopped, true);
  guard.observe({ rate: { resource: 'core', remaining: 3, resetAt: time + 1000 } });
  guard.observe({ rate: null });
  assert.equal(guard.blocked(), true);
  guard.observe({ rate: { resource: 'core', remaining: 2000, resetAt: time + 1000 } });
  assert.equal(guard.blocked(), false);
});

for (const who of ['personal', 'App']) for (const remaining of [5, 1000, 14000]) {
  test(`native ${who} floor uses its ${remaining} balance across repository ledgers`, async t => {
    const w = await githubAppWorld(t);
    if (who === 'personal') w.configure(undefined);
    const selected = who === 'App' ? w.identity : null;
    // Put the selected observation in another repository of the same identity.
    const ledger = githubLedger({ root: w.stateRoot, repository: w.repository });
    ledger.record({ ...entry, ...(who === 'App' ? {} : { identity: w.identity }), remaining: remaining < 1000 ? 14000 : 0, at: w.time + 1 });
    ledger.record({ ...entry, identity: 'app:1234:installation:other', remaining: remaining < 1000 ? 14000 : 0 });
    githubLedger({ root: w.stateRoot, repository: 'acme/another' }).record({ ...entry, ...(selected ? { identity: selected } : {}), remaining });
    const options = { env: w.env, autopilotStateRoot: w.stateRoot, execFile: w.gitExec, githubApp: w.appPorts, now: () => w.time };
    const guard = await commandGithubFloor({ cwd: w.cwd, repository: w.repository }, options);
    assert.equal(guard.blocked(), remaining < 1000, 'native guard must use the selected installation balance');
    const selectedEntries = githubMachineEntries({ root: w.stateRoot, identity: selected });
    assert.equal(selectedEntries.length, 1);
    assert.equal(githubFloorGuard({ entries: selectedEntries, now: options.now }).blocked(), remaining < 1000);
    w.time = entry.resetAt;
    assert.equal((await commandGithubFloor({ cwd: w.cwd, repository: w.repository }, options)).blocked(), false);
  });
}

test('native App dependency reads stop before gh while safety reads and writes proceed', async t => {
  const w = await githubAppWorld(t);
  w.github.add(1); const blocker = w.github.add(2);
  w.github.remaining = 5;
  githubLedger({ root: w.stateRoot, repository: w.repository }).record({ ...entry, identity: w.identity });
  const exec = nativeGithubCounter((file, args, options) => file === 'git' ? w.gitExec(file, args, options) : w.github.gh(args, options),
    { env: w.env, stateRoot: w.stateRoot, now: () => w.time, appPorts: w.appPorts });
  const ports = createDependencyReadPorts({ cwd: w.cwd }, { execFile: exec, env: w.env, autopilotStateRoot: w.stateRoot, githubApp: w.appPorts, now: () => w.time });
  const mark = w.github.mark();
  const result = JSON.parse((await ports.github.page({ repository: w.repository, kind: 'issues', cursor: '' })).json);
  assert.equal(result.status, 0);
  assert.equal(w.github.since(mark).calls.length, 0, 'reserve must block the first non-safety request');
  const safe = JSON.parse((await ports.github.issue({ repository: w.repository, issue: '1', safety: true })).json);
  assert.equal(safe.number, 1);
  assert.deepEqual(await ports.github.addBlocker({ repository: w.repository, issue: '1', blockerId: blocker.id }), { ok: true });
  assert.equal(w.github.since(mark).calls.length, 2);
  assert.deepEqual(w.github.issues.get(1).blockedBy, [2]);
  w.time = entry.resetAt;
  const resumed = JSON.parse((await ports.github.page({ repository: w.repository, kind: 'issues', cursor: '' })).json);
  assert.equal(resumed.items.length, 2);
});
