import test from 'node:test';
import assert from 'node:assert/strict';
import { basename } from 'node:path';
import { machineJson } from '../src/autopilot-store.mjs';
import { autopilotGithubWorld } from './helpers/autopilot-github-world.mjs';
import { createDependencyReadPorts, dependencySnapshotStore, readDependencySnapshot } from '../src/issue-dependencies-github.mjs';
import { checkDependencyStart } from '../src/issue-dependencies-intake.mjs';
import { githubLedger } from '../src/github-calls.mjs';

function limit(w, remaining) {
  w.github.remaining = remaining;
  githubLedger({ root: w.stateRoot, repository: w.repository }).record({
    at: w.time, api: 'rest', purpose: 'other', status: 200, resource: 'core',
    remaining, limit: 5000, resetAt: w.github.resetAt * 1000,
  });
}
const nonSafety = calls => calls.filter(c => c.endpoint.includes('/issues?') || c.endpoint === 'graphql');

for (const caller of ['snapshot', 'start']) for (const cold of [false, true]) {
  test(`${caller} initializes the persisted reserve guard with a ${cold ? 'cold' : 'saved'} snapshot`, async t => {
    const w = await autopilotGithubWorld({ issues: 200 }); t.after(w.cleanup);
    w.github.busy();
    assert.equal((await w.invoke('start')).exitCode, 0);
    if (cold) {
      const { file } = dependencySnapshotStore({ root: w.stateRoot, repository: w.repository });
      machineJson({ root: w.stateRoot, bucket: 'cache', key: `snapshot:${basename(file).split('.')[0]}`, file }).clear();
    }
    w.time += 600000;
    w.github.claim(130, { coordinatorId: 'new-owner', machine: 'new-machine' });
    limit(w, 900);
    const mark = w.github.mark();
    const ports = w.commandPorts();
    assert.equal(ports.githubFloor, undefined);
    if (caller === 'snapshot') {
      const { snapshot } = await readDependencySnapshot({ cwd: w.cwd, repository: w.repository }, ports);
      assert.equal(snapshot.complete, false);
    } else {
      const result = await checkDependencyStart({ cwd: w.cwd, repository: w.repository,
        issue: `https://github.com/${w.repository}/issues/130` }, ports);
      assert.equal(result.allowed, false);
      const calls = w.github.since(mark).calls;
      for (const suffix of ['', '/comments?per_page=100', '/timeline?per_page=100']) {
        assert.ok(calls.some(c => c.endpoint === `repos/${w.repository}/issues/130${suffix}`), `live claim read: ${suffix}`);
      }
      if (!cold) for (const direction of ['blocked_by', 'blocking']) {
        assert.ok(calls.some(c => c.endpoint.includes(`/issues/130/dependencies/${direction}`)), 'live subject links below the floor');
      }
    }
    const made = w.github.since(mark);
    t.diagnostic(JSON.stringify({ caller, cold, rest: made.rest, graphql: made.graphql }));
    assert.equal(nonSafety(made.calls).length, 0, 'persisted reserve stops native repository reads');
  });
}

test('an omitted repository uses the configured native reserve floor', async t => {
  const w = await autopilotGithubWorld({ github: { floor: 1500 } }); t.after(w.cleanup);
  assert.equal((await w.invoke('start')).exitCode, 0);
  w.time += 600000; limit(w, 1400);
  const mark = w.github.mark();
  await readDependencySnapshot({ cwd: w.cwd }, w.commandPorts());
  assert.equal(nonSafety(w.github.since(mark).calls).length, 0, 'configured reserve applies after repository resolution');
});

for (const derived of [false, true]) test(`a ${derived ? 'derived' : 'direct'} native snapshot stops at a reserve crossing and resumes after the reset`, async t => {
  const w = await autopilotGithubWorld(); t.after(w.cleanup);
  w.github.busy();
  assert.equal((await w.invoke('start')).exitCode, 0);
  w.time += 600000; limit(w, 1001);
  let mark = w.github.mark();
  const input = { cwd: w.cwd, repository: w.repository };
  const supplied = w.commandPorts();
  const ports = derived ? createDependencyReadPorts({ cwd: w.cwd }, supplied) : supplied;
  assert.equal((await readDependencySnapshot(input, ports)).snapshot.complete, false);
  const made = w.github.since(mark);
  assert.ok(nonSafety(made.calls).length <= 2, 'native repository reads stop when a reply crosses the reserve');
  assert.equal(made.graphql, 0);
  w.time = w.github.resetAt * 1000 + 1;
  w.github.remaining = 5000; w.github.resetAt += 3600;
  mark = w.github.mark();
  assert.equal((await readDependencySnapshot(input, w.commandPorts())).snapshot.complete, true);
  assert.ok(nonSafety(w.github.since(mark).calls).length > 0);
});

test('native saved-snapshot index calls keep the dependency ledger purpose', async t => {
  const w = await autopilotGithubWorld(); t.after(w.cleanup);
  assert.equal((await w.invoke('start')).exitCode, 0);
  w.time += 600000;
  const ledger = githubLedger({ root: w.stateRoot, repository: w.repository });
  const before = ledger.read().length;
  const native = w.commandPorts(), indexPurposes = [];
  await readDependencySnapshot({ cwd: w.cwd, repository: w.repository }, { ...native,
    execFile: async (file, args, options) => {
      if (file === 'gh' && args.some(arg => arg.includes('/issues?'))) indexPurposes.push(options.purpose);
      return native.execFile(file, args, options);
    },
  });
  assert.ok(indexPurposes.length > 0);
  assert.ok(indexPurposes.every(purpose => purpose === 'dependencies'), 'index calls retain the dependency subtotal');
  assert.ok(!ledger.read().slice(before).some(entry => entry.purpose === 'issues'));
});
