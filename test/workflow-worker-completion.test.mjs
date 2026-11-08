import './helpers/test-home.mjs';
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { waitForWorkerCompletion, armWorkerCompletion } from '../src/workflow-worker-completion.mjs';

const identity = { number: 42, sourceRoot: '/repo', runDir: '/run', runId: 'run', area: 'code', paneId: 'worker', startAnchor: 123, coordinatorPaneId: 'coordinator' };
const run = { runId: 'run', area: 0, areas: [{ name: 'code' }], chats: [{ area: 'code', paneId: 'worker', startedAt: 123 }] };

test('worker done and coordinator readiness precede the automatic callback under the run lock', async () => {
  const events = []; let ready;
  const pending = waitForWorkerCompletion(identity, {
    wait: async (session, pane, until) => { events.push([session, pane, until]); if (session === 'pdd-autopilot') await new Promise(resolve => { ready = resolve; }); },
    coordinatorState: () => ({ enabled: true, paneId: 'coordinator' }),
    acquireRunLock: () => { events.push('lock'); return () => events.push('release'); },
    readRun: () => run,
    yieldCapacity: async (args, ports) => { events.push('yield'); assert.deepEqual(args, { ref: '42', cwd: '/repo' }); assert.equal(ports.expectedCompletion, identity); ports.releaseRunLock(); },
  });
  await new Promise(resolve => setImmediate(resolve));
  assert.deepEqual(events, [['pdd', 'worker', ['done']], ['pdd-autopilot', 'coordinator', ['idle', 'done']]]);
  ready(); await pending;
  assert.deepEqual(events.slice(2), ['lock', 'yield', 'release']);
});

test('mismatched coordinator or failed wait does not yield; arm detaches', async () => {
  let yielded = false, unref = false, options;
  await waitForWorkerCompletion(identity, { wait: async () => {}, coordinatorState: () => ({ enabled: true, paneId: 'other' }), yieldCapacity: () => { yielded = true; } });
  await waitForWorkerCompletion(identity, { wait: async () => { throw Error('unavailable'); }, yieldCapacity: () => { yielded = true; } });
  armWorkerCompletion(identity, { spawn: (_command, _args, opts) => { options = opts; return { on() {}, unref() { unref = true; } }; } });
  assert.equal(yielded, false); assert.equal(options.detached, true); assert.equal(unref, true);
});


test('registration gap retries the same fresh worker and then yields after native done', async () => {
  let attempts = 0, yielded = false, time = 123;
  await waitForWorkerCompletion(identity, {
    now: () => time, sleep: async ms => { time += ms; }, readRun: () => run,
    wait: async (session, pane) => { if (session === 'pdd') { assert.equal(pane, 'worker'); if (++attempts === 1) throw Object.assign(Error(), { stderr: '{"error":{"code":"agent_not_found"}}' }); } },
    coordinatorState: () => ({ enabled: false }), acquireRunLock: () => () => {},
    yieldCapacity: async () => { yielded = true; },
  });
  assert.equal(attempts, 2); assert.equal(yielded, true);
});

test('a resumed worker requires fresh activity before completion', async () => {
  const resumed = { ...identity, startAnchor: 456, requireActivity: true };
  const resumedRun = { ...run, chats: [{ ...run.chats[0], resumedAt: 456 }] };
  const events = [];
  await waitForWorkerCompletion(resumed, {
    readRun: () => resumedRun, markActivity: () => {},
    wait: async (session, pane, until) => { events.push([session, pane, until]); },
    coordinatorState: () => ({ enabled: false }), acquireRunLock: () => () => {},
    yieldCapacity: async () => { events.push('yield'); },
  });
  assert.deepEqual(events, [['pdd', 'worker', ['working']], ['pdd', 'worker', ['done']], 'yield']);
});
