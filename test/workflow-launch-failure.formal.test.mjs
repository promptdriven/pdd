import test from 'node:test';
import assert from 'node:assert/strict';
import {observeLifecycle, applyLifecycle, START_GRACE_MS} from '../src/workflow-chat.mjs';

test('bounded launch lifecycle: absence and elapsed time cannot invent failure or completion', () => {
  let cases = 0;
  for (const state of ['starting', 'unknown'])
    for (const code of ['agent_not_found', 'server_not_running', 'server_unavailable', 'pane_not_found'])
      for (const at of [1000, 1001, 1000 + START_GRACE_MS, 1000 + START_GRACE_MS * 2])
        for (const startUnconfirmed of [false, true]) {
          const chat = {state, paneId: 'p2634', startedAt: 1000, startUnconfirmed};
          const got = observeLifecycle(chat, {alive: false, code}, at);
          assert.ok(!['failed', 'ended'].includes(got.state), JSON.stringify({chat, code, at, got}));
          cases++;
        }
  assert.equal(cases, 64);
});

test('bounded launch lifecycle: a definite failure survives unavailable inspection with its diagnostic', () => {
  let cases = 0;
  for (const state of ['starting', 'unknown'])
    for (const startUnconfirmed of [false, true])
      for (const exitCode of [0, 1, 126, 127, 255])
        for (const at of [1001, 1000 + START_GRACE_MS * 2]) {
          const chat = {state, paneId: 'p2634', startedAt: 1000, startUnconfirmed};
          const failure = {exitCode, message: 'unable to open database file'};
          applyLifecycle(chat, observeLifecycle(chat, {alive: false, code: 'agent_not_found', launchFailure: failure}, at));
          assert.equal(chat.state, 'failed', `launch failure must be saved: ${JSON.stringify({state, exitCode, at})}`);
          assert.equal(chat.code, 'agent_launch_failed');
          assert.equal(chat.startUnconfirmed, undefined);
          const evidence = structuredClone(chat.evidence);
          assert.equal(evidence.exitCode, exitCode);
          assert.equal(evidence.message, failure.message);
          applyLifecycle(chat, observeLifecycle(chat, {alive: false, code: 'server_unavailable'}, at + 1));
          assert.equal(chat.state, 'failed');
          assert.equal(chat.code, 'agent_launch_failed');
          assert.deepEqual(chat.evidence, evidence);
          cases++;
        }
  assert.equal(cases, 40);
});

test('bounded initial launch exits retain diagnostics after a brief running observation', () => {
  let cases = 0;
  for (const exitCode of [1, 126, 127, 255])
    for (const at of [1001, 1000 + START_GRACE_MS * 2]) {
      const chat = {state: 'running', paneId: 'p2634', startedAt: 1000};
      const launchFailure = {exitCode, message: 'unable to open database file'};
      applyLifecycle(chat, observeLifecycle(chat, {alive: false, code: 'agent_not_found', launchFailure}, at));
      assert.equal(chat.state, 'ended');
      assert.equal(chat.evidence.kind, 'launch-exit');
      assert.equal(chat.evidence.exitCode, exitCode);
      assert.equal(chat.evidence.message, launchFailure.message);
      const evidence = structuredClone(chat.evidence);
      applyLifecycle(chat, observeLifecycle(chat, {alive: false, code: 'server_unavailable'}, at + 1));
      assert.deepEqual(chat.evidence, evidence);
      cases++;
    }
  assert.equal(cases, 8);
});
