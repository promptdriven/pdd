// Approved final-write policy: native observations cannot overwrite public workflow progress.
import test from 'node:test';
import assert from 'node:assert/strict';
import { openRun, startRun, stepDone, askPerson, approveRun, cancelRun } from '../src/workflow-runner.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const fields = ['runId', 'state', 'area', 'done', 'gate', 'question', 'approvalRecord', 'decisions', 'changes', 'pr', 'prState', 'cancelled', 'chatReplacement', 'abandonedChats'];
const progress = run => Object.fromEntries(fields.map(key => [key, run[key]]));
const unavailable = () => Object.assign(Error('Delayed native failure'), { code: 'server_unavailable' });

for (const mode of ['focus', 'resume', 'open-start', 'run-start']) {
  for (const failure of [false, true]) {
    for (const action of ['done', 'ask', 'advance', 'cancel']) {
      test(`2627 default ${mode} ${failure ? 'failure' : 'success'} preserves concurrent ${action}`, async t => {
        const f = await fixture(t);
        if (mode === 'open-start') {
          const healthy = f.ports.herdr;
          f.ports.herdr = async () => { throw unavailable(); };
          assert.equal((await f.run()).exitCode, 1);
          f.ports.herdr = healthy;
          assert.equal(f.record().chats.length, 0);
        } else if (mode !== 'run-start') assert.equal((await f.run()).exitCode, 0);
        if (mode === 'resume') f.herdr.paneOf(f.record().chats[0]).agent = null;
        let enter, release, paused = false;
        const reached = new Promise(resolve => { enter = resolve; });
        const gate = new Promise(resolve => { release = resolve; });
        const ports = { ...f.ports, herdr: async args => {
          const selected = mode === 'focus' ? args[0] === 'agent' && args[1] === 'get' : args[0] === 'pane' && args[1] === 'run';
          if (!paused && selected) {
            paused = true; enter(); await gate;
            if (failure) throw unavailable();
          }
          return f.ports.herdr(args);
        } };
        const opening = mode === 'run-start'
          ? startRun({ name: 'small-change', issue: '17', agent: 'claude', cwd: f.source, packageRoot }, ports)
          : openRun({ ref: '17', cwd: f.source, packageRoot }, ports);
        assert.equal(await Promise.race([reached.then(() => true), opening.then(() => false)]), true, 'The native operation must still be awaiting its reply');
        let expected;
        try {
          const cwd = f.record().root;
          if (action === 'ask') assert.equal((await askPerson({ text: 'Keep this pending question', cwd }, f.agentPorts())).exitCode, 0);
          else if (action === 'cancel') assert.equal((await cancelRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
          else {
            assert.equal((await stepDone({ step: 'scope', summary: 'Completed during native wait', cwd }, f.agentPorts())).exitCode, 0);
            if (action === 'advance') assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
          }
          expected = f.record();
          if (action === 'advance') { assert.equal(expected.area, 1); assert.ok(expected.decisions.length); assert.ok(expected.approvalRecord); }
          if (action === 'done') { assert.ok(expected.done.scope); assert.ok(expected.gate); }
        } finally { release(); }
        // Cancel closes an already saved tab, so its delayed focus/resume must report the native failure.
        const closedSavedTab = action === 'cancel' && ['focus', 'resume'].includes(mode);
        assert.equal((await opening).exitCode, failure || closedSavedTab ? 1 : 0);
        const saved = f.record();
        assert.deepEqual(progress(saved), progress(expected), 'Native final writes must preserve every concurrent workflow field');
        if (action === 'advance' || action === 'cancel') assert.deepEqual(saved.chats.filter(chat => chat.area === expected.areas[expected.area].name), expected.chats.filter(chat => chat.area === expected.areas[expected.area].name), 'A late result cannot overwrite current chat custody');
        if (action === 'advance' || action === 'cancel') assert.deepEqual(saved.chatFailure, expected.chatFailure, 'A historical or cancelled operation cannot set or clear current failure');
        else if (failure) assert.equal(saved.chatFailure?.area, 'plan', 'A current failure is retained without discarding progress');
        else assert.equal(saved.chatFailure, undefined, 'Successful current recovery clears its prior chat failure');
      });
    }
  }
}
