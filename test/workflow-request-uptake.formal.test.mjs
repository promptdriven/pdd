import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { join } from 'node:path';
import { fixture } from './helpers/workflow-delivery-fixture.mjs';
import * as runner from '../src/workflow-runner.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { writeRun } from '../src/workflow-runs.mjs';

// Oracle: workflow-request-uptake.md, AC3/4/6 and Rules to check. These
// finite domains and expected effects are independent of the vector replay.
async function world(t) {
  const f = await fixture(t, { agent: 'codex', name: 'bug' });
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record(), chat = run.chats.at(-1);
  const path = join(run.runDir, 'delivery-journal.json');
  const entry = (id, extra = {}) => ({
    id, text: `Requested change ${id}`, kind: 'change', area: chat.area,
    paneId: chat.paneId, state: 'delivered', at: 5, deliveredAt: 0, ...extra,
  });
  const save = requests => fs.writeFileSync(path, JSON.stringify({ requests }, null, 2) + '\n');
  const bytes = () => fs.readFileSync(path, 'utf8');
  const read = () => JSON.parse(bytes()).requests;
  async function ack(id, summary, cwd = run.root, ports = f.ports) {
    return runPdd(['workflow', 'ack', id, '--summary', summary], {
      cwd, env: ports.env, stdout: { write() {} }, stderr: { write() {} },
      workflowRunner: {
        acknowledgeRequest: input => runner.acknowledgeRequest(input, ports),
      },
    });
  }
  return { ...f, entry, save, bytes, read, ack, path };
}

test('2722 formal: exhaustive 36-case acknowledgement eligibility', { timeout: 30000 }, async t => {
  const f = await world(t);
  let count = 0;
  for (const kind of ['change', 'answer'])
    for (const delivery of ['delivered', 'pending', 'uncertain'])
      for (const state of ['running', 'waiting', 'completed'])
        for (const inWorktree of [true, false]) {
          const label = JSON.stringify({ kind, delivery, state, inWorktree });
          const run = f.record();
          run.state = state;
          writeRun(run, f.ports);
          const selected = f.entry('selected', { kind, state: delivery });
          const unrelated = f.entry('other-request', { state: 'pending', extraCustody: 'retained' });
          f.save([selected, unrelated]);
          const before = f.bytes(), progress = f.record();
          f.ports.now = () => 23;
          const got = await f.ack('selected', 'Implemented selected change', inWorktree ? run.root : f.source);
          // Active includes an area waiting for the person; its run has not ended.
          const permitted = kind === 'change' && delivery === 'delivered' &&
            state !== 'completed' && inWorktree;
          if (permitted) {
            assert.equal(got, 0, label);
            assert.deepEqual(f.read(), [
              { ...selected, ackedAt: 23, ackSummary: 'Implemented selected change' }, unrelated,
            ], label);
          } else {
            assert.notEqual(got, 0, label);
            assert.equal(f.bytes(), before, label);
          }
          assert.deepEqual(f.record(), progress, `progress unchanged: ${label}`);
          count++;
        }
  assert.equal(count, 36);
});

test('2722 formal: first durable acknowledgement across eight time/absence cases', { timeout: 30000 }, async t => {
  const f = await world(t);
  let count = 0;
  for (const prior of ['absent', null, 0, 17])
    for (const now of [0, 23]) {
      const label = JSON.stringify({ prior, now });
      const selected = f.entry('selected');
      if (prior !== 'absent') Object.assign(selected, { ackedAt: prior, ackSummary: 'First durable note' });
      const other = f.entry('other-request');
      f.save([selected, other]);
      const before = f.bytes(), progress = f.record();
      f.ports.now = () => now;
      assert.equal(await f.ack('selected', 'New explicit note'), 0, label);
      const alreadyDurable = prior === 0 || prior === 17;
      const expected = alreadyDurable ? selected : {
        ...selected, ackedAt: now, ackSummary: 'New explicit note',
      };
      assert.deepEqual(f.read(), [expected, other], label);
      if (alreadyDurable) assert.equal(f.bytes(), before, `first write bytes: ${label}`);
      const durableBytes = f.bytes();
      f.ports.now = () => now + 41;
      assert.equal(await f.ack('selected', 'Later replacement attempt'), 0, label);
      assert.equal(f.bytes(), durableBytes, `repeat preserves bytes: ${label}`);
      assert.deepEqual(f.record(), progress, `progress unchanged: ${label}`);
      count++;
    }
  assert.equal(count, 8);
});

test('2722 formal: acknowledged/open snapshots preserve journal and protected ownership', { timeout: 30000 }, async t => {
  const f = await world(t);
  const protectedRequest = f.entry('protected', {
    state: 'pending', inFlight: true,
    owner: { pid: 654321, hostname: 'original-host.invalid', token: 'original-owner' },
  });
  f.save([f.entry('acknowledged'), f.entry('still-open'), protectedRequest]);
  f.ports.now = () => 0;
  assert.equal(await f.ack('acknowledged', 'Recorded actual change'), 0);
  const sends = () => f.herdr.calls.filter(args => args[0] === 'agent' && args[1] === 'prompt').length;
  const before = f.bytes(), progress = f.record(), sent = sends();
  let claims = 0;
  const ports = {
    ...f.ports,
    deliveryFiles: {
      ...fs,
      mkdirSync() { claims++; throw Error('A snapshot must not acquire a journal claim'); },
    },
  };
  for (const options of [{}, { json: true }, { ref: undefined }, { ref: undefined, all: true }]) {
    const result = await runner.runStatus({ ref: '17', cwd: f.source, ...options }, ports);
    assert.equal(result.exitCode, 0);
    if (options.json) {
      const row = JSON.parse(result.message).runs[0];
      assert.deepEqual(row.requests.map(({ id, ackedAt, ackSummary }) => ({ id, ackedAt, ackSummary })), [
        { id: 'acknowledged', ackedAt: 0, ackSummary: 'Recorded actual change' },
        { id: 'still-open', ackedAt: null, ackSummary: null },
      ]);
    }
  }
  assert.deepEqual(f.record(), progress, 'pure status preserves all run state');
  // A successful out-of-order completion can record its ordinary completion
  // summary, but its visibility warning cannot advance or approve an area.
  const done = await runner.stepDone({ step: 'unknown', summary: 'Everything done', cwd: progress.root }, ports);
  assert.equal(done.exitCode, 0);
  assert.ok(done.message.includes('still-open'));
  assert.equal(claims, 0);
  assert.equal(f.bytes(), before);
  const after = f.record();
  for (const key of ['area', 'gate', 'state', 'approvalRecord', 'decisions', 'steps', 'chats'])
    assert.deepEqual(after[key], progress[key], `warning preserves ${key}`);
  assert.equal(after.question ?? null, progress.question ?? null);
  assert.deepEqual(f.read()[2], protectedRequest);
  assert.equal(sends(), sent, 'visibility never resends a request');
});
