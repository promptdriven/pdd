import test from 'node:test';
import assert from 'node:assert/strict';
import {writeFileSync} from 'node:fs';
import {join} from 'node:path';
import * as runner from '../src/workflow-runner.mjs';
import {fixture} from './helpers/workflow-runner-fixture.mjs';

const error = () => Object.assign(Error('temporary refusal'), {code:'herdr_failed'});
const save = run => writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
const closes = f => f.herdr.calls.filter(args => args[1] === 'close');
const sweep = f => runner.tidyRuns({}, f.ports);
const processInfo = pane => ({pane_id:pane.pane_id, shell_pid:100, foreground_process_group_id:100,
  foreground_processes:[{pid:100, name:'bash'}]});

for (const timing of ['before-sweep', 'after-intent']) {
  for (const condition of ['foreground-job', 'shell-child', 'unknown-process', 'foreign-pane', 'unknown-name', 'unavailable']) {
    test(`2709 repair 2: area cleanup retains ${condition} ${timing}`, async t => {
      const f = await fixture(t);
      assert.equal((await f.run()).exitCode, 0);
      const run = f.record(), chat = run.chats[0], pane = f.herdr.paneOf(chat), command = f.ports.herdr;
      run.state = 'completed'; chat.endedAt = f.clock; save(run);
      f.tick(16 * 60_000); f.herdr.idle(); f.herdr.calls.length = 0;
      const occupy = () => {
        pane.agent = null; pane.processInfo = processInfo(pane);
        if (condition === 'foreground-job') Object.assign(pane.processInfo, {
          foreground_process_group_id:200, foreground_processes:[{pid:200, name:'make'}]
        });
        if (condition === 'shell-child') pane.processInfo.foreground_processes.push({pid:200, name:'make'});
        if (condition === 'unknown-process') pane.processInfo = {pane_id:pane.pane_id};
        if (condition === 'foreign-pane') pane.processInfo.pane_id = 'another-pane';
        if (condition === 'unknown-name') pane.processInfo.foreground_processes[0].name = 'unknown';
      };
      let changed = timing === 'before-sweep';
      if (changed) occupy();
      f.ports.herdr = async args => {
        if (!changed && f.record().chats[0].closed) { changed = true; occupy(); }
        if (changed && condition === 'unavailable' && args[1] === 'process-info' && args.at(-1) === pane.pane_id) throw error();
        return command(args);
      };
      const result = condition === 'foreground-job'
        ? await runner.tidyRuns({graceMs:0, need:3}, f.ports) : await sweep(f);
      assert.ok(changed, 'the test must reach its intended cleanup boundary');
      assert.equal(result.exitCode, 0);
      assert.ok(f.herdr.paneOf(chat), 'automatic area cleanup must retain foreground work or uncertain occupancy');
      assert.equal(closes(f).length, 0);
      assert.equal(result.closed, 0); assert.equal(result.kept, 1);
      const reason = ['foreground-job', 'shell-child'].includes(condition) ? 'pane-busy' : 'pane-unknown';
      assert.deepEqual(f.record().cleanupKept, [{area:chat.area, reason}]);
      if (timing === 'after-intent') assert.ok(f.record().chats[0].closed, 'keep the durable intent pending');
      else assert.equal(f.record().chats[0].closed, undefined);
      f.ports.herdr = command; delete pane.processInfo;
      const retry = await sweep(f);
      assert.equal(retry.closed, 1); assert.equal(retry.kept, 0);
      assert.equal(f.herdr.paneOf(chat), undefined, 'authoritative shell-only evidence permits later cleanup');
      assert.equal(f.record().layout.phase, 'closed');
    });
  }
}

test('2709 repair 2: area cleanup rechecks its caller after the intent checkpoint', async t => {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record(), chat = run.chats[0], command = f.ports.herdr;
  run.state = 'completed'; chat.endedAt = f.clock; save(run);
  f.tick(16 * 60_000); f.herdr.idle(); f.herdr.calls.length = 0;
  f.ports.herdr = async args => {
    if (f.record().chats[0].closed) f.ports.env.HERDR_PANE_ID = chat.paneId;
    return command(args);
  };
  await sweep(f);
  assert.ok(f.herdr.paneOf(chat), 'a caller observed after checkpoint must survive');
  assert.equal(closes(f).length, 0);
  assert.deepEqual(f.record().cleanupKept, [{area:chat.area, reason:'caller-pane'}]);
  // Explicit cancel retains its caller too, but can close foreground work from another terminal.
  assert.equal((await runner.cancelRun({ref:'17', cwd:f.source}, f.ports)).exitCode, 0);
  assert.ok(f.herdr.paneOf(chat));
  f.ports.herdr = command; delete f.ports.env.HERDR_PANE_ID;
  const pane = f.herdr.paneOf(chat); pane.agent = null;
  pane.processInfo = {...processInfo(pane), foreground_process_group_id:200, foreground_processes:[{pid:200, name:'make'}]};
  assert.equal((await runner.cancelRun({ref:'17', cwd:f.source}, f.ports)).exitCode, 0);
  assert.equal(f.herdr.paneOf(chat), undefined, 'explicit cancellation still bypasses occupancy checks');
});

for (const failure of ['rejected', 'lost-acknowledgement']) {
  test(`2709 repair 2: tidy recovers a zero-chat shell after ${failure}`, async t => {
    const f = await fixture(t), command = f.ports.herdr;
    f.ports.herdr = async args => {
      if (args[0] === 'tab' && args[1] === 'create') throw error();
      return command(args);
    };
    assert.notEqual((await f.run()).exitCode, 0);
    const run = f.record(), shell = f.herdr.paneOf(run.layout);
    assert.equal(run.chats.length, 0); assert.ok(shell);
    let requests = 0;
    f.ports.herdr = async args => {
      if (args[0] === 'workspace' && args[1] === 'close') {
        requests++;
        if (failure === 'lost-acknowledgement') await command(args);
        throw error();
      }
      return command(args);
    };
    assert.equal((await runner.cancelRun({ref:'17', cwd:f.source}, f.ports)).exitCode, 0);
    assert.equal(f.record().state, 'cancelled');
    assert.equal(f.record().layout.phase, 'close_intent'); assert.equal(requests, 1);
    f.ports.herdr = async args => {
      if (args[0] === 'workspace' && args[1] === 'close') requests++;
      return command(args);
    };
    if (failure === 'rejected') {
      for (const condition of ['caller', 'foreground-job', 'unknown-process', 'foreign-terminal']) {
        const terminal = shell.terminal_id;
        if (condition === 'caller') f.ports.env.HERDR_PANE_ID = shell.pane_id;
        if (condition === 'foreground-job') shell.processInfo = {...processInfo(shell), foreground_process_group_id:200,
          foreground_processes:[{pid:200, name:'make'}]};
        if (condition === 'unknown-process') shell.processInfo = {pane_id:shell.pane_id};
        if (condition === 'foreign-terminal') shell.terminal_id = 'reused-terminal';
        const kept = await sweep(f);
        assert.equal(kept.kept, 1, 'tidy must count a retained zero-chat run shell');
        assert.equal(requests, 1, 'unsafe shell retries must send no close');
        assert.ok(f.herdr.paneOf(run.layout));
        assert.equal(f.record().layout.phase, 'close_intent');
        assert.equal(f.record().cleanupKept[0].area, 'run shell');
        delete f.ports.env.HERDR_PANE_ID; delete shell.processInfo; shell.terminal_id = terminal;
      }
      const release = runner.acquireRunLock(run.runDir);
      try {
        assert.equal((await sweep(f)).kept, 1, 'a locked zero-chat run must remain a retained candidate');
        assert.equal(requests, 1);
      } finally { release(); }
      assert.equal((await runner.tidyRuns({timeBudgetMs:0}, f.ports)).kept, 1,
        'the sweep budget must count deferred shell-only candidates');
      assert.equal(requests, 1);
    }
    const retried = await sweep(f);
    assert.equal(retried.exitCode, 0); assert.equal(retried.closed, 0); assert.equal(retried.kept, 0);
    assert.equal(f.herdr.paneOf(run.layout), undefined, 'tidy must reconcile a zero-chat shell');
    assert.equal(f.record().layout.phase, 'closed');
    assert.deepEqual(f.record().cleanupKept, []);
    assert.equal(requests, failure === 'rejected' ? 2 : 1, 'absence reconciliation must not repeat a close');
    assert.equal(f.herdr.panes.length, 1, 'retain the repository shell');
  });
}

test('2709 repair 2: tidy includes a zero-chat shell without a close intent', async t => {
  const f = await fixture(t), command = f.ports.herdr;
  f.ports.herdr = async args => {
    if (args[0] === 'tab' && args[1] === 'create') throw error();
    return command(args);
  };
  assert.notEqual((await f.run()).exitCode, 0);
  const run = f.record(), shell = f.herdr.paneOf(run.layout);
  f.ports.herdr = command; f.ports.env.HERDR_PANE_ID = shell.pane_id;
  assert.equal((await runner.cancelRun({ref:'17', cwd:f.source}, f.ports)).exitCode, 0);
  assert.notEqual(f.record().layout.phase, 'close_intent');
  assert.equal((await sweep(f)).kept, 1, 'tidy must count an owned shell even without a saved close intent');
  const before = f.record(); f.herdr.calls.length = 0;
  await runner.tidyRuns({dryRun:true}, f.ports);
  assert.deepEqual(f.record(), before); assert.equal(closes(f).length, 0);
  delete f.ports.env.HERDR_PANE_ID;
  await sweep(f);
  assert.equal(f.record().layout.phase, 'closed');
  assert.equal(f.herdr.paneOf(run.layout), undefined);
});
