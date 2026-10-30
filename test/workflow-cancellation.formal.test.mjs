import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { approveRun, cancelRun, changeRun, openRun, stepDone } from '../src/workflow-runner.mjs';
import { stopChats } from '../src/workflow-chat.mjs';
import { allocateIssueWorktree, releaseIssueClaim } from '../src/workflow-worktree.mjs';
import { readRun, resolveRun, writeRun } from '../src/workflow-runs.mjs';
import { cancellationFixture } from './helpers/cancellation-fixture.mjs';

const bytes = path => readFileSync(path, 'utf8');
const status = f => bytes(join(f.runDir, 'status.json'));
const index = f => bytes(join(f.stateDir, 'runs.json'));
const issue = f => ({ ref: '17', cwd: f.source });
const oldRef = f => ({ ref: f.old.runId, cwd: f.source });

// Independent oracle: the approved Rules to check in both cancellation Stories.
// Each successful prerequisite adds the next permitted effect. An unconfirmed
// answer/stop cannot reach persistence; save/release failure cannot allocate.
function oracle({ operation, answer, stop, fault }) {
  const trace = ['confirm'];
  if (answer !== true) return { trace, exitCode: 0, cancelled: false, replaced: false };
  trace.push('stop');
  if (!['stopped', 'absent'].includes(stop)) return { trace, exitCode: 1, cancelled: false, replaced: false };
  trace.push('save');
  if (fault === 'save') return { trace, exitCode: 1, cancelled: false, replaced: false };
  trace.push('durable', 'release');
  if (fault === 'release') return { trace, exitCode: 1, cancelled: true, replaced: false };
  trace.push('released');
  const replaced = operation === 'replace';
  if (replaced) trace.push('allocate', 'start');
  return { trace, exitCode: 0, cancelled: true, replaced };
}

// Each row owns a real Git repository, worktree, hard-linked issue claim, status
// and machine index. Dispose it immediately, including on assertion failure.
async function fixture(options, action) {
  let cleanup;
  const f = await cancellationFixture({ after(fn) { cleanup = fn; } }, options);
  try { return await action(f); } finally { await cleanup(); }
}

function retained(run) {
  const copy = structuredClone(run);
  // These are precisely the lifecycle/C3/journal fields allowed to change.
  for (const key of ['state', 'cancelled', 'gate', 'journalSeq', 'updatedAt', 'stage', 'steps', 'waitingFor', 'resumeDecisions', 'waitingDecision', 'stageAgent', 'runDir']) delete copy[key];
  return copy;
}

function cancelledView(f, old, directory = f.runDir) {
  const saved = readRun(directory);
  assert.equal(saved.state, 'cancelled');
  assert.deepEqual(saved.cancelled, { state: 'cancelled', at: 600000 });
  assert.equal(saved.gate, null);
  assert.equal(saved.stage, null);
  assert.equal(saved.stageAgent, null);
  assert.equal(saved.waitingDecision, null);
  assert.deepEqual(saved.resumeDecisions, []);
  assert.deepEqual(saved.waitingFor, { decisions: [], what: null });
  assert.equal(saved.journalSeq, old.journalSeq + 1);
  assert.deepEqual(retained(saved), retained(old));
  const entry = JSON.parse(index(f)).runs.find(run => run.runDir === directory);
  assert.equal(entry?.state, 'cancelled');
  return saved;
}

function preservedFiles(f, old, directory) {
  for (const [path, expected] of [
    [join(old.root, 'work.txt'), 'keep original work\n'],
    [join(old.root, 'uncommitted.txt'), 'keep uncommitted work\n'],
    [join(directory, 'journal.md'), 'keep journal bytes\n'],
    [join(directory, 'evidence.txt'), 'keep artifact bytes\n'],
  ]) assert.equal(bytes(path), expected);
  assert.ok(f.git('show-ref', '--verify', `refs/heads/${old.branch}`));
}

test('bounded cancellation order and custody: all 180 public runner input combinations', async t => {
  let checked = 0;
  // Full Cartesian product: 2 operations x 2 lifecycle states x 3 answers x
  // 5 stop observations x 3 persistence/release outcomes = 180 real executions.
  for (const operation of ['cancel', 'replace']) for (const state of ['running', 'waiting'])
    for (const answer of [false, undefined, true]) for (const stop of ['unknown', 'unavailable', 'throws', 'stopped', 'absent'])
      for (const fault of ['none', 'save', 'release']) {
        const row = { operation, state, answer, stop, fault }, expected = oracle(row);
        try {
          await fixture({}, async f => {
            if (state === 'waiting') {
              const gate = await stepDone({ step: 'scope', summary: 'Scope reviewed.', cwd: f.old.root }, f.ports);
              assert.equal(gate.exitCode, 0, gate.message);
            }
            const old = f.read(), before = status(f), beforeIndex = index(f), claim = bytes(f.claim), trace = [];
            f.events.length = 0;
            f.ports.confirm = async () => { trace.push('confirm'); return answer; };
            f.ports.stopChats = async run => {
              trace.push('stop');
              if (stop === 'throws') throw Error('bounded stop transport failure');
              if (stop === 'absent') return stopChats(run, f.ports);
              return { stopped: stop === 'stopped' ? true : stop === 'unknown' ? false : undefined };
            };
            f.ports.writeRun = (run, ports) => {
              if (run.runId === old.runId) {
                trace.push('save');
                if (fault === 'save') throw Error('bounded durable-save failure');
                writeRun(run, ports);
                cancelledView(f, old);
                assert.equal(bytes(f.claim), claim);
                trace.push('durable');
              } else writeRun(run, ports);
            };
            f.ports.releaseIssueClaim = async (request, ports) => {
              trace.push('release');
              assert.deepEqual(request, { cwd: f.source, runId: old.runId, issueNumber: 17 });
              cancelledView(f, old);
              assert.equal(bytes(f.claim), claim);
              if (fault === 'release') return { state: 'recovery_required', message: 'bounded release failure' };
              const result = await releaseIssueClaim(request, ports);
              assert.equal(result.state, 'released', result.message);
              assert.equal(existsSync(f.claim), false);
              trace.push('released');
              return result;
            };
            f.ports.allocateIssueWorktree = async (request, ports) => {
              trace.push('allocate');
              cancelledView(f, old);
              assert.equal(existsSync(f.claim), false);
              return allocateIssueWorktree(request, ports);
            };
            const start = f.ports.startChat;
            f.ports.startChat = async input => { trace.push('start'); return start(input); };
            const out = operation === 'cancel' ? await cancelRun(oldRef(f), f.ports)
              : await f.start({ name: 'feature', replace: old.runId });
            assert.equal(out.exitCode, expected.exitCode, out.message);
            assert.deepEqual(trace, expected.trace, 'Story prerequisite order');
            const archived = expected.replaced ? `${f.runDir}-cancelled-${old.runId.slice(0, 8)}` : f.runDir;
            if (expected.cancelled) cancelledView(f, old, archived);
            else { assert.equal(status(f), before); assert.equal(index(f), beforeIndex); }
            preservedFiles(f, old, archived);
            if (expected.replaced) {
              const fresh = f.read();
              assert.notEqual(fresh.runId, old.runId); assert.notEqual(fresh.root, old.root); assert.notEqual(fresh.branch, old.branch);
              assert.equal(fresh.workflow, 'feature'); assert.equal(fresh.chats.length, 1);
              assert.equal(JSON.parse(bytes(f.claim)).runId, fresh.runId);
              assert.equal(fresh.previous.at(-1).runId, old.runId);
              assert.equal((await resolveRun(old.runId, { cwd: f.source }, f.ports)).run.runDir, archived);
            } else if (!expected.cancelled || fault === 'release') assert.equal(bytes(f.claim), claim);
            else assert.equal(existsSync(f.claim), false);
            assert.equal(f.chats.length, expected.replaced ? 2 : 1, 'no second writer without the prerequisites');
            assert.ok(!f.events.some(event => event[0] === 'herdr' && event[1] !== 'pane' && event[1] !== 'tab'));
            if (expected.cancelled && fault !== 'release') {
              const current = status(f), currentIndex = index(f), currentClaim = existsSync(f.claim) ? bytes(f.claim) : null, count = trace.length;
              assert.equal((await cancelRun(oldRef(f), f.ports)).exitCode, 0);
              const late = await stepDone({ step: 'scope', summary: 'delayed old completion', cwd: old.root }, f.ports);
              assert.match(late.message, /cancelled.*Stop/s);
              assert.equal(status(f), current); assert.equal(index(f), currentIndex);
              assert.equal(existsSync(f.claim) ? bytes(f.claim) : null, currentClaim);
              assert.equal(trace.length, count, 'cancelled old ID and late done have no effects');
            }
          });
          checked++;
        } catch (error) { error.message = `${JSON.stringify(row)}: ${error.message}`; throw error; }
      }
  assert.equal(checked, 180);
  t.diagnostic(`Exhausted ${checked}/180 input combinations; actual status/index/C3/journal/claim/worktree observations.`);
});

test('bounded exact-holder selection and alpha issue references: 13 public runner cases', async t => {
  let checked = 0;
  for (const name of ['feature', 'bug']) for (const identity of ['missing', 'unrelated', 'cross-issue', 'archived', 'ambiguous']) {
    await fixture({}, async f => {
      let replace = 'missing-id';
      if (identity !== 'missing') {
        const other = { ...f.old, runId: identity === 'ambiguous' ? f.old.runId : 'bbbbbbbb-bbbb-4bbb-8bbb-bbbbbbbbbbbb',
          runDir: join(f.commonDir, 'pdd/runs', identity === 'cross-issue' ? '18' : '17-cancelled-bbbbbbbb'),
          number: identity === 'cross-issue' ? 18 : 17, state: 'cancelled' };
        if (identity === 'cross-issue') other.repo = 'other/project';
        writeRun(other, f.ports); replace = other.runId;
        if (identity === 'unrelated') replace = 'unrelated-run';
      }
      const before = status(f), beforeIndex = index(f), claim = bytes(f.claim);
      f.events.length = 0;
      const out = await f.start({ name, replace });
      assert.equal(out.exitCode, 1, `${name}/${identity}: ${out.message}`);
      assert.deepEqual(f.events, []);
      assert.equal(status(f), before); assert.equal(index(f), beforeIndex); assert.equal(bytes(f.claim), claim);
      preservedFiles(f, f.old, f.runDir);
      checked++;
    });
  }
  for (const ref of ['17', 'example/project#17', 'https://github.com/example/project/issues/17']) {
    await fixture({}, async f => {
      const out = await cancelRun({ ref, cwd: f.source }, f.ports);
      assert.equal(out.exitCode, 0, out.message); cancelledView(f, f.old);
      assert.equal(existsSync(f.claim), false); preservedFiles(f, f.old, f.runDir); checked++;
    });
  }
  assert.equal(checked, 13); t.diagnostic(`Exhausted ${checked}/13 exact-holder/reference cases.`);
});

test('bounded scope custody: all 20 layout/history/advice combinations', async t => {
  let checked = 0;
  const advice = [
    ['Scope is too large; use feature instead.', 'feature'],
    ['Recommend `feature` because the scope is larger', 'feature'],
    ['Recommended workflow: feature', 'feature'],
    ['Do not use feature; keep small-change', null],
    ['No switch is needed.', null],
  ];
  for (const override of [false, true]) for (const previous of [false, true]) for (const [summary, recommended] of advice) {
    await fixture({ override }, async f => {
      if (previous) assert.equal((await stepDone({ step: 'scope', summary: 'Recommend feature', cwd: f.old.root }, f.ports)).exitCode, 0);
      const scoped = await stepDone({ step: 'scope', summary, cwd: f.old.root }, f.ports);
      assert.equal(scoped.exitCode, 0, scoped.message);
      let gate = scoped;
      if (override) gate = await stepDone({ step: 'change', summary: 'Work reviewed.', cwd: f.old.root }, f.ports);
      assert.equal(gate.exitCode, 0, gate.message); assert.equal(f.read().gate.area, 'plan');
      if (recommended) {
        assert.deepEqual(f.read().scopeRecommendation, { workflow: recommended, reason: summary });
        assert.ok(gate.message.includes(summary));
        assert.ok(gate.message.includes(`pdd workflow run feature 17 --replace ${f.old.runId}`));
      } else { assert.equal(f.read().scopeRecommendation, undefined); assert.ok(!gate.message.includes('Scope recommends feature:')); }
      assert.equal(f.read().done.scope.summary, summary);
      if (!override) {
        assert.equal((await approveRun(issue(f), f.ports)).exitCode, 0);
        assert.equal((await stepDone({ step: 'change', summary: 'Work reviewed.', cwd: f.old.root }, f.ports)).exitCode, 0);
      }
      const count = f.chats.length, claim = bytes(f.claim), confirmations = f.events.filter(event => event[0] === 'confirm').length;
      for (const name of ['feature', 'bug']) {
        const refusal = await f.start({ name }); assert.equal(refusal.exitCode, 1, refusal.message);
        assert.ok(refusal.message.includes(`pdd workflow run ${name} 17 --replace ${f.old.runId}`));
        for (const command of ['status', 'open']) assert.ok(refusal.message.includes(`pdd workflow ${command} 17`));
        assert.ok(!/workflow resume|--decision/.test(refusal.message));
        if (recommended) { assert.ok(refusal.message.includes(summary)); assert.ok(refusal.message.includes(`pdd workflow run feature 17 --replace ${f.old.runId}`)); }
        else assert.ok(!refusal.message.includes('Scope recommends feature:'));
      }
      assert.equal(f.read().workflow, 'small-change'); assert.equal(bytes(f.claim), claim); assert.equal(f.chats.length, count);
      assert.equal(f.events.filter(event => event[0] === 'confirm').length, confirmations, 'advice does not authorize switching');
      checked++;
    });
  }
  assert.equal(checked, 20); t.diagnostic(`Exhausted ${checked}/20 layout/history/advice combinations, two requested workflows each.`);
});

test('bounded writer exclusion: all 30 public entrypoint/barrier schedules', async t => {
  let checked = 0;
  for (const operation of ['cancel', 'replace']) for (const barrier of ['confirmation', 'stop', 'release'])
    for (const competing of ['replace', 'done', 'approve', 'open', 'changes']) {
      await fixture({}, async f => {
        assert.equal((await stepDone({ step: 'scope', summary: 'Scope reviewed.', cwd: f.old.root }, f.ports)).exitCode, 0);
        const before = f.read(), effects = [], transport = f.ports.herdr;
        f.ports.isTTY = competing !== 'open';
        f.ports.findNativeSessions = async () => [{ id: '00000011-0000-4000-8000-000000000011' }];
        f.ports.herdr = async args => {
          if (args[0] === 'status' && args[1] === 'server') return { running: true };
          if (args[0] === 'tab' && ['get', 'focus'].includes(args[1])) return {};
          if (args[0] === 'pane' && args[1] === 'run' || args[0] === 'agent' && args[1] === 'prompt') { effects.push(args); return {}; }
          return transport(args);
        };
        let unblock, entered, paused = false;
        const wait = new Promise(resolve => { unblock = resolve; }), ready = new Promise(resolve => { entered = resolve; });
        const pause = async point => { if (barrier === point && !paused) { paused = true; entered(); await wait; } };
        f.ports.confirm = async () => { await pause('confirmation'); return true; };
        f.ports.stopChats = async () => { await pause('stop'); return { stopped: true }; };
        f.ports.releaseIssueClaim = async (request, ports) => { await pause('release'); return releaseIssueClaim(request, ports); };
        const first = operation === 'cancel' ? cancelRun(oldRef(f), f.ports) : f.start({ name: 'feature', replace: f.old.runId });
        await ready;
        try {
          const requests = {
            replace: () => f.start({ name: 'bug', replace: f.old.runId }),
            done: () => stepDone({ step: 'scope', summary: 'racing completion', cwd: f.old.root }, f.ports),
            approve: () => approveRun(issue(f), f.ports),
            open: () => openRun(issue(f), f.ports),
            changes: () => changeRun({ ...issue(f), text: 'Please review the work.' }, f.ports),
          };
          const out = await requests[competing]();
          assert.equal(out.exitCode, 1, `${operation}/${barrier}/${competing}: ${out.message}`);
          assert.match(out.message, /custody/); assert.deepEqual(effects, []); assert.equal(f.chats.length, 1);
        } finally { unblock(); await first; }
        assert.equal((await first).exitCode, 0);
        const directory = operation === 'replace' ? `${f.runDir}-cancelled-${before.runId.slice(0, 8)}` : f.runDir;
        const old = readRun(directory);
        assert.deepEqual(old.decisions, before.decisions); assert.deepEqual(old.done, before.done); assert.deepEqual(old.changes, before.changes);
        assert.equal(f.chats.length, operation === 'replace' ? 2 : 1);
        checked++;
      });
    }
  assert.equal(checked, 30); t.diagnostic(`Exhausted ${checked}/30 schedules: two owner operations, three held boundaries, five competing public entrypoints.`);
});
