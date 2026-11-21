import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { readWorkflowPrStatus } from '../src/workflow-github.mjs';
import {
  DEFAULT_CLOSE_GRACE_MS,
  closeGraceMs,
  finishedAt,
  closeFinishedChats,
  ensurePaneBudget,
} from '../src/workflow-chat.mjs';
import * as runner from '../src/workflow-runner.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const PR_URL = 'https://github.com/example/project/pull/23';
const save = (run) => writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));

async function runExplicitTidy(f, dryRun = false) {
  let message = '';
  const output = { write: (text) => { message += text; } };
  const exitCode = await runPdd(['workflow', 'tidy', ...(dryRun ? ['--dry-run'] : [])], {
    cwd: f.source,
    env: f.ports.env,
    stdout: output,
    stderr: output,
    packageRoot,
    workflowRunner: { tidyRuns: (input) => runner.tidyRuns(input, f.ports) },
  });
  return { exitCode, message };
}

async function waitingPrRun(t, { issue = '17', existingFixture = null } = {}) {
  const f = existingFixture ?? await fixture(t, { agent: 'claude', name: 'small-change' });
  f.ports.skipMetricsDelivery = true;
  if (issue !== '17') {
    const origExec = f.ports.execFile;
    f.ports.execFile = (file, args, opts) => {
      if (file === 'gh' && args[0] === 'api' && args[1] === `repos/example/project/issues/${issue}`) {
        return {
          stdout: JSON.stringify({
            number: Number(issue),
            state: 'open',
            html_url: `https://github.com/example/project/issues/${issue}`,
            title: `Issue ${issue}`,
            body: `Change for issue ${issue}.`,
          }),
        };
      }
      return origExec(file, args, opts);
    };
  }
  const started = issue === '17'
    ? await f.run()
    : await runner.startRun({ name: 'small-change', issue, agent: 'claude', cwd: f.source, packageRoot }, f.ports);
  assert.equal(started.exitCode, 0, started.message);
  const runDir = join(f.git(f.source, 'rev-parse', '--path-format=absolute', '--git-common-dir'), 'pdd', 'runs', String(issue));
  const readIssueRun = () => JSON.parse(readFileSync(join(runDir, 'status.json'), 'utf8'));
  const root = readIssueRun().root;
  let out = await runner.stepDone({ step: 'scope', summary: 'scope', cwd: root }, f.agentPorts());
  assert.equal(out.exitCode, 0, out.message);
  f.herdr.idle();
  out = await runner.approveRun({ ref: String(issue), cwd: f.source, packageRoot }, f.ports);
  assert.equal(out.exitCode, 0, out.message);
  writeFileSync(join(root, 'value.mjs'), `export const value = ${issue};\n`);
  f.git(root, 'add', '.');
  f.git(root, 'commit', '-qm', `change for issue ${issue}`);
  for (const step of ['change', 'verify', 'formal']) {
    f.tick();
    out = await runner.stepDone({ step, summary: `done ${step}`, cwd: root, packageRoot }, f.agentPorts());
    assert.equal(out.exitCode, 0, out.message);
  }
  const run = readIssueRun();
  assert.equal(run.state, 'waiting');
  assert.equal(run.pr.length, 1);
  f.herdr.idle();
  return { f, run, readIssueRun };
}

function stubPrView(f, prUrl, reply) {
  const origExec = f.ports.execFile;
  f.ports.execFile = (file, args, opts) => {
    if (file === 'gh' && args[0] === 'pr' && args[1] === 'view' && args[2] === prUrl) {
      const value = typeof reply === 'function' ? reply() : reply;
      return { stdout: JSON.stringify(value) };
    }
    return origExec(file, args, opts);
  };
}

test('2709: readWorkflowPrStatus preserves valid ISO mergedAt and omits invalid, null, or non-merged mergedAt', async () => {
  const execReturning = (payload) => ({
    execFile: async () => ({ stdout: JSON.stringify(payload) }),
  });

  for (const ts of [
    '2026-10-27T16:40:00Z',
    '2026-10-27T16:40:00.123Z',
    '2026-10-27T08:40:00-08:00',
    '2026-10-27T18:40:00+02:00',
  ]) {
    const status = await readWorkflowPrStatus(
      { cwd: '/tmp', url: PR_URL },
      execReturning({ state: 'MERGED', mergedAt: ts, statusCheckRollup: [], baseRefName: 'main', headRefOid: 'a'.repeat(40) }),
    );
    assert.equal(status.state, 'merged');
    assert.equal(status.mergedAt, ts);
  }

  for (const bad of [null, undefined, '', '   ', 12345, 'not-a-date', '2026-10-27', '2026-13-45T00:00:00Z']) {
    const status = await readWorkflowPrStatus(
      { cwd: '/tmp', url: PR_URL },
      execReturning({ state: 'MERGED', mergedAt: bad, statusCheckRollup: [] }),
    );
    assert.equal(status.state, 'merged');
    assert.equal(Object.hasOwn(status, 'mergedAt'), false, `expected mergedAt omitted for ${JSON.stringify(bad)}`);
  }

  for (const nonMerged of ['OPEN', 'CLOSED']) {
    const status = await readWorkflowPrStatus(
      { cwd: '/tmp', url: PR_URL },
      execReturning({ state: nonMerged, mergedAt: '2026-10-27T16:40:00Z', statusCheckRollup: [] }),
    );
    assert.equal(status.state, nonMerged.toLowerCase());
    assert.equal(Object.hasOwn(status, 'mergedAt'), false, `expected mergedAt omitted for ${nonMerged}`);
  }
});

test('2709: PR merged 20 minutes ago discovered by refreshPr gets endedAt from mergedAt and auto-closes on first sweep under default 15-min grace', async (t) => {
  const { f, run } = await waitingPrRun(t);
  const planChat = run.chats[0];
  const buildChat = run.chats[1];
  const prUrl = run.pr[0].url;

  // Give planChat an already-earlier endedAt (60 minutes ago) to prove refreshPr never overwrites it.
  const earlierPlanEnd = f.clock - 60 * 60_000;
  run.chats[0].endedAt = earlierPlanEnd;
  save(run);

  // Simulate PR having merged 20 minutes before discovery.
  const mergedAtMs = f.clock - 20 * 60_000;
  const mergedAtIso = new Date(mergedAtMs).toISOString();
  stubPrView(f, prUrl, { state: 'MERGED', mergedAt: mergedAtIso, statusCheckRollup: [] });

  // Very first automatic sweep with default 15-minute grace (no clock advance!).
  const swept = await runner.tidyRuns({ graceMs: DEFAULT_CLOSE_GRACE_MS }, f.ports);
  assert.equal(swept.exitCode, 0, swept.message);
  assert.equal(swept.closed, 2, 'both plan and build chats must close on the very first sweep');
  assert.equal(swept.kept, 0);

  const after = f.record();
  assert.equal(after.state, 'completed');
  assert.equal(after.pr[0].state, 'merged');
  assert.equal(after.pr[0].mergedAt, mergedAtIso);
  assert.equal(after.chats[0].endedAt, earlierPlanEnd, 'earlier area endedAt must not be overwritten');
  assert.equal(after.chats[1].endedAt, mergedAtMs, 'newly discovered merge must stamp endedAt from mergedAt');
  assert.equal(after.chats[1].closed?.reason, 'run-end');
  assert.equal(after.layout?.phase, 'closed');
  assert.equal(f.herdr.paneOf(planChat), undefined);
  assert.equal(f.herdr.paneOf(buildChat), undefined);
  assert.equal(f.herdr.panes.length, 1, 'only repository anchor pane remains');

  // Clock-skewed future mergedAt is clamped to discovery time (p.now()).
  const skew = await waitingPrRun(t);
  const skewMergedIso = new Date(skew.f.clock + 10 * 60_000).toISOString();
  stubPrView(skew.f, skew.run.pr[0].url, { state: 'MERGED', mergedAt: skewMergedIso, statusCheckRollup: [] });
  const statusRes = await runner.runStatus({ ref: '17', cwd: skew.f.source }, skew.f.ports);
  assert.equal(statusRes.exitCode, 0, statusRes.message);
  assert.equal(skew.f.record().pr[0].mergedAt, skewMergedIso);
  assert.equal(skew.f.record().chats.at(-1).endedAt, skew.f.clock, 'future mergedAt must clamp to now');

  // Legacy completed run saved without chat.endedAt prefers Date.parse(pr.mergedAt) when <= updatedAt.
  const legacy = await fixture(t, { agent: 'claude' });
  assert.equal((await legacy.run()).exitCode, 0);
  const legacyRun = legacy.record();
  const legacyMergedMs = legacy.clock - 20 * 60_000;
  legacyRun.state = 'completed';
  legacyRun.updatedAt = legacy.clock;
  legacyRun.pr = [{ number: 23, url: PR_URL, state: 'merged', mergedAt: new Date(legacyMergedMs).toISOString() }];
  delete legacyRun.chats[0].endedAt;
  save(legacyRun);
  legacy.herdr.idle();
  assert.equal(finishedAt(legacyRun, legacyRun.chats[0]), legacyMergedMs);

  // If legacy mergedAt > updatedAt, finishedAt falls back to updatedAt (never after updatedAt).
  assert.equal(
    finishedAt(
      { ...legacyRun, pr: [{ state: 'merged', mergedAt: new Date(legacy.clock + 60_000).toISOString() }] },
      legacyRun.chats[0],
    ),
    legacyRun.updatedAt,
  );

  // Legacy completed run closes immediately under default 15-min grace without advancing the clock.
  const legacySweep = await runner.tidyRuns({ graceMs: DEFAULT_CLOSE_GRACE_MS }, legacy.ports);
  assert.equal(legacySweep.exitCode, 0);
  assert.equal(legacySweep.closed, 1);
  assert.equal(legacy.herdr.panes.length, 1);
});

test('2709: PR merged 2 minutes ago respects default 15-min grace, closes immediately with PDD_HERDR_CLOSE_GRACE_SEC=0, and closes immediately with explicit pdd workflow tidy', async (t) => {
  // 1) Default 15-minute automatic grace protects a PR merged 2 minutes ago; PDD_HERDR_CLOSE_GRACE_SEC=0 closes it immediately.
  const { f, run } = await waitingPrRun(t);
  const buildChat = run.chats[1];
  const mergedAtMs = f.clock - 2 * 60_000;
  stubPrView(f, run.pr[0].url, { state: 'MERGED', mergedAt: new Date(mergedAtMs).toISOString(), statusCheckRollup: [] });

  assert.equal(closeGraceMs(f.ports), DEFAULT_CLOSE_GRACE_MS);
  const autoDefault = await runner.tidyRuns({ graceMs: closeGraceMs(f.ports) }, f.ports);
  assert.equal(autoDefault.exitCode, 0);
  assert.equal(f.record().state, 'completed');
  assert.equal(f.record().chats[1].endedAt, mergedAtMs);
  assert.ok(f.herdr.paneOf(buildChat), 'default 15-min automatic grace must keep recently merged chat');
  assert.ok((autoDefault.reasonCounts.grace ?? 0) >= 1);

  f.ports.env.PDD_HERDR_CLOSE_GRACE_SEC = '0';
  assert.equal(closeGraceMs(f.ports), 0);
  const budgetSweep = await ensurePaneBudget(1, {
    ...f.ports,
    sweepFinished: (options) => runner.tidyRuns(options, f.ports),
  });
  assert.ok(budgetSweep.closed >= 1, 'ensurePaneBudget with PDD_HERDR_CLOSE_GRACE_SEC=0 must close immediately');
  assert.equal(f.herdr.paneOf(buildChat), undefined);
  assert.equal(f.herdr.panes.length, 1, 'only repository anchor pane remains after zero-grace sweep');

  // 2) Explicit `pdd workflow tidy` (with default unset PDD_HERDR_CLOSE_GRACE_SEC) immediately closes
  //    a PR merged 2 minutes ago while protecting another active/unmerged waiting run!
  const g = await waitingPrRun(t, { issue: '17' });
  const active = await waitingPrRun(t, { issue: '18', existingFixture: g.f });
  const mergedRun = g.readIssueRun();
  const openRun = active.readIssueRun();
  const mergedPrUrl = mergedRun.pr[0].url;
  const openPrUrl = openRun.pr[0].url;
  const merged2mIso = new Date(g.f.clock - 2 * 60_000).toISOString();

  stubPrView(g.f, mergedPrUrl, { state: 'MERGED', mergedAt: merged2mIso, statusCheckRollup: [] });
  stubPrView(g.f, openPrUrl, { state: 'OPEN', mergedAt: null, statusCheckRollup: [] });

  // Note: openRun's earlier plan chat ended <15m ago (active run, NOT ended -> must stay protected under 15m grace!).
  const explicit = await runExplicitTidy(g.f);
  assert.equal(explicit.exitCode, 0, explicit.message);

  const afterMerged = g.readIssueRun();
  const afterOpen = active.readIssueRun();
  assert.equal(afterMerged.state, 'completed');
  assert.equal(afterMerged.chats.every((c) => c.closed?.confirmedAt), true);
  assert.equal(afterMerged.chats.at(-1).closed?.reason, 'run-end', 'explicit tidy must record run-end, not budget');
  assert.equal(afterMerged.layout?.phase, 'closed');
  assert.equal(g.f.herdr.paneOf(mergedRun.chats[1]), undefined, 'explicit tidy closes ended merged run immediately');

  assert.equal(afterOpen.state, 'waiting', 'unmerged open PR run must remain waiting');
  assert.ok(g.f.herdr.paneOf(openRun.chats[1]), 'unmerged open PR build chat must remain open');
  assert.ok(g.f.herdr.paneOf(openRun.chats[0]), 'active run recent earlier area still obeys 15m grace');
});

test('2709: invalid PDD_HERDR_CLOSE_GRACE_SEC fails cleanly with invalid_close_grace across all entrypoints', async (t) => {
  assert.equal(closeGraceMs({ env: {} }), DEFAULT_CLOSE_GRACE_MS);
  assert.equal(closeGraceMs({ env: { PDD_HERDR_CLOSE_GRACE_SEC: '0' } }), 0);
  assert.equal(closeGraceMs({ env: { PDD_HERDR_CLOSE_GRACE_SEC: '30' } }), 30_000);

  const f = await fixture(t, { agent: 'claude' });
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  run.state = 'completed';
  run.chats[0].endedAt = f.clock - 20 * 60_000;
  save(run);
  f.herdr.idle();

  const invalidValues = ['', '-1', 'abc', '1.5', ' 10', '9999999999999999'];
  for (const bad of invalidValues) {
    assert.throws(
      () => closeGraceMs({ env: { PDD_HERDR_CLOSE_GRACE_SEC: bad } }),
      (err) => err?.code === 'invalid_close_grace' && /PDD_HERDR_CLOSE_GRACE_SEC/.test(err.message),
      `closeGraceMs must reject ${JSON.stringify(bad)}`,
    );

    const badPorts = { ...f.ports, env: { ...f.ports.env, PDD_HERDR_CLOSE_GRACE_SEC: bad } };
    await assert.rejects(
      () => closeFinishedChats(structuredClone(run), badPorts),
      (err) => err?.code === 'invalid_close_grace' && /PDD_HERDR_CLOSE_GRACE_SEC/.test(err.message),
      `closeFinishedChats must reject ${JSON.stringify(bad)}`,
    );
    await assert.rejects(
      () => ensurePaneBudget(1, badPorts),
      (err) => err?.code === 'invalid_close_grace' && /PDD_HERDR_CLOSE_GRACE_SEC/.test(err.message),
      `ensurePaneBudget must reject ${JSON.stringify(bad)}`,
    );

    const tidyResult = await runner.tidyRuns({}, badPorts);
    assert.equal(tidyResult.exitCode, 1, `tidyRuns must fail cleanly for ${JSON.stringify(bad)}`);
    assert.match(tidyResult.message, /PDD_HERDR_CLOSE_GRACE_SEC/);
    assert.equal(tidyResult.closed, 0);
  }

  // CLI `pdd workflow tidy` and `startRun` both fail cleanly before mutating Herdr or Git.
  f.ports.env.PDD_HERDR_CLOSE_GRACE_SEC = '-5';
  const branchesBefore = f.git(f.source, 'branch', '--format=%(refname)');
  const panesBefore = f.herdr.panes.length;
  f.herdr.calls.length = 0;

  const cliTidy = await runExplicitTidy(f);
  assert.equal(cliTidy.exitCode, 1);
  assert.match(cliTidy.message, /PDD_HERDR_CLOSE_GRACE_SEC/);
  assert.equal(f.herdr.panes.length, panesBefore);

  const started = await f.run();
  assert.notEqual(started.exitCode, 0);
  assert.match(started.message, /PDD_HERDR_CLOSE_GRACE_SEC/);
  assert.equal(f.git(f.source, 'branch', '--format=%(refname)'), branchesBefore, 'no branch created on invalid_close_grace');
  assert.equal(f.herdr.panes.length, panesBefore, 'no panes opened on invalid_close_grace');
});

test('2709: 20 sequential finished runs leave 0 finished panes open and pane budget refuses cleanly at limit', async (t) => {
  const f = await fixture(t, { agent: 'claude', name: 'small-change' });
  f.ports.skipMetricsDelivery = true;

  // Keep a mutable map of per-PR view overrides so mergedAt reflects each run's merge time.
  const prReplies = new Map();
  const origExec = f.ports.execFile;
  f.ports.execFile = (file, args, opts) => {
    if (file === 'gh' && args[0] === 'pr' && args[1] === 'view' && prReplies.has(args[2])) {
      return { stdout: JSON.stringify(prReplies.get(args[2])) };
    }
    return origExec(file, args, opts);
  };

  for (let i = 0; i < 20; i++) {
    const mode = i % 4;
    if (mode === 0 || mode === 1) {
      // Complete a PR run: mode 0 merged 20m ago (automatic grace sweep); mode 1 merged 2m ago (explicit tidy).
      const start = await f.run();
      assert.equal(start.exitCode, 0, `run ${i + 1}: ${start.message}`);
      const root = f.record().root;
      let reply = await runner.stepDone({ step: 'scope', summary: `scope ${i}`, cwd: root }, f.agentPorts());
      assert.equal(reply.exitCode, 0, reply.message);
      f.herdr.idle();
      reply = await runner.approveRun({ ref: '17', cwd: f.source, packageRoot }, f.ports);
      assert.equal(reply.exitCode, 0, reply.message);
      writeFileSync(join(root, 'value.mjs'), `export const value = ${i + 2};\n`);
      f.git(root, 'add', 'value.mjs');
      f.git(root, 'commit', '-qm', `change ${i + 1}`);
      for (const step of ['change', 'verify', 'formal']) {
        f.tick();
        reply = await runner.stepDone({ step, summary: `${step} ${i}`, cwd: root, packageRoot }, f.agentPorts());
        assert.equal(reply.exitCode, 0, reply.message);
      }
      f.herdr.idle();
      const prUrl = f.record().pr[0].url;
      if (mode === 0) {
        // Merged 20m ago -> closes on very first automatic 15-min grace sweep!
        const mergedAt = new Date(f.clock - 20 * 60_000).toISOString();
        prReplies.set(prUrl, { state: 'MERGED', mergedAt, statusCheckRollup: [] });
        const auto = await runner.tidyRuns({ graceMs: DEFAULT_CLOSE_GRACE_MS }, f.ports);
        assert.equal(auto.exitCode, 0, auto.message);
      } else {
        // Merged 2m ago -> explicit pdd workflow tidy closes immediately!
        const mergedAt = new Date(f.clock - 2 * 60_000).toISOString();
        prReplies.set(prUrl, { state: 'MERGED', mergedAt, statusCheckRollup: [] });
        const tidy = await runExplicitTidy(f);
        assert.equal(tidy.exitCode, 0, tidy.message);
      }
    } else if (mode === 2) {
      // Cancelled run closes its panes cleanly immediately.
      const start = await f.run();
      assert.equal(start.exitCode, 0, `run ${i + 1}: ${start.message}`);
      const cancelled = await runner.cancelRun({ ref: '17', cwd: f.source }, f.ports);
      assert.equal(cancelled.exitCode, 0, cancelled.message);
    } else {
      // Replaced run: start an idle run, replace it with a second start, then cancel the replacement.
      const first = await f.run();
      assert.equal(first.exitCode, 0, `run ${i + 1}a: ${first.message}`);
      f.herdr.idle();
      const replaced = await f.run();
      assert.equal(replaced.exitCode, 0, `run ${i + 1}b: ${replaced.message}`);
      const cancelled = await runner.cancelRun({ ref: '17', cwd: f.source }, f.ports);
      assert.equal(cancelled.exitCode, 0, cancelled.message);
    }

    assert.equal(f.herdr.panes.length, 1, `run ${i + 1} (mode ${mode}) must leave 0 finished panes open (only repo anchor)`);
    assert.equal(f.record().layout?.phase, 'closed', `run ${i + 1} workspace must be closed`);
    assert.ok(existsSync(f.record().root), `run ${i + 1} worktree preserved on disk`);
  }

  // At pane budget limit with an active live run, a new start refuses cleanly without opening any panes.
  const active = await f.run();
  assert.equal(active.exitCode, 0, active.message);
  const activePanes = f.herdr.panes.length;
  const branchesBefore = f.git(f.source, 'branch', '--format=%(refname)');
  f.ports.env.PDD_HERDR_PANE_BUDGET = String(activePanes);
  f.herdr.calls.length = 0;

  const refused = await f.run();
  assert.notEqual(refused.exitCode, 0);
  assert.match(refused.message, /herdr_pane_budget/);
  assert.equal(f.herdr.panes.length, activePanes, 'pane budget refusal must open 0 panes');
  assert.equal(f.git(f.source, 'branch', '--format=%(refname)'), branchesBefore, 'pane budget refusal must allocate 0 branches');
  assert.equal(f.herdr.calls.some((args) => ['create', 'open', 'run'].includes(args[1])), false);
});

test('2709 R1 P1-1: ensurePaneBudget passes closeGraceMs(ports) to sweepFinished and rejects invalid values before sweeping', async () => {
  const seen = [];
  let herdrCalls = 0;
  const herdr = async () => {
    herdrCalls++;
    return { result: { type: 'pane_list', panes: [{ pane_id: 'p1', workspace_id: 'w1', tab_id: 't1', terminal_id: 'term1' }] } };
  };
  const sweepFinished = async (options) => {
    seen.push(options);
    return { closed: 0, reasonCounts: {} };
  };

  await ensurePaneBudget(1, { env: {}, herdr, sweepFinished });
  await ensurePaneBudget(1, { env: { PDD_HERDR_CLOSE_GRACE_SEC: '0' }, herdr, sweepFinished });
  await ensurePaneBudget(1, { env: { PDD_HERDR_CLOSE_GRACE_SEC: '30' }, herdr, sweepFinished });
  assert.deepEqual(seen, [
    { graceMs: DEFAULT_CLOSE_GRACE_MS },
    { graceMs: 0 },
    { graceMs: 30_000 },
  ]);

  const callsBefore = herdrCalls;
  const sweepsBefore = seen.length;
  for (const bad of ['abc', '-1']) {
    await assert.rejects(
      () => ensurePaneBudget(1, { env: { PDD_HERDR_CLOSE_GRACE_SEC: bad }, herdr, sweepFinished }),
      (err) => err?.code === 'invalid_close_grace' && /PDD_HERDR_CLOSE_GRACE_SEC/.test(err.message),
    );
  }
  assert.equal(seen.length, sweepsBefore, 'invalid_close_grace must fail before invoking sweepFinished');
  assert.equal(herdrCalls, callsBefore, 'invalid_close_grace must fail before calling Herdr');
});

test('2709 R1 P1-2: 2-PR run selects per-area / latest mergedAt and absent panes persist chat.closed.confirmedAt', async (t) => {
  const now = Date.parse('2026-10-27T19:00:00Z');
  const pr1MergedMs = now - 2 * 60 * 60_000; // 2 hours ago
  const pr2MergedMs = now - 2 * 60_000;      // 2 minutes ago
  const pr1MergedIso = new Date(pr1MergedMs).toISOString();
  const pr2MergedIso = new Date(pr2MergedMs).toISOString();

  // 1) finishedAt on a legacy 2-PR completed run without chat.endedAt
  const legacyTwoPrRun = {
    state: 'completed',
    updatedAt: now,
    startedAt: now - 3 * 60 * 60_000,
    pr: [
      { number: 23, stage: 'prompt', state: 'merged', mergedAt: pr1MergedIso },
      { number: 24, stage: 'code', state: 'merged', mergedAt: pr2MergedIso },
    ],
    chats: [
      { area: 'story', startedAt: now - 3 * 60 * 60_000 },
      { area: 'prompt', startedAt: now - 2.5 * 60 * 60_000 },
      { area: 'code', startedAt: now - 30 * 60_000 },
    ],
  };
  assert.equal(finishedAt(legacyTwoPrRun, legacyTwoPrRun.chats[1]), pr1MergedMs, 'PR 1 area chat uses PR 1 mergedAt');
  assert.equal(finishedAt(legacyTwoPrRun, legacyTwoPrRun.chats[2]), pr2MergedMs, 'PR 2 area chat uses PR 2 mergedAt (not PR 1)');
  assert.equal(finishedAt(legacyTwoPrRun, legacyTwoPrRun.chats[0]), pr2MergedMs, 'unmatched area uses latest (Math.max) mergedAt');

  // 2) Live 2-PR waiting run discovered by refreshPr + automatic 15-min grace sweep:
  //    PR 1 (prompt) merged 2h ago closes immediately; PR 2 (code) merged 2m ago stays protected by 15m grace!
  const { f, run } = await waitingPrRun(t);
  const promptChat = run.chats[0];
  const codeChat = run.chats[1];
  const promptPrUrl = 'https://github.com/example/project/pull/22';
  const codePrUrl = run.pr[0].url;
  const runPr1MergedMs = f.clock - 2 * 60 * 60_000;
  const runPr2MergedMs = f.clock - 2 * 60_000;
  const runPr1MergedIso = new Date(runPr1MergedMs).toISOString();
  const runPr2MergedIso = new Date(runPr2MergedMs).toISOString();

  delete run.chats[0].endedAt;
  delete run.chats[1].endedAt;
  run.pr = [
    { number: 22, url: promptPrUrl, stage: promptChat.area, state: 'open' },
    { ...run.pr[0], stage: codeChat.area, state: 'open' },
  ];
  save(run);

  stubPrView(f, promptPrUrl, { state: 'MERGED', mergedAt: runPr1MergedIso, statusCheckRollup: [] });
  stubPrView(f, codePrUrl, { state: 'MERGED', mergedAt: runPr2MergedIso, statusCheckRollup: [] });

  const autoSweep = await runner.tidyRuns({ graceMs: DEFAULT_CLOSE_GRACE_MS }, f.ports);
  assert.equal(autoSweep.exitCode, 0, autoSweep.message);
  const afterAuto = f.record();
  assert.equal(afterAuto.state, 'completed');
  assert.equal(afterAuto.chats[0].endedAt, runPr1MergedMs, 'prompt chat gets PR 1 mergedAt');
  assert.equal(afterAuto.chats[1].endedAt, runPr2MergedMs, 'code chat gets PR 2 mergedAt (NOT PR 1)');
  assert.equal(f.herdr.paneOf(promptChat), undefined, 'PR 1 chat merged 2h ago closes immediately');
  assert.ok(f.herdr.paneOf(codeChat), 'PR 2 chat merged 2m ago stays protected under 15m grace');
  assert.deepEqual(afterAuto.cleanupKept, [{ area: codeChat.area, reason: 'grace' }]);

  const explicit = await runExplicitTidy(f);
  assert.equal(explicit.exitCode, 0, explicit.message);
  assert.equal(f.herdr.paneOf(codeChat), undefined, 'explicit tidy closes PR 2 chat immediately');
  assert.equal(f.herdr.panes.length, 1);

  // 3) Already-closed / absent pane discovered during refreshPr + tidy persists chat.closed.confirmedAt durably
  //    with zero close commands sent to Herdr.
  const absent = await waitingPrRun(t);
  const absentChat = absent.run.chats[1];
  await absent.f.herdr.herdr(['workspace', 'close', absentChat.workspaceId]);
  absent.f.herdr.calls.length = 0;
  stubPrView(absent.f, absent.run.pr[0].url, {
    state: 'MERGED',
    mergedAt: new Date(absent.f.clock - 20 * 60_000).toISOString(),
    statusCheckRollup: [],
  });
  const reconciled = await runner.tidyRuns({ graceMs: DEFAULT_CLOSE_GRACE_MS }, absent.f.ports);
  assert.equal(reconciled.exitCode, 0, reconciled.message);
  const savedAbsent = absent.f.record();
  assert.equal(savedAbsent.state, 'completed');
  assert.equal(savedAbsent.chats.every((c) => Number.isFinite(c.closed?.confirmedAt) && c.closed?.reason === 'absent'), true);
  assert.equal(savedAbsent.layout?.phase, 'closed');
  assert.equal(
    absent.f.herdr.calls.some((args) => args[1] === 'close'),
    false,
    'absent reconciliation must send zero close calls to Herdr',
  );
});

test('2709 R1 P1-3: cancelRun immediately closes all run panes and --new replacement closes old tab and stamps endedAt', async (t) => {
  // 1) Explicit cancel immediately closes all run panes (0 run panes left open).
  const f = await fixture(t, { agent: 'claude', name: 'small-change' });
  f.ports.skipMetricsDelivery = true;
  assert.equal((await f.run()).exitCode, 0);
  const runBeforeCancel = f.record();
  assert.ok(f.herdr.panes.length > 1);

  const cancelled = await runner.cancelRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(cancelled.exitCode, 0, cancelled.message);
  const afterCancel = f.record();
  assert.equal(afterCancel.state, 'cancelled');
  assert.ok(Number.isFinite(afterCancel.chats[0].endedAt), 'cancel must stamp chat.endedAt');
  assert.equal(afterCancel.chats[0].closed?.reason, 'cancel');
  assert.ok(Number.isFinite(afterCancel.chats[0].closed?.confirmedAt), 'cancel must persist chat.closed.confirmedAt');
  assert.equal(afterCancel.layout?.phase, 'closed');
  assert.equal(f.herdr.paneOf(runBeforeCancel.chats[0]), undefined);
  assert.equal(f.herdr.panes.length, 1, 'only repository anchor pane remains after cancel');

  // 2) Chat replacement (--new) closes the old tab without leaking panes and stamps endedAt on abandonedChats.
  const g = await fixture(t, { agent: 'claude', name: 'small-change' });
  g.ports.skipMetricsDelivery = true;
  assert.equal((await g.run()).exitCode, 0);
  const originalChat = g.record().chats[0];
  const panesBeforeReplace = g.herdr.panes.length;
  g.tick(5_000);

  const replaced = await runner.openRun({ ref: '17', cwd: g.source, newSession: true, packageRoot }, g.ports);
  assert.equal(replaced.exitCode, 0, replaced.message);
  const afterReplace = g.record();
  assert.equal(g.herdr.paneOf(originalChat), undefined, '--new must close the superseded chat tab');
  assert.equal(g.herdr.panes.length, panesBeforeReplace, '--new must not leak any extra Herdr panes');
  assert.equal(afterReplace.abandonedChats?.length, 1);
  assert.equal(afterReplace.abandonedChats[0].paneId, originalChat.paneId);
  assert.ok(Number.isFinite(afterReplace.abandonedChats[0].endedAt), 'superseded chat in abandonedChats must carry endedAt');
});
