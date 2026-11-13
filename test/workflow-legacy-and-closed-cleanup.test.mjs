import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';
import { approveRun, tidyRuns, runStatus, startRun, stepDone } from '../src/workflow-runner.mjs';

const save = run => writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));

async function legacyCompleted(t, { nullTerminal = false, omitLayout = false } = {}) {
  const f = await fixture(t, { agent: 'claude' });
  f.ports.skipMetricsDelivery = true;
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  run.state = 'completed';
  run.chats[0].endedAt = f.clock;
  if (nullTerminal) run.chats[0].terminalId = null;
  else delete run.chats[0].terminalId;
  if (omitLayout) delete run.layout;
  else run.layout = null;
  save(run);
  f.tick(16 * 60_000);
  f.herdr.idle();
  return { f, run, chat: run.chats[0] };
}

for (const [label, opts] of [
  ['omitted terminalId and null layout', { nullTerminal: false, omitLayout: false }],
  ['null terminalId and omitted layout', { nullTerminal: true, omitLayout: true }],
]) {
  test(`3345: tidy closes legacy completed chat and run workspace (${label}) while keeping repo workspace`, async t => {
    const { f, run, chat } = await legacyCompleted(t, opts);
    const liveChatPane = f.herdr.paneOf(chat);
    const expectedTerminal = liveChatPane.terminal_id;
    const repoWorkspaceId = chat.repoWorkspaceId;
    assert.ok(repoWorkspaceId, 'fixture creates a repository parent workspace');

    // Status classifies both the legacy chat and the legacy run shell under done (0 unowned)
    const beforeStatus = JSON.parse((await runStatus({ cwd: f.source, json: true }, f.ports)).message);
    assert.equal(beforeStatus.herdr.finishedOpen, 1);
    assert.equal(beforeStatus.herdr.owners.done, 2);
    assert.equal(beforeStatus.herdr.owners.working, 0);

    // Dry-run reports 1 eligible chat without mutating status.json or Herdr
    const rawBefore = readFileSync(join(run.runDir, 'status.json'), 'utf8');
    const dry = await tidyRuns({ dryRun: true }, f.ports);
    assert.equal(dry.closed, 1);
    assert.equal(dry.kept, 0);
    assert.equal(readFileSync(join(run.runDir, 'status.json'), 'utf8'), rawBefore);

    // Real tidy checkpoints the adopted terminalId before tab close, closes the run workspace, and retains the repo shell
    let checkedAtTabClose = false;
    const origHerdr = f.ports.herdr;
    f.ports.herdr = async args => {
      if (args[0] === 'tab' && args[1] === 'close') {
        checkedAtTabClose = true;
        assert.equal(f.record().chats[0].terminalId, expectedTerminal);
        assert.ok(f.record().chats[0].closed);
      }
      return origHerdr(args);
    };
    const swept = await tidyRuns({}, f.ports);
    assert.equal(swept.closed, 1);
    assert.equal(swept.kept, 0);
    assert.ok(checkedAtTabClose);
    assert.equal(f.herdr.workspaces.some(w => w.workspace_id === chat.workspaceId), false, 'run workspace closed');
    assert.equal(f.herdr.workspaces.some(w => w.workspace_id === repoWorkspaceId), true, 'repository anchor workspace retained');
    assert.equal(f.herdr.panes.length, 1, 'only repository shell pane remains');
    assert.equal(f.record().layout?.phase, 'closed');

    // Second sweep does zero work on the already-closed legacy run
    f.herdr.calls.length = 0;
    const second = await tidyRuns({}, f.ports);
    assert.equal(second.closed, 0);
    assert.equal(second.kept, 0);
    assert.equal(f.herdr.calls.length, 0);
  });
}

test('3345: legacy chat missing terminalId still fails closed on label mismatch, unconfirmed start, or busy foreground', async t => {
  for (const guard of ['wrong-label', 'unconfirmed-start', 'busy-shell']) {
    const { f, run, chat } = await legacyCompleted(t);
    if (guard === 'wrong-label') f.herdr.tabs.find(tab => tab.tab_id === chat.tabId).label = 'other-tab';
    if (guard === 'unconfirmed-start') { run.chats[0].startUnconfirmed = true; save(run); }
    if (guard === 'busy-shell') {
      const pane = f.herdr.paneOf(chat);
      pane.agent = null;
      pane.processInfo = { pane_id: pane.pane_id, shell_pid: 100, foreground_process_group_id: 205, foreground_processes: [{ pid: 205, name: 'vim' }] };
    }
    const result = await tidyRuns({}, f.ports);
    assert.equal(result.closed, 0, guard);
    assert.equal(result.kept, 1, guard);
    assert.equal(result.reasonCounts[guard === 'busy-shell' ? 'pane-busy' : 'chat-identity'], 1, guard);
    assert.ok(f.herdr.paneOf(chat), `retained pane for ${guard}`);
  }
});

test('3345: shell-only legacy run closes its verified run workspace, while explicit createdWorkspaceId:null stays protected', async t => {
  // 1. Shell-only legacy run (chat already closed earlier, layout still null)
  const { f, run, chat } = await legacyCompleted(t);
  await f.herdr.herdr(['tab', 'close', chat.tabId]);
  run.chats[0].state = 'ended';
  run.chats[0].closed = { at: f.clock, reason: 'run-end', screen: null, confirmedAt: f.clock };
  save(run);
  const result = await tidyRuns({}, f.ports);
  assert.equal(result.kept, 0);
  assert.equal(f.herdr.workspaces.some(w => w.workspace_id === chat.workspaceId), false, 'legacy shell-only workspace closed');
  assert.equal(f.record().layout?.phase, 'closed');

  // 2. Explicit createdWorkspaceId: null is NEVER adopted or closed
  const g = await fixture(t, { agent: 'claude' });
  g.ports.skipMetricsDelivery = true;
  assert.equal((await g.run()).exitCode, 0);
  const grun = g.record(), gchat = grun.chats[0];
  grun.state = 'completed';
  grun.chats[0].endedAt = g.clock;
  grun.layout.createdWorkspaceId = null;
  save(grun);
  g.tick(16 * 60_000);
  g.herdr.idle();
  const guarded = await tidyRuns({}, g.ports);
  assert.equal(guarded.closed, 1, 'chat tab may close');
  assert.equal(guarded.reasonCounts.layout_cleanup_uncertain, 1, 'unproved workspace creation stays open');
  assert.equal(g.herdr.workspaces.some(w => w.workspace_id === gchat.workspaceId), true);
});

async function waitingSmallChangeWithPr(t) {
  const f = await fixture(t, { agent: 'claude', name: 'small-change' });
  f.ports.skipMetricsDelivery = true;
  assert.equal((await f.run()).exitCode, 0);
  const root = f.record().root;
  assert.equal((await stepDone({ step: 'scope', summary: 'scope', cwd: root }, f.agentPorts())).exitCode, 0);
  f.tick(16 * 60_000);
  f.herdr.idle();
  assert.equal((await approveRun({ ref: '17', cwd: f.source, packageRoot }, f.ports)).exitCode, 0);
  writeFileSync(join(root, 'value.mjs'), 'export const value = 2;\n');
  f.git(root, 'add', '.');
  f.git(root, 'commit', '-qm', 'use value two');
  for (const step of ['change', 'verify', 'formal']) {
    f.tick();
    const out = await stepDone({ step, summary: step, cwd: root }, f.agentPorts());
    assert.equal(out.exitCode, 0, out.message);
  }
  assert.equal(f.record().state, 'waiting');
  assert.equal(f.prs.length, 1);
  f.herdr.idle();
  return f;
}

test('3346: saved closed PR on waiting run is cancelled offline by tidy and unblocks pane budget', async t => {
  const f = await waitingSmallChangeWithPr(t);
  const run = f.record(), chat = run.chats.at(-1);
  run.pr[0].state = 'closed';
  run.prState = { state: 'closed', ci: 'none', checkedAt: f.clock };
  save(run);
  f.tick(16 * 60_000);

  // Dry-run sees both the finished plan chat and the closed-PR build chat as eligible without mutating status.json
  const beforeBytes = readFileSync(join(run.runDir, 'status.json'), 'utf8');
  const dry = await tidyRuns({ dryRun: true }, f.ports);
  assert.equal(dry.closed, 2);
  assert.equal(readFileSync(join(run.runDir, 'status.json'), 'utf8'), beforeBytes);

  // Real tidy cancels the run with zero GitHub calls and closes both chat tabs and the run workspace
  let ghCalls = 0;
  const origExec = f.ports.execFile;
  f.ports.execFile = (file, args, opts) => {
    if (file === 'gh') ghCalls++;
    return origExec(file, args, opts);
  };
  const swept = await tidyRuns({}, f.ports);
  assert.equal(ghCalls, 0, 'already-saved closed PR needs zero gh calls');
  assert.equal(swept.closed, 2);
  assert.equal(swept.kept, 0);
  assert.equal(f.record().state, 'cancelled');
  assert.equal(f.record().cancelled?.reason, 'pr-closed');
  assert.equal(f.herdr.workspaces.some(w => w.workspace_id === chat.workspaceId), false);
  assert.equal(f.herdr.panes.length, 1, 'only repository shell remains');
});

test('3346: externally closed PR or GitHub issue is refreshed, stops counting as working, and frees pane budget for a new run', async t => {
  for (const mode of ['closed-pr', 'closed-issue']) {
    const f = await waitingSmallChangeWithPr(t);
    const activeChat = f.record().chats.at(-1);
    const origExec = f.ports.execFile;
    let issue17Closed = mode === 'closed-issue';
    let pr23Closed = true;
    if (mode === 'closed-issue') {
      // Simulate a waiting run at a gate with no open PR whose GitHub issue was closed externally
      const r = f.record();
      r.pr = [];
      r.prState = null;
      r.gate = { id: 'gate-1', area: 'build', kind: 'approve-pr', at: f.clock };
      save(r);
    }
    f.ports.execFile = (file, args, opts) => {
      if (file === 'gh' && args[0] === 'pr' && args[1] === 'view' && pr23Closed)
        return { stdout: JSON.stringify({ state: 'CLOSED', mergedAt: null, statusCheckRollup: [], body: f.prs[0]?.body ?? '' }) };
      if (file === 'gh' && args[0] === 'api' && args[1] === 'repos/example/project/issues/17')
        return { stdout: JSON.stringify({ number: 17, state: issue17Closed ? 'closed' : 'open', closed_at: new Date(f.clock).toISOString(), html_url: 'https://github.com/example/project/issues/17', title: 'Use value two', body: 'Value must be two.' }) };
      if (file === 'gh' && args[0] === 'api' && args[1] === 'repos/example/project/issues/18')
        return { stdout: JSON.stringify({ number: 18, state: 'open', html_url: 'https://github.com/example/project/issues/18', title: 'Next issue', body: 'Next change.' }) };
      return origExec(file, args, opts);
    };

    // Tight pane budget: 3 panes currently open (repo shell + #17 root + #17 build chat), budget=4, new run needs 3 -> must reclaim #17!
    f.ports.env.PDD_HERDR_PANE_BUDGET = '4';
    f.tick(60_000);
    const next = await startRun({ name: 'small-change', issue: '18', agent: 'claude', cwd: f.source, packageRoot }, f.ports);
    assert.equal(next.exitCode, 0, `${mode}: ${next.message}`);
    assert.equal(f.record().state, 'cancelled', `${mode} marked #17 cancelled`);
    assert.equal(f.record().cancelled?.reason, mode === 'closed-pr' ? 'pr-closed' : 'issue-closed');
    assert.equal(f.herdr.workspaces.some(w => w.workspace_id === activeChat.workspaceId), false, `${mode} closed #17 workspace`);

    const status = JSON.parse((await runStatus({ cwd: f.source, json: true }, f.ports)).message);
    assert.equal(status.runs.length, 1);
    assert.equal(status.runs[0].number, 18);
  }
});

test('3346: live manual waiting run with open PR and open issue stays working and protected', async t => {
  const f = await waitingSmallChangeWithPr(t);
  const planChat = f.record().chats[0];
  const buildChat = f.record().chats.at(-1);
  f.tick(60 * 60_000);
  const swept = await tidyRuns({ graceMs: 0 }, f.ports);
  assert.equal(swept.closed, 1, 'only the already-finished plan chat closes');
  assert.equal(f.record().state, 'waiting');
  assert.equal(f.herdr.paneOf(planChat), undefined);
  assert.ok(f.herdr.paneOf(buildChat), 'open PR manual build chat stays open');
  assert.equal(f.herdr.workspaces.some(w => w.workspace_id === buildChat.workspaceId), true, 'run workspace stays open');
});

test('3346: refreshWaitingIssue ignores non-zero replies and preserves runs entering parked or releasing in flight', async t => {
  const f = await fixture(t, { agent: 'claude', name: 'small-change' });
  f.ports.skipMetricsDelivery = true;
  assert.equal((await f.run()).exitCode, 0);
  assert.equal((await stepDone({ step: 'scope', summary: 'scope', cwd: f.record().root }, f.agentPorts())).exitCode, 0);
  assert.equal(f.record().state, 'waiting');

  const origExec = f.ports.execFile;

  // 1. Non-zero exit reply on gh api is ignored even if stdout looks like closed JSON
  f.ports.execFile = async (file, args, opts) => {
    if (file === 'gh' && args[0] === 'api' && args[1] === 'repos/example/project/issues/17')
      return { code: 1, stdout: JSON.stringify({ number: 17, state: 'closed' }), stderr: 'HTTP 502' };
    return origExec(file, args, opts);
  };
  await runStatus({ cwd: f.source, json: true }, f.ports);
  assert.equal(f.record().state, 'waiting', 'non-zero issue read does not cancel run');
  assert.equal(f.record().issue?.state, undefined);

  // 2. Concurrent transition to parked or releasing while gh api is in flight keeps parking custody intact
  for (const phase of ['parked', 'releasing']) {
    const reset = f.record();
    delete reset.parking;
    save(reset);

    let sawInFlightRead = false;
    f.ports.execFile = async (file, args, opts) => {
      if (file === 'gh' && args[0] === 'api' && args[1] === 'repos/example/project/issues/17') {
        sawInFlightRead = true;
        const concurrent = f.record();
        concurrent.parking = { phase, blocker: { kind: 'idle_question' }, parkedAt: f.clock };
        save(concurrent);
        return {
          code: 0,
          stdout: JSON.stringify({
            number: 17,
            state: 'closed',
            closed_at: new Date(f.clock).toISOString(),
            html_url: 'https://github.com/example/project/issues/17',
            title: 'Use value two',
            body: 'Value must be two.'
          })
        };
      }
      return origExec(file, args, opts);
    };

    // Check both list status and detail status
    await runStatus({ cwd: f.source, json: true }, f.ports);
    assert.ok(sawInFlightRead, `${phase}: issue read ran in flight`);
    assert.equal(f.record().state, 'waiting', `${phase}: run was not cancelled`);
    assert.equal(f.record().parking?.phase, phase, `${phase}: parking custody preserved`);
    assert.equal(f.record().cancelled, null, `${phase}: no cancelled record written`);

    // Open-state refresh also skips parked/releasing records in flight
    const reopened = f.record();
    delete reopened.parking;
    reopened.issue = { ...reopened.issue, state: 'reopening' };
    save(reopened);
    f.ports.execFile = async (file, args, opts) => {
      if (file === 'gh' && args[0] === 'api' && args[1] === 'repos/example/project/issues/17') {
        const concurrent = f.record();
        concurrent.parking = { phase, blocker: { kind: 'idle_question' }, parkedAt: f.clock };
        save(concurrent);
        return { code: 0, stdout: JSON.stringify({ number: 17, state: 'open', html_url: 'https://github.com/example/project/issues/17', title: 'Use value two', body: 'Value must be two.' }) };
      }
      return origExec(file, args, opts);
    };
    await runStatus({ ref: '17', cwd: f.source, json: true }, f.ports);
    assert.equal(f.record().parking?.phase, phase);
    assert.equal(f.record().issue?.state, 'reopening', `${phase}: open-state maintenance skipped parked/releasing record`);
  }
});
