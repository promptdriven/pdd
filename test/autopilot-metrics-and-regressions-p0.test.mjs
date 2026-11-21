import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { existsSync, mkdirSync, mkdtempSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import {
  calculateAutopilotMetrics,
  formatMetricsText,
  localAnchorUtcMs,
  renderMetricsHtml,
} from '../src/metrics-model.mjs';
import { readAutopilotMetricsState, recordAutopilotMetric } from '../src/autopilot-metrics.mjs';
import { runMetrics } from '../src/metrics-command.mjs';
import { checkPostMergeRegressions, runAutopilotRegressions } from '../src/autopilot-regressions.mjs';
import { runAutopilotLogs } from '../src/autopilot-logs.mjs';
import { runAutopilotAlerts } from '../src/autopilot-alerts.mjs';

function tempDir(t, prefix) {
  const dir = mkdtempSync(join(tmpdir(), prefix));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  return dir;
}

function capture() {
  let text = '';
  return { write: chunk => { text += String(chunk); }, get text() { return text; } };
}

test('P0-5a: Prompt Checks grades strictly at PR granularity and excludes not-run lines & raw vector test-case counts', t => {
  const stateDir = tempDir(t, 'pdd-metrics-p0-5a-');
  const coreDir = join(stateDir, 'autopilot', 'abc123-core');
  mkdirSync(join(coreDir, 'logs'), { recursive: true });
  writeFileSync(join(stateDir, 'autopilot', 'abc123.json'), JSON.stringify({ repo: 'acme/app', enabled: true, mode: 'auto' }));
  // Issue 1: all runtime lines are not-run (no prompt changed!) -> must NOT count as 0/3 or promptChanged:true!
  writeFileSync(join(coreDir, 'logs', '1-evidence-aaaa111.json'), JSON.stringify({
    runtime: { lines: [{ verdict: 'not-run' }, { verdict: 'not-run' }, { verdict: 'not-run' }] },
    evidence: { runtime: { state: 'not-run', passed: 0, total: 3 }, vectors: { state: 'not-run', passed: 0, total: 12 } },
  }));
  // Issue 2: real prompt PR with 47 passing vectors and 2 passing stories -> must grade as 1/1 per check (PR granularity)!
  writeFileSync(join(coreDir, 'logs', '2-evidence-bbbb222.json'), JSON.stringify({
    promptChanged: true,
    runtime: { lines: [{ verdict: 'pass' }, { verdict: 'pass' }] },
    evidence: {
      runtime: { state: 'pass', passed: 2, total: 2 },
      vectors: { state: 'pass', passed: 47, total: 47 },
      formal: { state: 'proved', passed: 11, total: 11 },
    },
  }));
  const atMs = Date.parse('2026-11-19T12:00:00Z');
  writeFileSync(join(coreDir, 'history.jsonl'), [
    JSON.stringify({ at: atMs, issue: 1, outcome: 'merged', pr: 101, text: 'merged aaaa111' }),
    JSON.stringify({ at: atMs + 1000, issue: 2, outcome: 'merged', pr: 102, text: 'merged bbbb222' }),
  ].join('\n') + '\n');

  const state = readAutopilotMetricsState({ stateDir, now: () => atMs + 2000 });
  const run1 = state.runs.find(r => r.issue === 1);
  assert.equal(run1.gates.runtime, 'not-run');
  assert.equal(run1.gateCounts, undefined, 'not-run lines must not produce gateCounts');
  assert.equal(run1.promptChanged, undefined, 'not-run lines must not infer promptChanged: true');

  const report = calculateAutopilotMetrics({
    now: '2026-11-19T18:00:00Z',
    repos: ['acme/app'],
    runs: [
      ...state.runs,
      {
        repo: 'acme/app',
        issue: 3,
        at: '2026-11-19T13:00:00Z',
        status: 'ended',
        pr: 103,
        promptChanged: true,
        gates: { runtime: 'fail', vectors: 'pass', formal: 'na', suite: 'pass', review: 'pass', ci: 'pass' },
        gateCounts: { runtime: { passed: 20, total: 301 }, vectors: { passed: 2928, total: 2928 } },
      },
    ],
  });
  assert.equal(report.stages.promptChecks.promptPrs, 2, 'only real prompt PRs (#2 and #3) count');
  assert.deepEqual(report.stages.promptChecks.runtime, { passed: 1, total: 2, display: '1/2' });
  assert.deepEqual(report.stages.promptChecks.vectors, { passed: 2, total: 2, display: '2/2' });
  assert.deepEqual(report.stages.promptChecks.formal, { passed: 1, total: 1, display: '1/1' });
  assert.equal(report.stages.promptChecks.summary, 'Prompt Checks (of 2 prompt PRs): Runtime 1/2 · Vectors 2/2 · Formal 1/1');
});

test('P0-5b & P0-5c: stage-by-stage Funnel % and DST-safe --standup 9am-9am America/Los_Angeles window', () => {
  // Spring-forward: 2026-03-08 (US Pacific springs forward 02:00 -> 03:00 => 9am Mar 7 to 9am Mar 8 is exact 23 hours!)
  const springStart = localAnchorUtcMs(2026, 3, 7, 9, 'America/Los_Angeles');
  const springEnd = localAnchorUtcMs(2026, 3, 8, 9, 'America/Los_Angeles');
  assert.equal((springEnd - springStart) / 3_600_000, 23, 'spring-forward 9am-9am PT is exact 23h');

  // Fall-back: 2026-11-01 (US Pacific falls back 02:00 -> 01:00 => 9am Oct 31 to 9am Nov 1 is exact 25 hours!)
  const fallStart = localAnchorUtcMs(2026, 10, 31, 9, 'America/Los_Angeles');
  const fallEnd = localAnchorUtcMs(2026, 11, 1, 9, 'America/Los_Angeles');
  assert.equal((fallEnd - fallStart) / 3_600_000, 25, 'fall-back 9am-9am PT is exact 25h');

  // Standard day: 2026-11-19 -> exact 24 hours
  const report = calculateAutopilotMetrics({
    now: '2026-11-19T18:00:00Z', // 10:00am PT
    standup: true,
    date: '2026-11-19',
    repos: ['acme/app'],
    openIssues: { 'acme/app': 6 },
    openIssueNumbers: [{ repo: 'acme/app', issues: [1, 2, 3, 4, 5, 6] }],
    closedIssues: [
      { repo: 'acme/app', issue: 10, closedAt: '2026-11-18T18:00:00Z' }, // 10am PT Nov 18 (inside 9am-9am standup!)
      { repo: 'acme/app', issue: 11, closedAt: '2026-11-18T20:00:00Z' },
    ],
    runs: [
      { repo: 'acme/app', issue: 10, at: '2026-11-18T18:00:00Z', status: 'merged', pr: 100 }, // inside [Nov 18 9am PT, Nov 19 9am PT)
      { repo: 'acme/app', issue: 11, at: '2026-11-18T20:00:00Z', status: 'merged', pr: 101 },
      { repo: 'acme/app', issue: 12, at: '2026-11-18T22:00:00Z', status: 'ended', pr: 102 },
      { repo: 'acme/app', issue: 13, at: '2026-11-19T01:00:00Z', status: 'ended', pr: null },
      // Outside standup (before 9am PT Nov 18: 08:30 PT = 16:30 UTC)
      { repo: 'acme/app', issue: 14, at: '2026-11-18T16:30:00Z', status: 'merged', pr: 104 },
      // Outside standup (after 9am PT Nov 19: 09:05 PT = 17:05 UTC)
      { repo: 'acme/app', issue: 15, at: '2026-11-19T17:05:00Z', status: 'merged', pr: 105 },
    ],
    regressions: [
      { repo: 'acme/app', pr: 100, issue: 10, reopened: true, reopenedAt: '2026-11-19T05:00:00.000Z' },
    ],
  });

  assert.equal(report.timezone, 'America/Los_Angeles');
  assert.equal(report.standup, true);
  assert.equal(report.overview.windows.length, 1);
  const win = report.overview.windows[0];
  assert.equal(win.key, 'standup');
  assert.equal(win.startAt, '2026-11-18T17:00:00.000Z'); // 9am PST (UTC-8)
  assert.equal(win.endAt, '2026-11-19T16:59:59.999Z');   // 8:59:59.999am PST
  assert.equal(win.taken, 4);
  assert.equal(win.prCreated, 3);
  assert.equal(win.merged, 2);
  assert.equal(win.regressions, 1);
  assert.equal(win.funnel.pool, 10);
  assert.equal(win.funnel.takenPct, 40);
  assert.equal(win.funnel.prPct, 75);
  assert.equal(win.funnel.mergedOfPrPct, 66.7);
  assert.equal(win.funnel.mergedOfTakenPct, 50);
  assert.equal(win.funnel.regressionsPct, 50);
  assert.equal(
    win.funnel.line,
    '10 Pool -> 4 Taken (40.0%) -> 3 PRs (75.0%) -> 2 Merged (66.7% of PRs, 50.0% of Taken) | 1 Regressions (50.0%)',
  );
  assert.equal(report.stages.funnel.line, win.funnel.line);
  assert.equal(report.stages.regressions.events.length, 1);
  assert.equal(report.stages.regressions.events[0].reopenedAt, '2026-11-19T05:00:00.000Z');
  assert.equal(report.stages.regressions.events[0].detectedAt, '2026-11-19T05:00:00.000Z');

  const text = formatMetricsText(report);
  assert.match(text, /- Funnel: 10 Pool -> 4 Taken \(40\.0%\) -> 3 PRs \(75\.0%\) -> 2 Merged \(66\.7% of PRs, 50\.0% of Taken\) \| 1 Regressions \(50\.0%\)/);
  const html = renderMetricsHtml(report);
  assert.match(html, /Funnel: 10 Pool -&gt; 4 Taken \(40\.0%\)/);
});

test('P0-5d: runMetrics --standup uses America/Los_Angeles and extracts GraphQL REOPENED_EVENT timestamps in 1 query', async t => {
  const dir = tempDir(t, 'pdd-metrics-gql-reopen-');
  const stateDir = join(dir, 'state');
  mkdirSync(join(stateDir, 'autopilot'), { recursive: true });
  writeFileSync(join(stateDir, 'autopilot', 'app.json'), JSON.stringify({ repo: 'acme/app', enabled: true, mode: 'auto' }));
  const nowMs = Date.parse('2026-11-19T18:00:00Z');
  recordAutopilotMetric({
    repo: 'acme/app',
    issue: 77,
    skill: 'bug',
    startedAt: '2026-11-18T18:00:00Z',
    at: '2026-11-18T19:00:00Z',
    status: 'merged',
    pr: 707,
  }, { stateDir, now: () => nowMs });

  const gqlQueries = [];
  const fakeExecFile = async (_cmd, args) => {
    if (args[0] === 'api' && args[1] === 'graphql') {
      gqlQueries.push(args[3]);
      return {
        stdout: JSON.stringify({
          data: {
            r0: {
              issues: {
                totalCount: 1,
                pageInfo: { hasNextPage: false, endCursor: null },
                nodes: [{
                  number: 77,
                  timelineItems: {
                    nodes: [{ createdAt: '2026-11-19T04:30:00Z', actor: { login: 'dev' } }],
                  },
                }],
              },
              closedIssues: { pageInfo: { hasNextPage: false, endCursor: null }, nodes: [] },
              pr_707: { number: 707, state: 'MERGED', merged: true, mergedAt: '2026-11-18T19:00:00Z', title: 'Fix bug', mergeCommit: { oid: 'a'.repeat(40) } },
            },
          },
        }),
      };
    }
    return { stdout: 'HTTP/2.0 200 OK\r\n\r\n[]' };
  };

  // --standup rejected on `on`/`off`
  const badErr = capture();
  assert.equal(await runMetrics({ argv: ['on', '--standup'], cwd: dir, stdout: capture(), stderr: badErr, ports: { stateDir, now: () => nowMs } }), 2);
  assert.match(badErr.text, /--standup/);

  const out = capture(), err = capture();
  const code = await runMetrics({
    argv: ['--standup', '--json'],
    cwd: dir,
    stdout: out,
    stderr: err,
    ports: { stateDir, now: () => nowMs, execFile: fakeExecFile },
  });
  assert.equal(code, 0, err.text);
  assert.equal(gqlQueries.length, 1, 'REOPENED_EVENT rides inside the single batched GraphQL query');
  assert.match(gqlQueries[0], /REOPENED_EVENT/);
  const json = JSON.parse(out.text);
  assert.equal(json.timezone, 'America/Los_Angeles');
  assert.equal(json.standup, true);
  assert.equal(json.overview.windows[0].key, 'standup');
  assert.equal(json.stages.regressions.reopened, 1);
  assert.equal(json.stages.regressions.events[0].reopenedAt, '2026-11-19T04:30:00.000Z');
});

test('P0-5e: PDD_STATE_DIR is honored uniformly by logs, regressions, and alerts', async t => {
  const dir = tempDir(t, 'pdd-state-dir-unify-');
  const repoDir = join(dir, 'repo');
  const customState = join(dir, 'custom-state');
  const fakeHome = join(dir, 'empty-home');
  mkdirSync(repoDir, { recursive: true });
  mkdirSync(fakeHome, { recursive: true });
  const id = createHash('sha256').update(repoDir).digest('hex').slice(0, 20);
  const autopilotDir = join(customState, 'autopilot');
  const coreDir = join(autopilotDir, `${id}-core`);
  mkdirSync(join(coreDir, 'jobs'), { recursive: true });
  mkdirSync(join(autopilotDir, 'alerts'), { recursive: true });
  writeFileSync(join(autopilotDir, `${id}.json`), JSON.stringify({ repo: 'acme/app', cwd: repoDir, enabled: true, mode: 'observe', machine: 'vm-custom' }));
  writeFileSync(join(coreDir, 'history.jsonl'), '');

  const env = { HOME: fakeHome, PDD_STATE_DIR: customState };
  const logsRes = await runAutopilotLogs({ cwd: repoDir, env, json: true }, { gitRoot: repoDir });
  assert.equal(logsRes.exitCode, 0, logsRes.message);
  assert.equal(JSON.parse(logsRes.message).mode, 'observe', 'autopilot-logs reads launcher state from PDD_STATE_DIR');

  const regRes = await runAutopilotRegressions({ cwd: repoDir, env, json: true }, {
    run: async (_cmd, args) => ({ code: 0, stdout: args[0] === 'rev-parse' ? repoDir : '', stderr: '' }),
    gh: async () => ({ code: 0, stdout: 'HTTP/2.0 200 OK\r\n\r\n[]', stderr: '' }),
  });
  assert.equal(regRes.exitCode, 0, regRes.message);

  const alertRes = await runAutopilotAlerts({
    action: 'alert',
    cwd: repoDir,
    kind: 'stuck',
    issue: '42',
    text: JSON.stringify({ cause: 'test stuck', tried: 'retry', need: 'inspect' }),
    env,
  }, { repository: async () => ({ nameWithOwner: 'acme/app' }) });
  assert.equal(alertRes.exitCode, 0, alertRes.message);
  assert.ok(readdirSync(join(autopilotDir, 'alerts')).some(f => f.endsWith('.json')), 'alert incident written under PDD_STATE_DIR/autopilot/alerts');
  assert.equal(existsSync(join(fakeHome, '.local')), false, 'nothing written under HOME/.local when PDD_STATE_DIR is set');
});

test('P0-7: checkPostMergeRegressions does not falsely flag still-open issues without reopened timeline events and records reverts once', async t => {
  const root = tempDir(t, 'pdd-p0-7-open-issue-');
  const repo = 'acme/app';
  const mergedAt = '2026-11-01T12:00:00Z';
  const later = '2026-11-02T12:00:00Z';
  const now = Date.parse('2026-11-03T12:00:00Z');
  const m1 = '1'.repeat(40), p1 = '2'.repeat(40), rev = '3'.repeat(40);
  const m2 = '4'.repeat(40), p2 = '5'.repeat(40);
  writeFileSync(join(root, 'history.jsonl'), [
    JSON.stringify({ at: Date.parse(mergedAt), issue: 10, outcome: 'merged', pr: 101 }),
    JSON.stringify({ at: Date.parse(mergedAt), issue: 20, outcome: 'merged', pr: 102 }),
  ].join('\n') + '\n');

  const okJson = body => ({ code: 0, stdout: `HTTP/2.0 200 OK\r\nx-ratelimit-remaining: 4990\r\n\r\n${JSON.stringify(body)}`, stderr: '' });
  const gh = async args => {
    const endpoint = args[args.indexOf('--method') + 2].replace(`repos/${repo}/`, '');
    if (endpoint === 'pulls/101') return okJson({ number: 101, title: 'Partial step 1', merged: true, merged_at: mergedAt, merge_commit_sha: m1 });
    if (endpoint === 'pulls/102') return okJson({ number: 102, title: 'Feature 2', merged: true, merged_at: mergedAt, merge_commit_sha: m2 });
    if (endpoint === `commits/${m1}`) return okJson({ sha: m1, parents: [{ sha: p1 }] });
    if (endpoint === `commits/${m2}`) return okJson({ sha: m2, parents: [{ sha: p2 }] });
    if (endpoint.includes('/check-runs')) return okJson({ check_runs: [] });
    if (endpoint.includes('/statuses')) return okJson([]);
    // Issue #10 is STILL OPEN on GitHub (e.g. tracking/multi-PR issue) with NO reopened timeline event!
    if (endpoint === 'issues/10') return okJson({ number: 10, state: 'open', updated_at: later, html_url: `https://github.com/${repo}/issues/10` });
    if (endpoint === 'issues/10/timeline?per_page=100') return okJson([]);
    if (endpoint === 'issues/20') return okJson({ number: 20, state: 'closed', updated_at: mergedAt, html_url: `https://github.com/${repo}/issues/20` });
    if (endpoint === 'issues/20/timeline?per_page=100') return okJson([]);
    if (endpoint.startsWith('commits?since=')) {
      return okJson([{ sha: rev, html_url: `https://github.com/${repo}/commit/${rev}`, commit: { message: `Revert\n\nThis reverts commit ${m2}.`, committer: { date: later } } }]);
    }
    if (endpoint.startsWith('pulls?state=all')) return okJson([]);
    throw Error(`Unexpected endpoint: ${endpoint}`);
  };

  const res = await checkPostMergeRegressions({ root, repo, gh, now: () => now, maxRequests: 40, minRecheckMs: 0 });
  assert.equal(res.state.merges['101'].reopened, false, 'normal still-open issue without reopened event must NOT be marked reopened');
  assert.equal(res.state.merges['101'].status, 'ok');
  assert.equal(res.state.merges['102'].reverted, true, 'reverted merge detected once cleanly');
  assert.equal(res.state.merges['102'].signals.filter(s => s.kind === 'revert').length, 1);
  assert.equal(res.counts.reopened, 0);
  assert.equal(res.counts.reverted, 1);
  assert.equal(res.counts.ok, 1);
});
