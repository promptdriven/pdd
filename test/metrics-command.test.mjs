import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { recordAutopilotMetric } from '../src/autopilot-metrics.mjs';
import { runMetrics } from '../src/metrics-command.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

const repoRoot = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const pddBin = join(repoRoot, 'bin', 'pdd.mjs');

function makeSandbox(t) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-metrics-cmd-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const stateDir = join(dir, 'state');
  mkdirSync(join(stateDir, 'autopilot'), { recursive: true });
  return { dir, stateDir };
}

function capture() {
  return {
    text: '',
    write(chunk) {
      this.text += String(chunk);
    },
  };
}

function seedTwoRepos(stateDir, nowMs) {
  writeFileSync(join(stateDir, 'autopilot', 'a.json'), JSON.stringify({ repo: 'promptdriven/pdd', enabled: true, mode: 'observe' }));
  writeFileSync(join(stateDir, 'autopilot', 'b.json'), JSON.stringify({ repo: 'promptdriven/pocket', enabled: true, mode: 'auto' }));

  recordAutopilotMetric({
    repo: 'promptdriven/pdd',
    issue: 301,
    skill: 'small-change',
    startedAt: nowMs - 30 * 60_000,
    at: nowMs - 20 * 60_000,
    status: 'would-merge',
    pr: 401,
    durationMinutes: 10,
    gates: { runtime: 'na', vectors: 'na', formal: 'na', suite: 'pass', review: 'pass', ci: 'pass' },
  }, { stateDir, now: () => nowMs });

  recordAutopilotMetric({
    repo: 'promptdriven/pdd',
    issue: 302,
    skill: 'bug',
    startedAt: nowMs - 50 * 60_000,
    at: nowMs - 35 * 60_000,
    status: 'ended',
    pr: 402,
    durationMinutes: 15,
    gates: { runtime: 'pass', vectors: 'pass', formal: 'na', suite: 'fail', review: 'pass', ci: 'pass' },
  }, { stateDir, now: () => nowMs });

  recordAutopilotMetric({
    repo: 'promptdriven/pocket',
    issue: 12,
    skill: 'feature',
    startedAt: nowMs - 40 * 60_000,
    at: nowMs - 15 * 60_000,
    status: 'merged',
    pr: 22,
    durationMinutes: 25,
    gates: { runtime: 'pass', vectors: 'pass', formal: 'bounded', suite: 'pass', review: 'pass', ci: 'pass' },
  }, { stateDir, now: () => nowMs });
}

test('CLI overview, --repos, --repo, stages, skills, full, --date, --json, and single batched GraphQL query', async t => {
  const { dir, stateDir } = makeSandbox(t);
  const nowMs = Date.parse('2026-11-17T18:00:00Z');
  seedTwoRepos(stateDir, nowMs);

  const ghCalls = [];
  const fakeExecFile = async (cmd, args) => {
    ghCalls.push([cmd, ...args]);
    return {
      stdout: JSON.stringify({
        data: {
          r0: {
            issues: { totalCount: 14, nodes: [{ number: 302 }] },
            closedIssues: { nodes: [{ number: 301, closedAt: '2026-11-17T17:45:00Z' }] },
            pr_401: { number: 401, state: 'MERGED', isDraft: false, merged: true, mergedAt: '2026-11-17T17:45:00Z' },
            pr_402: { number: 402, state: 'OPEN', isDraft: true, merged: false, mergedAt: null },
          },
          r1: {
            issues: { totalCount: 8, nodes: [{ number: 13 }] },
            closedIssues: { nodes: [{ number: 12, closedAt: '2026-11-17T17:45:00Z' }] },
            pr_22: { number: 22, state: 'MERGED', isDraft: false, merged: true, mergedAt: '2026-11-17T17:45:00Z' },
          },
        },
      }),
    };
  };
  const emptyScanner = async () => ({ merges: [], counts: { ok: 0, suspect: 0, proven: 0 }, complete: true, errors: [] });

  // 1. Unified overview (v2 scorecard: Overview + Target + Funnel & Gates)
  {
    const out = capture(), err = capture();
    const code = await runMetrics({
      argv: ['--timezone', 'America/Los_Angeles'],
      cwd: dir,
      stdout: out,
      stderr: err,
      ports: { stateDir, now: () => nowMs, execFile: fakeExecFile, regressionScan: emptyScanner },
    });
    assert.equal(code, 0, err.text);
    assert.equal(ghCalls.length, 1, 'Open counts, closed issues, and PR merge states must use 1 batched GraphQL call');
    assert.match(out.text, /PDD Autopilot Metrics · pdd \+ pocket · Tue, Nov 17 · Open now: 22/);
    assert.match(out.text, /Window\s+Pool\s+Taken\s+PRs\s+Merged \(Conv%\)\s+Regressions/);
    assert.match(out.text, /Last 24h\s+24\s+3\s+3\s+2 \(66\.7%\)\s+0 \(0\.0%\)/);
    assert.match(out.text, /Week \(Mon-Sun\)\s+24\s+3\s+3\s+2 \(66\.7%\)\s+0 \(0\.0%\)/);
    assert.match(out.text, /Target \(Nov\)\s+-\s+-\s+-\s+>=90%\s+0\.0%/);
    assert.match(out.text, /Funnel & Gates · Week \(Mon-Sun\) · 3 Taken -> 3 PRs -> 2 Merged/);
    assert.match(out.text, /- Before PR \(0\): none/);
    assert.match(out.text, /- Unmerged PRs \(1\): 1 failed suite/);
    assert.match(out.text, /- PR Gates \(of 3 PRs\): Suite 2\/3 · Review 3\/3 · CI 3\/3/);
    assert.match(out.text, /- Prompt Checks \(of 2 prompt PRs\): Runtime 2\/2 · Vectors 2\/2 · Formal 1\/1/);
    assert.match(out.text, /- Regressions \(0\): 0 reopened · 0 reverted · 0 regression issues/);
  }

  // 2. Per-repo breakdown (--repos)
  {
    const out = capture(), err = capture();
    const code = await runMetrics({
      argv: ['--repos', '--timezone', 'America/Los_Angeles'],
      cwd: dir,
      stdout: out,
      stderr: err,
      ports: { stateDir, now: () => nowMs, execFile: fakeExecFile, regressionScan: emptyScanner },
    });
    assert.equal(code, 0, err.text);
    assert.match(out.text, /promptdriven\/pdd\s+15\s+2\s+2\s+1 \(50\.0%\)\s+0 \(0\.0%\)/);
    assert.match(out.text, /promptdriven\/pocket\s+9\s+1\s+1\s+1 \(100\.0%\)\s+0 \(0\.0%\)/);
    assert.match(out.text, /Total\s+24\s+3\s+3\s+2 \(66\.7%\)\s+0 \(0\.0%\)/);
  }

  // 3. Stages view
  {
    const out = capture(), err = capture();
    const code = await runMetrics({
      argv: ['stages', '--timezone', 'America/Los_Angeles'],
      cwd: dir,
      stdout: out,
      stderr: err,
      ports: { stateDir, now: () => nowMs, execFile: fakeExecFile, regressionScan: emptyScanner },
    });
    assert.equal(code, 0, err.text);
    assert.match(out.text, /Funnel & Gates · Week \(Mon-Sun\) · 3 Taken -> 3 PRs -> 2 Merged/);
    assert.match(out.text, /- Unmerged PRs \(1\): 1 failed suite/);
  }

  // 4. Skills view
  {
    const out = capture(), err = capture();
    const code = await runMetrics({
      argv: ['skills', '--timezone', 'America/Los_Angeles'],
      cwd: dir,
      stdout: out,
      stderr: err,
      ports: { stateDir, now: () => nowMs, execFile: fakeExecFile, regressionScan: emptyScanner },
    });
    assert.equal(code, 0, err.text);
    assert.match(out.text, /small-change\s+1\s+1\s+1 \(100\.0%\)\s+10m/);
    assert.match(out.text, /bug\s+1\s+1\s+0 \(0\.0%\)\s+n\/a/);
    assert.match(out.text, /feature\s+1\s+1\s+1 \(100\.0%\)\s+25m/);
    assert.match(out.text, /Total\s+3\s+3\s+2 \(66\.7%\)\s+18m/);
  }

  // 5. Single-repo filter + JSON
  {
    const out = capture(), err = capture();
    const code = await runMetrics({
      argv: ['full', '--repo', 'promptdriven/pocket', '--json', '--timezone', 'America/Los_Angeles'],
      cwd: dir,
      stdout: out,
      stderr: err,
      ports: { stateDir, now: () => nowMs, openIssues: { 'promptdriven/pocket': 8 }, regressions: [] },
    });
    assert.equal(code, 0, err.text);
    const parsed = JSON.parse(out.text);
    assert.equal(parsed.schema, 'pdd.autopilot.metrics.v1');
    assert.equal(parsed.repoFilter, 'promptdriven/pocket');
    assert.equal(parsed.overview.windows[0].taken, 1);
    assert.equal(parsed.stages.merged, 1);
    assert.equal(parsed.stages.mwm, 1);
  }
});

test('CLI HTML dashboard output, on/off switch via runPdd, offline Open fallback, and input validation', async t => {
  const { dir, stateDir } = makeSandbox(t);
  const nowMs = Date.parse('2026-11-17T18:00:00Z');
  seedTwoRepos(stateDir, nowMs);

  const htmlFile = join(dir, 'dashboard.html');
  let openedPath = null;
  {
    const out = capture(), err = capture();
    const code = await runMetrics({
      argv: ['--html', '--file', htmlFile, '--timezone', 'UTC'],
      cwd: dir,
      env: {},
      stdout: out,
      stderr: err,
      ports: {
        stateDir,
        now: () => nowMs,
        openIssues: { 'promptdriven/pdd': 14, 'promptdriven/pocket': 8 },
        openBrowser: path => { openedPath = path; },
      },
    });
    assert.equal(code, 0, err.text);
    assert.equal(openedPath, htmlFile);
    assert.ok(existsSync(htmlFile));
    assert.match(readFileSync(htmlFile, 'utf8'), /PDD Autopilot Metrics/);
  }

  // Real pdd CLI process: off -> check -> on, plus offline zero-gh safety (strip tokens and /usr/bin so Linux CI gh never leaks)
  const env = {
    ...process.env,
    HOME: dir,
    PDD_STATE_DIR: stateDir,
    PDD_NO_OPEN: '1',
    GH_TOKEN: '',
    GITHUB_TOKEN: '',
    PATH: dirname(process.execPath),
  };

  const offRes = spawnSync(process.execPath, [pddBin, 'metrics', 'off'], { cwd: dir, env, encoding: 'utf8' });
  assert.equal(offRes.status, 0, offRes.stderr);
  assert.match(offRes.stdout, /Autopilot metrics recording is OFF/);

  const jsonWhileOff = spawnSync(process.execPath, [pddBin, 'metrics', '--date', '2026-11-17', '--timezone', 'UTC', '--json'], { cwd: dir, env, encoding: 'utf8' });
  assert.equal(jsonWhileOff.status, 0, jsonWhileOff.stderr);
  const parsedOff = JSON.parse(jsonWhileOff.stdout);
  assert.equal(parsedOff.recording.enabled, false);
  assert.equal(parsedOff.openNowDisplay, '?');
  assert.equal(parsedOff.overview.windows[0].poolDisplay, '?');
  assert.equal(parsedOff.overview.windows[0].taken, 3, 'Existing history stays readable when recording is OFF');
  assert.equal(parsedOff.overview.windows[0].merged, 1);
  assert.equal(parsedOff.regressionsComplete, false, 'Offline CLI run must not report regressions scan as complete');
  assert.equal(parsedOff.overview.windows[0].regressionsDisplay, '?');
  assert.equal(parsedOff.stages.regressions.complete, false);
  assert.match(parsedOff.stages.regressions.summary, /\(scan incomplete\)$/);

  const onRes = spawnSync(process.execPath, [pddBin, 'metrics', 'on', '--json'], { cwd: dir, env, encoding: 'utf8' });
  assert.equal(onRes.status, 0, onRes.stderr);
  assert.equal(JSON.parse(onRes.stdout).enabled, true);

  // Validation errors return exit code 2 via runPdd
  for (const badArgv of [
    ['metrics', 'on', '--repos'],
    ['metrics', 'stages', '--repos'],
    ['metrics', '--json', '--html'],
    ['metrics', '--file', 'out.html'],
    ['metrics', '--date', 'not-a-date'],
    ['metrics', '--repo', 'invalid'],
  ]) {
    const out = capture(), err = capture();
    const exitCode = await runPdd(badArgv, { cwd: dir, env, stdout: out, stderr: err });
    assert.equal(exitCode, 2, `Expected exit 2 for ${badArgv.join(' ')}`);
    assert.ok(err.text.trim().length > 0);
  }
});

test('CLI reuses regressionScan across auto + observe-merged PRs and excludes turned-off sandbox repos (#3530)', async t => {
  const { dir, stateDir } = makeSandbox(t);
  const nowMs = Date.parse('2026-11-19T18:00:00Z');
  seedTwoRepos(stateDir, nowMs);

  // Seed a third sandbox repo and turn it off via `pdd metrics off --repo`
  writeFileSync(join(stateDir, 'autopilot', 'c.json'), JSON.stringify({ repo: 'Serhan-Asad/pdd-autopilot-sandbox', enabled: true, mode: 'auto' }));
  recordAutopilotMetric({
    repo: 'Serhan-Asad/pdd-autopilot-sandbox',
    issue: 99,
    skill: 'small-change',
    startedAt: nowMs - 4 * 3600_000,
    at: nowMs - 3 * 3600_000,
    status: 'merged',
    pr: 990,
  }, { stateDir, now: () => nowMs - 3 * 3600_000 });

  {
    const out = capture(), err = capture();
    const code = await runMetrics({
      argv: ['off', '--repo', 'Serhan-Asad/pdd-autopilot-sandbox'],
      cwd: dir,
      stdout: out,
      stderr: err,
      ports: { stateDir, now: () => nowMs - 2 * 3600_000 },
    });
    assert.equal(code, 0, err.text);
  }

  const m401 = '1'.repeat(40), p401 = 'a'.repeat(40);
  const m22 = '2'.repeat(40), p22 = 'b'.repeat(40);
  const revSha = '9'.repeat(40);
  const mergedAt = '2026-11-19T17:45:00.000Z';
  const laterAt = '2026-11-19T17:55:00.000Z';
  const httpOk = body => ({ stdout: `HTTP/2.0 200 OK\r\nx-ratelimit-remaining: 4999\r\n\r\n${JSON.stringify(body)}`, stderr: '' });

  const graphqlQueries = [];
  const fakeExecFile = async (cmd, args) => {
    assert.equal(cmd, 'gh');
    if (args[1] === 'graphql') {
      const q = args[3];
      graphqlQueries.push(q);
      if (q.includes('pdd-autopilot-sandbox')) {
        return {
          stdout: JSON.stringify({
            data: {
              r0: {
                issues: { totalCount: 5, nodes: [{ number: 100 }] },
                closedIssues: { nodes: [] },
                pr_990: { number: 990, state: 'MERGED', isDraft: false, merged: true, mergedAt: '2026-11-19T15:00:00Z' },
              },
            },
          }),
        };
      }
      return {
        stdout: JSON.stringify({
          data: {
            r0: {
              issues: { totalCount: 14, nodes: [{ number: 302 }] },
              closedIssues: { nodes: [{ number: 301, closedAt: mergedAt }] },
              pr_401: { number: 401, state: 'MERGED', merged: true, mergedAt, title: 'Observe fix', mergeCommit: { oid: m401 } },
              pr_402: { number: 402, state: 'OPEN', merged: false, mergedAt: null, title: 'Open PR', mergeCommit: null },
            },
            r1: {
              issues: { totalCount: 8, nodes: [{ number: 13 }] },
              closedIssues: { nodes: [{ number: 12, closedAt: mergedAt }] },
              pr_22: { number: 22, state: 'MERGED', merged: true, mergedAt, title: 'Pocket feature', mergeCommit: { oid: m22 } },
            },
          },
        }),
      };
    }

    // Real regressionScan REST calls (with includeCi: false + boundedPulls: true + pre-resolved GraphQL mergeCommit)
    const endpoint = args[4];
    if (endpoint.startsWith('repos/promptdriven/pdd/issues?state=all')) return httpOk([]);
    if (endpoint.startsWith('repos/promptdriven/pdd/pulls?state=all&sort=updated&direction=desc')) return httpOk([]);
    if (endpoint.startsWith('repos/promptdriven/pdd/commits?since=')) {
      return httpOk([
        { sha: revSha, html_url: `https://github.com/promptdriven/pdd/commit/${revSha}`, commit: { message: `Revert "Observe fix"\n\nThis reverts commit ${m401}.`, committer: { date: laterAt } } },
      ]);
    }
    if (endpoint.startsWith('repos/promptdriven/pdd/issues/')) return httpOk([]);

    if (endpoint.startsWith('repos/promptdriven/pocket/issues?state=all')) {
      return httpOk([
        { number: 3528, title: 'Pocket regression', body: 'Follow-up for #22', created_at: laterAt, labels: [{ name: 'regression' }], html_url: 'https://github.com/promptdriven/pocket/issues/3528', repository_url: 'https://api.github.com/repos/promptdriven/pocket' },
      ]);
    }
    if (endpoint.startsWith('repos/promptdriven/pocket/pulls?state=all&sort=updated&direction=desc')) return httpOk([]);
    if (endpoint.startsWith('repos/promptdriven/pocket/commits?since=')) return httpOk([]);
    if (endpoint.startsWith('repos/promptdriven/pocket/issues/')) return httpOk([]);
    assert.fail(`Unexpected REST call (GraphQL mergeCommit + includeCi:false should avoid pulls/{pr} & CI calls): ${endpoint}`);
  };

  // Unified metrics excludes sandbox from GraphQL AND detects both auto (#22) and observe (#401) regressions
  {
    const out = capture(), err = capture();
    const code = await runMetrics({
      argv: ['--timezone', 'America/Los_Angeles'],
      cwd: dir,
      stdout: out,
      stderr: err,
      ports: { stateDir, now: () => nowMs, execFile: fakeExecFile },
    });
    assert.equal(code, 0, err.text);
    assert.equal(graphqlQueries.length, 1);
    assert.doesNotMatch(graphqlQueries[0], /pdd-autopilot-sandbox/);
    assert.match(out.text, /PDD Autopilot Metrics · pdd \+ pocket · Thu, Nov 19 · Open now: 22/);
    assert.match(out.text, /Week \(Mon-Sun\)\s+24\s+3\s+3\s+2 \(66\.7%\)\s+2 \(100\.0%\)/);
    assert.match(out.text, /- Regressions \(2\): 0 reopened · 1 reverted · 1 regression issue \(#3528\)/);
  }

  // Explicit --repo still shows turned-off sandbox repo's pre-pause history with Recording: OFF
  {
    const out = capture(), err = capture();
    const code = await runMetrics({
      argv: ['--repo', 'Serhan-Asad/pdd-autopilot-sandbox', '--timezone', 'America/Los_Angeles'],
      cwd: dir,
      stdout: out,
      stderr: err,
      ports: { stateDir, now: () => nowMs, execFile: fakeExecFile, regressions: [] },
    });
    assert.equal(code, 0, err.text);
    assert.match(out.text, /Serhan-Asad\/pdd-autopilot-sandbox/);
    assert.match(out.text, /Recording: OFF/);
    assert.match(out.text, /Week \(Mon-Sun\)\s+6\s+1\s+1\s+1 \(100\.0%\)/);
  }
});

test('CLI paginates GraphQL open/closed issues in UPDATED_AT DESC order, survives partial GraphQL errors, and surfaces incomplete regression scans honestly (#3530)', async t => {
  const { dir, stateDir } = makeSandbox(t);
  const nowMs = Date.parse('2026-11-19T18:00:00Z');
  writeFileSync(join(stateDir, 'autopilot', 'pdd.json'), JSON.stringify({ repo: 'promptdriven/pdd', enabled: true, mode: 'observe' }));
  recordAutopilotMetric({
    repo: 'promptdriven/pdd',
    issue: 502,
    skill: 'small-change',
    startedAt: nowMs - 3600_000,
    at: nowMs - 1800_000,
    status: 'would-merge',
    pr: 602,
  }, { stateDir, now: () => nowMs });
  recordAutopilotMetric({
    repo: 'promptdriven/pdd',
    issue: 503,
    skill: 'bug',
    startedAt: nowMs - 3000_000,
    at: nowMs - 1200_000,
    status: 'ended',
    pr: 99999, // simulates a deleted/missing PR causing a partial GraphQL error
  }, { stateDir, now: () => nowMs });

  const queries = [];
  const fakeExecFile = async (cmd, args) => {
    assert.equal(cmd, 'gh');
    assert.equal(args[1], 'graphql');
    const q = args[3];
    queries.push(q);
    if (q.includes('after: "open_c1"')) {
      return {
        stdout: JSON.stringify({
          data: {
            repo: {
              issues: {
                pageInfo: { hasNextPage: false, endCursor: null },
                nodes: [{ number: 503 }], // taken open issue lives on page 2 -> must NOT double count!
              },
            },
          },
        }),
      };
    }
    if (q.includes('after: "closed_c1"')) {
      return {
        stdout: JSON.stringify({
          data: {
            repo: {
              issues: {
                pageInfo: { hasNextPage: false, endCursor: null },
                nodes: [{ number: 504, closedAt: '2026-11-19T15:00:00Z' }],
              },
            },
          },
        }),
      };
    }
    // Initial batched call returns valid partial data alongside a GraphQL error and non-zero exit code!
    const err = new Error('gh api graphql partial error');
    err.code = 1;
    err.stdout = JSON.stringify({
      data: {
        r0: {
          issues: {
            totalCount: 2,
            pageInfo: { hasNextPage: true, endCursor: 'open_c1' },
            nodes: [{ number: 501 }],
          },
          closedIssues: {
            pageInfo: { hasNextPage: true, endCursor: 'closed_c1' },
            nodes: [{ number: 502, closedAt: '2026-11-19T17:40:00Z' }],
          },
          pr_602: { number: 602, state: 'MERGED', merged: true, mergedAt: '2026-11-19T17:40:00Z', title: 'Fix 502', mergeCommit: { oid: 'c'.repeat(40) } },
          pr_99999: null,
        },
      },
      errors: [{ type: 'NOT_FOUND', path: ['r0', 'pr_99999'], message: 'Could not resolve to a PullRequest' }],
    });
    throw err;
  };

  const incompleteScanner = async opts => {
    assert.equal(opts.includeCi, false);
    assert.equal(opts.boundedPulls, true);
    assert.equal(opts.candidates[0].mergeCommit, 'c'.repeat(40));
    return { merges: [], counts: { ok: 0, suspect: 0, proven: 0 }, complete: false, errors: ['Rate limited'] };
  };

  const out = capture(), err = capture();
  const code = await runMetrics({
    argv: ['--timezone', 'UTC'],
    cwd: dir,
    stdout: out,
    stderr: err,
    ports: { stateDir, now: () => nowMs, execFile: fakeExecFile, regressionScan: incompleteScanner },
  });
  assert.equal(code, 0, err.text);
  assert.equal(queries.length, 3, 'Initial batched query + open page 2 + closed page 2');
  assert.match(queries[0], /orderBy: \{ field: UPDATED_AT, direction: DESC \}/);
  // Open now = 2 ({501, 503}), Closed in window = {502, 504}, Taken = {502, 503} => Pool union = {501, 502, 503, 504} = 4!
  assert.match(out.text, /Open now: 2/);
  assert.match(out.text, /Week \(Mon-Sun\)\s+4\s+2\s+2\s+1 \(50\.0%\)\s+\?/);
  assert.match(out.text, /- Regressions \(0\): 0 reopened · 0 reverted · 0 regression issues \(scan incomplete\)/);
});

test('CLI offline GraphQL failure with 1 merged run marks regressions incomplete and shared-PR runs backfill mergedAt (#3530)', async t => {
  const { dir, stateDir } = makeSandbox(t);
  const nowMs = Date.parse('2026-11-19T18:00:00Z');
  recordAutopilotMetric({
    repo: 'promptdriven/pdd',
    issue: 701,
    pr: 801,
    status: 'merged',
    at: '2026-11-19T17:00:00Z',
    mergedAt: '2026-11-19T17:00:00Z',
    skill: 'bug',
  }, { stateDir, now: () => nowMs });

  // 1. Offline (gh api graphql throws) -> regressionsComplete: false and '?' instead of silent '0 (0.0%)'
  {
    const out = capture(), err = capture();
    const code = await runMetrics({
      argv: ['--json', '--timezone', 'UTC'],
      cwd: dir,
      stdout: out,
      stderr: err,
      ports: {
        stateDir,
        now: () => nowMs,
        execFile: async () => { throw new Error('gh unavailable'); },
      },
    });
    assert.equal(code, 0, err.text);
    const parsed = JSON.parse(out.text);
    assert.equal(parsed.regressionsComplete, false);
    assert.equal(parsed.overview.windows[0].merged, 1);
    assert.equal(parsed.overview.windows[0].regressionsDisplay, '?');
    assert.equal(parsed.stages.regressions.complete, false);
    assert.match(parsed.stages.regressions.summary, /\(scan incomplete\)$/);
  }

  // 2. Two runs sharing the same PR where only the second carries mergedAt still backfill mergedAt on the candidate
  const runsPath = join(stateDir, 'autopilot', 'metrics', 'runs.jsonl');
  writeFileSync(runsPath, [
    JSON.stringify({ repo: 'promptdriven/pdd', issue: 702, pr: 802, status: 'merged', at: '2026-11-19T17:05:00Z', skill: 'bug' }),
    JSON.stringify({ repo: 'promptdriven/pdd', issue: 703, pr: 802, status: 'merged', at: '2026-11-19T17:10:00Z', mergedAt: '2026-11-19T17:10:00Z', skill: 'bug' }),
  ].join('\n') + '\n');
  let seen802 = null;
  const out = capture(), err = capture();
  const code = await runMetrics({
    argv: ['--json', '--timezone', 'UTC'],
    cwd: dir,
    stdout: out,
    stderr: err,
    ports: {
      stateDir,
      now: () => nowMs,
      openIssues: { 'promptdriven/pdd': 5 },
      regressionScan: async opts => {
        seen802 = opts.candidates.find(c => c.pr === 802);
        return { merges: [], counts: { ok: 0, suspect: 0, proven: 0 }, complete: true, errors: [] };
      },
    },
  });
  assert.equal(code, 0, err.text);
  assert.ok(seen802);
  assert.deepEqual(seen802.issues, [702, 703]);
  assert.equal(seen802.mergedAt, '2026-11-19T17:10:00Z');
});
