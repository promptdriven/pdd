import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { CommandInputError, parseArgv } from '../src/argument-parser.mjs';
import { PUBLIC_COMMAND_ROUTES } from '../src/command-catalog.mjs';
import { runMetrics } from '../src/metrics-command.mjs';
import { calculateMetrics } from '../src/metrics-model.mjs';
import { checkInput, interfaceBlocks } from '../src/runtime-seam.mjs';

const modelPrompt = readFileSync(new URL('../prompts/cli/metrics-model.prompt.md', import.meta.url), 'utf8');
const modelContract = JSON.parse(interfaceBlocks(modelPrompt)[0][1]);
const calcSchema = modelContract.entries.find(e => e.operation === 'calculateMetrics');

const ev = (id, issue, type, at, data, source = 'm1') => ({
  schema: 'pdd.metrics.event.v1',
  id,
  repo: 'acme/demo',
  issue,
  type,
  at,
  observedAt: at,
  source,
  data,
});

test('calculateMetrics computes Monday-to-Sunday week, distinct weekly issues, daily rows, Monday reset, and schema compliance', () => {
  const events = [
    // Prior Sunday 2026-11-08: belongs to previous Mon..Sun week (2026-11-02..2026-11-08)
    ev('prev-sun', 1, 'delivery', '2026-11-08T22:00:00Z', { pr: 101, head: 'h101', explicit: true, evidence: 'https://github.com/acme/demo/pull/101' }),
    // Issue #2 worked on Tuesday (start + ready) AND Wednesday (delivery): counted ONCE in weekly totals
    ev('i2-skill', 2, 'milestone', '2026-11-10T09:00:00Z', { stage: 'skill', reason: 'feature', pr: 102 }),
    ev('i2-start', 2, 'start', '2026-11-10T09:05:00Z', { origin: 'autopilot', requiredOutcome: 'code' }),
    ev('i2-ready', 2, 'milestone', '2026-11-10T11:00:00Z', { stage: 'implementation-ready', pr: 102, head: 'h102' }),
    ev('i2-check', 2, 'check', '2026-11-11T10:00:00Z', { pr: 102, head: 'h102', verdict: 'PASS', reviewer: 'codex:session-s1', checkerFamily: 'codex', checkerMode: 'same-family', evidence: 'https://github.com/acme/demo/pull/102#issuecomment-1', acceptance: 'accepted' }),
    ev('i2-merge', 2, 'delivery', '2026-11-11T14:00:00Z', { pr: 102, head: 'h102', explicit: true, evidence: 'https://github.com/acme/demo/pull/102' }),
    // Issue #3 worked on Friday with would-merge
    ev('i3-skill', 3, 'milestone', '2026-11-13T12:00:00Z', { stage: 'skill', reason: 'bug', pr: 103 }),
    ev('i3-pr', 3, 'milestone', '2026-11-13T12:10:00Z', { stage: 'code-pr', pr: 103, head: 'h103' }),
    ev('i3-wm', 3, 'milestone', '2026-11-13T13:00:00Z', { stage: 'would-merge', pr: 103, evidence: 'https://github.com/acme/demo/pull/103' }),
    // Poll-only / snapshot-only events for issue #99 on Saturday must NOT add #99 to weekly issues
    ev('i99-sel', 99, 'selection', '2026-11-14T08:00:00Z', { snapshotId: 'snap1', inScope: true, state: 'ready', reasons: [] }),
    ev('i99-head', 99, 'milestone', '2026-11-14T08:05:00Z', { stage: 'candidate-head', pr: 199, head: 'h199' }),
    ev('i99-ci', 99, 'ci', '2026-11-14T08:06:00Z', { pr: 199, head: 'h199', status: 'passed' }),
  ];

  // 1. Full Sunday report (2026-11-15): 7 elapsed days (Mon 2026-11-09 .. Sun 2026-11-15)
  const sunInput = {
    events,
    repo: 'acme/demo',
    scope: { kind: 'week', date: '2026-11-15' },
    timezone: 'UTC',
    observedAt: '2026-11-15T23:59:00Z',
    sources: ['m1'],
  };
  assert.deepEqual(checkInput(sunInput, calcSchema.input_schema, 0).refusals, []);
  const sun = calculateMetrics(sunInput);
  assert.deepEqual(checkInput(sun, calcSchema.result_schema, 0).refusals, []);

  assert.deepEqual(sun.issues.map(i => i.issue), [2, 3]);
  assert.equal(sun.bySkill.all.issues, 2);
  assert.equal(sun.bySkill.all.merged, 1);
  assert.equal(sun.bySkill.all.wouldMerge, 1);
  assert.equal(sun.bySkill.all.mergedOrWouldMerge, 2);
  assert.equal(sun.bySkill.all.conversionPct, 100);
  assert.equal(sun.activity.starts.count, 1);
  assert.equal(sun.activity.candidateCompletions.count, 1);
  assert.equal(sun.activity.validationResults.count, 1);
  assert.equal(sun.activity.deliveries.count, 1);

  assert.equal(sun.week.weekStart, '2026-11-09');
  assert.equal(sun.week.weekEnd, '2026-11-15');
  assert.equal(sun.week.throughDate, '2026-11-15');
  assert.equal(sun.week.elapsedDays, 7);
  assert.equal(sun.week.refreshesOn, 'Monday');
  assert.equal(sun.week.mergedOrWouldMergePerDay, 2 / 7);
  assert.deepEqual(sun.week.days.map(d => [d.weekday, d.date, d.issues, d.activity.starts, d.activity.deliveries]), [
    ['Mon', '2026-11-09', 0, 0, 0],
    ['Tue', '2026-11-10', 1, 1, 0],
    ['Wed', '2026-11-11', 1, 0, 1],
    ['Thu', '2026-11-12', 0, 0, 0],
    ['Fri', '2026-11-13', 1, 0, 0],
    ['Sat', '2026-11-14', 0, 0, 0],
    ['Sun', '2026-11-15', 0, 0, 0],
  ]);

  // 2. Monday refresh (2026-11-16): resets cleanly to 1 elapsed day (Mon 2026-11-16 .. Sun 2026-11-22)
  const mon = calculateMetrics({
    events,
    repo: 'acme/demo',
    scope: { kind: 'week', date: '2026-11-16' },
    timezone: 'UTC',
    observedAt: '2026-11-16T09:00:00Z',
    sources: ['m1'],
  });
  assert.deepEqual(checkInput(mon, calcSchema.result_schema, 0).refusals, []);
  assert.equal(mon.week.weekStart, '2026-11-16');
  assert.equal(mon.week.weekEnd, '2026-11-22');
  assert.equal(mon.week.throughDate, '2026-11-16');
  assert.equal(mon.week.elapsedDays, 1);
  assert.equal(mon.bySkill.all.issues, 0);
  assert.equal(mon.week.mergedOrWouldMergePerDay, 0);
  assert.equal(mon.week.days.length, 1);
  assert.equal(mon.week.days[0].weekday, 'Mon');

  // 3. Non-week scope has report.week === null
  const cohort = calculateMetrics({
    events,
    repo: 'acme/demo',
    scope: { kind: 'cohort', snapshotId: 'snap1' },
    timezone: 'UTC',
    observedAt: '2026-11-16T09:00:00Z',
    sources: ['m1'],
  });
  assert.equal(cohort.week, null);
  assert.deepEqual(checkInput(cohort, calcSchema.result_schema, 0).refusals, []);

  // 4. Invalid calendar date throws TypeError
  assert.throws(
    () => calculateMetrics({ events: [], repo: 'acme/demo', scope: { kind: 'week', date: '2026-02-30' }, timezone: 'UTC', observedAt: '2026-11-16T00:00:00Z', sources: [] }),
    TypeError,
  );
});

test('catalog, argument parser, option exclusivity, and timezone-local Monday boundary work for --week', async () => {
  const route = PUBLIC_COMMAND_ROUTES.find(r => r.id === 'metrics');
  assert.ok(route);
  assert.deepEqual(route.options.find(o => o.name === '--week'), { name: '--week', kind: 'optional-text' });

  assert.deepEqual(parseArgv(['metrics', '--week']).options, { '--week': true });
  assert.deepEqual(
    parseArgv(['metrics', '--week', '--timezone', 'America/Los_Angeles', '--json']).options,
    { '--week': true, '--timezone': 'America/Los_Angeles', '--json': true },
  );
  assert.deepEqual(
    parseArgv(['metrics', '--week', '2026-11-16', '--json']).options,
    { '--week': '2026-11-16', '--json': true },
  );
  for (const bad of [['metrics', '--week', '--week'], ['metrics', '--week', '   '], ['metrics', '--week', '2026-11-16', 'extra']]) {
    assert.throws(() => parseArgv(bad), CommandInputError);
  }

  const runMem = async (argv, now = '2026-11-16T03:00:00.000Z', savedEvents = []) => {
    let out = '', err = '';
    const saved = [...savedEvents];
    const code = await runMetrics({
      argv,
      stdout: s => { out += s; },
      stderr: s => { err += s; },
      ports: {
        repository: async () => ({ root: '/repo', repo: 'acme/demo' }),
        now: () => now,
        historical: async () => [],
        github: async () => [],
        store: {
          readEvents: async () => ({ events: saved }),
          appendEvents: async ({ events: rows }) => { saved.push(...rows); },
          exportMetrics: async () => ({ repo: 'acme/demo' }),
          importMetrics: async () => {},
        },
      },
    });
    return { code, out, err };
  };

  // Mutual exclusivity & date validation
  for (const badArgv of [
    ['--week', '--date', '2026-11-16'],
    ['--week', '2026-11-16', '--snapshot', 's1'],
    ['export', 'out.json', '--week'],
  ]) {
    const res = await runMem(badArgv);
    assert.equal(res.code, 1);
    assert.match(res.err, /Options cannot be combined/);
  }
  for (const badDate of [['--week', '2026-02-30'], ['--week', 'not-a-date']]) {
    const res = await runMem(badDate);
    assert.equal(res.code, 1);
    assert.match(res.err, /Invalid date/);
  }

  // Timezone boundary: 2026-11-16T03:00:00Z is Monday in UTC (refreshed week 1/7) but Sunday night 19:00 PST in America/Los_Angeles (7/7)!
  const sunNightEvent = ev('la-sun', 7, 'delivery', '2026-11-16T02:00:00Z', {
    pr: 70,
    head: 'a'.repeat(40),
    explicit: true,
    evidence: 'https://github.com/acme/demo/pull/70',
  });

  const utcRes = await runMem(['--week', '--timezone', 'UTC', '--json'], '2026-11-16T03:00:00.000Z', [sunNightEvent]);
  assert.equal(utcRes.code, 0, utcRes.err);
  const utcReport = JSON.parse(utcRes.out);
  assert.equal(utcReport.week.weekStart, '2026-11-16');
  assert.equal(utcReport.week.throughDate, '2026-11-16');
  assert.equal(utcReport.week.elapsedDays, 1);
  assert.equal(utcReport.bySkill.all.merged, 1);

  const laRes = await runMem(['--week', '--timezone', 'America/Los_Angeles', '--json'], '2026-11-16T03:00:00.000Z', [sunNightEvent]);
  assert.equal(laRes.code, 0, laRes.err);
  const laReport = JSON.parse(laRes.out);
  assert.equal(laReport.week.weekStart, '2026-11-09');
  assert.equal(laReport.week.weekEnd, '2026-11-15');
  assert.equal(laReport.week.throughDate, '2026-11-15');
  assert.equal(laReport.week.elapsedDays, 7);
  assert.equal(laReport.bySkill.all.merged, 1);
  assert.equal(laReport.week.days[6].date, '2026-11-15');
  assert.equal(laReport.week.days[6].activity.deliveries, 1);

  // At 2026-11-16T09:00:00Z (Monday 01:00 PST in America/Los_Angeles), --week refreshes to Monday 2026-11-16 with 0 issues!
  const laMonRes = await runMem(['--week', '--timezone', 'America/Los_Angeles', '--json'], '2026-11-16T09:00:00.000Z', [sunNightEvent]);
  assert.equal(laMonRes.code, 0, laMonRes.err);
  const laMonReport = JSON.parse(laMonRes.out);
  assert.equal(laMonReport.week.weekStart, '2026-11-16');
  assert.equal(laMonReport.week.elapsedDays, 1);
  assert.equal(laMonReport.bySkill.all.issues, 0);
});

test('pdd metrics --week CLI reconciles GitHub merged PRs across the whole Mon..Sun week and renders weekly summary + daily rows', t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-metrics-week-cli-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const repoDir = join(root, 'repo');
  const binDir = join(root, 'bin');
  const callsFile = join(root, 'gh-calls.log');
  mkdirSync(repoDir, { recursive: true });
  mkdirSync(binDir, { recursive: true });
  writeFileSync(callsFile, '');

  execFileSync('git', ['init', '-q', repoDir]);
  execFileSync('git', ['-C', repoDir, 'remote', 'add', 'origin', 'https://github.com/acme/weekly-demo.git']);

  const sha = ch => ch.repeat(40);
  const ghFixture = {
    allIssues: [
      {
        number: 1,
        state: 'closed',
        html_url: 'https://github.com/acme/weekly-demo/issues/1',
        labels: [{ name: 'pdd:small-change' }],
        comments: 0,
        created_at: '2026-11-02T10:00:00Z',
        updated_at: '2026-11-02T12:00:00Z',
      },
      {
        number: 2,
        state: 'closed',
        html_url: 'https://github.com/acme/weekly-demo/issues/2',
        labels: [{ name: 'pdd:bug' }],
        comments: 0,
        created_at: '2026-11-09T10:00:00Z',
        updated_at: '2026-11-09T14:00:00Z',
      },
      {
        number: 3,
        state: 'open',
        html_url: 'https://github.com/acme/weekly-demo/issues/3',
        labels: [{ name: 'pdd:feature' }, { name: 'pdd:would-merge' }],
        comments: 0,
        created_at: '2026-11-12T09:00:00Z',
        updated_at: '2026-11-12T15:00:00Z',
      },
    ],
    pulls: [
      {
        // Prior week merged PR (Monday 2026-11-02) -> outside Mon 2026-11-09 .. Fri 2026-11-13
        number: 11,
        state: 'closed',
        merged_at: '2026-11-02T12:00:00Z',
        created_at: '2026-11-02T10:30:00Z',
        updated_at: '2026-11-02T12:00:00Z',
        html_url: 'https://github.com/acme/weekly-demo/pull/11',
        author_association: 'OWNER',
        user: { login: 'dana' },
        head: { sha: sha('1'), ref: 'pdd/small-change-1' },
        title: 'Old week PR (#1)',
        body: 'Closes #1\nPrompt tests: 1 of 1 Stories pass.\nCode replay: PASS\nFormal check: not needed\nMade with `pdd workflow run small-change`.',
        labels: [],
      },
      {
        // Monday of target week (2026-11-09) merged PR -> MUST be reconciled as merged even when querying Friday 2026-11-13!
        number: 22,
        state: 'closed',
        merged_at: '2026-11-09T14:00:00Z',
        created_at: '2026-11-09T11:00:00Z',
        updated_at: '2026-11-09T14:00:00Z',
        html_url: 'https://github.com/acme/weekly-demo/pull/22',
        author_association: 'OWNER',
        user: { login: 'dana' },
        head: { sha: sha('2'), ref: 'pdd/core-2-fix' },
        title: 'Monday fix (#2)',
        body: 'Closes #2\nPrompt tests: 1 of 1 Stories pass.\nCode replay: PASS\nFormal check: PASS\nMade with `pdd workflow run bug`.',
        labels: [],
      },
      {
        // Thursday of target week (2026-11-12) open would-merge PR
        number: 33,
        state: 'open',
        merged_at: null,
        created_at: '2026-11-12T11:00:00Z',
        updated_at: '2026-11-12T15:00:00Z',
        html_url: 'https://github.com/acme/weekly-demo/pull/33',
        author_association: 'OWNER',
        user: { login: 'dana' },
        head: { sha: sha('3'), ref: 'pdd/core-3-feat' },
        title: 'Thursday feature (#3)',
        body: 'Closes #3\nPrompt tests: 1 of 1 Stories pass.\nCode replay: PASS\nFormal check: PASS\nMade with `pdd workflow run feature`.',
        labels: [{ name: 'pdd:would-merge' }],
      },
    ],
  };
  const fixturePath = join(root, 'gh-week.json');
  writeFileSync(fixturePath, JSON.stringify(ghFixture));

  const mockGh = `#!/usr/bin/env node
const fs = require('node:fs');
const data = JSON.parse(fs.readFileSync(process.env.GH_WEEK_FIXTURE, 'utf8'));
const endpoint = process.argv.slice(2).find(a => a.startsWith('repos/')) || '';
fs.appendFileSync(process.env.GH_CALLS_LOG, endpoint + '\\n');
if (endpoint.includes('/pulls?state=all')) {
  process.stdout.write(JSON.stringify(data.pulls));
} else if (endpoint.includes('/issues?state=all')) {
  process.stdout.write(JSON.stringify(data.allIssues));
} else if (/\\/pulls\\/(\\d+)$/.test(endpoint)) {
  const num = Number(/\\/pulls\\/(\\d+)$/.exec(endpoint)[1]);
  const pr = data.pulls.find(p => p.number === num);
  if (!pr) process.exit(1);
  process.stdout.write(JSON.stringify(pr));
} else if (/\\/issues\\/(\\d+)\\/comments/.test(endpoint)) {
  process.stdout.write('');
} else if (endpoint.includes('/check-runs')) {
  process.stdout.write(JSON.stringify({ check_runs: [] }));
} else {
  process.exit(1);
}
`;
  writeFileSync(join(binDir, 'gh'), mockGh, { mode: 0o755 });

  const cli = resolve('bin/pdd.mjs');
  const env = { ...process.env, PATH: `${binDir}:${process.env.PATH}`, GH_WEEK_FIXTURE: fixturePath, GH_CALLS_LOG: callsFile };

  const jsonOut = execFileSync(
    process.execPath,
    [cli, 'metrics', '--week', '2026-11-13', '--json'],
    { cwd: repoDir, env, encoding: 'utf8' },
  );
  const report = JSON.parse(jsonOut);
  assert.deepEqual(report.issues.map(i => i.issue), [2, 3]);
  assert.equal(report.bySkill.all.issues, 2);
  assert.equal(report.bySkill.all.merged, 1);
  assert.equal(report.bySkill.all.wouldMerge, 1);
  assert.equal(report.bySkill.all.mergedOrWouldMerge, 2);
  assert.equal(report.week.weekStart, '2026-11-09');
  assert.equal(report.week.weekEnd, '2026-11-15');
  assert.equal(report.week.throughDate, '2026-11-13');
  assert.equal(report.week.elapsedDays, 5);

  // Prior-week closed PR #11 must not have its comments polled, while Monday merged PR #22 within weekStart IS reconciled!
  const calls = readFileSync(callsFile, 'utf8').trim().split('\n').filter(Boolean);
  assert.equal(calls.some(c => c.includes('/issues/11/comments')), false);
  assert.equal(calls.some(c => c.includes('/issues/22/comments')), true);

  const textOut = execFileSync(
    process.execPath,
    [cli, 'metrics', '--week', '2026-11-13'],
    { cwd: repoDir, env, encoding: 'utf8' },
  );
  assert.match(textOut, /Week: Mon 2026-11-09 to Sun 2026-11-15 \(through 2026-11-13, 5\/7 days; refreshes Monday\)/);
  assert.match(textOut, /Day \| Date \| Issues \| M\/WM \(Conv%\) \| PR \| Starts \| Ready \| Checks \| Deliveries/);
  assert.match(textOut, /Mon \| 2026-11-09 \| 1 \| 1\/0 \(100%\) \| 1 \| 0 \| 0 \| 0 \| 1/);
  assert.match(textOut, /Thu \| 2026-11-12 \| 1 \| 0\/1 \(100%\) \| 1 \| 0 \| 0 \| 0 \| 0/);

  // Also verify --week with --at cutoff via the real CLI binary on recorded observations
  const recordedFile = join(root, 'recorded.json');
  writeFileSync(recordedFile, JSON.stringify([
    ev('rec-mon', 4, 'delivery', '2026-11-09T16:00:00Z', { pr: 44, head: sha('4'), explicit: true, evidence: 'https://github.com/acme/weekly-demo/pull/44' }, 'fixture'),
    ev('rec-after-cutoff', 5, 'delivery', '2026-11-13T22:00:00Z', { pr: 55, head: sha('5'), explicit: true, evidence: 'https://github.com/acme/weekly-demo/pull/55' }, 'fixture'),
  ].map(x => ({ ...x, repo: 'acme/weekly-demo' }))));
  execFileSync(process.execPath, [cli, 'metrics', 'record', recordedFile], { cwd: repoDir, env, encoding: 'utf8' });
  const atReport = JSON.parse(execFileSync(
    process.execPath,
    [cli, 'metrics', '--week', '--at', '2026-11-13T18:00:00Z', '--json'],
    { cwd: repoDir, env, encoding: 'utf8' },
  ));
  assert.equal(atReport.week.throughDate, '2026-11-13');
  assert.deepEqual(atReport.issues.map(i => i.issue), [4]);
});
