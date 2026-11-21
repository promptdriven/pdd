import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { performance } from 'node:perf_hooks';
import { coreWorld } from './helpers/core-world.mjs';
import { coreStatus } from '../src/autopilot-core.mjs';
import { runAutopilotLauncher } from '../src/autopilot-launcher.mjs';
import {
  FLAKE_LEDGER_MAX_ENTRIES,
  FLAKE_REPEAT_THRESHOLD,
  FLAKE_WINDOW_DAYS,
  appendBoundedFlakeEntries,
  formatRecurringFlakesLine,
  normalizeFlakeEntry,
  parseFlakeLedger,
  summarizeRecurringFlakes,
} from '../src/autopilot-regressions.mjs';
import { calculateAutopilotMetrics, formatMetricsText, renderMetricsHtml } from '../src/metrics-model.mjs';
import { runMetrics } from '../src/metrics-command.mjs';
import {
  lintRepoProject,
  lintTestFixedSleeps,
  lintTestUnexcusedSkips,
} from '../src/repo-hygiene-lint.mjs';

const DAY_MS = 86_400_000;

function makeBufferStream() {
  let text = '';
  return {
    write(chunk) { text += String(chunk); },
    text: () => text,
  };
}

function makeTempRepo(t, files = {}) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-flake-3562-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  for (const [rel, content] of Object.entries(files)) {
    const full = join(dir, rel);
    mkdirSync(join(full, '..'), { recursive: true });
    writeFileSync(full, content, 'utf8');
  }
  return dir;
}

test('3562 Part 1A: pure flake ledger normalization, dedupe, bounding, malformed-line tolerance, and recurring threshold', () => {
  assert.equal(FLAKE_LEDGER_MAX_ENTRIES, 500);
  assert.equal(FLAKE_REPEAT_THRESHOLD, 3);
  assert.equal(FLAKE_WINDOW_DAYS, 7);

  const nowMs = Date.parse('2026-11-21T10:00:00.000Z');
  const norm = normalizeFlakeEntry({
    ts: nowMs,
    repo: 'acme/widgets',
    issue: 42,
    pr: 101,
    head: 'ABCDEF1234567890ABCDEF1234567890ABCDEF12',
    target: 'test-shard (4/8)\n\t',
    outcome: 'flaked-then-passed',
    detail: 'passed on rerun token=ghp_1234567890abcdefghijklmnopqrstuv\nsecond line',
  });
  assert.equal(norm.ts, '2026-11-21T10:00:00.000Z');
  assert.equal(norm.repo, 'acme/widgets');
  assert.equal(norm.issue, 42);
  assert.equal(norm.pr, 101);
  assert.equal(norm.head, 'abcdef1234567890abcdef1234567890abcdef12');
  assert.equal(norm.target, 'test-shard (4/8)');
  assert.equal(norm.outcome, 'flaked-then-passed');
  assert.ok(!norm.detail.includes('ghp_1234567890'), 'secrets must be redacted');
  assert.ok(!norm.detail.includes('\n'), 'control chars and newlines must be stripped');

  // Invalid outcomes, empty targets, or invalid timestamps return null.
  assert.equal(normalizeFlakeEntry({ target: 'test/a.test.mjs', outcome: 'unknown-outcome', ts: nowMs }), null);
  assert.equal(normalizeFlakeEntry({ target: '   ', outcome: 'reproduced-red', ts: nowMs }), null);
  assert.equal(normalizeFlakeEntry({ target: 'test/a.test.mjs', outcome: 'base-test-red', ts: 'not-a-date' }), null);
  assert.equal(normalizeFlakeEntry({ target: 'test/a.test.mjs', outcome: 'base-test-red' }, { requireTs: true }), null);

  // Malformed JSONL lines and timestamp-less lines are safely skipped without throwing.
  const messyRaw = [
    '',
    'not json at all',
    '{"target":"test/a.test.mjs","outcome":"flaked-then-passed"}',
    JSON.stringify({ ts: '2026-11-20T01:00:00.000Z', repo: 'acme/widgets', issue: 1, pr: 11, head: '1'.repeat(40), target: 'test-shard (4/8)', outcome: 'flaked-then-passed', detail: null }),
    '[]',
    JSON.stringify({ ts: '2026-11-20T02:00:00.000Z', repo: 'acme/widgets', issue: 2, pr: 12, head: '2'.repeat(40), target: 'test-shard (4/8)', outcome: 'bad', detail: null }),
  ].join('\n');
  const parsed = parseFlakeLedger(messyRaw);
  assert.equal(parsed.length, 1);
  assert.equal(parsed[0].target, 'test-shard (4/8)');

  // Dedupe identical (repo, head, target, outcome) and cap to newest maxEntries.
  const firstAppend = appendBoundedFlakeEntries(messyRaw, [
    // Exact duplicate on same head -> ignored
    { ts: '2026-11-20T05:00:00.000Z', repo: 'acme/widgets', issue: 1, pr: 11, head: '1'.repeat(40), target: 'test-shard (4/8)', outcome: 'flaked-then-passed' },
    // Same head, different outcome -> kept
    { ts: '2026-11-20T06:00:00.000Z', repo: 'acme/widgets', issue: 1, pr: 11, head: '1'.repeat(40), target: 'test-shard (4/8)', outcome: 'reproduced-red' },
    { ts: '2026-11-20T07:00:00.000Z', repo: 'acme/widgets', issue: 2, pr: 12, head: '2'.repeat(40), target: 'test-shard (4/8)', outcome: 'flaked-then-passed' },
    { ts: '2026-11-20T08:00:00.000Z', repo: 'acme/widgets', issue: 3, pr: 13, head: '3'.repeat(40), target: 'test/db.test.mjs', outcome: 'base-test-red' },
    { ts: '2026-11-20T09:00:00.000Z', repo: 'acme/widgets', issue: 4, pr: 14, head: '4'.repeat(40), target: 'test/net.test.mjs', outcome: 'base-test-red' },
    { ts: '2026-11-20T10:00:00.000Z', repo: 'acme/widgets', issue: 5, pr: 15, head: '5'.repeat(40), target: 'test/cache.test.mjs', outcome: 'base-test-red' },
  ], { maxEntries: 4 });
  assert.ok(firstAppend.endsWith('\n'));
  const capped = parseFlakeLedger(firstAppend);
  assert.equal(capped.length, 4, 'bounded to newest maxEntries');
  assert.deepEqual(capped.map(e => e.issue), [2, 3, 4, 5]);

  // Recurring summary: trailing 7d window, threshold >= 3, sorted by count desc then target asc.
  const entries = [
    // Outside 7-day window (10 days ago) -> excluded!
    { ts: new Date(nowMs - 10 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 1, pr: 10, head: 'a'.repeat(40), target: 'test/old.test.mjs', outcome: 'flaked-then-passed' },
    { ts: new Date(nowMs - 9 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 2, pr: 11, head: 'b'.repeat(40), target: 'test/old.test.mjs', outcome: 'flaked-then-passed' },
    { ts: new Date(nowMs - 8 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 3, pr: 12, head: 'c'.repeat(40), target: 'test/old.test.mjs', outcome: 'flaked-then-passed' },
    // Below threshold (2 occurrences) -> excluded from recurring!
    { ts: new Date(nowMs - 2 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 4, pr: 13, head: 'd'.repeat(40), target: 'test/twice.test.mjs', outcome: 'flaked-then-passed' },
    { ts: new Date(nowMs - 1 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 5, pr: 14, head: 'e'.repeat(40), target: 'test/twice.test.mjs', outcome: 'reproduced-red' },
    // 4 occurrences -> #1
    { ts: new Date(nowMs - 4 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 10, pr: 20, head: '1'.repeat(40), target: 'test-shard (4/8)', outcome: 'flaked-then-passed' },
    { ts: new Date(nowMs - 3 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 11, pr: 21, head: '2'.repeat(40), target: 'test-shard (4/8)', outcome: 'flaked-then-passed' },
    { ts: new Date(nowMs - 2 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 12, pr: 22, head: '3'.repeat(40), target: 'test-shard (4/8)', outcome: 'reproduced-red' },
    { ts: new Date(nowMs - 1 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 13, pr: 23, head: '4'.repeat(40), target: 'test-shard (4/8)', outcome: 'flaked-then-passed' },
    // 3 occurrences -> #2 (alphabetical tiebreak with z-test)
    { ts: new Date(nowMs - 3 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 20, pr: 30, head: '5'.repeat(40), target: 'test/alpha.test.mjs', outcome: 'base-test-red' },
    { ts: new Date(nowMs - 2 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 21, pr: 31, head: '6'.repeat(40), target: 'test/alpha.test.mjs', outcome: 'base-test-red' },
    { ts: new Date(nowMs - 1 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 22, pr: 32, head: '7'.repeat(40), target: 'test/alpha.test.mjs', outcome: 'base-test-red' },
    // 3 occurrences -> #3
    { ts: new Date(nowMs - 3 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 30, pr: 40, head: '8'.repeat(40), target: 'test/zeta.test.mjs', outcome: 'reproduced-red' },
    { ts: new Date(nowMs - 2 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 31, pr: 41, head: '9'.repeat(40), target: 'test/zeta.test.mjs', outcome: 'reproduced-red' },
    { ts: new Date(nowMs - 1 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 32, pr: 42, head: '0'.repeat(40), target: 'test/zeta.test.mjs', outcome: 'flaked-then-passed' },
  ];
  const summary = summarizeRecurringFlakes(entries, { nowMs });
  assert.equal(summary.totalEntries, 12);
  assert.equal(summary.windowDays, 7);
  assert.equal(summary.threshold, 3);
  assert.deepEqual(summary.recurring.map(r => [r.target, r.count]), [
    ['test-shard (4/8)', 4],
    ['test/alpha.test.mjs', 3],
    ['test/zeta.test.mjs', 3],
  ]);
  assert.deepEqual(summary.recurring[0].outcomes, { 'flaked-then-passed': 3, 'reproduced-red': 1, 'base-test-red': 0 });
  assert.deepEqual(summary.recurring[0].issues, [10, 11, 12, 13]);
  assert.equal(summary.recurring[0].lastSeen, new Date(nowMs - 1 * DAY_MS).toISOString());

  const line = formatRecurringFlakesLine(summary);
  assert.match(line, /^Recurring flakes \(7d, >=3\): test-shard \(4\/8\) \(4x: 3 flaked-then-passed, 1 reproduced-red\); test\/alpha\.test\.mjs \(3x: 3 base-test-red\)/);
  assert.equal(formatRecurringFlakesLine(summarizeRecurringFlakes([], { nowMs })), null);
});

test('3562 Part 1B: coreWorld persists shard-flake flaked-then-passed, reproduced-red, and base-test-red across jobs into flakes.jsonl and surfaces in coreStatus', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, repairs: 2 } });
  const origGh = w.github.gh;
  w.github.gh = async (args, opts) => {
    if (args[0] === 'run' && args[1] === 'rerun') {
      w.github.reruns.push({ kind: 'cli-rerun-failed', id: Number(args[2]), at: w.now() });
      return { code: 0, stdout: '', stderr: '' };
    }
    return origGh(args, opts);
  };

  const makeMatrix = (runId, states, completedAt) => states.map((st, idx) => ({
    id: runId * 10 + idx + 1,
    name: `test-shard (${idx + 1}/${states.length})`,
    status: st === 'in_progress' ? 'in_progress' : 'completed',
    conclusion: st === 'in_progress' ? null : st,
    ...(st === 'in_progress' ? { started_at: '2026-11-20T08:00:00Z' } : { completed_at: completedAt }),
    details_url: `https://github.com/${w.github.repo}/actions/runs/${runId}/job/${runId * 10 + idx + 1}`,
  }));

  // Job 1 (Issue #51): shard 4 flakes -> rerun -> passes -> recorded as flaked-then-passed once!
  w.issue(51, { title: 'Flaky shard passes on rerun' });
  await w.tick();
  const built51 = w.build(51, { body: 'Fixes #51\n\nRuntime: not run (no prompt)', result: { promptChanged: false }, checks: null });
  const stale51 = makeMatrix(8101, ['success', 'success', 'success', 'failure', 'success', 'success', 'success', 'success'], '2026-11-20T08:02:00Z');
  w.github.checks.set(built51.head, stale51);
  await w.tick();
  // Stale token still present on next tick -> must NOT record yet.
  await w.tick();
  assert.deepEqual(parseFlakeLedger((() => { try { return readFileSync(join(w.root, 'flakes.jsonl'), 'utf8'); } catch { return ''; } })()), []);

  // Rerun finishes green -> records flaked-then-passed.
  w.github.checks.set(built51.head, makeMatrix(8101, Array(8).fill('success'), '2026-11-20T08:05:00Z'));
  await w.tick();
  w.review(51, 'PASS');
  w.suite(51, 0);
  await w.tick(); // Second tick on same head before merge must NOT double-record!
  assert.deepEqual(w.github.merges, [built51.pr.number]);

  let entries = parseFlakeLedger(readFileSync(join(w.root, 'flakes.jsonl'), 'utf8'));
  assert.equal(entries.length, 1);
  assert.equal(entries[0].issue, 51);
  assert.equal(entries[0].pr, built51.pr.number);
  assert.equal(entries[0].head, built51.head);
  assert.equal(entries[0].target, 'test-shard (4/8)');
  assert.equal(entries[0].outcome, 'flaked-then-passed');

  // Job 2 (Issue #52): 2 shards fail (shard 4 & shard 5) -> rerun -> shard 4 fails again (reproduced-red), shard 5 passes (flaked-then-passed)!
  w.issue(52, { title: 'Mixed rerun outcomes' });
  await w.tick();
  const built52 = w.build(52, { body: 'Fixes #52\n\nRuntime: not run (no prompt)', result: { promptChanged: false }, checks: null });
  w.github.checks.set(built52.head, makeMatrix(8201, ['success', 'success', 'success', 'failure', 'failure', 'success', 'success', 'success'], '2026-11-20T08:12:00Z'));
  await w.tick();
  // Rerun finishes with a new completion timestamp: shard 4 stays red, shard 5 turns green.
  w.github.checks.set(built52.head, makeMatrix(8201, ['success', 'success', 'success', 'failure', 'success', 'success', 'success', 'success'], '2026-11-20T08:15:00Z'));
  await w.tick();

  entries = parseFlakeLedger(readFileSync(join(w.root, 'flakes.jsonl'), 'utf8'));
  assert.equal(entries.length, 3);
  const job52ByTarget = Object.fromEntries(entries.filter(e => e.issue === 52).map(e => [e.target, e.outcome]));
  assert.deepEqual(job52ByTarget, {
    'test-shard (4/8)': 'reproduced-red',
    'test-shard (5/8)': 'flaked-then-passed',
  });

  // Finish Job 2 via base-test-red so we also test base-test-red persistence on the same job!
  w.finish(52, 'repair', {
    result: {
      outcome: 'failed',
      kind: 'pdd',
      component: 'base-suite',
      code: 'base-test-red',
      cause: 'test/shared-queue.test.mjs also fails on origin/main',
      detail: 'CI=true node --test test/shared-queue.test.mjs -> exit 1 on merge-base',
    },
  });
  await w.tick();
  entries = parseFlakeLedger(readFileSync(join(w.root, 'flakes.jsonl'), 'utf8'));
  const baseRed = entries.find(e => e.outcome === 'base-test-red');
  assert.ok(baseRed, 'base-test-red entry persisted to flakes.jsonl');
  assert.equal(baseRed.issue, 52);
  assert.equal(baseRed.target, 'test/shared-queue.test.mjs');

  // Below threshold (test-shard (4/8) has only 2 occurrences so far) -> coreStatus omits Recurring flakes!
  const statusBeforeThreshold = coreStatus({ state: w.state, settings: w.settings }, { root: w.root, reportRoot: w.reportRoot, now: w.now });
  assert.doesNotMatch(statusBeforeThreshold, /Recurring flakes/);

  // Job 3 (Issue #53): shard 4 flakes a 3rd time -> crosses >= 3 threshold -> coreStatus surfaces Recurring flakes!
  w.issue(53, { title: 'Third shard 4 flake crosses threshold' });
  await w.tick();
  const built53 = w.build(53, { body: 'Fixes #53\n\nRuntime: not run (no prompt)', result: { promptChanged: false }, checks: null });
  w.github.checks.set(built53.head, makeMatrix(8301, ['success', 'success', 'success', 'failure', 'success', 'success', 'success', 'success'], '2026-11-20T08:30:00Z'));
  await w.tick();
  w.github.checks.set(built53.head, makeMatrix(8301, Array(8).fill('success'), '2026-11-20T08:33:00Z'));
  await w.tick();
  w.review(53, 'PASS');
  w.suite(53, 0);
  await w.tick();

  const statusAfterThreshold = coreStatus({ state: w.state, settings: w.settings }, { root: w.root, reportRoot: w.reportRoot, now: w.now });
  assert.match(statusAfterThreshold, /Recurring flakes \(7d, >=3\): test-shard \(4\/8\) \(3x: 2 flaked-then-passed, 1 reproduced-red\)/);

  // Symlink safety: if flakes.jsonl is replaced with a symlink, coreStatus ignores it safely without throwing.
  const decoy = join(w.dir, 'decoy.jsonl');
  writeFileSync(decoy, readFileSync(join(w.root, 'flakes.jsonl'), 'utf8'));
  rmSync(join(w.root, 'flakes.jsonl'));
  symlinkSync(decoy, join(w.root, 'flakes.jsonl'));
  const statusWithSymlink = coreStatus({ state: w.state, settings: w.settings }, { root: w.root, reportRoot: w.reportRoot, now: w.now });
  assert.doesNotMatch(statusWithSymlink, /Recurring flakes/, 'symlinked flakes.jsonl is ignored safely');
});

test('3562 Part 1C: recurring flakes surface in pdd autopilot status (--json, --all, text) and pdd metrics (JSON, text, HTML), and stay omitted when below threshold or stale', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-flake-surface-3562-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const stateDir = join(dir, 'state');
  const autopilotRoot = join(stateDir, 'autopilot');
  const repoDir = join(dir, 'repo');
  const pkgDir = join(dir, 'pkg');
  mkdirSync(autopilotRoot, { recursive: true });
  mkdirSync(repoDir, { recursive: true });
  mkdirSync(pkgDir, { recursive: true });
  writeFileSync(join(pkgDir, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.40' }));
  spawnSync('git', ['init', '-q', repoDir], { encoding: 'utf8' });
  const realRepo = spawnSync('git', ['rev-parse', '--show-toplevel'], { cwd: repoDir, encoding: 'utf8' }).stdout.trim();
  const id = createHash('sha256').update(realRepo).digest('hex').slice(0, 20);
  const coreDir = join(autopilotRoot, `${id}-core`);
  mkdirSync(coreDir, { recursive: true });
  writeFileSync(join(autopilotRoot, `${id}.json`), JSON.stringify({
    enabled: true,
    engine: 'core',
    mode: 'observe',
    repo: 'acme/widgets',
    cwd: realRepo,
    baseBranch: 'main',
    agent: { id: 'codex', kind: 'codex', command: 'codex' },
    packageRoot: pkgDir,
  }));

  const nowMs = Date.parse('2026-11-21T12:00:00.000Z');
  const nowFn = () => nowMs;
  const env = { HOME: dir, PDD_STATE_DIR: stateDir, PATH: process.env.PATH };

  // 1) Write only 2 recent entries + 3 old entries (> 7 days) -> below threshold, omitted from text & HTML!
  const belowThresholdJsonl = appendBoundedFlakeEntries('', [
    { ts: new Date(nowMs - 10 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 1, pr: 11, head: '1'.repeat(40), target: 'test/old.test.mjs', outcome: 'base-test-red' },
    { ts: new Date(nowMs - 9 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 2, pr: 12, head: '2'.repeat(40), target: 'test/old.test.mjs', outcome: 'base-test-red' },
    { ts: new Date(nowMs - 8 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 3, pr: 13, head: '3'.repeat(40), target: 'test/old.test.mjs', outcome: 'base-test-red' },
    { ts: new Date(nowMs - 2 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 4, pr: 14, head: '4'.repeat(40), target: 'test-shard (2/8)', outcome: 'flaked-then-passed' },
    { ts: new Date(nowMs - 1 * DAY_MS).toISOString(), repo: 'acme/widgets', issue: 5, pr: 15, head: '5'.repeat(40), target: 'test-shard (2/8)', outcome: 'reproduced-red' },
  ]);
  writeFileSync(join(coreDir, 'flakes.jsonl'), belowThresholdJsonl);

  const launcherPorts = {
    stateRoot: autopilotRoot,
    now: nowFn,
    env,
    timer: async () => true,
    warn: () => {},
    machineGuard: async () => ({ share: 50, slots: 2, auto: 2, room: { ok: true, free: 2 }, line: 'Machine: ok' }),
  };

  const statusJsonLow = JSON.parse((await runAutopilotLauncher({ command: 'status', json: true, cwd: realRepo, packageRoot: pkgDir, env }, launcherPorts)).message);
  assert.equal(statusJsonLow.recurringFlakes.totalEntries, 2);
  assert.deepEqual(statusJsonLow.recurringFlakes.recurring, []);

  const statusAllLow = await runAutopilotLauncher({ command: 'status', all: true, cwd: realRepo, packageRoot: pkgDir, env }, launcherPorts);
  assert.equal(statusAllLow.exitCode, 0);
  assert.doesNotMatch(statusAllLow.message, /Recurring flakes/);

  const outLow = makeBufferStream();
  const errLow = makeBufferStream();
  const exitLow = await runMetrics({
    argv: [],
    cwd: realRepo,
    env,
    stdout: outLow,
    stderr: errLow,
    ports: { stateDir, env, now: nowFn, openIssues: { 'acme/widgets': 5 }, regressions: [], regressionsComplete: true },
  });
  assert.equal(exitLow, 0, errLow.text());
  assert.doesNotMatch(outLow.text(), /Recurring flakes/);

  // 2) Add a 3rd recent occurrence of test-shard (2/8) -> crosses >= 3 threshold!
  const aboveThresholdJsonl = appendBoundedFlakeEntries(belowThresholdJsonl, [
    { ts: new Date(nowMs - 3600_000).toISOString(), repo: 'acme/widgets', issue: 6, pr: 16, head: '6'.repeat(40), target: 'test-shard (2/8)', outcome: 'flaked-then-passed' },
  ]);
  writeFileSync(join(coreDir, 'flakes.jsonl'), aboveThresholdJsonl);

  const statusJsonHigh = JSON.parse((await runAutopilotLauncher({ command: 'status', json: true, cwd: realRepo, packageRoot: pkgDir, env }, launcherPorts)).message);
  assert.equal(statusJsonHigh.recurringFlakes.recurring.length, 1);
  assert.equal(statusJsonHigh.recurringFlakes.recurring[0].target, 'test-shard (2/8)');
  assert.equal(statusJsonHigh.recurringFlakes.recurring[0].count, 3);

  const statusAllHigh = await runAutopilotLauncher({ command: 'status', all: true, cwd: realRepo, packageRoot: pkgDir, env }, launcherPorts);
  assert.match(statusAllHigh.message, /Recurring flakes \(7d, >=3\): acme\/widgets:test-shard \(2\/8\) \(3x: 2 flaked-then-passed, 1 reproduced-red\)/);

  const statusSingleHigh = await runAutopilotLauncher({ command: 'status', cwd: realRepo, packageRoot: pkgDir, env }, launcherPorts);
  assert.match(statusSingleHigh.message, /Recurring flakes \(7d, >=3\): test-shard \(2\/8\) \(3x: 2 flaked-then-passed, 1 reproduced-red\)/);

  // Metrics JSON & Text & HTML surface recurring flakes cleanly.
  const outJson = makeBufferStream();
  const exitJson = await runMetrics({
    argv: ['--json'],
    cwd: realRepo,
    env,
    stdout: outJson,
    stderr: makeBufferStream(),
    ports: { stateDir, env, now: nowFn, openIssues: { 'acme/widgets': 5 }, regressions: [], regressionsComplete: true },
  });
  assert.equal(exitJson, 0);
  const metricsReport = JSON.parse(outJson.text());
  assert.equal(metricsReport.recurringFlakes.recurring.length, 1);
  assert.equal(metricsReport.recurringFlakes.recurring[0].target, 'test-shard (2/8)');
  assert.equal(metricsReport.recurringFlakes.recurring[0].count, 3);

  const outText = makeBufferStream();
  const exitText = await runMetrics({
    argv: [],
    cwd: realRepo,
    env,
    stdout: outText,
    stderr: makeBufferStream(),
    ports: { stateDir, env, now: nowFn, openIssues: { 'acme/widgets': 5 }, regressions: [], regressionsComplete: true },
  });
  assert.equal(exitText, 0);
  assert.match(outText.text(), /Recurring flakes \(7d, >=3\)/);
  assert.match(outText.text(), /- test-shard \(2\/8\): 3x \(2 flaked-then-passed, 1 reproduced-red\)/);

  // Pure model HTML check + repo exclusion check.
  const html = renderMetricsHtml(metricsReport);
  assert.match(html, /4\. Recurring Flakes/);
  assert.match(html, /test-shard \(2\/8\)/);

  const excludedReport = calculateAutopilotMetrics({
    repos: ['acme/widgets'],
    runs: [],
    flakeEntries: parseFlakeLedger(aboveThresholdJsonl),
    now: new Date(nowMs).toISOString(),
    recording: { enabled: true, repos: { 'acme/widgets': false } },
  });
  assert.deepEqual(excludedReport.recurringFlakes.recurring, [], 'turned-off repo flakes excluded in unified metrics');
  assert.doesNotMatch(formatMetricsText(excludedReport), /Recurring flakes/);
  assert.doesNotMatch(renderMetricsHtml(excludedReport), /Recurring Flakes/);
});

test('3562 Part 2A: test-fixed-sleep detects JS/TS and Python fixed sleeps while guarding zero-delay, watchdogs, strings, comments, annotations, and non-test paths', t => {
  const badJs = [
    "import { setTimeout } from 'node:timers/promises';",
    "import timersPromises from 'node:timers/promises';",
    'const WAIT_MS = 350;',
    "test('flaky sleeps', async () => {",
    '  await new Promise(r => setTimeout(r, 500));',
    '  await new Promise((resolve) => setTimeout(resolve, 100));',
    '  await new Promise((resolve) => { setTimeout(() => resolve(), 250); });',
    '  await sleep(200);',
    '  await setTimeout(100);',
    '  await timersPromises.setTimeout(150);',
    '  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 50);',
    '  await sleep(WAIT_MS);',
    '});',
  ].join('\n');
  const jsWarnings = lintTestFixedSleeps(badJs, { path: 'test/flaky-sleeps.test.mjs' });
  assert.equal(jsWarnings.length, 8, `expected 8 sleep warnings, got:\n${jsWarnings.join('\n')}`);
  for (const w of jsWarnings) assert.match(w, /\[test-fixed-sleep\]/);

  const badPy = [
    'import time',
    'import asyncio',
    'def test_slow():',
    '    time.sleep(1)',
    'async def test_async_slow():',
    '    await asyncio.sleep(0.5)',
  ].join('\n');
  const pyWarnings = lintTestFixedSleeps(badPy, { path: 'tests/test_slow.py' });
  assert.equal(pyWarnings.length, 2, `expected 2 python sleep warnings, got:\n${pyWarnings.join('\n')}`);
  assert.match(pyWarnings[0], /tests\/test_slow\.py:4 \[test-fixed-sleep\]/);
  assert.match(pyWarnings[1], /tests\/test_slow\.py:6 \[test-fixed-sleep\]/);

  // False-positive guards: ZERO warnings allowed!
  const safeJs = [
    "import timersPromises from 'node:timers/promises';",
    'const sleep = ms => new Promise(r => setTimeout(r, ms));',
    'function customSleep(ms) { return new Promise(resolve => setTimeout(resolve, ms)); }',
    "test('safe patterns', async () => {",
    '  await new Promise(r => setTimeout(r, 0));',
    '  await sleep(0);',
    '  await timersPromises.setTimeout(0);',
    '  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 0);',
    '  const controller = new AbortController();',
    '  const watchdog = setTimeout(() => controller.abort(), 5000);',
    "  const raced = new Promise((_, reject) => setTimeout(() => reject(new Error('timeout')), 5000));",
    "  const fixture = 'await new Promise(r => setTimeout(r, 500)); sleep(200);';",
    '  const tpl = `await sleep(300)`;',
    '  // await new Promise(r => setTimeout(r, 500));',
    '  await new Promise(r => setTimeout(r, 250)); // pdd-allow-sleep: testing TTL expiration',
    '  // sleep-ok: filesystem mtime resolution test',
    '  await sleep(100);',
    '  await sleep(100); // tracked in #3562',
    '  clearTimeout(watchdog);',
    '  void raced; void fixture; void tpl; void sleep; void customSleep;',
    '});',
  ].join('\n');
  assert.deepEqual(lintTestFixedSleeps(safeJs, { path: 'test/safe-sleeps.test.mjs' }), []);

  const safePy = [
    'import time, asyncio',
    'def test_safe():',
    '    time.sleep(0)',
    '    s = "time.sleep(5)"',
    '    # time.sleep(5)',
    '    time.sleep(0.2)  # pdd-allow-sleep: TTL window',
    'async def test_async_safe():',
    '    await asyncio.sleep(0)',
    '    # #1234 kernel clock boundary',
    '    await asyncio.sleep(0.1)',
  ].join('\n');
  assert.deepEqual(lintTestFixedSleeps(safePy, { path: 'tests/test_safe.py' }), []);

  // Non-test files and fixtures/helpers subdirs are never flagged.
  assert.deepEqual(lintTestFixedSleeps(badJs, { path: 'src/worker.mjs' }), []);
  assert.deepEqual(lintTestFixedSleeps(badJs, { path: 'test/fixtures/sample.test.mjs' }), []);
  assert.deepEqual(lintTestFixedSleeps(badJs, { path: 'test/helpers/wait.mjs' }), []);

  // pdd.json severity overrides: default warn, error promotion, off suppression.
  const root = makeTempRepo(t, {
    'test/sample.test.mjs': "test('x', async () => {\n  await new Promise(r => setTimeout(r, 400));\n});\n",
    'src/prod.mjs': 'export const wait = () => new Promise(r => setTimeout(r, 400));\n',
  });
  const defRes = lintRepoProject({ root, files: ['test/sample.test.mjs', 'src/prod.mjs'], config: {} });
  assert.equal(defRes.ok, true);
  assert.equal(defRes.warnings.filter(w => w.includes('[test-fixed-sleep]')).length, 1);
  assert.equal(defRes.errors.length, 0);

  const errRes = lintRepoProject({ root, files: ['test/sample.test.mjs', 'src/prod.mjs'], config: { rules: { 'test-fixed-sleep': 'error' } } });
  assert.equal(errRes.ok, false);
  assert.equal(errRes.errors.filter(e => e.includes('[test-fixed-sleep]')).length, 1);

  const offRes = lintRepoProject({ root, files: ['test/sample.test.mjs', 'src/prod.mjs'], config: { rules: { 'test-fixed-sleep': 'off' } } });
  assert.equal(offRes.ok, true);
  assert.equal(offRes.warnings.filter(w => w.includes('[test-fixed-sleep]')).length, 0);
  assert.equal(offRes.errors.length, 0);
});

test('3562 Part 2B: test-unexcused-skip detects JS/TS and Python unexcused skips while honoring issue refs, conditional skips, substantive reasons, strings, comments, and pdd.json overrides', t => {
  const badJs = [
    "test.skip('broken auth', () => {});",
    "it.skip('broken checkout', () => {});",
    "describe.skip('legacy suite', () => {});",
    "suite.skip('old suite', () => {});",
    "xit('disabled case', () => {});",
    "xtest('disabled case 2', () => {});",
    "xdescribe('disabled block', () => {});",
    "test('opts true', { skip: true }, () => {});",
    "it('opts empty', { skip: '' }, () => {});",
    "test('opts placeholder', { skip: 'todo' }, () => {});",
    "test('ctx empty', (t) => { t.skip(); });",
    "test('ctx blank', (ctx) => { ctx.skip(''); });",
  ].join('\n');
  const jsWarnings = lintTestUnexcusedSkips(badJs, { path: 'test/unexcused.test.mjs' });
  assert.equal(jsWarnings.length, 12, `expected 12 unexcused skip warnings, got:\n${jsWarnings.join('\n')}`);
  for (const w of jsWarnings) assert.match(w, /\[test-unexcused-skip\]/);

  const badPy = [
    'import pytest, unittest',
    '@pytest.mark.skip',
    'def test_bare():',
    '    assert True',
    '@pytest.mark.skip()',
    'def test_empty_call():',
    '    assert True',
    '@pytest.mark.skip(reason="")',
    'def test_empty_reason():',
    '    assert True',
    '@unittest.skip("")',
    'def test_unittest_empty():',
    '    assert True',
    'def test_runtime_skip():',
    '    pytest.skip()',
  ].join('\n');
  const pyWarnings = lintTestUnexcusedSkips(badPy, { path: 'tests/test_skips.py' });
  assert.equal(pyWarnings.length, 5, `expected 5 python skip warnings, got:\n${pyWarnings.join('\n')}`);

  // False-positive guards: justified skips, conditionals, issue citations, strings, comments.
  const safeJs = [
    "test.skip('tracked in #1234', () => {});",
    "it.skip('broken flow', () => {}); // tracked in GH-456",
    '// Blocked by JIRA-789 waiting for backend schema',
    "describe.skip('migrations', () => {});",
    '// See https://github.com/acme/widgets/issues/99',
    "xit('wait for upstream', () => {});",
    "test('env gated', { skip: !process.env.LIVE_API }, () => {});",
    "it('platform gated', { skip: process.platform === 'win32' }, () => {});",
    "test('with issue reason', { skip: 'requires macOS Keychain (#1234)' }, () => {});",
    "test('substantive reason', { skip: 'requires running local Docker daemon' }, () => {});",
    "test('not skipped', { skip: false }, () => {});",
    "test('ctx with reason', (t) => { t.skip('missing live credentials (#1234)'); });",
    "const sample = `test.skip('inside string', () => {})`;",
    "// test.skip('inside comment', () => {});",
    'void sample;',
  ].join('\n');
  assert.deepEqual(lintTestUnexcusedSkips(safeJs, { path: 'test/justified-skips.test.mjs' }), []);

  const safePy = [
    'import os, sys, pytest, unittest',
    '@pytest.mark.skip(reason="blocked on #1234")',
    'def test_issue_reason():',
    '    assert True',
    '@pytest.mark.skipif(sys.platform == "win32", reason="posix only")',
    'def test_conditional():',
    '    assert True',
    '@unittest.skipIf(not os.environ.get("LIVE"), "needs live env")',
    'def test_unittest_cond():',
    '    assert True',
    '# TODO(#555) re-enable after migration',
    '@pytest.mark.skip',
    'def test_comment_excused():',
    '    assert True',
    'def test_string_and_comment():',
    '    doc = "@pytest.mark.skip"',
    '    # @pytest.mark.skip',
    '    assert doc',
  ].join('\n');
  assert.deepEqual(lintTestUnexcusedSkips(safePy, { path: 'tests/test_justified.py' }), []);

  // Non-test paths and fixtures/helpers excluded.
  assert.deepEqual(lintTestUnexcusedSkips(badJs, { path: 'src/runner.mjs' }), []);
  assert.deepEqual(lintTestUnexcusedSkips(badJs, { path: 'test/fixtures/bad.test.mjs' }), []);
  assert.deepEqual(lintTestUnexcusedSkips(badJs, { path: 'test/helpers/util.mjs' }), []);

  // pdd.json severity overrides (warn, error, off).
  const root = makeTempRepo(t, {
    'test/skip-sample.test.mjs': "test.skip('forgotten test', () => {});\n",
  });
  const defRes = lintRepoProject({ root, files: ['test/skip-sample.test.mjs'], config: {} });
  assert.equal(defRes.ok, true);
  assert.equal(defRes.warnings.filter(w => w.includes('[test-unexcused-skip]')).length, 1);

  const errRes = lintRepoProject({ root, files: ['test/skip-sample.test.mjs'], config: { rules: { 'test-unexcused-skip': 'error' } } });
  assert.equal(errRes.ok, false);
  assert.equal(errRes.errors.filter(e => e.includes('[test-unexcused-skip]')).length, 1);

  const offRes = lintRepoProject({ root, files: ['test/skip-sample.test.mjs'], config: { disable: ['test-unexcused-skip'] } });
  assert.equal(offRes.ok, true);
  assert.equal(offRes.warnings.filter(w => w.includes('[test-unexcused-skip]')).length, 0);
});

test('3562 Part 2C: test-fixed-sleep and test-unexcused-skip stay strictly linear O(N) on 50k–100k+ adversarial inputs (< 500ms)', () => {
  const adversarialPayloads = [
    // Original nested/unclosed delimiter payload (~101KB)
    [
      'new Promise('.repeat(4500),
      'test.skip('.repeat(2000),
      'setTimeout('.repeat(2000),
      `test('a', { skip: ${'('.repeat(200)}true${')'.repeat(200)} }, () => {});\n`,
      '// '.padEnd(5000, 'a') + '\n',
    ].join(''),
    // P1-2 #1: import backtracking bomb (~65KB)
    ('import ' + ' '.repeat(155) + '\n').repeat(400),
    // P1-2 #2: const/let/var backtracking bomb (~61KB)
    ('const ' + ' '.repeat(115) + '\n').repeat(500),
    // P1-2 #3: deep nested outer parens (depth 25,000, ~50KB)
    `test('deep', { skip: ${'('.repeat(25_000)}true${')'.repeat(25_000)} }, () => {});\n`,
    // P1-2 #4: deeply nested test(..., { x: test(..., { ... }) }) (~45KB)
    `${'test("a", { x: '.repeat(1500)}true${' }, () => {})'.repeat(1500)};\n`,
  ];

  for (const payload of adversarialPayloads) {
    const t0 = performance.now();
    const sleepOut = lintTestFixedSleeps(payload, { path: 'test/adversarial.test.mjs' });
    const skipOut = lintTestUnexcusedSkips(payload, { path: 'test/adversarial.test.mjs' });
    const elapsedMs = performance.now() - t0;
    assert.ok(Array.isArray(sleepOut) && Array.isArray(skipOut));
    assert.ok(elapsedMs < 500, `expected < 500ms for ${payload.length} chars, took ${elapsedMs.toFixed(1)}ms`);
  }
});

test('3562 R1 regressions: P1-1..P1-5 and P2-1..P2-2 edge cases', () => {
  // P1-1: out-of-range numeric timestamps, non-string target coercion, non-finite windowDays, negative outcomes
  assert.equal(normalizeFlakeEntry({ ts: 1e20, target: 'test/a.test.mjs', outcome: 'base-test-red' }), null);
  assert.equal(normalizeFlakeEntry({ ts: -1e17, target: 'test/a.test.mjs', outcome: 'base-test-red' }), null);
  assert.equal(normalizeFlakeEntry({ target: 'test/a.test.mjs', outcome: 'base-test-red' }, { now: () => 1e20 }), null);
  assert.equal(normalizeFlakeEntry({ ts: Date.now(), target: { foo: 1 }, outcome: 'base-test-red' }), null);
  assert.equal(normalizeFlakeEntry({ ts: Date.now(), target: 12345, outcome: 'base-test-red' }), null);
  assert.deepEqual(
    parseFlakeLedger(`${JSON.stringify({ ts: 1e20, target: 'test/a.test.mjs', outcome: 'base-test-red' })}\n${JSON.stringify({ ts: Date.now(), target: { bad: true }, outcome: 'base-test-red' })}\n`),
    [],
  );

  const metricsOutOfRange = calculateAutopilotMetrics({
    repos: ['acme/widgets'],
    runs: [],
    now: '2026-11-21T12:00:00.000Z',
    flakeWindowDays: 1e12,
    flakeEntries: [
      { ts: -1e17, repo: 'acme/widgets', target: 'test/a.test.mjs', outcome: 'base-test-red' },
      { ts: 1e20, repo: 'acme/widgets', target: 'test/a.test.mjs', outcome: 'base-test-red' },
    ],
  });
  assert.deepEqual(metricsOutOfRange.recurringFlakes.recurring, []);

  const metricsSanitizedPreSummary = calculateAutopilotMetrics({
    repos: ['acme/widgets'],
    runs: [],
    now: '2026-11-21T12:00:00.000Z',
    recurringFlakes: {
      totalEntries: 3,
      windowDays: Infinity,
      threshold: 3,
      recurring: [{
        repo: 'acme/widgets',
        target: 'test/x.test.mjs',
        count: 3,
        outcomes: { 'flaked-then-passed': -1, 'reproduced-red': 3, 'base-test-red': -5 },
        lastSeen: '2026-11-21T10:00:00.000Z',
      }],
    },
  });
  assert.equal(metricsSanitizedPreSummary.recurringFlakes.windowDays, 7);
  assert.deepEqual(metricsSanitizedPreSummary.recurringFlakes.recurring[0].outcomes, {
    'flaked-then-passed': 0,
    'reproduced-red': 3,
    'base-test-red': 0,
  });

  // P1-3 #1 & #2: template literal and Python triple-quoted strings cannot spoof allow/excuse comments
  const spoofSleepJs = [
    'const s = `hello',
    '// pdd-allow-sleep: fake`;',
    'await sleep(500);',
  ].join('\n');
  assert.equal(lintTestFixedSleeps(spoofSleepJs, { path: 'test/spoof.test.mjs' }).length, 1);

  const spoofSkipJs = [
    'const doc = `line 1',
    '// #1234`;',
    'test.skip("unexcused", () => {});',
  ].join('\n');
  assert.equal(lintTestUnexcusedSkips(spoofSkipJs, { path: 'test/spoof.test.mjs' }).length, 1);

  const spoofPy = [
    'import time',
    'def test_spoof():',
    '    s = """line1',
    '# pdd-allow-sleep"""',
    '    time.sleep(1)',
  ].join('\n');
  assert.equal(lintTestFixedSleeps(spoofPy, { path: 'tests/test_spoof.py' }).length, 1);

  // P1-3 #3: valid multi-line /* ... */ block comments excuse both skip and sleep
  const blockCommentExcuses = [
    '/*',
    ' * Tracked in #1234',
    ' */',
    'test.skip("block excused", () => {});',
    '/*',
    ' * pdd-allow-sleep: fs mtime',
    ' */',
    'await sleep(200);',
  ].join('\n');
  assert.deepEqual(lintTestUnexcusedSkips(blockCommentExcuses, { path: 'test/block.test.mjs' }), []);
  assert.deepEqual(lintTestFixedSleeps(blockCommentExcuses, { path: 'test/block.test.mjs' }), []);

  // P1-3 #4: Python // floor division does NOT hide subsequent time.sleep on the same line
  assert.equal(
    lintTestFixedSleeps('import time\ndef test_div():\n    x = 10 // 2; time.sleep(1)\n', { path: 'tests/test_div.py' }).length,
    1,
  );

  // P1-3 #5: JS regex literal containing an apostrophe does NOT swallow trailing allow comment
  assert.deepEqual(
    lintTestFixedSleeps("const r = /foo'bar/; await sleep(500); // pdd-allow-sleep: ok\nvoid r;\n", { path: 'test/regex.test.mjs' }),
    [],
  );

  // P1-4: whole-identifier reject/resolve matching (single-letter reject params `e`/`r` and `$` resolve param)
  const p14Js = [
    "test('p14', async () => {",
    '  await new Promise((resolve, e) => setTimeout(() => resolve(), 500));',
    '  await new Promise((resolve, r) => setTimeout(() => resolve(), 500));',
    '  await new Promise(($) => setTimeout(() => $(), 500));',
    '});',
  ].join('\n');
  assert.equal(lintTestFixedSleeps(p14Js, { path: 'test/p14.test.mjs' }).length, 3);

  // P1-5: parameterized helpers and shadowed zero-delay vars must NOT falsely flag
  const p15ParamHelper = [
    'const delay = ms => new Promise(r => setTimeout(r, ms));',
    "test('unrelated', () => { const ms = 100; return ms; });",
    'void delay;',
  ].join('\n');
  assert.deepEqual(lintTestFixedSleeps(p15ParamHelper, { path: 'test/p15-helper.test.mjs' }), []);

  const p15ShadowedZero = [
    "test('one', () => { const ms = 500; return ms; });",
    "test('two', async () => { const ms = 0; await sleep(ms); });",
  ].join('\n');
  assert.deepEqual(lintTestFixedSleeps(p15ShadowedZero, { path: 'test/p15-shadow.test.mjs' }), []);

  // P2-1: semicolon-less side-effect import does not break default/namespace timers/promises import
  const p21NoSemi = [
    "import './helpers/test-home.mjs'",
    "import tp from 'node:timers/promises'",
    "test('x', async () => { await tp.setTimeout(500); })",
  ].join('\n');
  assert.equal(lintTestFixedSleeps(p21NoSemi, { path: 'test/p21.test.mjs' }).length, 1);

  // P2-2: owner/repo#N, interpolated template titles with #N, and 1st-arg test({ skip: true }, fn)
  const p22Excused = [
    "test.skip('see promptdriven/pdd#3562', () => {});",
    'const osName = process.platform;',
    'test.skip(`broken on ${osName} (#1234)`, () => {});',
    'test(`also tracked in ${osName} (acme/widgets#99)`, { skip: true }, () => {});',
  ].join('\n');
  assert.deepEqual(lintTestUnexcusedSkips(p22Excused, { path: 'test/p22-ok.test.mjs' }), []);

  const p22FirstArgSkip = [
    'test({ skip: true }, () => {});',
    "it({ skip: '' }, () => {});",
    'test({ skip: !process.env.LIVE }, () => {});',
  ].join('\n');
  const p22Warnings = lintTestUnexcusedSkips(p22FirstArgSkip, { path: 'test/p22-first-arg.test.mjs' });
  assert.equal(p22Warnings.length, 2, `expected 2 first-arg skip warnings, got:\n${p22Warnings.join('\n')}`);
});
