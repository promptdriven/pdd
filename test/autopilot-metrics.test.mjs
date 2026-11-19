import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import {
  readAutopilotMetricsState,
  readMetricsConfig,
  recordAutopilotMetric,
  setAutopilotMetricsRecording,
} from '../src/autopilot-metrics.mjs';

function makeStateDir(t) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-autopilot-metrics-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  return dir;
}

test('recording defaults to ON, pauses writes when OFF, and resumes when ON while keeping history', t => {
  const stateDir = makeStateDir(t);
  let clock = Date.parse('2026-11-17T12:00:00Z');
  const opts = { stateDir, now: () => clock };

  assert.equal(readMetricsConfig(opts).enabled, true);

  const r1 = recordAutopilotMetric({
    repo: 'promptdriven/pdd',
    issue: 101,
    skill: 'bug',
    startedAt: clock - 600_000,
    at: clock,
    status: 'would-merge',
    pr: 201,
    durationMinutes: 10,
  }, opts);
  assert.equal(r1.recorded, true);

  clock += 60_000;
  setAutopilotMetricsRecording({ ...opts, action: 'off' });
  assert.equal(readMetricsConfig(opts).enabled, false);

  clock += 60_000;
  const r2 = recordAutopilotMetric({
    repo: 'promptdriven/pdd',
    issue: 102,
    skill: 'feature',
    startedAt: clock - 30_000,
    at: clock,
    status: 'merged',
    pr: 202,
  }, opts);
  assert.equal(r2.recorded, false);
  assert.equal(r2.enabled, false);

  const stateWhileOff = readAutopilotMetricsState(opts);
  assert.equal(stateWhileOff.runs.length, 1);
  assert.equal(stateWhileOff.runs[0].issue, 101);

  clock += 60_000;
  setAutopilotMetricsRecording({ ...opts, action: 'on' });
  assert.equal(readMetricsConfig(opts).enabled, true);

  clock += 60_000;
  const r3 = recordAutopilotMetric({
    repo: 'promptdriven/pdd',
    issue: 103,
    skill: 'small-change',
    startedAt: clock - 20_000,
    at: clock,
    status: 'merged',
    pr: 203,
    durationMinutes: 5,
  }, opts);
  assert.equal(r3.recorded, true);

  const stateAfterOn = readAutopilotMetricsState(opts);
  assert.equal(stateAfterOn.runs.length, 2);
  assert.deepEqual(stateAfterOn.runs.map(r => r.issue).sort((a, b) => a - b), [101, 103]);
});

test('reads existing Autopilot core history, active jobs, evidence logs, skill logs, and post-merge reopens while ignoring disabled 0-run configs', t => {
  const stateDir = makeStateDir(t);
  const autoDir = join(stateDir, 'autopilot');
  mkdirSync(autoDir, { recursive: true });

  // Stale disabled config with 0 runs -> ignored
  writeFileSync(join(autoDir, 'stale000.json'), JSON.stringify({
    repo: 'acme/stale-trial',
    enabled: false,
    cwd: '/nonexistent/stale',
  }));

  // Active enabled config with history, evidence, build log, active job, and post-merge regression
  writeFileSync(join(autoDir, 'live111.json'), JSON.stringify({
    repo: 'promptdriven/pocket',
    enabled: true,
    mode: 'auto',
    cwd: '/tmp/pocket',
  }));
  const coreDir = join(autoDir, 'live111-core');
  mkdirSync(join(coreDir, 'jobs'), { recursive: true });
  mkdirSync(join(coreDir, 'logs'), { recursive: true });

  const buildLog = join(coreDir, 'logs', '10-build-abc.log');
  writeFileSync(buildLog, 'Reading /opt/pdd/skills/pdd-small-change/SKILL.md\nDone.\n');

  writeFileSync(join(coreDir, 'logs', '10-evidence-deadbeef12345678.json'), JSON.stringify({
    issue: 10,
    pr: 25,
    ci: { state: 'green' },
    review: { state: 'pass' },
    suite: { state: 'pass' },
    evidence: {
      runtime: { state: 'not-run' },
      vectors: { state: 'pass', passed: 12, total: 12 },
      formal: { state: 'bounded' },
    },
  }));

  writeFileSync(join(coreDir, 'post-merge.json'), JSON.stringify({
    items: [{ issue: 10, pr: 25, reopened: true }],
  }));

  const atMs = Date.parse('2026-11-17T15:00:00Z');
  const historyLines = [
    // Strike metadata row with no outcome -> skipped!
    JSON.stringify({ at: atMs - 5000, issue: 99, strike: true }),
    // Real merged run -> read with skill, duration, evidence, and reopen!
    JSON.stringify({
      at: atMs,
      issue: 10,
      outcome: 'merged',
      pr: 25,
      text: 'merged PR #25 at deadbeef',
      log: buildLog,
      telemetry: { phases: { wallClockMinutes: 14.2 } },
    }),
  ];
  writeFileSync(join(coreDir, 'history.jsonl'), `${historyLines.join('\n')}\n`);

  writeFileSync(join(coreDir, 'jobs', '11.json'), JSON.stringify({
    issue: 11,
    title: 'fix login retry bug',
    started: atMs + 60_000,
    progress: { at: atMs + 120_000 },
    phase: 'running',
    role: 'build',
  }));

  const state = readAutopilotMetricsState({ stateDir });
  assert.deepEqual(state.repos, ['promptdriven/pocket']);
  assert.equal(state.runs.length, 2);

  const merged = state.runs.find(r => r.issue === 10);
  assert.equal(merged.skill, 'small-change');
  assert.equal(merged.status, 'merged');
  assert.equal(merged.reopened, true);
  assert.equal(merged.durationMinutes, 14.2);
  assert.equal(merged.gates.vectors, 'pass');
  assert.equal(merged.gates.formal, 'bounded');
  assert.equal(merged.gates.suite, 'pass');

  const running = state.runs.find(r => r.issue === 11);
  assert.equal(running.status, 'running');
  assert.equal(running.skill, 'bug');
});

test('supports post-merge merges object map, avoids misclassifying ended outcome text as bug, and keeps winning PR outcome', t => {
  const stateDir = makeStateDir(t);
  const autoDir = join(stateDir, 'autopilot');
  mkdirSync(autoDir, { recursive: true });

  writeFileSync(join(autoDir, 'repoA.json'), JSON.stringify({
    repo: 'promptdriven/pdd',
    enabled: true,
    cwd: '/tmp/pdd',
  }));
  writeFileSync(join(autoDir, 'repoB.json'), JSON.stringify({
    repo: 'promptdriven/other',
    enabled: true,
    cwd: '/tmp/other',
  }));

  const coreA = join(autoDir, 'repoA-core');
  mkdirSync(coreA, { recursive: true });
  writeFileSync(join(coreA, 'post-merge.json'), JSON.stringify({
    schema: 1,
    merges: {
      '88': { pr: 88, issue: 40, issues: [40, 41], reopened: false, reverted: true },
    },
    counts: { reverted: 1 },
  }));

  const baseMs = Date.parse('2026-11-17T16:00:00Z');
  writeFileSync(join(coreA, 'history.jsonl'), [
    // Resumed PR #88 first stopped, then merged -> merged wins
    JSON.stringify({ at: baseMs, issue: 40, pr: 88, outcome: 'stopped', text: 'stopped before review' }),
    JSON.stringify({ at: baseMs + 60_000, issue: 40, issues: [40, 41], pr: 88, outcome: 'merged', text: 'merged PR #88' }),
    // Ended run with "failed" in row.text (outcome summary, not issue title) stays feature when no bug hint exists
    JSON.stringify({ at: baseMs + 120_000, issue: 50, pr: 90, outcome: 'ended', text: 'ended: full test suite failed' }),
  ].join('\n') + '\n');

  const filtered = readAutopilotMetricsState({ stateDir, repoFilter: 'promptdriven/pdd', now: () => baseMs + 180_000 });
  assert.deepEqual(filtered.repos, ['promptdriven/pdd']);
  assert.equal(filtered.runs.length, 2);

  const pr88 = filtered.runs.find(r => r.issue === 40);
  assert.equal(pr88.status, 'merged');
  assert.equal(pr88.reopened, false);
  assert.equal(pr88.reverted, true);
  assert.equal(filtered.coreDirs['promptdriven/pdd'], coreA);

  const issue50 = filtered.runs.find(r => r.issue === 50);
  assert.equal(issue50.skill, 'feature');
  assert.equal(issue50.gates.suite, 'fail');
});

test('extracts promptChanged, numeric gateCounts, optional e2e, and preserves targets across on/off toggles (#3530)', t => {
  const stateDir = makeStateDir(t);
  const autoDir = join(stateDir, 'autopilot');
  mkdirSync(autoDir, { recursive: true });
  writeFileSync(join(autoDir, 'metrics-config.json'), JSON.stringify({
    enabled: true,
    targets: { convMinPct: 95, maxRegressionPct: 2, label: 'Q4' },
  }));
  setAutopilotMetricsRecording({ stateDir, action: 'off', repo: 'promptdriven/sandbox', at: '2026-11-18T00:00:00Z' });
  const cfg = readMetricsConfig({ stateDir });
  assert.deepEqual(cfg.targets, { convMinPct: 95, maxRegressionPct: 2, label: 'Q4' });
  assert.equal(cfg.repos['promptdriven/sandbox'], false);

  writeFileSync(join(autoDir, 'pdd.json'), JSON.stringify({ repo: 'promptdriven/pdd', enabled: true, cwd: '/tmp/pdd' }));
  const coreDir = join(autoDir, 'pdd-core');
  mkdirSync(coreDir, { recursive: true });
  const baseMs = Date.parse('2026-11-18T12:00:00Z');
  writeFileSync(join(coreDir, 'history.jsonl'), `${JSON.stringify({ at: baseMs, issue: 77, pr: 277, outcome: 'merged', text: 'merged PR #277 abcdef1' })}\n`);
  const logsDir = join(coreDir, 'logs');
  mkdirSync(logsDir, { recursive: true });
  writeFileSync(join(logsDir, '77-evidence-abcdef1.json'), JSON.stringify({
    evidence: {
      runtime: { state: 'pass', passed: 6, total: 6 },
      vectors: { state: 'pass', passed: 14, total: 14 },
      formal: { state: 'proved', passed: 3, total: 3 },
      e2e: { state: 'pass' },
    },
    suite: { state: 'pass' },
    review: { state: 'pass' },
    ci: { state: 'green' },
  }));

  const state = readAutopilotMetricsState({ stateDir, now: () => baseMs + 60_000 });
  const run = state.runs.find(r => r.issue === 77);
  assert.equal(run.promptChanged, true);
  assert.deepEqual(run.gateCounts, {
    runtime: { passed: 6, total: 6 },
    vectors: { passed: 14, total: 14 },
    formal: { passed: 3, total: 3 },
  });
  assert.equal(run.gates.e2e, 'pass');
});
