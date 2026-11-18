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

test('CLI overview, --repos, --repo, stages, skills, full, --date, --json, and single batched GraphQL Open query', async t => {
  const { dir, stateDir } = makeSandbox(t);
  const nowMs = Date.parse('2026-11-17T18:00:00Z');
  seedTwoRepos(stateDir, nowMs);

  const ghCalls = [];
  const fakeExecFile = async (cmd, args) => {
    ghCalls.push([cmd, ...args]);
    return {
      stdout: JSON.stringify({
        data: {
          r0: { issues: { totalCount: 14 } },
          r1: { issues: { totalCount: 8 } },
        },
      }),
    };
  };

  // 1. Unified overview
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
    assert.equal(ghCalls.length, 1, 'Open issue counts must use 1 batched GraphQL call');
    assert.match(out.text, /Unified \(2 repos\)/);
    assert.match(out.text, /Last 24h\s+22\s+3\s+3\s+2 \(66\.7%\)/);
    assert.match(out.text, /Week \(Mon-Sun\)\s+22\s+3\s+3\s+2 \(66\.7%\)/);
  }

  // 2. Per-repo breakdown (--repos)
  {
    const out = capture(), err = capture();
    const code = await runMetrics({
      argv: ['--repos', '--timezone', 'America/Los_Angeles'],
      cwd: dir,
      stdout: out,
      stderr: err,
      ports: { stateDir, now: () => nowMs, execFile: fakeExecFile },
    });
    assert.equal(code, 0, err.text);
    assert.match(out.text, /promptdriven\/pdd\s+14\s+2\s+2\s+1 \(50\.0%\)/);
    assert.match(out.text, /promptdriven\/pocket\s+8\s+1\s+1\s+1 \(100\.0%\)/);
    assert.match(out.text, /Total\s+22\s+3\s+3\s+2 \(66\.7%\)/);
  }

  // 3. Stages view
  {
    const out = capture(), err = capture();
    const code = await runMetrics({
      argv: ['stages', '--timezone', 'America/Los_Angeles'],
      cwd: dir,
      stdout: out,
      stderr: err,
      ports: { stateDir, now: () => nowMs, execFile: fakeExecFile },
    });
    assert.equal(code, 0, err.text);
    assert.match(out.text, /Week \(Mon-Sun\)\s+3\s+3\s+2\/2\s+2\/2\s+1\/1\s+2\/3\s+3\/3\s+3\/3\s+2\s+0/);
    assert.match(out.text, /Non-merged \(1\): 1 failed suite/);
  }

  // 4. Skills view
  {
    const out = capture(), err = capture();
    const code = await runMetrics({
      argv: ['skills', '--timezone', 'America/Los_Angeles'],
      cwd: dir,
      stdout: out,
      stderr: err,
      ports: { stateDir, now: () => nowMs, execFile: fakeExecFile },
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
      ports: { stateDir, now: () => nowMs, openIssues: { 'promptdriven/pocket': 8 } },
    });
    assert.equal(code, 0, err.text);
    const parsed = JSON.parse(out.text);
    assert.equal(parsed.schema, 'pdd.autopilot.metrics.v1');
    assert.equal(parsed.repoFilter, 'promptdriven/pocket');
    assert.equal(parsed.overview.windows[0].taken, 1);
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

  // Real pdd CLI process: off -> check -> on, plus offline zero-gh safety
  const env = {
    ...process.env,
    HOME: dir,
    PDD_STATE_DIR: stateDir,
    PDD_NO_OPEN: '1',
    PATH: `${dirname(process.execPath)}:/usr/bin:/bin`,
  };

  const offRes = spawnSync(process.execPath, [pddBin, 'metrics', 'off'], { cwd: dir, env, encoding: 'utf8' });
  assert.equal(offRes.status, 0, offRes.stderr);
  assert.match(offRes.stdout, /Autopilot metrics recording is OFF/);

  const jsonWhileOff = spawnSync(process.execPath, [pddBin, 'metrics', '--json'], { cwd: dir, env, encoding: 'utf8' });
  assert.equal(jsonWhileOff.status, 0, jsonWhileOff.stderr);
  const parsedOff = JSON.parse(jsonWhileOff.stdout);
  assert.equal(parsedOff.recording.enabled, false);
  assert.equal(parsedOff.overview.windows[0].taken, 3, 'Existing history stays readable when recording is OFF');

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
