import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { coreWorld } from './helpers/core-world.mjs';
import { coreStatus } from '../src/autopilot-core.mjs';
import { runAutopilotLauncher, tickAutopilot } from '../src/autopilot-launcher.mjs';
import { evaluateShardFlakeRerun, selectCircuitBreakerRegression } from '../src/autopilot-regressions.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { productNext, productStart, productStatus, runProduct } from '../src/product.mjs';

const MIN = 60 * 1000;

test('3484: selectCircuitBreakerRegression and evaluateShardFlakeRerun enforce exact safety and shard boundaries', () => {
  const fixedNow = () => Date.parse('2026-11-17T08:00:00Z');
  assert.equal(selectCircuitBreakerRegression([], { now: fixedNow }), null);
  assert.equal(selectCircuitBreakerRegression([{ pr: 12, issue: 4, kind: 'reopened', code: 'post-merge-reopen', detail: 'reopened' }], { now: fixedNow }), null);

  const ciBreaker = selectCircuitBreakerRegression([
    { pr: 41, issues: [9], kind: 'ci', code: 'post-merge-ci', url: 'https://github.com/acme/widgets/runs/1', detail: 'shard failed token=ghp_1234567890abcdefghijklmnopqrstuv' },
  ], { now: fixedNow });
  assert.equal(ciBreaker.active, true);
  assert.equal(ciBreaker.kind, 'ci_broken');
  assert.equal(ciBreaker.code, 'post-merge-ci');
  assert.equal(ciBreaker.pr, 41);
  assert.equal(ciBreaker.issue, 9);
  assert.equal(ciBreaker.trippedAt, '2026-11-17T08:00:00.000Z');
  assert.ok(!ciBreaker.reason.includes('ghp_1234567890'));

  const revertBreaker = selectCircuitBreakerRegression([
    { pr: 41, issue: 9, kind: 'ci', code: 'post-merge-ci', detail: 'ci red' },
    { pr: 42, issue: 10, kind: 'revert', code: 'post-merge-revert', detail: 'Reverts #42' },
  ], { now: fixedNow });
  assert.equal(revertBreaker.kind, 'reverted');
  assert.equal(revertBreaker.code, 'post-merge-revert');
  assert.equal(revertBreaker.pr, 42);

  const makeShard = (idx, total, conclusion = 'success', status = 'completed', runId = 7001) => ({
    id: 500 + idx,
    name: `test-shard (${idx}/${total})`,
    status,
    conclusion: status === 'completed' ? conclusion : null,
    completed_at: status === 'completed' ? '2026-11-17T08:01:00Z' : null,
    details_url: `https://github.com/acme/widgets/actions/runs/${runId}/job/${500 + idx}`,
  });

  // 2 failed shards + 6 passing siblings -> rerun once
  const eightShards = Array.from({ length: 8 }, (_, i) => makeShard(i + 1, 8, i < 2 ? 'failure' : 'success'));
  const rerunDecision = evaluateShardFlakeRerun({ checkRuns: eightShards, statuses: [], headSha: 'a'.repeat(40), flakeRerunHead: null });
  assert.equal(rerunDecision.action, 'rerun');
  assert.deepEqual(rerunDecision.runIds, [7001]);
  assert.deepEqual(rerunDecision.failedNames, ['test-shard (1/8)', 'test-shard (2/8)']);

  // Already reran on this head -> none
  assert.equal(
    evaluateShardFlakeRerun({ checkRuns: eightShards, statuses: [], headSha: 'a'.repeat(40), flakeRerunHead: 'a'.repeat(40) }).action,
    'none',
  );

  // Sibling shards still in progress -> wait-siblings
  const pendingSiblings = Array.from({ length: 8 }, (_, i) => makeShard(i + 1, 8, i === 0 ? 'failure' : 'success', i === 0 ? 'completed' : 'in_progress'));
  assert.equal(evaluateShardFlakeRerun({ checkRuns: pendingSiblings, statuses: [], headSha: 'b'.repeat(40), flakeRerunHead: null }).action, 'wait-siblings');

  // 3 failed shards -> none
  const threeFailed = Array.from({ length: 8 }, (_, i) => makeShard(i + 1, 8, i < 3 ? 'failure' : 'success'));
  assert.equal(evaluateShardFlakeRerun({ checkRuns: threeFailed, statuses: [], headSha: 'c'.repeat(40), flakeRerunHead: null }).action, 'none');

  // Fewer than 3 passing siblings (2 failed + 2 passed) -> none
  const twoOfFour = Array.from({ length: 4 }, (_, i) => makeShard(i + 1, 4, i < 2 ? 'failure' : 'success'));
  assert.equal(evaluateShardFlakeRerun({ checkRuns: twoOfFour, statuses: [], headSha: 'd'.repeat(40), flakeRerunHead: null }).action, 'none');

  // Universal lint or CI (lint) failure -> none
  const lintFailed = [
    { id: 1, name: 'CI (lint)', status: 'completed', conclusion: 'failure', completed_at: '2026-11-17T08:01:00Z' },
    { id: 2, name: 'CI (build)', status: 'completed', conclusion: 'success', completed_at: '2026-11-17T08:01:00Z' },
    { id: 3, name: 'CI (typecheck)', status: 'completed', conclusion: 'success', completed_at: '2026-11-17T08:01:00Z' },
    { id: 4, name: 'CI (docs)', status: 'completed', conclusion: 'success', completed_at: '2026-11-17T08:01:00Z' },
  ];
  assert.equal(evaluateShardFlakeRerun({ checkRuns: lintFailed, statuses: [], headSha: 'e'.repeat(40), flakeRerunHead: null }).action, 'none');
});

test('3484: post-merge CI regression trips safety circuit breaker, downgrades saved mode auto -> observe before merging queued PRs, fires one deduplicated alert, and resets on start --mode auto', async t => {
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 2, report: 'file', label: 'pdd:autopilot' } });
  w.github.mergeMovesBase = true;
  writeFileSync(join(w.cwd, 'pdd.json'), JSON.stringify({
    autopilot: { mode: 'auto', trust: [], engine: 'core', testCommand: 'npm test', label: 'pdd:autopilot', quietMinutes: 40 },
  }));

  const cwd = w.git(w.cwd, 'rev-parse', '--show-toplevel');
  const pkgDir = join(w.dir, 'pkg');
  mkdirSync(pkgDir, { recursive: true });
  writeFileSync(join(pkgDir, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.35' }));

  const stateRoot = join(w.dir, 'launcher-state');
  mkdirSync(stateRoot, { recursive: true });
  const stateId = createHash('sha256').update(cwd).digest('hex').slice(0, 20);
  const stateFile = join(stateRoot, `${stateId}.json`);
  const homeDir = join(w.dir, 'home');
  mkdirSync(join(homeDir, '.config', 'pdd'), { recursive: true });
  writeFileSync(
    join(homeDir, '.config', 'pdd', 'autopilot-alerts.json'),
    JSON.stringify({ v: 1, service: 'slack', url: 'https://hooks.slack.com/services/T000/B000/secret' }),
    { mode: 0o600 },
  );

  const deliveredAlerts = [];
  const env = { HOME: homeDir, PATH: process.env.PATH };
  const launcherPorts = {
    stateRoot,
    now: w.now,
    env,
    timer: async () => true,
    warn: () => {},
    authority: { read: async () => ({ authority: 'trusted' }) },
    selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex' }),
    pathDiagnostic: () => [],
    machineGuard: w.machineGuard,
    alertPorts: {
      http: async ({ body }) => {
        deliveredAlerts.push(body?.text ?? body?.content ?? '');
        return { status: 200, text: 'ok' };
      },
    },
    run: async (command, args, options = {}) => {
      if (command === 'gh') return w.gh(args, options);
      const r = spawnSync('git', args, { cwd: options.cwd ?? cwd, encoding: 'utf8' });
      return { code: r.status, stdout: r.stdout, stderr: r.stderr };
    },
    corePorts: {
      jobs: w.jobs,
      checkBase: async () => ({ exitCode: 0, message: 'ok' }),
      agentReady: async () => true,
    },
  };

  writeFileSync(stateFile, JSON.stringify({
    enabled: true,
    engine: 'core',
    mode: 'auto',
    label: 'pdd:autopilot',
    cwd,
    repo: 'acme/widgets',
    defaultBranch: 'main',
    coordinatorId: 'coord-1',
    machine: 'runner-box',
    startedAt: new Date(w.now()).toISOString(),
    activatedAt: new Date(w.now()).toISOString(),
    agent: { id: 'codex', kind: 'codex', command: 'codex' },
    packageRoot: pkgDir,
  }));

  // 1) Merge issue #17 cleanly in auto mode.
  const baseParentSha = w.git(w.cwd, 'rev-parse', 'HEAD');
  w.github.checks.set(baseParentSha, [{
    id: 7001, name: 'ci', status: 'completed', conclusion: 'success',
    completed_at: new Date(w.now() - MIN).toISOString(), app: { id: 11 },
  }]);

  w.issue(17, { title: 'Add helper', labels: ['pdd:autopilot'] });
  await tickAutopilot(stateFile, launcherPorts);
  const { pr: pr17 } = w.build(17);
  await tickAutopilot(stateFile, launcherPorts);
  w.review(17, 'PASS');
  w.suite(17, 0);
  await tickAutopilot(stateFile, launcherPorts);
  assert.deepEqual(w.github.merges, [pr17.number]);

  // 2) Start issue #18 and get its PR #101 completely ready to merge (green CI, PASS review, green suite).
  w.advance(2 * MIN);
  w.issue(18, { title: 'Follow-up cleanup', labels: ['pdd:autopilot'] });
  await tickAutopilot(stateFile, launcherPorts);
  const { pr: pr18 } = w.build(18);
  await tickAutopilot(stateFile, launcherPorts);
  w.review(18, 'PASS');
  w.suite(18, 0);

  // 3) Before the tick that would merge PR #101, default-branch CI on PR #100's merge commit fails!
  const mergedPr17 = w.github.prs.get(pr17.number);
  const mergeSha = mergedPr17.mergeSha;
  const parentOfMerge = spawnSync('git', ['--git-dir', w.remote, 'rev-parse', `${mergeSha}^1`], { encoding: 'utf8' }).stdout.trim();
  w.github.checks.set(parentOfMerge, [{
    id: 7002, name: 'ci', status: 'completed', conclusion: 'success',
    completed_at: mergedPr17.mergedAt, app: { id: 11 },
  }]);
  w.advance(20 * MIN);
  w.github.checks.set(mergeSha, [{
    id: 7003, name: 'ci', status: 'completed', conclusion: 'failure',
    completed_at: new Date(w.now() - MIN).toISOString(),
    html_url: 'https://github.com/acme/widgets/actions/runs/8801/job/7003',
    app: { id: 11 },
  }]);

  const breakerTick = await tickAutopilot(stateFile, launcherPorts);
  assert.equal(breakerTick.exitCode, 0, breakerTick.message);
  assert.match(breakerTick.message, /observe: no merge/, 'same tick downgrades to observe mode');
  assert.deepEqual(w.github.merges, [pr17.number], 'PR #101 was prevented from merging onto broken main');

  const savedAfterTrip = JSON.parse(readFileSync(stateFile, 'utf8'));
  assert.equal(savedAfterTrip.mode, 'observe', 'saved launcher repo mode downgraded from auto to observe');
  assert.equal(savedAfterTrip.circuitBreaker?.kind, 'ci_broken');
  assert.equal(savedAfterTrip.circuitBreaker?.code, 'post-merge-ci');
  assert.equal(savedAfterTrip.circuitBreaker?.pr, pr17.number);
  assert.equal(savedAfterTrip.circuitBreaker?.issue, 17);

  assert.equal(deliveredAlerts.length, 1, 'fires one immediate Autopilot alert to Slack/Discord');
  assert.match(deliveredAlerts[0], /circuit breaker/i);
  assert.match(deliveredAlerts[0], /observe/);

  // 4) Subsequent tick does NOT send a duplicate alert and stays in observe mode.
  w.advance(20 * MIN);
  await tickAutopilot(stateFile, launcherPorts);
  assert.equal(deliveredAlerts.length, 1, 'alert is deduplicated across subsequent ticks');

  // 5) Status text and JSON report the circuit breaker clearly.
  const statusText = await runAutopilotLauncher({ command: 'status', cwd, packageRoot: pkgDir, env }, launcherPorts);
  assert.equal(statusText.exitCode, 0);
  assert.match(statusText.message, /mode observe \(this machine\) \(every check, no merge\)/);
  assert.match(statusText.message, /Circuit breaker: mode downgraded from auto to observe/);

  const statusJson = JSON.parse((await runAutopilotLauncher({ command: 'status', json: true, cwd, packageRoot: pkgDir, env }, launcherPorts)).message);
  assert.equal(statusJson.repositories[0].mode, 'observe');
  assert.equal(statusJson.repositories[0].circuitBreaker?.code, 'post-merge-ci');

  // 6) Operator fixes main and runs `pdd autopilot start --mode auto` -> clears circuit breaker.
  const restarted = await runAutopilotLauncher({ command: 'start', mode: 'auto', cwd, packageRoot: pkgDir, env }, launcherPorts);
  assert.equal(restarted.exitCode, 0, restarted.message);
  const savedAfterReset = JSON.parse(readFileSync(stateFile, 'utf8'));
  assert.equal(savedAfterReset.mode, 'auto');
  assert.equal(savedAfterReset.circuitBreaker, undefined);
  const statusAfterReset = await runAutopilotLauncher({ command: 'status', cwd, packageRoot: pkgDir, env }, launcherPorts);
  assert.doesNotMatch(statusAfterReset.message, /Circuit breaker:/);
});

test('3484: reverted Autopilot merge trips safety circuit breaker in core ticks', async t => {
  const alerts = [];
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1, report: 'file' } });
  w.github.mergeMovesBase = true;

  w.issue(21, { title: 'Add parser shortcut' });
  await w.tick({ alert: a => alerts.push(a) });
  const { pr } = w.build(21);
  await w.tick({ alert: a => alerts.push(a) });
  w.review(21, 'PASS');
  w.suite(21, 0);
  await w.tick({ alert: a => alerts.push(a) });
  assert.deepEqual(w.github.merges, [pr.number]);

  const mergeSha = w.github.prs.get(pr.number).mergeSha;
  const parentSha = spawnSync('git', ['--git-dir', w.remote, 'rev-parse', `${mergeSha}^1`], { encoding: 'utf8' }).stdout.trim();
  w.github.checks.set(parentSha, [{ id: 1, name: 'ci', status: 'completed', conclusion: 'success', completed_at: new Date(w.now()).toISOString(), app: { id: 11 } }]);
  w.github.checks.set(mergeSha, [{ id: 2, name: 'ci', status: 'completed', conclusion: 'success', completed_at: new Date(w.now()).toISOString(), app: { id: 11 } }]);

  // Push a revert commit onto origin/main after merge.
  w.advance(5 * MIN);
  const cloneDir = join(w.dir, 'revert-push');
  w.git(w.dir, 'clone', '-q', w.remote, cloneDir);
  const commitIso = new Date(w.now()).toISOString();
  const revCommit = spawnSync('git', ['-c', 'user.name=Dev', '-c', 'user.email=dev@example.com', 'commit', '--allow-empty', '-m', `Revert "Merge PR #${pr.number}"\n\nThis reverts commit ${mergeSha}.`], {
    cwd: cloneDir,
    encoding: 'utf8',
    env: { ...process.env, GIT_AUTHOR_DATE: commitIso, GIT_COMMITTER_DATE: commitIso },
  });
  assert.equal(revCommit.status, 0, revCommit.stderr);
  w.git(cloneDir, 'push', '-q', 'origin', 'HEAD:main');

  w.advance(20 * MIN);
  const res = await w.tick({ alert: a => alerts.push(a) });
  assert.equal(w.settings.mode, 'observe');
  assert.equal(w.state.mode, 'observe');
  assert.equal(res.circuitBreaker?.kind, 'reverted');
  assert.equal(res.circuitBreaker?.code, 'post-merge-revert');
  assert.equal(alerts.length, 1);
  assert.equal(alerts[0].kind, 'test-suite');
  assert.equal(alerts[0].issue, 21);

  const rendered = coreStatus({ state: w.state, settings: w.settings }, { root: w.root, reportRoot: w.reportRoot, now: w.now });
  assert.match(rendered, /Circuit breaker: mode downgraded from auto to observe.*reverted/);
});

test('3484: Autopilot waits for pending sibling shards, reruns failed shard subset once via gh run rerun --failed without burning a repair, and repairs if rerun still fails', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, repairs: 2 } });
  const cliReruns = [];
  const origGh = w.github.gh;
  w.github.gh = async (args, opts) => {
    if (args[0] === 'run' && args[1] === 'rerun') {
      cliReruns.push(args);
      const runId = Number(args[2]);
      w.github.reruns.push({ kind: 'cli-rerun-failed', id: runId, at: w.now() });
      return { code: 0, stdout: '', stderr: '' };
    }
    return origGh(args, opts);
  };

  // Part A: Flaky shard recovers on bounded rerun -> 0 repairs burned, merges cleanly!
  w.issue(31, { title: 'Flaky matrix shard PR' });
  await w.tick();
  const built31 = w.build(31, { body: 'Fixes #31\n\nRuntime: not run (no prompt)', result: { promptChanged: false }, checks: null });

  const makeMatrix = (sha, runId, states, completedAt) => states.map((st, idx) => ({
    id: runId * 10 + idx + 1,
    name: `test-shard (${idx + 1}/${states.length})`,
    status: st === 'in_progress' ? 'in_progress' : 'completed',
    conclusion: st === 'in_progress' ? null : st,
    ...(st === 'in_progress' ? { started_at: '2026-11-17T08:00:00Z' } : { completed_at: completedAt }),
    details_url: `https://github.com/${w.github.repo}/actions/runs/${runId}/job/${runId * 10 + idx + 1}`,
  }));

  // 1) Shard 1 fails early while shards 2..8 are still in_progress -> waits without rerunning or repairing!
  w.github.checks.set(built31.head, makeMatrix(built31.head, 9901, ['failure', ...Array(7).fill('in_progress')], '2026-11-17T08:02:00Z'));
  await w.tick();
  assert.equal(cliReruns.length, 0, 'waits for in-progress sibling shards before invoking gh run rerun');
  assert.equal(w.started.filter(j => j.issue === 31 && j.role === 'repair').length, 0, 'burns zero repairs while waiting');

  // 2) Shards 2 fails too (2 failed) and shards 3..8 succeed (6 passing siblings, 8 completed) -> invokes gh run rerun 9901 --failed once!
  const staleFailedMatrix = makeMatrix(built31.head, 9901, ['failure', 'failure', ...Array(6).fill('success')], '2026-11-17T08:04:00Z');
  w.github.checks.set(built31.head, staleFailedMatrix);
  await w.tick();
  assert.equal(cliReruns.length, 1, 'invokes gh run rerun --failed once');
  assert.deepEqual(cliReruns[0], ['run', 'rerun', '9901', '--repo', 'acme/widgets', '--failed']);
  assert.equal(w.started.filter(j => j.issue === 31 && j.role === 'repair').length, 0, 'burns zero repairs on initial shard flake');
  const job31 = JSON.parse(readFileSync(join(w.root, 'jobs', '31.json'), 'utf8'));
  assert.equal(job31.flakeRerunHead, built31.head);

  // 3) Next poll briefly sees stale pre-rerun check-runs -> still pending, 0 repairs!
  w.advance(30 * 1000);
  await w.tick();
  assert.equal(cliReruns.length, 1);
  assert.equal(w.started.filter(j => j.issue === 31 && j.role === 'repair').length, 0);

  // 4) Rerun finishes all green -> review + suite pass -> merges with 0 repairs!
  w.github.checks.set(built31.head, makeMatrix(built31.head, 9901, Array(8).fill('success'), '2026-11-17T08:06:00Z'));
  await w.tick();
  w.review(31, 'PASS');
  w.suite(31, 0);
  await w.tick();
  assert.deepEqual(w.github.merges, [built31.pr.number]);
  assert.equal(w.started.filter(j => j.issue === 31 && j.role === 'repair').length, 0);

  // Part B: Persistent failure in 1 of 8 shards -> reruns once, then on second failure at same head proceeds normally to repair!
  w.issue(32, { title: 'Real shard-1 regression' });
  await w.tick();
  const built32 = w.build(32, { body: 'Fixes #32\n\nRuntime: not run (no prompt)', result: { promptChanged: false }, checks: null });
  w.github.checks.set(built32.head, makeMatrix(built32.head, 9902, ['failure', ...Array(7).fill('success')], '2026-11-17T08:10:00Z'));
  await w.tick();
  assert.equal(cliReruns.length, 2, 'reruns 9902 once on first failure');
  assert.equal(w.started.filter(j => j.issue === 32 && j.role === 'repair').length, 0);

  // Rerun completes with a newer timestamp and STILL fails shard 1 -> does NOT rerun again, starts repair!
  w.github.checks.set(built32.head, makeMatrix(built32.head, 9902, ['failure', ...Array(7).fill('success')], '2026-11-17T08:14:00Z'));
  await w.tick();
  assert.equal(cliReruns.length, 2, 'never reruns a second time on the same headSha');
  assert.equal(w.started.filter(j => j.issue === 32 && j.role === 'repair').length, 1, 'proceeds normally to LLM repair');
});

test('3484: pdd product status, next, and start recover closed-unbuilt slice issues without deadlocking or duplicating issues', async t => {
  const cwd = mkdtempSync(join(tmpdir(), 'pdd-product-closed-unbuilt-'));
  t.after(() => rmSync(cwd, { recursive: true, force: true }));
  mkdirSync(join(cwd, 'product'), { recursive: true });
  mkdirSync(join(cwd, 'contracts'), { recursive: true });

  writeFileSync(join(cwd, 'contracts', 'world.md'), '# World\n');
  writeFileSync(join(cwd, 'product', 'map.md'), [
    '# Pocket: map',
    '',
    'Size: medium',
    '',
    '## Parts',
    '| Part | Folder | What it is |',
    '| --- | --- | --- |',
    '| hub | prompts/hub | Hub service |',
    '| node | prompts/node | Edge node |',
    '| phone | prompts/phone | Mobile client |',
    '',
    '## Stories',
    '| Id | Part | Story | Tag |',
    '| --- | --- | --- | --- |',
    '| H01 | hub | Hub registers devices. | CORE |',
    '| H02 | hub | Hub relays events. | CORE |',
    '| N01 | node | Node pairs with hub. | CORE |',
    '| N02 | node | Node streams status. | CORE |',
    '| N03 | node | Node caches offline queue. | CORE |',
    '| P01 | phone | Phone lists paired nodes. | CORE |',
    '| P02 | phone | Phone triggers node action. | CORE |',
    '',
    '## Journeys',
    '| Id | Journey | Stories |',
    '| --- | --- | --- |',
    '| J1 | Pair and trigger action end to end. | H01, N01, P01, P02 |',
    '',
    '## Questions',
    '| Id | Question | Recommendation | Example | Answer |',
    '| --- | --- | --- | --- | --- |',
  ].join('\n'));

  writeFileSync(join(cwd, 'product', 'plan.md'), [
    '# Pocket: plan',
    '',
    '## Boundaries',
    '| From | To | What crosses | Contract |',
    '| --- | --- | --- | --- |',
    '| phone | hub | register, relay | contracts/world.md |',
    '| node | hub | pair, status | contracts/world.md |',
    '',
    '## Runs',
    '| Run | Part | Slice | Stories | Needs |',
    '| --- | --- | --- | --- | --- |',
    '| hub-1 | hub | 1 | H01, H02 | - |',
    '| node-1 | node | 1 | N01, N02, N03 | - |',
    '| phone-1 | phone | 1 | P01, P02 | - |',
    '| journeys | all | 1 | J1 | hub-1, node-1, phone-1 |',
  ].join('\n'));

  const state = {
    productState: null,
    clock: 1000,
    reopened: [],
    created: [],
    starts: [],
    prs: [],
    events: {},
    savedStories: [],
    issues: [
      { number: 3, state: 'CLOSED', author_association: 'OWNER', user: { login: 'owner' }, created_at: '2026-11-16T01:00:00Z', body: '<!-- pdd-product: run=hub-1 -->' },
      { number: 4, state: 'CLOSED', author_association: 'OWNER', user: { login: 'owner' }, created_at: '2026-11-16T01:01:00Z', body: '<!-- pdd-product: run=node-1 -->' },
    ],
  };

  const ports = {
    env: { HOME: process.env.HOME, PATH: process.env.PATH },
    lockProductState: async () => ({ handle: 'lock-1' }),
    unlockProductState: async () => ({}),
    readProductState: async () => ({ json: state.productState }),
    writeProductState: async ({ json }) => { state.productState = json; return {}; },
    now: async () => ({ milliseconds: (state.clock += 1000) }),
    resolveRepository: async () => ({ repository: 'acme/pocket', defaultBranch: 'main' }),
    planOnBase: async () => true,
    listRuns: async () => [],
    storyEvidence: async () => [],
    savedStoryEvidence: async () => ({ stories: state.savedStories, warnings: [] }),
    issuePage: async ({ page, perPage }) => ({
      items: state.issues.slice((page - 1) * perPage, page * perPage),
      total_count: state.issues.length,
      incomplete_results: false,
    }),
    issueByNumber: async ({ number }) => state.issues.find(i => i.number === number) ?? { status: 404, message: 'Not Found' },
    timelinePage: async ({ issue }) => state.events[issue] ?? [],
    pullRequest: async ({ number }) => state.prs.find(p => p.number === number),
    currentActor: async () => ({ login: 'owner' }),
    openBaseSource: async () => ({ root: cwd, handle: null }),
    closeBaseSource: async () => ({}),
    reopenIssue: async ({ number }) => {
      state.reopened.push(number);
      const found = state.issues.find(i => i.number === number);
      if (found) found.state = 'OPEN';
      return {};
    },
    createIssue: async payload => {
      const nextNum = 10 + state.created.length;
      state.created.push(payload);
      state.issues.push({ number: nextNum, state: 'OPEN', author_association: 'OWNER', user: { login: 'owner' }, created_at: '2026-11-16T02:00:00Z', body: payload.body });
      return { url: `https://github.com/acme/pocket/issues/${nextNum}` };
    },
    startRun: async args => {
      state.starts.push(args);
      return { exitCode: 0, message: `Started feature #${args.issue}.` };
    },
  };

  // 1) Status reports closed-unbuilt issues honestly and includes them in Can start now!
  const statusObj = await productStatus({ cwd }, ports);
  assert.deepEqual(
    statusObj.runs.map(r => [r.run, r.state, r.issue]),
    [
      ['hub-1', 'issue closed (0 of 2 pass)', 3],
      ['node-1', 'issue closed (0 of 3 pass)', 4],
      ['phone-1', 'planned', null],
      ['journeys', 'planned', null],
    ],
  );
  assert.deepEqual(statusObj.ready, ['hub-1', 'node-1', 'phone-1']);

  const cliStatus = await runProduct({ command: 'status', cwd }, ports);
  assert.equal(cliStatus.exitCode, 0);
  assert.match(cliStatus.message, /hub-1: issue closed \(0 of 2 pass\) · issue #3/);
  assert.match(cliStatus.message, /node-1: issue closed \(0 of 3 pass\) · issue #4/);
  assert.match(cliStatus.message, /Can start now: hub-1, node-1, phone-1\./);

  // 2) Next offers hub-1, node-1, phone-1 and keeps journeys waiting on all three.
  const nextObj = await productNext({ cwd }, ports);
  assert.deepEqual(nextObj.ready, ['hub-1', 'node-1', 'phone-1']);
  assert.deepEqual(nextObj.waiting, [{ run: 'journeys', needs: ['hub-1', 'node-1', 'phone-1'] }]);

  // 3) Partial saved pass (1 of 2 on hub-1) still reports `issue closed (1 of 2 pass)` and stays startable.
  state.savedStories = [{ story: 'H01-register.md', pass: true, current: true, at: 5000 }];
  const partialStatus = await runProduct({ command: 'status', cwd }, ports);
  assert.match(partialStatus.message, /hub-1: issue closed \(1 of 2 pass\) · issue #3/);

  // 4) Starting hub-1 reopens existing issue #3 on GitHub without creating a duplicate issue!
  const startedHub = await productStart({ cwd, run: 'hub-1', agent: 'codex' }, ports);
  assert.equal(startedHub.exitCode, 0, startedHub.message);
  assert.equal(startedHub.issue, 3);
  assert.equal(startedHub.created, false);
  assert.equal(startedHub.started, true);
  assert.deepEqual(state.reopened, [3]);
  assert.equal(state.created.length, 0, 'reopens #3 instead of creating a duplicate issue');
  assert.equal(state.starts.length, 1);
  assert.equal(state.starts[0].issue, 3);

  // 5) Now #3 is OPEN on GitHub, so status reports `issue ready · issue #3` while node-1 remains `issue closed (0 of 3 pass)`.
  const afterReopen = await runProduct({ command: 'status', cwd }, ports);
  assert.match(afterReopen.message, /hub-1: issue ready · issue #3/);
  assert.match(afterReopen.message, /node-1: issue closed \(0 of 3 pass\) · issue #4/);
  assert.match(afterReopen.message, /Can start now: node-1, phone-1\./);

  // 6) When hub-1 merges its code PR and #3 closes again, status reports `merged` (never `issue closed` or reopened).
  state.issues.find(i => i.number === 3).state = 'CLOSED';
  state.events[3] = [{ event: 'cross-referenced', source: { issue: { pull_request: { html_url: 'https://github.com/acme/pocket/pull/55' } } } }];
  state.prs.push({
    number: 55,
    url: 'https://github.com/acme/pocket/pull/55',
    state: 'MERGED',
    isDraft: false,
    isCrossRepository: false,
    headRefName: 'feat/hub-1',
    updatedAt: '2026-11-16T03:00:00Z',
    body: '<!-- pdd-product: run=hub-1 -->\n<!-- pdd-workflow:run-hub:code -->',
  });
  const afterMerge = await runProduct({ command: 'status', cwd }, ports);
  assert.match(afterMerge.message, /hub-1: merged · issue #3/);
  assert.match(afterMerge.message, /Can start now: node-1, phone-1\./);
});

test('3484: parseShardFamily runs in linear time without ReDoS and evaluateShardFlakeRerun normalizes uppercase GraphQL checks and camelCase runId/detailsUrl', () => {
  const head = 'f'.repeat(40);
  const start = performance.now();
  const pathologicalNames = [
    'x'.repeat(301) + ' (1/4)',
    'a('.repeat(2000) + '1)',
    'test (' + 'a, '.repeat(120) + 'end)',
    'suite-' + 'shard-'.repeat(200) + 'tail',
    'nested ((1/4))',
  ];
  for (const bad of pathologicalNames) {
    const checks = [
      { id: 1, name: bad, status: 'completed', conclusion: 'failure', run_id: 10 },
      { id: 2, name: 'test-shard (2/4)', status: 'completed', conclusion: 'success', run_id: 10 },
      { id: 3, name: 'test-shard (3/4)', status: 'completed', conclusion: 'success', run_id: 10 },
      { id: 4, name: 'test-shard (4/4)', status: 'completed', conclusion: 'success', run_id: 10 },
    ];
    assert.equal(evaluateShardFlakeRerun({ checkRuns: checks, statuses: [], headSha: head, flakeRerunHead: null }).action, 'none');
  }
  assert.ok(performance.now() - start < 250, 'pathological inputs complete in milliseconds');

  // Uppercase COMPLETED + SKIPPED / NEUTRAL / SUCCESS checks with camelCase runId & detailsUrl:
  // never falsely wait on COMPLETED+SKIPPED, and extract both camelCase runId and detailsUrl!
  const graphqlChecks = [
    { id: 901, name: 'matrix [ubuntu, 1]', status: 'COMPLETED', conclusion: 'FAILURE', runId: 4401, completedAt: '2026-11-17T08:05:00Z' },
    { id: 902, name: 'matrix [ubuntu, 2]', status: 'COMPLETED', conclusion: 'FAILURE', detailsUrl: 'https://github.com/acme/widgets/actions/runs/4402/job/902', completedAt: '2026-11-17T08:05:01Z' },
    { id: 903, name: 'matrix [ubuntu, 3]', status: 'COMPLETED', conclusion: 'SUCCESS', runId: 4401 },
    { id: 904, name: 'matrix [ubuntu, 4]', status: 'COMPLETED', conclusion: 'SUCCESS', runId: 4401 },
    { id: 905, name: 'matrix [ubuntu, 5]', status: 'COMPLETED', conclusion: 'SUCCESS', runId: 4401 },
    { id: 906, name: 'docs-gate', status: 'COMPLETED', conclusion: 'SKIPPED', runId: 4403 },
    { id: 907, name: 'optional-bench', status: 'COMPLETED', conclusion: 'NEUTRAL', runId: 4403 },
  ];
  const decision = evaluateShardFlakeRerun({
    checkRuns: graphqlChecks,
    statuses: [{ context: 'cla', state: 'SUCCESS' }],
    headSha: head,
    flakeRerunHead: null,
  });
  assert.equal(decision.action, 'rerun');
  assert.deepEqual(decision.runIds, [4401, 4402]);
  assert.equal(decision.shards.length, 2);
  assert.deepEqual(decision.shards.map(s => [s.checkId, s.runId]), [[901, 4401], [902, 4402]]);

  // Uppercase COMPLETED + CANCELLED in another shard family is a failure, NEVER waited on as pending.
  const cancelledCheck = [
    ...graphqlChecks.slice(0, 5),
    { id: 908, name: 'deploy-preview', status: 'COMPLETED', conclusion: 'CANCELLED', runId: 4404 },
  ];
  assert.equal(
    evaluateShardFlakeRerun({ checkRuns: cancelledCheck, statuses: [], headSha: head, flakeRerunHead: null }).action,
    'none',
  );
});

test('3484: circuitBreakerClearedAt ignores pre-clear regressions and pdd autopilot auto/off + start without --mode clear breaker overrides cleanly', async t => {
  const fixedNow = () => Date.parse('2026-11-17T10:00:00Z');
  const clearedAfter = Date.parse('2026-11-17T09:30:00Z');

  // Pre-clear revert and pre-clear CI failure are ignored; post-clear revert still trips.
  assert.equal(selectCircuitBreakerRegression([
    { pr: 50, issue: 7, kind: 'revert', code: 'post-merge-revert', at: '2026-11-17T09:29:59Z', mergedAt: '2026-11-17T09:00:00Z', detail: 'human revert fixing main' },
    { pr: 51, issue: 8, kind: 'ci', code: 'post-merge-ci', at: '2026-11-17T09:45:00Z', mergedAt: '2026-11-17T09:15:00Z', detail: 'late check on old pre-clear merge' },
  ], { now: fixedNow, clearedAfter }), null);

  const postClear = selectCircuitBreakerRegression([
    { pr: 52, issue: 9, kind: 'ci', code: 'post-merge-ci', at: '2026-11-17T09:50:00Z', mergedAt: '2026-11-17T09:40:00Z', detail: 'new merge broke main' },
  ], { now: fixedNow, clearedAfter });
  assert.equal(postClear?.pr, 52);

  // Full repo + launcher + CLI flow with mode="auto" in pdd.json (NO --mode passed to start!):
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1, report: 'file', label: 'pdd:autopilot' } });
  w.github.mergeMovesBase = true;
  const cwd = w.git(w.cwd, 'rev-parse', '--show-toplevel');
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({
    autopilot: { mode: 'auto', trust: [], engine: 'core', testCommand: 'npm test', label: 'pdd:autopilot', quietMinutes: 40 },
  }));

  const pkgDir = join(w.dir, 'pkg2');
  mkdirSync(pkgDir, { recursive: true });
  writeFileSync(join(pkgDir, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.35' }));
  const stateRoot = join(w.dir, 'launcher-state-2');
  mkdirSync(stateRoot, { recursive: true });
  const stateId = createHash('sha256').update(cwd).digest('hex').slice(0, 20);
  const stateFile = join(stateRoot, `${stateId}.json`);
  const coreFile = join(stateRoot, `${stateId}-core`, 'core.json');
  const homeDir = join(w.dir, 'home2');
  mkdirSync(homeDir, { recursive: true });
  const env = { HOME: homeDir, PATH: process.env.PATH };

  let fakeRegressionQueue = [];
  const launcherPorts = {
    stateRoot,
    now: w.now,
    env,
    timer: async () => true,
    warn: () => {},
    authority: { read: async () => ({ authority: 'trusted' }) },
    selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex' }),
    pathDiagnostic: () => [],
    machineGuard: w.machineGuard,
    run: async (command, args, options = {}) => {
      if (command === 'codex') return { code: 0, stdout: 'Logged in using ChatGPT\n', stderr: '' };
      if (command === 'gh') {
        if (args[0] === 'auth') return { code: 0, stdout: 'ok', stderr: '' };
        if (args[0] === 'repo' && args[1] === 'view') {
          return { code: 0, stdout: JSON.stringify({ nameWithOwner: 'acme/widgets', defaultBranchRef: { name: 'main' } }), stderr: '' };
        }
        return w.gh(args, options);
      }
      const r = spawnSync('git', args, { cwd: options.cwd ?? cwd, encoding: 'utf8' });
      return { code: r.status, stdout: r.stdout, stderr: r.stderr };
    },
    corePorts: {
      jobs: w.jobs,
      checkBase: async () => ({ exitCode: 0, message: 'ok' }),
      agentReady: async () => true,
      checkPostMerge: async () => ({ newlyDetected: fakeRegressionQueue.splice(0) }),
    },
  };

  // 1) Start WITHOUT --mode (relying on pdd.json mode: "auto").
  const started = await runAutopilotLauncher({ command: 'start', cwd, packageRoot: pkgDir, env }, launcherPorts);
  assert.equal(started.exitCode, 0, started.message);
  assert.match(started.message, /Mode auto /);

  // 2) Trip the circuit breaker on a tick -> sets mode='observe' and circuitBreakerForcedObserve=true.
  w.advance(MIN);
  const regressionAt = new Date(w.now()).toISOString();
  fakeRegressionQueue.push({
    pr: 88, issue: 12, kind: 'revert', code: 'post-merge-revert',
    at: regressionAt, mergedAt: new Date(w.now() - 5 * MIN).toISOString(), detail: 'Revert bad change',
  });
  await tickAutopilot(stateFile, launcherPorts);
  const trippedState = JSON.parse(readFileSync(stateFile, 'utf8'));
  assert.equal(trippedState.mode, 'observe');
  assert.equal(trippedState.circuitBreakerForcedObserve, true);
  assert.equal(trippedState.circuitBreaker?.pr, 88);

  // 3) Operator runs `pdd autopilot start` WITHOUT --mode -> clears breaker-forced observe and resumes pdd.json "auto"!
  // Even if the human's earlier revert (dated <= now) is emitted by post-merge scan during start's tick, circuitBreakerClearedAt ignores it!
  w.advance(2 * MIN);
  fakeRegressionQueue.push({
    pr: 88, issue: 12, kind: 'revert', code: 'post-merge-revert',
    at: new Date(w.now() - MIN).toISOString(), mergedAt: new Date(w.now() - 6 * MIN).toISOString(), detail: 'Revert commit seen on rescan',
  });
  const resumedNoModeFlag = await runAutopilotLauncher({ command: 'start', cwd, packageRoot: pkgDir, env }, launcherPorts);
  assert.equal(resumedNoModeFlag.exitCode, 0, resumedNoModeFlag.message);
  assert.match(resumedNoModeFlag.message, /Mode auto /);
  const afterStartNoMode = JSON.parse(readFileSync(stateFile, 'utf8'));
  assert.equal(afterStartNoMode.mode, undefined, 'breaker-forced observe override cleared so pdd.json auto applies');
  assert.equal(afterStartNoMode.circuitBreaker, undefined, 'pre-clear revert did not re-trip breaker');
  assert.equal(typeof afterStartNoMode.circuitBreakerClearedAt, 'number');

  // 4) Trip breaker again, then run `pdd autopilot start --mode observe` -> clears stale tripped banner while keeping explicit observe!
  w.advance(2 * MIN);
  fakeRegressionQueue.push({
    pr: 89, issue: 13, kind: 'ci', code: 'post-merge-ci',
    at: new Date(w.now()).toISOString(), mergedAt: new Date(w.now() - 30_000).toISOString(), detail: 'CI broke',
  });
  await tickAutopilot(stateFile, launcherPorts);
  assert.ok(JSON.parse(readFileSync(stateFile, 'utf8')).circuitBreaker);
  w.advance(MIN);
  const startedObserve = await runAutopilotLauncher({ command: 'start', mode: 'observe', cwd, packageRoot: pkgDir, env }, launcherPorts);
  assert.equal(startedObserve.exitCode, 0, startedObserve.message);
  const statusObserve = await runAutopilotLauncher({ command: 'status', cwd, packageRoot: pkgDir, env }, launcherPorts);
  assert.doesNotMatch(statusObserve.message, /Circuit breaker:/, 'start --mode observe clears stale circuitBreaker banner');
  assert.equal(JSON.parse(readFileSync(stateFile, 'utf8')).mode, 'observe');

  // 5) Trip breaker after returning to auto, then test CLI `pdd autopilot auto` and `pdd autopilot off`!
  await runAutopilotLauncher({ command: 'start', mode: 'auto', cwd, packageRoot: pkgDir, env }, launcherPorts);
  w.advance(2 * MIN);
  fakeRegressionQueue.push({
    pr: 90, issue: 14, kind: 'revert', code: 'post-merge-revert',
    at: new Date(w.now()).toISOString(), mergedAt: new Date(w.now() - 20_000).toISOString(), detail: 'Reverted #90',
  });
  await tickAutopilot(stateFile, launcherPorts);
  assert.equal(JSON.parse(readFileSync(stateFile, 'utf8')).mode, 'observe');
  assert.ok(JSON.parse(readFileSync(coreFile, 'utf8')).circuitBreaker);

  const capture = () => { const out = { text: '' }; out.write = s => { out.text += s; }; return out; };
  w.advance(MIN);
  const outAuto = capture(), errAuto = capture();
  const autoExit = await runPdd(['autopilot', 'auto'], {
    cwd, packageRoot: pkgDir, env, stdout: outAuto, stderr: errAuto,
    syncOwnedUserSkills: () => ({ updated: [] }),
    autopilotLauncherPorts: launcherPorts,
    autopilotGithub: { publishAutopilotSettings: async () => '' },
  });
  assert.equal(autoExit, 0, errAuto.text);
  const afterCliAuto = JSON.parse(readFileSync(stateFile, 'utf8'));
  assert.equal(afterCliAuto.circuitBreaker, undefined, 'pdd autopilot auto clears saved circuitBreaker');
  assert.equal(afterCliAuto.mode, undefined, 'pdd autopilot auto clears machine observe override');
  assert.equal(JSON.parse(readFileSync(coreFile, 'utf8')).circuitBreaker, undefined);
  assert.equal(typeof JSON.parse(readFileSync(coreFile, 'utf8')).circuitBreakerClearedAt, 'number');

  // Trip once more and run `pdd autopilot off` -> clears machine observe override so off takes effect!
  w.advance(2 * MIN);
  fakeRegressionQueue.push({
    pr: 91, issue: 15, kind: 'ci', code: 'post-merge-ci',
    at: new Date(w.now()).toISOString(), mergedAt: new Date(w.now() - 10_000).toISOString(), detail: 'CI red',
  });
  await tickAutopilot(stateFile, launcherPorts);
  assert.equal(JSON.parse(readFileSync(stateFile, 'utf8')).mode, 'observe');

  w.advance(MIN);
  const outOff = capture(), errOff = capture();
  const offExit = await runPdd(['autopilot', 'off'], {
    cwd, packageRoot: pkgDir, env, stdout: outOff, stderr: errOff,
    syncOwnedUserSkills: () => ({ updated: [] }),
    autopilotLauncherPorts: launcherPorts,
    autopilotGithub: { publishAutopilotSettings: async () => '' },
  });
  assert.equal(offExit, 0, errOff.text);
  const afterCliOff = JSON.parse(readFileSync(stateFile, 'utf8'));
  assert.equal(afterCliOff.circuitBreaker, undefined, 'pdd autopilot off clears saved circuitBreaker');
  assert.equal(afterCliOff.mode, undefined, 'pdd autopilot off clears machine observe override so pdd.json off applies');
  const tickWhenOff = await tickAutopilot(stateFile, launcherPorts);
  assert.match(tickWhenOff.message, /Autopilot is off./);
});

test('3484: multi-runId shard-flake rerun falls back per failed shard to check-runs rerequest and tracks only actually-reran shards in staleTokens', async t => {
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1, repairs: 2 } });

  const origGh = w.github.gh;
  const readJobFile = n => JSON.parse(readFileSync(join(w.root, 'jobs', `${n}.json`), 'utf8'));

  // Sub-case A: runId 501 succeeds via gh run rerun; runId 502 fails rerun AND rerun-failed-jobs, then succeeds via check-runs/9002/rerequest!
  w.issue(41, { title: 'Multi-workflow shard flake A' });
  await w.tick();
  const builtA = w.build(41, { body: 'Fixes #41\n\nRuntime: not run (no prompt)', result: { promptChanged: false }, checks: null });
  const prA = builtA.pr, headA = builtA.head;
  w.github.checks.set(headA, [
    { id: 9001, name: 'unit-shard (1/4)', status: 'completed', conclusion: 'failure', run_id: 501, completed_at: '2026-11-17T08:10:00Z' },
    { id: 9002, name: 'e2e-shard (1/4)', status: 'completed', conclusion: 'failure', run_id: 502, completed_at: '2026-11-17T08:10:01Z' },
    { id: 9003, name: 'unit-shard (2/4)', status: 'completed', conclusion: 'success', run_id: 501 },
    { id: 9004, name: 'unit-shard (3/4)', status: 'completed', conclusion: 'success', run_id: 501 },
    { id: 9005, name: 'unit-shard (4/4)', status: 'completed', conclusion: 'success', run_id: 501 },
    { id: 9006, name: 'e2e-shard (2/4)', status: 'completed', conclusion: 'success', run_id: 502 },
    { id: 9007, name: 'e2e-shard (3/4)', status: 'completed', conclusion: 'success', run_id: 502 },
    { id: 9008, name: 'e2e-shard (4/4)', status: 'completed', conclusion: 'success', run_id: 502 },
  ]);

  const callsA = [];
  w.github.gh = async (args, options = {}) => {
    if (args[0] === 'run' && args[1] === 'rerun') {
      callsA.push(`cli:${args[2]}`);
      return args[2] === '501' ? { code: 0, stdout: '', stderr: '' } : { code: 1, stdout: '', stderr: 'cannot rerun 502' };
    }
    if (args[0] === 'api' && args.includes('POST')) {
      const endpoint = args.find(a => a.startsWith('repos/')) ?? '';
      if (endpoint.endsWith('/actions/runs/502/rerun-failed-jobs')) {
        callsA.push(`rest:${endpoint}`);
        return { code: 1, stdout: 'HTTP/2 403\r\n\r\n{"message":"forbidden"}', stderr: '' };
      }
      if (endpoint.endsWith('/check-runs/9002/rerequest')) {
        callsA.push(`rest:${endpoint}`);
        return { code: 0, stdout: 'HTTP/2 201\r\n\r\n{}', stderr: '' };
      }
    }
    return origGh(args, options);
  };

  await w.tick();
  assert.deepEqual(callsA, [
    'cli:501',
    'cli:502',
    'rest:repos/acme/widgets/actions/runs/502/rerun-failed-jobs',
    'rest:repos/acme/widgets/check-runs/9002/rerequest',
  ]);
  const job41 = readJobFile(41);
  assert.equal(w.started.filter(j => j.issue === 41 && j.role === 'repair').length, 0, 'both failed shards reran -> waits instead of starting repair');
  assert.equal(job41.ciRerunPending?.staleTokens?.length, 2);

  // Release #41 slot by marking both green, reviewing, and merging.
  w.github.gh = origGh;
  w.github.checks.set(headA, w.github.checks.get(headA).map(c => ({ ...c, conclusion: 'success' })));
  await w.tick();
  w.review(41, 'PASS');
  w.suite(41, 0);
  await w.tick();
  assert.deepEqual(w.github.merges, [prA.number]);

  // Sub-case B: runId 601 succeeds, while runId 602 fails BOTH workflow rerun AND check-runs/9102/rerequest!
  // Only shard 9101 is recorded in staleTokens, and un-reran shard 9102 proceeds immediately to repair!
  w.issue(42, { title: 'Multi-workflow shard flake B' });
  await w.tick();
  const builtB = w.build(42, { body: 'Fixes #42\n\nRuntime: not run (no prompt)', result: { promptChanged: false }, checks: null });
  const headB = builtB.head;
  w.github.checks.set(headB, [
    { id: 9101, name: 'unit-shard (1/4)', status: 'completed', conclusion: 'failure', run_id: 601, completed_at: '2026-11-17T08:20:00Z' },
    { id: 9102, name: 'e2e-shard (1/4)', status: 'completed', conclusion: 'failure', run_id: 602, completed_at: '2026-11-17T08:20:01Z' },
    { id: 9103, name: 'unit-shard (2/4)', status: 'completed', conclusion: 'success', run_id: 601 },
    { id: 9104, name: 'unit-shard (3/4)', status: 'completed', conclusion: 'success', run_id: 601 },
    { id: 9105, name: 'unit-shard (4/4)', status: 'completed', conclusion: 'success', run_id: 601 },
    { id: 9106, name: 'e2e-shard (2/4)', status: 'completed', conclusion: 'success', run_id: 602 },
    { id: 9107, name: 'e2e-shard (3/4)', status: 'completed', conclusion: 'success', run_id: 602 },
    { id: 9108, name: 'e2e-shard (4/4)', status: 'completed', conclusion: 'success', run_id: 602 },
  ]);

  w.github.gh = async (args, options = {}) => {
    if (args[0] === 'run' && args[1] === 'rerun') {
      return args[2] === '601' ? { code: 0, stdout: '', stderr: '' } : { code: 1, stdout: '', stderr: 'no' };
    }
    if (args[0] === 'api' && args.includes('POST')) {
      const endpoint = args.find(a => a.startsWith('repos/')) ?? '';
      if (endpoint.endsWith('/actions/runs/602/rerun-failed-jobs') || endpoint.endsWith('/check-runs/9102/rerequest')) {
        return { code: 1, stdout: 'HTTP/2 500\r\n\r\n{"message":"boom"}', stderr: '' };
      }
    }
    return origGh(args, options);
  };

  await w.tick();
  const job42 = readJobFile(42);
  assert.equal(job42.flakeRerunHead, headB);
  assert.deepEqual(
    job42.ciRerunPending?.staleTokens,
    ['r:9101:unit-shard (1/4):failure:2026-11-17T08:20:00Z'],
    'ONLY actually-reran shard 9101 is included in staleTokens (never un-reran 9102)',
  );
  assert.equal(w.started.filter(j => j.issue === 42 && j.role === 'repair').length, 1, 'un-reran shard 9102 proceeds immediately to repair instead of stalling');
});

test('3484: productStatus and productStart never reopen closed slices with merged PRs or planned Story files on cold local test caches', async t => {
  const cwd = mkdtempSync(join(tmpdir(), 'pdd-product-cold-cache-3484-'));
  t.after(() => rmSync(cwd, { recursive: true, force: true }));
  mkdirSync(join(cwd, 'product'), { recursive: true });
  mkdirSync(join(cwd, 'user_stories', 'single'), { recursive: true });

  writeFileSync(join(cwd, 'product', 'map.md'), `# Demo: map
Sentence: "Demo slices"
Size: medium (4 CORE Stories, 3 parts)

## Parts
| Part | Folder | What it is |
| --- | --- | --- |
| unbuilt | prompts/unbuilt | Unbuilt slice |
| single | prompts/single | Autopilot single-PR slice with cold cache |
| prmerged | prompts/prmerged | Closed slice with merged non-code PR |

## Stories
| Id | Part | Story | Tag |
| --- | --- | --- | --- |
| U01 | unbuilt | As an operator, I want U01, so that unbuilt works. | CORE |
| S01 | single | As an operator, I want S01, so that single works. | CORE |
| S02 | single | As an operator, I want S02, so that single syncs. | CORE |
| M01 | prmerged | As an operator, I want M01, so that merged PR displays. | CORE |

## Journeys
| Id | Journey | Stories |
| --- | --- | --- |

## Questions
| Id | Question | Recommendation | Example | Answer |
| --- | --- | --- | --- | --- |
`);

  writeFileSync(join(cwd, 'product', 'plan.md'), `# Demo: plan

## Boundaries
| From | To | What crosses | Contract |
| --- | --- | --- | --- |
| unbuilt | single | events | contracts/unbuilt-single.md |

## Runs
| Run | Part | Slice | Stories | Needs |
| --- | --- | --- | --- | --- |
| unbuilt-1 | unbuilt | 1 | U01 | - |
| single-1 | single | 1 | S01, S02 | - |
| prmerged-1 | prmerged | 1 | M01 | - |
`);

  // Planned Story files for single-1 already exist on cwd (merged via Autopilot single-PR flow),
  // while local savedStoryEvidence cache is cold (0 of 2 pass, notRun === 2)!
  writeFileSync(join(cwd, 'user_stories', 'single', 'S01-login.md'), '# S01\n');
  writeFileSync(join(cwd, 'user_stories', 'single', 'S02-sync.md'), '# S02\n');

  const reopened = [];
  const starts = [];
  const state = {
    productState: null,
    issues: [
      { number: 11, state: 'CLOSED', author_association: 'OWNER', user: { login: 'owner' }, created_at: '2026-11-17T01:00:00Z', body: '<!-- pdd-product: run=unbuilt-1 -->' },
      { number: 12, state: 'CLOSED', author_association: 'OWNER', user: { login: 'owner' }, created_at: '2026-11-17T01:01:00Z', body: '<!-- pdd-product: run=single-1 -->' },
      { number: 13, state: 'CLOSED', author_association: 'OWNER', user: { login: 'owner' }, created_at: '2026-11-17T01:02:00Z', body: '<!-- pdd-product: run=prmerged-1 -->' },
    ],
    events: {
      11: [],
      12: [],
      13: [{ event: 'cross-referenced', source: { issue: { pull_request: { html_url: 'https://github.com/acme/demo/pull/77' } } } }],
    },
    prs: [
      {
        number: 77,
        url: 'https://github.com/acme/demo/pull/77',
        state: 'MERGED',
        isDraft: false,
        isCrossRepository: false,
        headRefName: 'feat/prmerged-1',
        updatedAt: '2026-11-17T02:00:00Z',
        body: '<!-- pdd-product: run=prmerged-1 -->\nMerged without :code workflow marker.',
      },
    ],
  };

  const ports = {
    env: { HOME: process.env.HOME, PATH: process.env.PATH },
    lockProductState: async () => ({ handle: 'lock-demo' }),
    unlockProductState: async () => ({}),
    readProductState: async () => ({ json: state.productState }),
    writeProductState: async ({ json }) => { state.productState = json; return {}; },
    now: async () => ({ milliseconds: 2000 }),
    listRuns: async () => [],
    resolveRepository: async () => ({ repository: 'acme/demo', defaultBranch: 'main' }),
    planOnBase: async () => true,
    savedStoryEvidence: async () => ({ stories: [], warnings: [] }), // Cold local cache: notRun === total!
    issuePage: async ({ page }) => ({ items: page === 1 ? state.issues : [], total_count: state.issues.length, incomplete_results: false }),
    issueByNumber: async ({ number }) => state.issues.find(i => i.number === number) ?? { status: 404, message: 'Not Found' },
    timelinePage: async ({ issue }) => state.events[issue] ?? [],
    pullRequest: async ({ number }) => state.prs.find(p => p.number === number),
    currentActor: async () => ({ login: 'owner' }),
    openBaseSource: async () => ({ root: cwd, handle: null }),
    closeBaseSource: async () => ({}),
    reopenIssue: async ({ number }) => { reopened.push(number); return {}; },
    startRun: async args => { starts.push(args); return { exitCode: 0, message: `Started #${args.issue}.` }; },
  };

  const status = await productStatus({ cwd }, ports);
  assert.deepEqual(
    status.runs.map(r => [r.run, r.state, r.issue]),
    [
      ['unbuilt-1', 'issue closed (0 of 1 pass)', 11],
      ['single-1', 'issue ready', 12],
      ['prmerged-1', 'PR #77 (merged)', 13],
    ],
  );
  assert.deepEqual(status.ready, ['unbuilt-1'], 'ONLY unbuilt-1 (0 Story files, 0 merged PRs) is ready/closedUnbuilt');
  const next = await productNext({ cwd }, ports);
  assert.deepEqual(next.ready, ['unbuilt-1']);

  // Starting single-1 (cold cache, Story files exist) must NOT reopen #12!
  await productStart({ cwd, run: 'single-1', noRun: true }, ports);
  assert.deepEqual(reopened, [], 'closed slice with existing Story files is NOT reopened');

  // Starting prmerged-1 (MERGED PR in detail.prs without :code marker) must NOT reopen #13!
  await productStart({ cwd, run: 'prmerged-1', noRun: true }, ports);
  assert.deepEqual(reopened, [], 'closed slice with MERGED PR is NOT reopened');

  // Starting unbuilt-1 (0 Story files, 0 merged PRs) DOES reopen #11!
  await productStart({ cwd, run: 'unbuilt-1', noRun: true }, ports);
  assert.deepEqual(reopened, [11]);

  // Terminal local workflow records (cancelled or failed) must NOT shadow closedUnbuilt or block recovery!
  for (const terminalState of ['cancelled', 'failed']) {
    const termPorts = {
      ...ports,
      listRuns: async () => [{ id: `r-${terminalState}`, workflow: 'feature', issue: 11, run: 'unbuilt-1', state: terminalState, baseBranch: 'main' }],
    };
    const termStatus = await productStatus({ cwd }, termPorts);
    assert.deepEqual(
      termStatus.runs.find(r => r.run === 'unbuilt-1'),
      { run: 'unbuilt-1', issue: 11, state: 'issue closed (0 of 1 pass)', prs: [], fromPr: null },
      `terminal local state ${terminalState} still surfaces issue closed (0 of 1 pass)`,
    );
    assert.deepEqual(termStatus.ready, ['unbuilt-1']);
  }

  // Story files committed only on git baseBranch (main) when absent from cwd working tree still prevent false reopen via git ls-tree!
  const { execFileSync } = await import('node:child_process');
  execFileSync('git', ['init', '-q', '-b', 'main'], { cwd });
  execFileSync('git', ['config', 'user.name', 'Test'], { cwd });
  execFileSync('git', ['config', 'user.email', 'test@example.com'], { cwd });
  execFileSync('git', ['add', '.'], { cwd });
  execFileSync('git', ['commit', '-qm', 'base stories on main'], { cwd });
  execFileSync('git', ['checkout', '-qb', 'clean-wt'], { cwd });
  rmSync(join(cwd, 'user_stories'), { recursive: true, force: true });
  reopened.length = 0;
  const gitBranchStatus = await productStatus({ cwd }, ports);
  assert.equal(gitBranchStatus.runs.find(r => r.run === 'single-1')?.state, 'issue ready', 'git ls-tree on main detects planned Story files even when absent from cwd');
  await productStart({ cwd, run: 'single-1', noRun: true }, ports);
  assert.deepEqual(reopened, [], 'closed slice with Story files on main branch is NOT reopened');
});
