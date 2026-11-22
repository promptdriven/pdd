import test from 'node:test';
import assert from 'node:assert/strict';
import dns from 'node:dns';
import http from 'node:http';
import net from 'node:net';
import tls from 'node:tls';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import {
  MAX_CAPTURED_PROCESSES,
  SNAPSHOT_INTERVAL_MS,
  cleanupAgentJob,
  snapshotAgentJob,
} from '../src/agent-job.mjs';
import { boundSuiteCommand, runtimeVerdicts } from '../src/autopilot-core.mjs';
import {
  isCreditOrResetAccount,
  selectCloudPoolLogin,
  writeCloudAccountsState,
} from '../src/login-pool.mjs';
import { loadLoginPool, selectPoolLogin } from '../src/autopilot/local-pool.mjs';
import { runStepAgentProcess } from '../src/agent-adapters.mjs';
import { runAutopilotLauncher } from '../src/autopilot-launcher.mjs';
import {
  NET_BLOCKED_CODE,
  installOfflineNetGuard,
  isAllowedOfflineHost,
} from './helpers/test-net-guard.mjs';
import { coreWorld } from './helpers/core-world.mjs';

function makeTempDir(t, prefix = 'pdd-hardening-') {
  const dir = mkdtempSync(join(tmpdir(), prefix));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  return dir;
}

function writeIn(cwd, path, text) {
  mkdirSync(join(cwd, path, '..'), { recursive: true });
  writeFileSync(join(cwd, path), text);
}

test('Fix 1a: runtimeVerdicts ignores prose starting with "Runtime ..." without a colon while matching real Runtime: lines', () => {
  const body = [
    '## Runtime Safety & Engine Hardening',
    'Runtime errors are caught cleanly before socket teardown.',
    '- **Runtime** checks stay isolated per worktree.',
    'In prose we explain why Runtime: FAIL blocks a merge.',
    '- **Runtime:** ✅ PASS (user_stories/alpha_flow.md, 4/4 checks)',
    'Runtime: not run (user_stories/beta_flow.md: real-binding-unavailable)',
  ].join('\n');

  const verdicts = runtimeVerdicts(body);
  assert.equal(verdicts.length, 2);
  assert.deepEqual(
    verdicts.map(v => ({ story: v.story, verdict: v.verdict })),
    [
      { story: 'user_stories/alpha_flow.md', verdict: 'pass' },
      { story: 'user_stories/beta_flow.md', verdict: 'not-run' },
    ],
  );

  // Table rows and semicolon status clauses still parse fail-closed.
  assert.equal(runtimeVerdicts('| Runtime | FAIL |')[0]?.verdict, 'other');
  assert.equal(runtimeVerdicts('Tests: pass; Runtime: FAIL')[0]?.verdict, 'other');
});

test('Fix 1b: mergeCheck mechanically formats verified Runtime: lines from savedRuntime when omitted or unnamed on multi-Story PRs', async t => {
  const storyA = 'user_stories/order-create.md';
  const storyB = 'user_stories/order-cancel.md';
  const prompt = 'prompts/orders.prompt.md';

  // 1. Worker writes "Runtime ..." prose and omits Runtime: lines completely after passing saved checks -> mechanically synced and merged with 0 repairs!
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.baseCommit(prompt, '# Orders\n\nManage orders.\n');
  w.baseCommit(storyA, '# Create order\n\nCreate an order.\n');
  w.baseCommit(storyB, '# Cancel order\n\nCancel an order.\n');
  w.issue(17);
  await w.tick();

  const cwd = w.job(17, 'build').cwd;
  writeIn(cwd, prompt, '# Orders\n\nManage orders safely.\n');
  writeIn(cwd, storyA, '# Create order\n\nCreate an order safely.\n');
  writeIn(cwd, storyB, '# Cancel order\n\nCancel an order safely.\n');

  w.runtimeEvidence = async () => ({
    stories: [
      { story: storyA, pass: true, current: true, at: 1000, checks: { passed: 3, total: 3 } },
      { story: storyB, pass: true, current: true, at: 1001, checks: { passed: 2, total: 2 } },
    ],
    storyFiles: [storyA, storyB],
    tests: [],
    footprints: { [storyA]: [prompt], [storyB]: [prompt] },
  });

  const prBody = [
    'Fixes #17',
    '',
    'Runtime errors are caught cleanly during order validation.',
    'Evidence: runtime=not-run; vectors=not-run; formal=not-applicable; tests=pass (5/5)',
    `Path: a — ${prompt} — ${prompt} — prompt changed — Test: done check`,
    `Path: d — ${storyA}, ${storyB}, change-17.txt — unowned — no contract change — Test: done check`,
  ].join('\n');

  const { pr } = w.build(17, { body: prBody });
  await w.tick();
  assert.equal(w.job(17, 'repair'), undefined, 'verified saved checks prevent paperwork repair rounds');
  w.review(17, 'PASS');
  w.suite(17, 0);
  await w.tick();
  assert.deepEqual(w.github.merges, [pr.number]);

  const syncedLines = runtimeVerdicts(pr.body);
  assert.deepEqual(
    syncedLines.map(row => ({ story: row.story, verdict: row.verdict })).sort((a, b) => a.story.localeCompare(b.story)),
    [
      { story: storyB, verdict: 'pass' },
      { story: storyA, verdict: 'pass' },
    ],
  );
  const evidenceIdx = pr.body.indexOf('<!-- pdd:autopilot-core:evidence:start -->');
  if (evidenceIdx >= 0) {
    assert.ok(pr.body.indexOf(`Runtime: PASS (${storyA}`) < evidenceIdx, 'Runtime lines stay above the Autopilot evidence block');
  }

  // 2. Missing/failing saved checks STILL fail closed (never invent a pass).
  const wMissing = await coreWorld(t, { settings: { runs: 1 } });
  wMissing.baseCommit(storyA, '# Create order\n\nCreate an order.\n');
  wMissing.issue(18);
  await wMissing.tick();
  writeIn(wMissing.job(18, 'build').cwd, storyA, '# Create order\n\nChanged without running pdd test.\n');
  wMissing.runtimeEvidence = async () => ({
    stories: [],
    storyFiles: [storyA],
    tests: [],
    footprints: {},
  });
  wMissing.build(18, {
    body: `Fixes #18\n\nPath: d — ${storyA}, change-18.txt — unowned — no contract change — Test: done check`,
  });
  await wMissing.tick();
  assert.ok(wMissing.job(18, 'repair'), 'unverified changes without saved checks still go to repair');
  assert.equal(wMissing.github.merges.length, 0);
});

test('Fix 2: real-binding-unavailable saved rows fail closed to Bucket 2 auth-wait with 0 repair rounds, cooldown, and freed slot', async t => {
  const story = 'user_stories/cloud-webhook.md';
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.baseCommit(story, '# Webhook\n\nDeliver webhook.\n');
  w.issue(17);
  await w.tick();
  writeIn(w.job(17, 'build').cwd, story, '# Webhook\n\nDeliver signed webhook.\n');

  // real-binding-unavailable is NEVER silently skipped or merged: it routes to Bucket 2 (park-auth-wait)
  // with 0 repair rounds, keeps the PR open, frees the worker slot, and records runtime-binding cooldown.
  w.runtimeEvidence = async ({ base }) => base
    ? { stories: [{ story, pass: true, current: true, at: 500 }], storyFiles: [story], tests: [] }
    : {
        stories: [{
          story,
          pass: false,
          current: true,
          sent: false,
          at: 1000,
          reason: { code: 'real-binding-unavailable' },
          codes: ['real-binding-unavailable'],
          refusals: ['real-binding-unavailable'],
          states: ['refused'],
          client_advice: 'Reconcile possible external effects with the operator before retrying.',
          advice: ['Reconcile possible external effects with the operator before retrying.'],
        }],
        storyFiles: [story],
        tests: [],
        footprints: { [story]: [] },
      };

  const { pr } = w.build(17, {
    body: `Fixes #17\n\nPath: d — ${story}, change-17.txt — unowned — no contract change — Test: done check`,
    runtime: { state: 'not-run' },
  });
  await w.tick();
  assert.equal(w.job(17, 'repair'), undefined, 'real-binding-unavailable spends 0 repair rounds');
  assert.equal(pr.state, 'open', 'finished PR stays open while parked');
  assert.equal(pr.merged, false, 'real-binding-unavailable never merges');
  assert.ok(w.labels(17).includes('pdd:needs-decision'), 'parks as needs-person wait');
  assert.ok(!w.labels(17).includes('pdd:working'), 'worker slot freed immediately');
  assert.ok(pr.comments.some(c => /<!-- pdd:autopilot-core:auth-wait:/.test(c.body)), 'PR carries auth-wait marker');
  const machine = JSON.parse(readFileSync(join(w.root, 'core.json'), 'utf8'));
  assert.equal(machine.toolCooldowns?.['runtime-binding']?.active, true, 'runtime-binding placed on cooldown');
  assert.equal(machine.validationParks?.some(p => p.pr === pr.number && p.issue === 17), true, 'PR recorded for validate-only resume');
});

test('Fix 3a: snapshot interval is 2000 ms and captured process manifests deduplicate and bound to 512 entries', t => {
  assert.equal(SNAPSHOT_INTERVAL_MS, 2000);
  assert.equal(MAX_CAPTURED_PROCESSES, 512);

  const dir = makeTempDir(t, 'pdd-proc-cap-');
  const token = join(dir, 'cap.spec.json');
  const wrapperPid = 41000;
  const root = { pid: wrapperPid, ppid: 1, pgid: wrapperPid, rss: 10, start: '@wrap-0', args: `node --wrapper ${token}` };
  const activeGroupLeader = { pid: 41001, ppid: wrapperPid, pgid: 41001, rss: 10, start: '@leader-1', args: 'node child-leader' };

  const historical = Array.from({ length: 700 }, (_, i) => ({
    pid: 50000 + i,
    ppid: wrapperPid,
    pgid: wrapperPid,
    rss: 4,
    start: `@hist-${i}`,
    args: `git status --short ${i}`,
  }));
  writeFileSync(`${token}.processes.json`, JSON.stringify([root, activeGroupLeader, ...historical]));

  const liveChild = { pid: 61000, ppid: wrapperPid, pgid: wrapperPid, rss: 8, start: '@live-now', args: 'node focused-test' };
  const job = { pid: wrapperPid, token, processes: { seen: [root, activeGroupLeader, ...historical] } };

  // Poll twice with identical live rows: duplicates must not grow the manifest, and total stays <= 512.
  const first = snapshotAgentJob(job, { list: () => [root, activeGroupLeader, liveChild] });
  const second = snapshotAgentJob(job, { list: () => [root, activeGroupLeader, liveChild] });
  assert.equal(first.length, MAX_CAPTURED_PROCESSES);
  assert.equal(second.length, MAX_CAPTURED_PROCESSES);
  assert.equal(job.processes.seen.length, MAX_CAPTURED_PROCESSES);
  assert.ok(second.some(r => r.pid === wrapperPid), 'wrapper root stays pinned');
  assert.ok(second.some(r => r.pid === activeGroupLeader.pid), 'active child group leader stays pinned');
  assert.ok(second.some(r => r.pid === liveChild.pid), 'currently live descendant stays pinned');
  assert.ok(second.some(r => r.pid === 50699), 'most recent exited processes are kept up to the cap');
  assert.equal(second.some(r => r.pid === 50000), false, 'oldest exited processes beyond 512 are evicted');
});

test('Fix 3b: cleanupAgentJob recovers stopped/timed-out jobs with latched .processes.error, escalates SIGTERM->SIGKILL, wipes cleanupDirs, and clears progress.running', async t => {
  const dir = makeTempDir(t, 'pdd-wedged-slot-');
  const overlay = mkdtempSync(join(dir, 'pdd-cx-'));
  const token = join(dir, 'wedged.spec.json');
  const exitFile = join(dir, 'wedged.exit.json');
  const wrapperPid = 72000;
  writeFileSync(token, JSON.stringify({
    command: 'codex',
    args: ['exec'],
    cwd: dir,
    input: join(dir, 'wedged.input'),
    log: join(dir, 'wedged.log'),
    exit: exitFile,
    cleanupDirs: [overlay],
  }));

  // Simulate a wedged stopped job: .processes.error was written earlier and job.processesUncertain = true,
  // while a stubborn child in -wrapperPid ignores SIGTERM and only dies on SIGKILL.
  const wrapperRow = { pid: wrapperPid, ppid: 1, pgid: wrapperPid, rss: 10, start: '@wedged-wrap', args: `node --wrapper ${token}` };
  const stubbornChild = { pid: 72005, ppid: 1, pgid: wrapperPid, rss: 12, start: '@stubborn-child', args: 'node hung-worker' };
  writeFileSync(`${token}.processes.json`, JSON.stringify([wrapperRow]));
  writeFileSync(`${token}.processes.error`, 'inventory unavailable\n', { mode: 0o600 });

  let wrapperAlive = true;
  let liveRows = [wrapperRow, stubbornChild];
  const signals = [];

  const job = {
    pid: wrapperPid,
    token,
    exit: exitFile,
    cleanupDirs: [overlay],
    processesUncertain: true,
    watch: { stopped: 'quiet' },
    progress: { sig: 'cleanup', at: 100, running: true },
  };

  const proof = await cleanupAgentJob(job, {
    recoverStopped: true,
    alive: () => wrapperAlive,
    list: () => liveRows,
    kill: (targetPid, sig) => {
      signals.push([targetPid, sig]);
      if ((targetPid === -wrapperPid || targetPid === wrapperPid) && sig === 'SIGTERM') {
        wrapperAlive = false;
        liveRows = [stubbornChild]; // wrapper exits on SIGTERM, stubborn child ignores SIGTERM
      }
      if ((targetPid === stubbornChild.pid || targetPid === -wrapperPid) && sig === 'SIGKILL') {
        liveRows = []; // stubborn child dies on SIGKILL
      }
    },
    sleep: async () => {},
    grace: 5,
    poll: 1,
  });

  assert.equal(proof.confirmed, true, 'stopped job recovers cleanly instead of returning confirmed: false forever');
  assert.equal(job.progress.running, false, 'progress.running is cleared once process group is dead');
  assert.equal(job.processesUncertain, undefined);
  assert.equal(existsSync(`${token}.processes.error`), false, 'stale .processes.error latch is cleared');
  assert.equal(existsSync(overlay), false, 'disposable pdd-cx-* overlay is wiped');
  assert.ok(signals.some(([pid, sig]) => (pid === stubbornChild.pid || pid === -wrapperPid) && sig === 'SIGKILL'), 'escalates to SIGKILL when stubborn process survives SIGTERM');
});

test('Fix 3c: boundSuiteCommand caps full-suite Node test concurrency to Math.max(1, Math.min(6, shareCpus))', async t => {
  const pkg = {
    scripts: {
      test: 'node --import ./test/helpers/test-home.mjs --test test/*.test.mjs',
    },
  };

  assert.equal(
    boundSuiteCommand('npm test', pkg, 2),
    'node --import ./test/helpers/test-home.mjs --test --test-concurrency=2 test/*.test.mjs',
  );
  assert.equal(
    boundSuiteCommand('npm test', pkg, 16),
    'node --import ./test/helpers/test-home.mjs --test --test-concurrency=6 test/*.test.mjs',
  );
  assert.equal(
    boundSuiteCommand('node --test test/foo.test.mjs', {}, 4),
    'node --test --test-concurrency=4 test/foo.test.mjs',
  );
  assert.equal(
    boundSuiteCommand('node --test --test-concurrency=1 test/*.test.mjs', {}, 6),
    'node --test --test-concurrency=1 test/*.test.mjs',
    'preserves an explicit --test-concurrency flag',
  );

  // Verify end-to-end queuedCommand wiring in Autopilot core when machine shareCpus is configured.
  const w = await coreWorld(t, { settings: { runs: 1 } });
  writeFileSync(join(w.cwd, 'package.json'), JSON.stringify({ name: 'demo', scripts: pkg.scripts }));
  w.git(w.cwd, 'add', 'package.json');
  w.git(w.cwd, 'commit', '-m', 'add node --test script');
  w.git(w.cwd, 'push', 'origin', 'main');

  w.issue(17);
  await w.tick({ machine: { priority: () => ({ checkCpus: 3 }) } });
  w.build(17, { result: { promptChanged: false } });
  await w.tick({ machine: { priority: () => ({ checkCpus: 3 }) } });
  const suiteJob = w.job(17, 'suite');
  const cmdIdx = suiteJob.args.indexOf('--command');
  assert.ok(cmdIdx >= 0);
  assert.match(suiteJob.args[cmdIdx + 1], /--test-concurrency=3\b/);
});

test('Fix 4a: offline test-net-guard allows loopback & Unix sockets while blocking external IP/DNS/fetch with ERR_PDD_OFFLINE_TEST_NET_BLOCKED', async t => {
  installOfflineNetGuard();

  assert.equal(isAllowedOfflineHost('127.0.0.1'), true);
  assert.equal(isAllowedOfflineHost('::1'), true);
  assert.equal(isAllowedOfflineHost('[::1]'), true);
  assert.equal(isAllowedOfflineHost('localhost'), true);
  assert.equal(isAllowedOfflineHost('0.0.0.0'), true);
  assert.equal(isAllowedOfflineHost('example.com'), false);
  assert.equal(isAllowedOfflineHost('93.184.216.34'), false);

  const prevAllow = process.env.PDD_ALLOW_NET;
  const prevCanary = process.env.PDD_LIVE_CANARY;
  delete process.env.PDD_ALLOW_NET;
  delete process.env.PDD_LIVE_CANARY;
  t.after(() => {
    if (prevAllow === undefined) delete process.env.PDD_ALLOW_NET; else process.env.PDD_ALLOW_NET = prevAllow;
    if (prevCanary === undefined) delete process.env.PDD_LIVE_CANARY; else process.env.PDD_LIVE_CANARY = prevCanary;
  });

  // 1. Loopback 127.0.0.1 HTTP server works.
  const httpServer = http.createServer((_req, res) => { res.writeHead(200); res.end('ok'); });
  await new Promise(resolve => httpServer.listen(0, '127.0.0.1', resolve));
  t.after(() => httpServer.close());
  const { port } = httpServer.address();
  const res = await fetch(`http://127.0.0.1:${port}/ping`);
  assert.equal(await res.text(), 'ok');

  // 2. Unix domain socket works.
  const sockDir = makeTempDir(t, 'pdd-sock-');
  const sockPath = join(sockDir, 'ipc.sock');
  const unixServer = net.createServer(conn => conn.end('unix-ok'));
  await new Promise(resolve => unixServer.listen(sockPath, resolve));
  t.after(() => unixServer.close());
  const unixText = await new Promise((resolve, reject) => {
    const client = net.connect(sockPath);
    let data = '';
    client.setEncoding('utf8');
    client.on('data', chunk => { data += chunk; });
    client.on('end', () => resolve(data));
    client.on('error', reject);
  });
  assert.equal(unixText, 'unix-ok');

  // 3. External fetch, net.connect, tls.connect, and dns.promises.lookup fail fast with ERR_PDD_OFFLINE_TEST_NET_BLOCKED.
  await assert.rejects(() => fetch('https://example.com/v1/test'), { code: NET_BLOCKED_CODE });
  await assert.rejects(() => dns.promises.lookup('example.com'), { code: NET_BLOCKED_CODE });
  await assert.rejects(
    () => new Promise((resolve, reject) => {
      const sock = net.connect({ host: '93.184.216.34', port: 80 }, resolve);
      sock.on('error', reject);
    }),
    { code: NET_BLOCKED_CODE },
  );
  await assert.rejects(
    () => new Promise((resolve, reject) => {
      const sock = tls.connect({ host: '93.184.216.34', port: 443 }, resolve);
      sock.on('error', reject);
    }),
    { code: NET_BLOCKED_CODE },
  );
});

test('Fix 4b: Cloud and local login selection skip credits/allowReset/allow_reset accounts for automated steps unless allowCredits is explicitly requested', async t => {
  assert.equal(isCreditOrResetAccount({ credits: true }), true);
  assert.equal(isCreditOrResetAccount({ allowReset: true }), true);
  assert.equal(isCreditOrResetAccount({ allow_reset: true }), true);
  assert.equal(isCreditOrResetAccount({ credits: false, allowReset: false }), false);

  const dir = makeTempDir(t, 'pdd-cloud-credit-guard-');
  const env = { HOME: dir, PDD_STATE_DIR: join(dir, 'state'), PDD_TOKEN: 'pdd_test_token_123' };
  writeCloudAccountsState({ enrolled: true, providers: ['codex'], active: {}, cooling: {} }, { env });

  const cloudAccounts = [
    { account_id: 'acc-credit', label: 'credit-acct', provider: 'codex', credits: true, five_hour_used_percent: 10, weekly_used_percent: 20 },
    { account_id: 'acc-reset', label: 'reset-acct', provider: 'codex', allow_reset: true, five_hour_used_percent: 15, weekly_used_percent: 25 },
    { account_id: 'acc-standard', label: 'standard-acct', provider: 'codex', credits: false, five_hour_used_percent: 30, weekly_used_percent: 40 },
  ];

  const ports = {
    fetch: async (_url, init) => {
      const body = JSON.parse(init.body);
      const skip = new Set(body.skip_account_ids ?? []);
      const picked = cloudAccounts.find(a => !skip.has(a.account_id));
      const payload = picked
        ? {
            state: 'leased',
            pool_size: 3,
            account: picked,
            lease: { lease_id: `lease-${picked.account_id}`, delivery_mode: 'codex_auth_json', auth_json: { tokens: { access_token: 'tok', refresh_token: 'ref' } } },
          }
        : { state: 'all_cooling', wake_at: '2026-11-15T12:00:00Z' };
      return new Response(JSON.stringify(payload), { status: 200, headers: { 'content-type': 'application/json' } });
    },
  };

  // Automated Autopilot step (default allowCredits: false) skips acc-credit and acc-reset and leases acc-standard!
  const autoPick = await selectCloudPoolLogin({ cwd: dir, env, fallbackAgent: { kind: 'codex', command: 'codex' } }, ports);
  assert.equal(autoPick.state, 'ready');
  assert.equal(autoPick.login.id, 'acc-standard');

  // Explicit human CLI override ({ allowCredits: true }) can select acc-credit.
  const humanPick = await selectCloudPoolLogin({ cwd: dir, env, fallbackAgent: { kind: 'codex', command: 'codex' }, allowCredits: true }, ports);
  assert.equal(humanPick.state, 'ready');
  assert.equal(humanPick.login.id, 'acc-credit');

  // Local pool with ONLY credit/reset logins stays unavailable/exhausted for automated selection.
  const poolPath = join(dir, 'credit-only-pool.json');
  writeFileSync(poolPath, JSON.stringify({
    reset: 'never',
    logins: [
      { id: 'only-credit', kind: 'codex', credits: true, codexHome: join(dir, '.cx1') },
      { id: 'only-reset', kind: 'claude', allowReset: true, claudeConfigDir: join(dir, '.cl1') },
    ],
  }));
  const blockedAuto = await selectPoolLogin(
    { cwd: dir, env, poolPath, stateRoot: join(dir, 'pool-state') },
    { probeLogin: async () => assert.fail('automated selection must skip credit/reset logins before probing') },
  );
  assert.equal(blockedAuto.state, 'exhausted');
  assert.deepEqual(
    blockedAuto.unavailable.map(u => [u.id, u.reason]),
    [['only-credit', 'credit_or_reset_guarded'], ['only-reset', 'credit_or_reset_guarded']],
  );
});

test('Review Fix 1 & 2: cleanupAgentJob handles null wrapper in retryPending recovery, fails closed on resolution write error, and never signals recycled -job.pid process groups', async t => {
  // 1. retryPending with wrapper: null resolves cleanly without TypeError.
  const dir1 = makeTempDir(t, 'pdd-retry-null-wrap-');
  const token1 = join(dir1, 'nullwrap.spec.json');
  const exit1 = join(dir1, 'nullwrap.exit.json');
  writeFileSync(token1, JSON.stringify({ command: 'codex', args: ['exec'], cwd: dir1, input: join(dir1, 'in'), log: join(dir1, 'log'), exit: exit1 }));
  writeFileSync(`${token1}.processes.cleanup-snapshot.json`, JSON.stringify({
    schema: 1,
    pid: 81000,
    token: token1,
    attempts: [{ at: 1000, reason: 'ps unavailable', wrapper: null }],
    resolutions: [],
  }));
  const proof1 = await cleanupAgentJob(
    { pid: 81000, token: token1, exit: exit1, stopped: true },
    { alive: () => false, list: () => [{ pid: process.pid, ppid: 1, pgid: process.pid, rss: 10, start: '@me', args: 'node test' }], kill: () => {} },
  );
  assert.equal(proof1.confirmed, true);
  const resolved1 = JSON.parse(readFileSync(`${token1}.processes.cleanup-snapshot.json`, 'utf8'));
  assert.equal(resolved1.resolutions.length, 1);
  assert.equal(resolved1.resolutions[0].wrapper, null);

  // 2. PID recycled to an unrelated process group leader: never collect pgid === job.pid or send SIGTERM/SIGKILL to -job.pid.
  const dir2 = makeTempDir(t, 'pdd-recycled-pgid-');
  const token2 = join(dir2, 'recycled.spec.json');
  const exit2 = join(dir2, 'recycled.exit.json');
  const recycledPid = 82000;
  writeFileSync(token2, JSON.stringify({ command: 'codex', args: ['exec'], cwd: dir2, input: join(dir2, 'in'), log: join(dir2, 'log'), exit: exit2 }));
  writeFileSync(`${token2}.processes.error`, 'stale error\n', { mode: 0o600 });

  const signals = [];
  const unrelatedLeader = { pid: recycledPid, ppid: 1, pgid: recycledPid, rss: 20, start: '@new-unrelated', args: '/usr/bin/python3 unrelated-daemon.py' };
  const unrelatedChild = { pid: 82001, ppid: recycledPid, pgid: recycledPid, rss: 15, start: '@new-child', args: '/usr/bin/python3 worker.py' };
  const proof2 = await cleanupAgentJob(
    { pid: recycledPid, token: token2, exit: exit2, processesUncertain: true, stopped: true },
    {
      recoverStopped: true,
      alive: () => false,
      list: () => [unrelatedLeader, unrelatedChild],
      kill: (pid, sig) => { signals.push([pid, sig]); },
      sleep: async () => {},
      grace: 5,
      poll: 1,
    },
  );
  assert.equal(proof2.confirmed, true, 'recycled PID proves original -job.pid process group already ended');
  assert.deepEqual(signals, [], 'zero signals sent to recycled PID or its unrelated process group');
});

test('Review Fix 3: real-binding-unavailable on one test never excuses unrun sibling tests of the same Story', async t => {
  const story = 'user_stories/multi-test-webhook.md';
  const testA = 'tests/webhook-live.json';
  const testB = 'tests/webhook-validation.json';

  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.baseCommit(story, '# Webhook\n\nDeliver and validate webhook.\n');
  w.baseCommit(testA, '{"story":"user_stories/multi-test-webhook.md"}\n');
  w.baseCommit(testB, '{"story":"user_stories/multi-test-webhook.md"}\n');
  w.issue(17);
  await w.tick();
  writeIn(w.job(17, 'build').cwd, story, '# Webhook\n\nDeliver and validate signed webhook.\n');

  // Only testA has a saved local skip; sibling testB was NEVER run, while the merge base passed both!
  w.runtimeEvidence = async ({ base }) => base
    ? {
        stories: [{ story, pass: true, current: true, at: 500, tests: [testA, testB] }],
        storyFiles: [story],
        tests: [
          { path: testA, files: [testA], stories: [story] },
          { path: testB, files: [testB], stories: [story] },
        ],
      }
    : {
        stories: [{
          story,
          pass: false,
          current: true,
          sent: false,
          at: 1000,
          tests: [testA],
          reason: { code: 'real-binding-unavailable' },
          codes: ['real-binding-unavailable'],
          refusals: ['real-binding-unavailable'],
          states: ['refused'],
        }],
        storyFiles: [story],
        tests: [
          { path: testA, files: [testA], stories: [story] },
          { path: testB, files: [testB], stories: [story] },
        ],
        footprints: { [story]: [] },
      };

  const { pr } = w.build(17, {
    body: `Fixes #17\n\nRuntime: not run (${story}: real-binding-unavailable)\nPath: d — ${story}, change-17.txt — unowned — no contract change — Test: done check`,
    runtime: { state: 'not-run' },
  });
  await w.tick();
  const repair = w.job(17, 'repair');
  assert.ok(repair, 'unrun sibling testB must trigger repair instead of being excused by testA skip');
  assert.match(repair.input, /unrun pdd test checks at this source/);
  assert.equal(w.github.merges.length, 0);
  assert.ok(pr.number > 0);
});

test('Review Fix 4: runStepAgentProcess, loadLoginPool fallback, and runAutopilotLauncher enforce credit/reset account guards', async t => {
  const dir = makeTempDir(t, 'pdd-step-credit-guard-');
  const env = { HOME: dir, PDD_STATE_DIR: join(dir, 'state'), PDD_TOKEN: 'pdd_test_token_123' };
  writeCloudAccountsState({ enrolled: true, providers: ['codex'], active: {}, cooling: {} }, { env });

  // 1. normalizeFallback preserves credits and allowReset / allow_reset.
  const fbPool = loadLoginPool({ cwd: dir, env, fallbackAgent: { id: 'fb', kind: 'codex', credits: true, allow_reset: true } });
  assert.equal(fbPool.logins[0].credits, true);
  assert.equal(fbPool.logins[0].allowReset, true);

  // 2. runStepAgentProcess skips credit/reset Cloud accounts by default and leases standard account.
  const leasedIds = [];
  const stepRes = await runStepAgentProcess({
    agent: 'codex',
    args: ['exec', '-'],
    cwd: dir,
    env,
    run: async () => ({ code: 0, stdout: 'ok\n', stderr: '' }),
    accountsPorts: {
      fetch: async (_url, init) => {
        const body = JSON.parse(init.body);
        const skip = new Set(body.skip_account_ids ?? []);
        const accounts = [
          { account_id: 'acc-credit', label: 'c', provider: 'codex', credits: true, five_hour_used_percent: 5, weekly_used_percent: 5 },
          { account_id: 'acc-std', label: 's', provider: 'codex', credits: false, five_hour_used_percent: 10, weekly_used_percent: 10 },
        ];
        const acc = accounts.find(a => !skip.has(a.account_id));
        if (acc) leasedIds.push(acc.account_id);
        return new Response(JSON.stringify({
          state: 'leased',
          pool_size: 2,
          account: acc,
          lease: { lease_id: `l-${acc.account_id}`, delivery_mode: 'codex_auth_json', codex_auth_json: { tokens: { access_token: 'tok', refresh_token: 'ref' } } },
        }), { status: 200, headers: { 'content-type': 'application/json' } });
      },
    },
  });
  assert.equal(stepRes.code, 0);
  assert.deepEqual(leasedIds, ['acc-credit', 'acc-std']);

  // 2b. Sticky/malformed credit lease (repeats same account_id or omits account_id) terminates immediately with all_cooling instead of looping.
  let stickyCalls = 0;
  await assert.rejects(
    () => runStepAgentProcess({
      agent: 'codex',
      args: ['exec', '-'],
      cwd: dir,
      env,
      run: async () => assert.fail('must never execute on sticky credit account'),
      accountsPorts: {
        fetch: async () => {
          stickyCalls += 1;
          return new Response(JSON.stringify({
            state: 'leased',
            pool_size: 1,
            account: { account_id: 'acc-sticky-credit', label: 'c', provider: 'codex', credits: true },
            lease: { lease_id: 'l-sticky', delivery_mode: 'codex_auth_json', codex_auth_json: { tokens: { access_token: 'tok', refresh_token: 'ref' } } },
          }), { status: 200, headers: { 'content-type': 'application/json' } });
        },
      },
    }),
    { code: 'all_cooling' },
  );
  assert.equal(stickyCalls, 2, 'stops as soon as repeated credit account_id is seen');

  let missingIdCalls = 0;
  await assert.rejects(
    () => runStepAgentProcess({
      agent: 'codex',
      args: ['exec', '-'],
      cwd: dir,
      env,
      run: async () => assert.fail('must never execute on missing-id credit account'),
      accountsPorts: {
        fetch: async () => {
          missingIdCalls += 1;
          return new Response(JSON.stringify({
            state: 'leased',
            pool_size: 1,
            account: { account_id: '', label: 'c', provider: 'codex', allow_reset: true },
            lease: { lease_id: 'l-noid', delivery_mode: 'codex_auth_json', codex_auth_json: { tokens: { access_token: 'tok', refresh_token: 'ref' } } },
          }), { status: 200, headers: { 'content-type': 'application/json' } });
        },
      },
    }),
    { code: 'all_cooling' },
  );
  assert.equal(missingIdCalls, 1, 'stops immediately when credit/reset account omits account_id');

  // 3. runAutopilotLauncher start refuses a pool whose logins are all credit/reset-flagged before doctor or state writes.
  const { execFileSync } = await import('node:child_process');
  const repoDir = makeTempDir(t, 'pdd-launcher-credit-pool-');
  execFileSync('git', ['init', '-q'], { cwd: repoDir });
  const poolPath = join(repoDir, 'pool.json');
  writeFileSync(poolPath, JSON.stringify({
    reset: 'never',
    logins: [{ id: 'credit-only', kind: 'codex', credits: true, codexHome: join(repoDir, '.cx') }],
  }));
  const launchRes = await runAutopilotLauncher(
    { command: 'start', cwd: repoDir, env, label: 'pdd:autopilot', pool: poolPath },
    { stateRoot: join(dir, 'ap-state') },
  );
  assert.equal(launchRes.exitCode, 1);
  assert.match(launchRes.message, /credits or allowReset/);
});
