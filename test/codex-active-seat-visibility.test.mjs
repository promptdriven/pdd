import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { spawn } from 'node:child_process';
import {
  chmodSync,
  existsSync,
  mkdirSync,
  mkdtempSync,
  readdirSync,
  readFileSync,
  realpathSync,
  rmSync,
  symlinkSync,
  writeFileSync,
} from 'node:fs';
import { createServer } from 'node:http';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import {
  resolveCodexSeatNotice,
  summarizeCodexRuntimeStatus,
} from '../src/accounts/codex-seat-visibility.mjs';
import { readLiveCodexRuntimeLeases } from '../src/accounts/runtime-session.mjs';
import { runPddCodexCli, sharedRuntimeDirPath } from '../src/pdd-codex.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { writeCloudAccountsState } from '../src/login-pool.mjs';

const BIN_PDD = join(process.cwd(), 'bin', 'pdd.mjs');
const BIN_CODEX = join(process.cwd(), 'bin', 'pdd-codex.mjs');

function makeSink(isTTY = false) {
  return {
    isTTY,
    text: '',
    write(chunk) {
      this.text += String(chunk);
      return true;
    },
  };
}

function makeSandbox(t) {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-codex-seat-3679-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const home = join(root, 'home');
  const stateDir = join(root, 'state');
  const runtimeRoot = join(stateDir, 'codex-runtime');
  mkdirSync(home, { recursive: true, mode: 0o700 });
  mkdirSync(stateDir, { recursive: true, mode: 0o700 });
  const env = {
    HOME: home,
    PDD_STATE_DIR: stateDir,
    PDD_CODEX_RUNTIME_ROOT: runtimeRoot,
    PATH: process.env.PATH,
  };
  return { root, home, stateDir, runtimeRoot, env };
}

function makeLeaseReply({
  leaseId = 'lse_seat_001',
  accountId = 'acc_cx4',
  label = 'cx4',
  isOwner = true,
  ownerLogin = 'serhan',
  grant = 'pddg_lse_seat_001_secretvalue',
  baseUrl = 'https://api.promptdriven.ai',
  autoRotate = true,
  expiresAt = new Date(Date.now() + 7 * 24 * 60 * 60 * 1000).toISOString(),
} = {}) {
  const account = {
    account_id: accountId,
    label,
    provider: 'codex',
    state: 'ready',
    plan_type: 'pro',
    ...(isOwner !== null ? { is_owner: isOwner } : {}),
    ...(ownerLogin !== null ? { owner_login: ownerLogin } : {}),
  };
  return {
    state: 'leased',
    account,
    lease: {
      lease_id: leaseId,
      expires_at: expiresAt,
      delivery_mode: 'gateway_grant',
      codex_gateway_url: `${baseUrl}/v1/codex-gateway`,
      codex_backend_api_url: `${baseUrl}/v1/codex-gateway/backend-api`,
      codex_gateway_token: grant,
      gateway_bearer_token: grant,
      auto_rotate: autoRotate,
    },
  };
}

async function startMockPoolServer(t, { accounts = [], leaseAccounts = null } = {}) {
  let seq = 0;
  const revoked = [];
  const server = createServer((req, res) => {
    const chunks = [];
    req.on('data', c => chunks.push(c));
    req.on('end', () => {
      const raw = Buffer.concat(chunks).toString('utf8');
      const body = raw ? JSON.parse(raw) : {};
      const url = new URL(req.url, 'http://127.0.0.1');
      const send = (code, payload) => {
        res.writeHead(code, { 'content-type': 'application/json', connection: 'close' });
        res.end(JSON.stringify(payload));
      };
      const origin = `http://127.0.0.1:${server.address().port}`;
      if (req.method === 'GET' && url.pathname === '/v1/accounts') {
        return send(200, { accounts, pending_invites: [] });
      }
      if (req.method === 'POST' && url.pathname === '/v1/accounts/lease') {
        const pool = leaseAccounts ?? accounts;
        const chosen = (body.preferred_label && pool.find(a => a.label === body.preferred_label))
          || (body.current_account_id && pool.find(a => a.account_id === body.current_account_id))
          || pool[0];
        if (!chosen) return send(200, { state: 'all_cooling', lease: null });
        const leaseId = `lse_live_${++seq}`;
        const token = `pddg_${leaseId}_secretTok`;
        return send(200, {
          state: 'leased',
          account: chosen,
          lease: {
            lease_id: leaseId,
            expires_at: new Date(Date.now() + 7 * 86400_000).toISOString(),
            delivery_mode: 'gateway_grant',
            auto_rotate: body.auto_rotate !== false,
            codex_gateway_url: `${origin}/v1/codex-gateway`,
            codex_backend_api_url: `${origin}/v1/codex-gateway/backend-api`,
            codex_gateway_token: token,
            gateway_bearer_token: token,
          },
        });
      }
      if (req.method === 'POST' && /^\/v1\/accounts\/leases\/([^/]+)\/heartbeat$/.test(url.pathname)) {
        return send(200, { ok: true, expires_at: new Date(Date.now() + 7 * 86400_000).toISOString() });
      }
      if (req.method === 'POST' && /^\/v1\/accounts\/leases\/([^/]+)\/release$/.test(url.pathname)) {
        revoked.push(url.pathname.split('/')[4]);
        return send(200, { revoked: true });
      }
      return send(404, { error: 'not_found' });
    });
  });
  await new Promise(r => server.listen(0, '127.0.0.1', r));
  t.after(() => {
    server.closeAllConnections?.();
    server.close();
  });
  return { url: `http://127.0.0.1:${server.address().port}`, revoked };
}

test('AC1-AC3 pure visibility logic: interactive notices, pinned fallback, non-interactive/JSON suppression, value-flag safety, and sanitization', () => {
  // AC1: Interactive shared owned and teammate seats
  assert.deepEqual(
    resolveCodexSeatNotice({
      codexArgs: [],
      isInteractiveTty: true,
      seat: { label: 'cx4', accountId: 'acc_cx4', pinned: false, autoRotate: true, isOwner: true, ownerLogin: 'serhan' },
    }),
    { shouldPrint: true, reason: 'interactive', notice: 'pdd-codex: using PDD Cloud seat "cx4" (owner, auto-rotate on)' },
  );
  assert.deepEqual(
    resolveCodexSeatNotice({
      codexArgs: ['-m', 'gpt-5.4', 'fix the bug'],
      isInteractiveTty: true,
      seat: { label: 'team-cx', accountId: 'acc_team', pinned: false, autoRotate: true, isOwner: false, ownerLogin: 'alice' },
    }),
    { shouldPrint: true, reason: 'interactive', notice: 'pdd-codex: using PDD Cloud seat "team-cx" (shared by alice, auto-rotate on)' },
  );
  assert.equal(
    resolveCodexSeatNotice({
      codexArgs: ['-C', 'exec', '-p', 'review'],
      isInteractiveTty: true,
      seat: { label: 'team-cx', pinned: false, autoRotate: true, shared: true },
    }).notice,
    'pdd-codex: using PDD Cloud seat "team-cx" (shared, auto-rotate on)',
  );
  assert.equal(
    resolveCodexSeatNotice({
      codexArgs: ['--', '--json', 'exec'],
      isInteractiveTty: true,
      seat: { label: 'cx4', pinned: false, autoRotate: true },
    }).notice,
    'pdd-codex: using PDD Cloud seat "cx4" (auto-rotate on)',
  );

  // AC2: Pinned launches with owned vs absent access metadata
  assert.deepEqual(
    resolveCodexSeatNotice({
      codexArgs: ['resume', '--last'],
      isInteractiveTty: true,
      seat: { label: 'cx4', pinned: true, autoRotate: false, isOwner: true },
    }),
    { shouldPrint: true, reason: 'interactive', notice: 'pdd-codex: pinned to "cx4" (owner, auto-rotate off)' },
  );
  assert.deepEqual(
    resolveCodexSeatNotice({
      codexArgs: ['fork'],
      isInteractiveTty: true,
      seat: { label: 'cx4', pinned: true, autoRotate: false },
    }),
    { shouldPrint: true, reason: 'interactive', notice: 'pdd-codex: pinned to "cx4" (auto-rotate off)' },
  );

  // AC3: Non-interactive subcommands, machine flags, and non-TTY
  for (const args of [
    ['exec', 'summarize'],
    ['exec', '--json', 'summarize'],
    ['--json', 'exec', 'summarize'],
    ['e', 'quick'],
    ['app-server'],
    ['mcp-server'],
    ['exec-server'],
    ['review'],
    ['login', 'status'],
  ]) {
    const res = resolveCodexSeatNotice({ codexArgs: args, isInteractiveTty: true, seat: { label: 'cx4', isOwner: true } });
    assert.equal(res.shouldPrint, false, `expected skip for ${JSON.stringify(args)}`);
    assert.equal(res.reason, 'non_interactive_subcommand');
    assert.equal(res.notice, null);
  }
  for (const args of [
    ['--json'],
    ['resume', '--json'],
    ['--experimental-json'],
    ['--quiet'],
    ['-q'],
    ['-o', 'out.txt'],
    ['-o=out.txt'],
    ['--output-last-message=out.txt'],
    ['--output-schema', 'schema.json'],
    ['--format=json'],
    ['--output-format', 'JSON'],
  ]) {
    const res = resolveCodexSeatNotice({ codexArgs: args, isInteractiveTty: true, seat: { label: 'cx4', isOwner: true } });
    assert.equal(res.shouldPrint, false, `expected machine skip for ${JSON.stringify(args)}`);
    assert.equal(res.reason, 'machine_output_flag');
    assert.equal(res.notice, null);
  }
  // Non-json --format does not suppress interactive notice
  assert.equal(
    resolveCodexSeatNotice({ codexArgs: ['--format', 'text'], isInteractiveTty: true, seat: { label: 'cx4', isOwner: true } }).shouldPrint,
    true,
  );
  assert.deepEqual(
    resolveCodexSeatNotice({ codexArgs: [], isInteractiveTty: false, seat: { label: 'cx4', isOwner: true } }),
    { shouldPrint: false, reason: 'non_interactive_tty', notice: null },
  );

  // Control characters and ANSI escape sequences are stripped to guarantee 1 safe line
  const sanitized = resolveCodexSeatNotice({
    codexArgs: [],
    isInteractiveTty: true,
    seat: { label: '\u001b[31mcx4\u001b[0m\ninjected', isOwner: false, ownerLogin: 'al\rice\u001b[2J' },
  });
  assert.equal(sanitized.shouldPrint, true);
  assert.equal(sanitized.notice, 'pdd-codex: using PDD Cloud seat "cx4 injected" (shared by al ice, auto-rotate on)');
  assert.equal(sanitized.notice.includes('\n'), false);
  assert.equal(sanitized.notice.includes('\r'), false);
  assert.equal(sanitized.notice.includes('\u001b'), false);

  // Conflicting account_id on a same-label account must NEVER contaminate ownership metadata
  const conflictingIdStatus = summarizeCodexRuntimeStatus({
    runtimeLeases: [{
      mode: 'shared',
      lease_id: 'lse_old_1',
      account_id: 'acc_old_cx4',
      label: 'cx4',
      auto_rotate: true,
      live_sessions: 1,
    }],
    accounts: [{
      account_id: 'acc_new_cx4',
      label: 'cx4',
      provider: 'codex',
      is_owner: false,
      owner_login: 'wrong-owner',
    }],
    cachedActiveCodex: { account_id: 'acc_new_cx4', label: 'cx4', is_owner: true, owner_login: 'wrong-cached' },
  });
  assert.equal(conflictingIdStatus.codex_runtime.access_type, 'unknown');
  assert.equal(conflictingIdStatus.codex_runtime.owner_login, null);
  assert.equal(conflictingIdStatus.lines[0], 'Active pdd-codex: cx4 (access: unknown, auto-rotate: on, 1 live session)');
});

test('AC1-AC3 through runPddCodexCli: prints stderr notice on interactive TTY (fresh, reused, pinned), skips exec --json/non-TTY/fail-open, keeps ~/.codex/auth.json untouched', async t => {
  const sb = makeSandbox(t);
  const userCodex = join(sb.home, '.codex');
  mkdirSync(userCodex, { recursive: true, mode: 0o700 });
  const personalAuthPath = join(userCodex, 'auth.json');
  const personalAuthContent = JSON.stringify({ auth_mode: 'chatgpt', tokens: { access_token: 'personal_keep_3679' } });
  writeFileSync(personalAuthPath, personalAuthContent, { mode: 0o600 });

  // 1. Two concurrent interactive sessions share 1 lease for shared seat "team-cx" (alice): both print 1-line notice on stderr
  const livePids = new Set([61001, 61002]);
  let releaseFirst;
  const firstGate = new Promise(r => { releaseFirst = r; });
  let firstStartedResolve;
  const firstStarted = new Promise(r => { firstStartedResolve = r; });
  let leaseCalls = 0;

  const out1 = makeSink(true), err1 = makeSink(true);
  const out2 = makeSink(true), err2 = makeSink(true);

  const p1 = runPddCodexCli(
    [],
    { cwd: sb.root, env: sb.env, stdin: { isTTY: true }, stdout: out1, stderr: err1 },
    {
      tmpRoot: sb.runtimeRoot,
      uid: 601,
      pid: 61001,
      isPidAlive: pid => livePids.has(pid),
      heartbeatIntervalMs: 0,
      spawnSync: () => ({ status: 0 }),
      leaseCloudAccount: async () => {
        leaseCalls += 1;
        return makeLeaseReply({ leaseId: 'lse_team_1', accountId: 'acc_team_1', label: 'team-cx', isOwner: false, ownerLogin: 'alice' });
      },
      releaseCloudLease: async () => ({ revoked: true }),
      spawnCodex: async () => {
        firstStartedResolve();
        await firstGate;
        return { code: 0 };
      },
    },
  );
  await firstStarted;

  const p2 = runPddCodexCli(
    ['resume', '--last'],
    { cwd: sb.root, env: sb.env, stdin: { isTTY: true }, stdout: out2, stderr: err2 },
    {
      tmpRoot: sb.runtimeRoot,
      uid: 601,
      pid: 61002,
      isPidAlive: pid => livePids.has(pid),
      heartbeatIntervalMs: 0,
      spawnSync: () => ({ status: 0 }),
      leaseCloudAccount: async () => { throw new Error('second session should reuse lease'); },
      releaseCloudLease: async () => ({ revoked: true }),
      spawnCodex: async () => ({ code: 0 }),
    },
  );
  assert.equal((await p2).exitCode, 0);
  livePids.delete(61002);
  releaseFirst();
  assert.equal((await p1).exitCode, 0);
  livePids.delete(61001);

  assert.equal(leaseCalls, 1);
  assert.equal(out1.text, '');
  assert.equal(out2.text, '');
  assert.equal(err1.text, 'pdd-codex: using PDD Cloud seat "team-cx" (shared by alice, auto-rotate on)\n');
  assert.equal(err2.text, 'pdd-codex: using PDD Cloud seat "team-cx" (shared by alice, auto-rotate on)\n');
  assert.doesNotMatch(err1.text, /pddg_/);

  // 2. Pinned interactive launch (with owner metadata and without access metadata)
  const pinErrOwned = makeSink(true);
  const rPinOwned = await runPddCodexCli(
    ['--account', 'cx4'],
    { cwd: sb.root, env: sb.env, stdin: { isTTY: true }, stdout: makeSink(true), stderr: pinErrOwned },
    {
      tmpRoot: sb.runtimeRoot,
      uid: 601,
      pid: 61003,
      heartbeatIntervalMs: 0,
      leaseCloudAccount: async () => makeLeaseReply({ leaseId: 'lse_pin_1', label: 'cx4', isOwner: true, ownerLogin: 'serhan', autoRotate: false }),
      releaseCloudLease: async () => ({ revoked: true }),
      spawnCodex: async () => ({ code: 0 }),
    },
  );
  assert.equal(rPinOwned.exitCode, 0);
  assert.equal(pinErrOwned.text, 'pdd-codex: pinned to "cx4" (owner, auto-rotate off)\n');

  const pinErrNoAccess = makeSink(true);
  const rPinNoAccess = await runPddCodexCli(
    ['--account', 'cx4'],
    { cwd: sb.root, env: sb.env, stdin: { isTTY: true }, stdout: makeSink(true), stderr: pinErrNoAccess },
    {
      tmpRoot: sb.runtimeRoot,
      uid: 601,
      pid: 61004,
      heartbeatIntervalMs: 0,
      leaseCloudAccount: async () => makeLeaseReply({ leaseId: 'lse_pin_2', label: 'cx4', isOwner: null, ownerLogin: null, autoRotate: false }),
      releaseCloudLease: async () => ({ revoked: true }),
      spawnCodex: async () => ({ code: 0 }),
    },
  );
  assert.equal(rPinNoAccess.exitCode, 0);
  assert.equal(pinErrNoAccess.text, 'pdd-codex: pinned to "cx4" (auto-rotate off)\n');

  // 3. Non-interactive `exec --json` even on a TTY, non-TTY bare launch, and auto fail-open print ZERO notice
  const execErr = makeSink(true);
  const rExec = await runPddCodexCli(
    ['exec', '--json', 'hi'],
    { cwd: sb.root, env: sb.env, stdin: { isTTY: true }, stdout: makeSink(true), stderr: execErr },
    {
      tmpRoot: sb.runtimeRoot,
      uid: 601,
      pid: 61005,
      isPidAlive: p => p === 61005,
      heartbeatIntervalMs: 0,
      spawnSync: () => ({ status: 0 }),
      leaseCloudAccount: async () => makeLeaseReply({ leaseId: 'lse_exec_1' }),
      releaseCloudLease: async () => ({ revoked: true }),
      spawnCodex: async () => ({ code: 0 }),
    },
  );
  assert.equal(rExec.exitCode, 0);
  assert.equal(execErr.text, '');

  const nonTtyErr = makeSink(false);
  const rNonTty = await runPddCodexCli(
    [],
    { cwd: sb.root, env: sb.env, stdin: { isTTY: false }, stdout: makeSink(false), stderr: nonTtyErr },
    {
      tmpRoot: sb.runtimeRoot,
      uid: 601,
      pid: 61006,
      isPidAlive: p => p === 61006,
      heartbeatIntervalMs: 0,
      spawnSync: () => ({ status: 0 }),
      leaseCloudAccount: async () => makeLeaseReply({ leaseId: 'lse_nontty_1' }),
      releaseCloudLease: async () => ({ revoked: true }),
      spawnCodex: async () => ({ code: 0 }),
    },
  );
  assert.equal(rNonTty.exitCode, 0);
  assert.equal(nonTtyErr.text, '');

  const failOpenErr = makeSink(true);
  const rFailOpen = await runPddCodexCli(
    [],
    { cwd: sb.root, env: { ...sb.env, PDD_CODEX_AUTO_FAIL_OPEN: '1' }, stdin: { isTTY: true }, stdout: makeSink(true), stderr: failOpenErr },
    {
      tmpRoot: sb.runtimeRoot,
      uid: 601,
      leaseCloudAccount: async () => {
        const err = new Error('gateway down');
        err.code = 'service_unavailable';
        err.status = 503;
        throw err;
      },
      spawnCodex: async () => ({ code: 0 }),
    },
  );
  assert.equal(rFailOpen.exitCode, 0);
  assert.equal(failOpenErr.text, '');

  assert.equal(readFileSync(personalAuthPath, 'utf8'), personalAuthContent, 'personal ~/.codex/auth.json untouched');
});

test('AC4-AC5 through pdd accounts status [--json]: surfaces live shared + pinned leases, enriches offline/legacy lease.json, hides dead/exited leases, and stays strictly read-only & symlink-safe', async t => {
  const sb = makeSandbox(t);
  const accounts = [
    { account_id: 'acc_team_1', label: 'team-cx', provider: 'codex', is_owner: false, owner_login: 'alice', state: 'ready', five_hour_used_percent: 20, weekly_used_percent: 10 },
    { account_id: 'acc_cx4', label: 'cx4', provider: 'codex', is_owner: true, owner_login: 'serhan', state: 'ready', five_hour_used_percent: 5, weekly_used_percent: 15 },
  ];
  const server = await startMockPoolServer(t, { accounts });
  const env = { ...sb.env, PDD_ACCOUNTS_URL: server.url, PDD_TOKEN: 'pdd_test_token_3679' };

  const runStatus = async (args, ports = {}) => {
    const stdout = makeSink(false);
    const stderr = makeSink(false);
    const exit = await runPdd(['accounts', 'status', ...args], {
      cwd: sb.root,
      env,
      stdout,
      stderr,
      pathDiagnostic: () => [],
      accountsPorts: { uid: 602, ...ports },
    });
    return { exit, stdout: stdout.text, stderr: stderr.text };
  };

  // 1. Before any pdd-codex runs: runtimeRoot does not exist, status creates NOTHING, reports 0 live sessions and no Active pdd-codex line
  assert.equal(existsSync(sb.runtimeRoot), false);
  const idleHuman = await runStatus([]);
  assert.equal(idleHuman.exit, 0, idleHuman.stderr);
  assert.doesNotMatch(idleHuman.stdout, /Active pdd-codex/);
  assert.equal(existsSync(sb.runtimeRoot), false, 'status must remain strictly read-only and never create runtimeRoot');

  const idleJson = JSON.parse((await runStatus(['--json'])).stdout);
  assert.deepEqual(idleJson.codex_runtime, {
    active: false,
    live_sessions: 0,
    label: null,
    account_id: null,
    access_type: null,
    owner_login: null,
    auto_rotate: null,
    pinned: null,
    expires_at: null,
    leases: [],
  });

  // 2. Seed shared runtime dir with 2 live PIDs + 1 dead PID (omitting is_owner/owner_login to prove live enrichment!)
  //    AND 1 live pinned dir + 1 dead/crashed pinned dir, with accounts-state.json active: {}
  const sharedDir = sharedRuntimeDirPath({ env, uid: 602 });
  mkdirSync(join(sharedDir, 'pids'), { recursive: true, mode: 0o700 });
  writeFileSync(join(sharedDir, 'auth.json'), JSON.stringify({ tokens: { access_token: 'pddg_lse_secret_must_never_leak' } }), { mode: 0o600 });
  writeFileSync(join(sharedDir, 'lease.json'), JSON.stringify({
    lease_id: 'lse_shared_live',
    account_id: 'acc_team_1',
    label: 'team-cx',
    auto_rotate: true,
    expires_at: '2026-12-02T00:00:00Z',
  }), { mode: 0o600 });
  writeFileSync(join(sharedDir, 'pids', '71001'), '{"pid":71001}', { mode: 0o600 });
  writeFileSync(join(sharedDir, 'pids', '71002'), '{"pid":71002}', { mode: 0o600 });
  writeFileSync(join(sharedDir, 'pids', '79999'), '{"pid":79999}', { mode: 0o600 });

  const pinLiveDir = join(sb.runtimeRoot, 'pdd-codex-pin-live1');
  mkdirSync(pinLiveDir, { recursive: true, mode: 0o700 });
  writeFileSync(join(pinLiveDir, 'lease.json'), JSON.stringify({
    lease_id: 'lse_pin_live',
    account_id: 'acc_cx4',
    label: 'cx4',
    is_owner: true,
    auto_rotate: false,
    pid: 71003,
    expires_at: '2026-12-01T00:00:00Z',
  }), { mode: 0o600 });

  const pinDeadDir = join(sb.runtimeRoot, 'pdd-codex-pin-dead1');
  mkdirSync(pinDeadDir, { recursive: true, mode: 0o700 });
  writeFileSync(join(pinDeadDir, 'lease.json'), JSON.stringify({
    lease_id: 'lse_pin_dead',
    account_id: 'acc_cx4',
    label: 'cx4',
    is_owner: true,
    auto_rotate: false,
    pid: 79998,
  }), { mode: 0o600 });

  const alive = new Set([71001, 71002, 71003]);
  const liveHuman = await runStatus([], { isPidAlive: pid => alive.has(pid) });
  assert.equal(liveHuman.exit, 0, liveHuman.stderr);
  assert.match(liveHuman.stdout, /Active pdd-codex: team-cx \(shared \(alice\), auto-rotate: on, 2 live sessions\)/);
  assert.match(liveHuman.stdout, /Active pdd-codex \(pinned\): cx4 \(owner \(serhan\), auto-rotate: off, 1 live session\)/);
  assert.doesNotMatch(liveHuman.stdout, /pddg_/);
  // Dead PID file must NOT be deleted by read-only status!
  assert.equal(existsSync(join(sharedDir, 'pids', '79999')), true, 'status must not delete dead PID files');
  assert.equal(readdirSync(join(sharedDir, 'pids')).length, 3);

  const liveJsonRes = await runStatus(['--json'], { isPidAlive: pid => alive.has(pid) });
  assert.equal(liveJsonRes.exit, 0);
  assert.doesNotMatch(liveJsonRes.stdout, /pddg_/);
  const liveJson = JSON.parse(liveJsonRes.stdout);
  assert.equal(liveJson.codex_runtime.active, true);
  assert.equal(liveJson.codex_runtime.live_sessions, 3);
  assert.equal(liveJson.codex_runtime.label, 'team-cx');
  assert.equal(liveJson.codex_runtime.access_type, 'shared');
  assert.equal(liveJson.codex_runtime.owner_login, 'alice');
  assert.equal(liveJson.codex_runtime.auto_rotate, true);
  assert.equal(liveJson.codex_runtime.leases.length, 2);
  assert.equal(liveJson.codex_runtime.leases[0].live_sessions, 2);
  assert.equal(liveJson.codex_runtime.leases[1].pinned, true);
  assert.equal(liveJson.codex_runtime.leases[1].auto_rotate, false);
  assert.equal(liveJson.codex_runtime.leases[1].live_sessions, 1);

  // 3. Offline fallback: even when Cloud is unreachable, cached active.codex + lease.json still surface the live runtime lease
  writeCloudAccountsState({
    enrolled: true,
    providers: ['codex'],
    active: { codex: { account_id: 'acc_team_1', label: 'team-cx', provider: 'codex', is_owner: false, state: 'ready' } },
  }, { env });
  const offlineOut = makeSink(false);
  const offlineExit = await runPdd(['accounts', 'status'], {
    cwd: sb.root,
    env: { ...env, PDD_ACCOUNTS_URL: 'http://127.0.0.1:1' },
    stdout: offlineOut,
    stderr: makeSink(false),
    pathDiagnostic: () => [],
    accountsPorts: { uid: 602, isPidAlive: pid => alive.has(pid) },
  });
  assert.equal(offlineExit, 0);
  assert.match(offlineOut.text, /Active pdd-codex: team-cx \(shared, auto-rotate: on, 2 live sessions\)/);
  assert.match(offlineOut.text, /Active pdd-codex \(pinned\): cx4 \(owner, auto-rotate: off, 1 live session\)/);

  // 4. Once all live PIDs exit (even if stale lease.json remains), status hides the stale lease completely
  alive.clear();
  const afterExitHuman = await runStatus([], { isPidAlive: () => false });
  assert.equal(afterExitHuman.exit, 0);
  assert.doesNotMatch(afterExitHuman.stdout, /Active pdd-codex/);
  const afterExitJson = JSON.parse((await runStatus(['--json'], { isPidAlive: () => false })).stdout);
  assert.equal(afterExitJson.codex_runtime.active, false);
  assert.equal(afterExitJson.codex_runtime.live_sessions, 0);

  // 5. Security: symlinked runtime root / lease.json and foreign-UID ownership are refused safely without crashing
  const symRoot = join(sb.root, 'sym-runtime-root');
  symlinkSync(sb.runtimeRoot, symRoot);
  assert.deepEqual(
    readLiveCodexRuntimeLeases({ env: { ...env, PDD_CODEX_RUNTIME_ROOT: symRoot }, uid: 602 }, { isPidAlive: () => true }),
    [],
  );
  assert.deepEqual(
    readLiveCodexRuntimeLeases({ env, uid: 602 }, { isPidAlive: () => true, expectedUid: 999_999 }),
    [],
  );
  const symLeasePath = join(pinLiveDir, 'lease.json');
  const realLeaseTarget = join(sb.root, 'outside-lease.json');
  writeFileSync(realLeaseTarget, JSON.stringify({ lease_id: 'lse_sym', label: 'evil', pid: 71003 }), { mode: 0o600 });
  rmSync(symLeasePath);
  symlinkSync(realLeaseTarget, symLeasePath);
  assert.deepEqual(
    readLiveCodexRuntimeLeases({ env, uid: 602 }, { isPidAlive: p => p === 71003 }),
    [],
    'symlinked lease.json must be ignored',
  );
});

test('heartbeat seat rotation updates lease.json so status reflects rotated seat cleanly', async t => {
  const sb = makeSandbox(t);
  let observedStatus = null;
  const res = await runPddCodexCli(
    ['exec', 'wait-for-rotate'],
    { cwd: sb.root, env: sb.env, stdin: { isTTY: false }, stdout: makeSink(false), stderr: makeSink(false) },
    {
      tmpRoot: sb.runtimeRoot,
      uid: 603,
      pid: 72001,
      isPidAlive: p => p === 72001,
      heartbeatIntervalMs: 15,
      spawnSync: () => ({ status: 0 }),
      leaseCloudAccount: async () => makeLeaseReply({ leaseId: 'lse_rot_1', accountId: 'acc_a', label: 'seat-a', isOwner: true, ownerLogin: 'serhan' }),
      heartbeatCloudLease: async id => ({
        lease_id: id,
        expires_at: new Date(Date.now() + 7 * 86400_000).toISOString(),
        account: { account_id: 'acc_b', label: 'seat-b', is_owner: false, owner_login: 'alice' },
      }),
      releaseCloudLease: async () => ({ revoked: true }),
      spawnCodex: async () => {
        await new Promise(r => setTimeout(r, 75));
        const rawLeases = readLiveCodexRuntimeLeases(
          { env: sb.env, tmpRoot: sb.runtimeRoot, uid: 603 },
          { isPidAlive: p => p === 72001 },
        );
        observedStatus = summarizeCodexRuntimeStatus({ runtimeLeases: rawLeases });
        return { code: 0 };
      },
    },
  );
  assert.equal(res.exitCode, 0);
  assert.equal(observedStatus?.codex_runtime?.label, 'seat-b');
  assert.equal(observedStatus?.codex_runtime?.access_type, 'shared');
  assert.equal(observedStatus?.codex_runtime?.owner_login, 'alice');
  assert.equal(observedStatus?.lines?.[0], 'Active pdd-codex: seat-b (shared (alice), auto-rotate: on, 1 live session)');
});

function runSubprocessAsync(bin, args, { cwd, env, timeoutMs = 10_000 } = {}) {
  return new Promise(resolveRun => {
    const child = spawn(bin, args, { cwd, env, stdio: ['ignore', 'pipe', 'pipe'] });
    let stdout = '';
    let stderr = '';
    let settled = false;
    const finish = status => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      resolveRun({ status, stdout, stderr });
    };
    const timer = setTimeout(() => {
      try { child.kill('SIGKILL'); } catch {}
      finish(124);
    }, timeoutMs);
    child.stdout.on('data', d => { stdout += d.toString('utf8'); });
    child.stderr.on('data', d => { stderr += d.toString('utf8'); });
    child.on('error', err => finish(err?.code === 'ENOENT' ? 127 : 1));
    child.on('close', (code, sig) => finish(code ?? (sig ? 128 : 1)));
  });
}

test('real subprocess + real PTY end-to-end proof: bin/pdd-codex.mjs prints startup notice on PTY stderr, bin/pdd.mjs accounts status surfaces live seat while running and clears after exit, and exec --json stays silent', async t => {
  const sb = makeSandbox(t);
  const accounts = [
    { account_id: 'acc_cx4', label: 'cx4', provider: 'codex', is_owner: true, owner_login: 'alice', state: 'ready', five_hour_used_percent: 10, weekly_used_percent: 20 },
  ];
  const server = await startMockPoolServer(t, { accounts });

  const userCodex = join(sb.home, '.codex');
  mkdirSync(userCodex, { recursive: true, mode: 0o700 });
  const personalAuthPath = join(userCodex, 'auth.json');
  writeFileSync(personalAuthPath, '{"tokens":{"access_token":"real_user_keep"}}\n', { mode: 0o600 });
  const authHashBefore = createHash('sha256').update(readFileSync(personalAuthPath)).digest('hex');

  const binDir = join(sb.root, 'bin');
  mkdirSync(binDir, { recursive: true, mode: 0o700 });
  const mockCodexPath = join(binDir, 'codex');
  writeFileSync(mockCodexPath, `#!/usr/bin/env node
import { createInterface } from 'node:readline';
const args = process.argv.slice(2);
if (args.includes('app-server')) process.exit(0);
if (args.includes('exec')) {
  process.stdout.write(JSON.stringify({ ok: true, type: 'exec-json' }) + '\\n');
  process.exit(0);
}
if (!process.stdin.isTTY || !process.stdout.isTTY) {
  process.stderr.write('NOT_A_TTY\\n');
  process.exit(2);
}
process.stdout.write('MOCK_CODEX_READY\\n');
for await (const line of createInterface({ input: process.stdin })) {
  if (line.trim() === 'EXIT') process.exit(0);
}
`, { mode: 0o755 });
  chmodSync(mockCodexPath, 0o755);

  const childEnv = {
    ...sb.env,
    PDD_ACCOUNTS_URL: server.url,
    PDD_TOKEN: 'pdd_real_pty_token',
    PDD_CODEX_BIN: mockCodexPath,
  };

  // 1. Real subprocess non-interactive `pdd-codex exec --json hi`: stdout is pure JSON, stderr has ZERO notice
  const execRun = await runSubprocessAsync(process.execPath, [BIN_CODEX, 'exec', '--json', 'hi'], {
    cwd: sb.root,
    env: childEnv,
  });
  assert.equal(execRun.status, 0, execRun.stderr);
  assert.deepEqual(JSON.parse(execRun.stdout.trim()), { ok: true, type: 'exec-json' });
  assert.equal(execRun.stderr, '', 'non-interactive exec --json must print nothing to stderr');

  // 2. Real PTY launch of `node bin/pdd-codex.mjs`
  const ptyBridge = `
import fcntl, os, pty, select, signal, struct, subprocess, sys, termios
m, s = pty.openpty()
fcntl.ioctl(s, termios.TIOCSWINSZ, struct.pack("HHHH", 24, 120, 0, 0))
p = subprocess.Popen(sys.argv[1:], stdin=s, stdout=s, stderr=s, start_new_session=True, close_fds=True)
os.close(s)
in_fd, in_open = sys.stdin.fileno(), True
try:
  while True:
    r, _, _ = select.select([m] + ([in_fd] if in_open else []), [], [], 0.05)
    if m in r:
      try: d = os.read(m, 4096)
      except OSError: d = b""
      if d: os.write(1, d)
      elif p.poll() is not None: break
    if in_open and in_fd in r:
      cmd = os.read(in_fd, 4096)
      if not cmd: in_open = False
      else:
        try: os.write(m, cmd)
        except OSError: pass
    if p.poll() is not None:
      while select.select([m], [], [], 0.03)[0]:
        try: d2 = os.read(m, 4096)
        except OSError: break
        if not d2: break
        os.write(1, d2)
      break
finally:
  if p.poll() is None:
    try: os.killpg(p.pid, signal.SIGKILL)
    except OSError: pass
  try: os.close(m)
  except OSError: pass
sys.exit(p.wait())
`;
  const ptyProc = spawn('python3', ['-u', '-c', ptyBridge, process.execPath, BIN_CODEX], {
    cwd: sb.root,
    env: childEnv,
    stdio: ['pipe', 'pipe', 'pipe'],
  });
  t.after(() => { try { ptyProc.kill('SIGKILL'); } catch {} });

  let ptyBuf = '';
  await new Promise((resolveReady, rejectReady) => {
    const timer = setTimeout(() => rejectReady(new Error(`PTY timeout. Output:\n${ptyBuf}`)), 8000);
    ptyProc.stdout.on('data', chunk => {
      ptyBuf += chunk.toString('utf8');
      if (ptyBuf.includes('MOCK_CODEX_READY')) {
        clearTimeout(timer);
        resolveReady();
      }
    });
    ptyProc.on('exit', code => {
      clearTimeout(timer);
      rejectReady(new Error(`PTY exited early (${code}). Output:\n${ptyBuf}`));
    });
  });

  // Verify the 1-line startup notice appeared on the real PTY before MOCK_CODEX_READY!
  assert.match(ptyBuf, /pdd-codex: using PDD Cloud seat "cx4" \(owner, auto-rotate on\)/);
  assert.doesNotMatch(ptyBuf, /pddg_/);

  // While the real PTY pdd-codex process is running, run real `node bin/pdd.mjs accounts status` & `--json`!
  const statusLive = await runSubprocessAsync(process.execPath, [BIN_PDD, 'accounts', 'status'], {
    cwd: sb.root,
    env: childEnv,
  });
  assert.equal(statusLive.status, 0, statusLive.stderr);
  assert.match(statusLive.stdout, /Active pdd-codex: cx4 \(owner \(alice\), auto-rotate: on, 1 live session\)/);

  const statusLiveJsonRun = await runSubprocessAsync(process.execPath, [BIN_PDD, 'accounts', 'status', '--json'], {
    cwd: sb.root,
    env: childEnv,
  });
  assert.equal(statusLiveJsonRun.status, 0, statusLiveJsonRun.stderr);
  const statusLiveJson = JSON.parse(statusLiveJsonRun.stdout);
  assert.equal(statusLiveJson.codex_runtime.active, true);
  assert.equal(statusLiveJson.codex_runtime.label, 'cx4');
  assert.equal(statusLiveJson.codex_runtime.access_type, 'owner');
  assert.equal(statusLiveJson.codex_runtime.owner_login, 'alice');
  assert.equal(statusLiveJson.codex_runtime.auto_rotate, true);
  assert.equal(statusLiveJson.codex_runtime.live_sessions, 1);

  // Exit the real PTY session and confirm status clears immediately!
  ptyProc.stdin.write('EXIT\n');
  const exitCode = await new Promise(r => ptyProc.on('close', code => r(code)));
  assert.equal(exitCode, 0);

  const statusAfter = await runSubprocessAsync(process.execPath, [BIN_PDD, 'accounts', 'status'], {
    cwd: sb.root,
    env: childEnv,
  });
  assert.equal(statusAfter.status, 0, statusAfter.stderr);
  assert.doesNotMatch(statusAfter.stdout, /Active pdd-codex/);

  const statusAfterJsonRun = await runSubprocessAsync(process.execPath, [BIN_PDD, 'accounts', 'status', '--json'], {
    cwd: sb.root,
    env: childEnv,
  });
  assert.equal(statusAfterJsonRun.status, 0, statusAfterJsonRun.stderr);
  const statusAfterJson = JSON.parse(statusAfterJsonRun.stdout);
  assert.equal(statusAfterJson.codex_runtime.active, false);
  assert.equal(statusAfterJson.codex_runtime.live_sessions, 0);
  assert.equal(createHash('sha256').update(readFileSync(personalAuthPath)).digest('hex'), authHashBefore);
});
