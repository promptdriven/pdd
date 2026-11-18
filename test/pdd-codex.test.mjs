import test from 'node:test';
import assert from 'node:assert/strict';
import {
  existsSync,
  lstatSync,
  mkdirSync,
  mkdtempSync,
  readdirSync,
  readFileSync,
  readlinkSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import {
  parsePddCodexArgs,
  runPddCodexCli,
  sharedRuntimeDirPath,
} from '../src/pdd-codex.mjs';
import {
  createCodexStepOverlay,
  materializeLocalCodexAuth,
} from '../src/login-pool.mjs';
import { parse as parseToml } from '../src/vendor/smol-toml/parse.js';

function makeSandbox(t) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-codex-test-'));
  const home = join(root, 'home');
  const tmpRoot = join(root, 'tmp');
  mkdirSync(home, { recursive: true, mode: 0o700 });
  mkdirSync(tmpRoot, { recursive: true, mode: 0o700 });
  t.after(() => rmSync(root, { recursive: true, force: true }));
  return { root, home, tmpRoot, env: { ...process.env, HOME: home, PDD_CODEX_RUNTIME_ROOT: tmpRoot } };
}

function makeLeaseReply({
  leaseId = 'lse_shared_001',
  accountId = 'acc_codex_1',
  label = 'team-pro-1',
  grant = 'pddg_lse_shared_001_secretval',
  baseUrl = 'https://api.promptdriven.ai',
  autoRotate = true,
  expiresAt = new Date(Date.now() + 7 * 24 * 60 * 60 * 1000).toISOString(),
} = {}) {
  return {
    state: 'leased',
    account: {
      account_id: accountId,
      label,
      provider: 'codex',
      state: 'ready',
      plan_type: 'pro',
    },
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

test('parsePddCodexArgs parses leading --account and --pdd-help without mutating Codex prompt flags', () => {
  const a = parsePddCodexArgs(['--account', 'work-pro', 'exec', 'describe --account inside prompt']);
  assert.equal(a.preferredAccount, 'work-pro');
  assert.equal(a.showPddHelp, false);
  assert.deepEqual(a.codexArgs, ['exec', 'describe --account inside prompt']);

  const b = parsePddCodexArgs(['--account=team-2', '--', '--model', 'gpt-5.4']);
  assert.equal(b.preferredAccount, 'team-2');
  assert.deepEqual(b.codexArgs, ['--model', 'gpt-5.4']);

  const c = parsePddCodexArgs(['exec', '--account', 'not-a-pdd-flag']);
  assert.equal(c.preferredAccount, null);
  assert.deepEqual(c.codexArgs, ['exec', '--account', 'not-a-pdd-flag']);

  assert.throws(() => parsePddCodexArgs(['--account']), /Missing account label/);
  assert.throws(() => parsePddCodexArgs(['--account=']), /Missing account label/);
});

test('20 concurrent pdd-codex sessions share 1 runtime folder and 1 cloud lease, and clean up auth.json + revoke lease only on last exit', async t => {
  const sb = makeSandbox(t);
  const livePids = new Set();
  const leaseCalls = [];
  const releaseCalls = [];
  const gates = new Map();
  let startedCount = 0;
  let allStartedResolve;
  const allStarted = new Promise(r => { allStartedResolve = r; });

  const envWithDirtyKeys = {
    ...sb.env,
    OPENAI_API_KEY: 'sk-dirty-personal-key',
    CODEX_API_KEY: 'sk-dirty-codex-key',
    CODEX_ACCESS_TOKEN: 'dirty-access-token',
    OPENAI_BASE_URL: 'https://dirty.example.test',
    PDD_CODEX_GATEWAY_GRANT: 'pddg_stale_env_grant',
  };

  const promises = [];
  for (let i = 0; i < 20; i += 1) {
    const pid = 20_000 + i;
    livePids.add(pid);
    let releaseChild;
    const childGate = new Promise(r => { releaseChild = r; });
    gates.set(pid, releaseChild);

    promises.push(runPddCodexCli(
      ['exec', `task-${i}`],
      { cwd: sb.root, env: envWithDirtyKeys, stdout: { write() {} }, stderr: { write() {} } },
      {
        tmpRoot: sb.tmpRoot,
        uid: 501,
        pid,
        isPidAlive: candidate => livePids.has(candidate),
        heartbeatIntervalMs: 0,
        spawnSync: () => ({ status: 0 }),
        leaseCloudAccount: async req => {
          leaseCalls.push(req);
          await new Promise(r => setTimeout(r, 25));
          return makeLeaseReply();
        },
        releaseCloudLease: async leaseId => {
          releaseCalls.push(leaseId);
          return { lease_id: leaseId, revoked: true };
        },
        spawnCodex: async (_bin, args, opts) => {
          // Verify dirty env vars stripped & CODEX_HOME points to shared runtime dir.
          assert.equal(opts.env.OPENAI_API_KEY, undefined);
          assert.equal(opts.env.CODEX_API_KEY, undefined);
          assert.equal(opts.env.CODEX_ACCESS_TOKEN, undefined);
          assert.equal(opts.env.OPENAI_BASE_URL, undefined);
          assert.equal(opts.env.PDD_CODEX_GATEWAY_GRANT, undefined);
          assert.equal(opts.env.CODEX_HOME, sharedRuntimeDirPath({ env: sb.env, tmpRoot: sb.tmpRoot, uid: 501 }));
          // Verify native /backend-api + /codex CLI flags & zero responses_websockets=false!
          assert.ok(args.includes('chatgpt_base_url="https://api.promptdriven.ai/v1/codex-gateway/backend-api"'));
          assert.ok(args.includes('openai_base_url="https://api.promptdriven.ai/v1/codex-gateway/backend-api/codex"'));
          assert.ok(args.includes(`sqlite_home=${JSON.stringify(join(sb.home, '.codex'))}`));
          assert.ok(args.includes('features.daemon_auto_start=false'));
          assert.ok(args.includes('features.shell_snapshot=false'));
          assert.ok(args.some(a => a.startsWith('shell_environment_policy.set.CODEX_HOME=')));
          assert.ok(!args.includes('features.responses_websockets=false'));

          startedCount += 1;
          if (startedCount === 20) allStartedResolve();
          await childGate;
          return { code: 0 };
        },
      },
    ));
  }

  await allStarted;

  const runtimeDir = sharedRuntimeDirPath({ env: sb.env, tmpRoot: sb.tmpRoot, uid: 501 });
  // Only ONE cloud lease was requested across all 20 simultaneous launches!
  assert.equal(leaseCalls.length, 1);
  assert.equal(leaseCalls[0].autoRotate, true);
  assert.equal(existsSync(join(runtimeDir, 'auth.json')), true);
  assert.equal(existsSync(join(runtimeDir, 'lease.json')), true);
  assert.equal(readdirSync(join(runtimeDir, 'pids')).length, 20);

  // Verify brand-new VM ~/.codex baseline & config.toml symlink (zero gateway URLs in user config.toml).
  const userCodex = join(sb.home, '.codex');
  assert.equal(existsSync(join(userCodex, 'config.toml')), true);
  assert.equal(readFileSync(join(userCodex, 'config.toml'), 'utf8'), '');
  assert.equal(lstatSync(join(runtimeDir, 'config.toml')).isSymbolicLink(), true);
  assert.equal(readlinkSync(join(runtimeDir, 'config.toml')), resolve(userCodex, 'config.toml'));
  for (const dirName of ['sessions', 'archived_sessions', 'plugins', 'skills', 'rules', 'memories']) {
    assert.equal(existsSync(join(userCodex, dirName)), true);
    assert.equal(lstatSync(join(runtimeDir, dirName)).isSymbolicLink(), true);
  }

  // Exit first 19 sessions: auth.json & lease MUST stay alive!
  for (let i = 0; i < 19; i += 1) {
    const pid = 20_000 + i;
    gates.get(pid)();
    const res = await promises[i];
    assert.equal(res.exitCode, 0);
    livePids.delete(pid);
  }
  assert.equal(existsSync(join(runtimeDir, 'auth.json')), true, 'auth.json stays intact while session #20 is running');
  assert.equal(releaseCalls.length, 0, 'lease is NOT revoked while session #20 is still alive');

  // Exit the 20th (last) session: auth.json deleted & cloud lease revoked immediately!
  gates.get(20_019)();
  const lastRes = await promises[19];
  assert.equal(lastRes.exitCode, 0);
  livePids.delete(20_019);

  assert.equal(existsSync(join(runtimeDir, 'auth.json')), false, 'auth.json deleted on last session exit');
  assert.equal(existsSync(join(runtimeDir, 'lease.json')), false, 'lease.json deleted on last session exit');
  assert.deepEqual(releaseCalls, ['lse_shared_001']);
});

test('stale dead PID files are swept automatically so last live exit still cleans auth.json and revokes lease', async t => {
  const sb = makeSandbox(t);
  const runtimeDir = sharedRuntimeDirPath({ env: sb.env, tmpRoot: sb.tmpRoot, uid: 502 });
  mkdirSync(join(runtimeDir, 'pids'), { recursive: true, mode: 0o700 });
  writeFileSync(join(runtimeDir, 'pids', '999999'), '{"pid":999999}\n', 'utf8');

  const releaseCalls = [];
  const res = await runPddCodexCli(
    ['exec', 'hi'],
    { cwd: sb.root, env: sb.env, stdout: { write() {} }, stderr: { write() {} } },
    {
      tmpRoot: sb.tmpRoot,
      uid: 502,
      pid: 30_001,
      isPidAlive: pid => pid === 30_001,
      heartbeatIntervalMs: 0,
      spawnSync: () => ({ status: 0 }),
      leaseCloudAccount: async () => makeLeaseReply({ leaseId: 'lse_sweep_1' }),
      releaseCloudLease: async id => { releaseCalls.push(id); return { revoked: true }; },
      spawnCodex: async () => ({ code: 0 }),
    },
  );
  assert.equal(res.exitCode, 0);
  assert.equal(existsSync(join(runtimeDir, 'pids', '999999')), false);
  assert.equal(existsSync(join(runtimeDir, 'auth.json')), false);
  assert.deepEqual(releaseCalls, ['lse_sweep_1']);
});

test('pinned --account <label> uses an isolated temp folder with autoRotate=false without disturbing shared sessions', async t => {
  const sb = makeSandbox(t);
  const sharedDir = sharedRuntimeDirPath({ env: sb.env, tmpRoot: sb.tmpRoot, uid: 503 });
  const leaseReqs = [];
  const releaseIds = [];
  let pinDirSeen = null;

  const res = await runPddCodexCli(
    ['--account', 'serhan-pro', 'exec', 'check'],
    { cwd: sb.root, env: sb.env, stdout: { write() {} }, stderr: { write() {} } },
    {
      tmpRoot: sb.tmpRoot,
      uid: 503,
      pid: 40_001,
      heartbeatIntervalMs: 0,
      leaseCloudAccount: async req => {
        leaseReqs.push(req);
        return makeLeaseReply({ leaseId: 'lse_pinned_99', autoRotate: false, label: 'serhan-pro' });
      },
      releaseCloudLease: async id => { releaseIds.push(id); return { revoked: true }; },
      spawnCodex: async (_bin, _args, opts) => {
        pinDirSeen = opts.env.CODEX_HOME;
        assert.notEqual(pinDirSeen, sharedDir);
        assert.equal(existsSync(join(pinDirSeen, 'auth.json')), true);
        assert.equal(lstatSync(join(pinDirSeen, 'config.toml')).isSymbolicLink(), true);
        return { code: 0 };
      },
    },
  );
  assert.equal(res.exitCode, 0);
  assert.equal(leaseReqs.length, 1);
  assert.equal(leaseReqs[0].preferredLabel, 'serhan-pro');
  assert.equal(leaseReqs[0].autoRotate, false);
  assert.equal(existsSync(pinDirSeen), false, 'isolated pinned temp dir removed on exit');
  assert.deepEqual(releaseIds, ['lse_pinned_99']);
});

test('pdd-codex logout, login, and mcp add never touch personal ~/.codex/auth.json and work safely', async t => {
  const sb = makeSandbox(t);
  const userCodex = join(sb.home, '.codex');
  mkdirSync(userCodex, { recursive: true, mode: 0o700 });
  const personalAuth = JSON.stringify({ auth_mode: 'chatgpt', tokens: { access_token: 'personal_user_token' } });
  writeFileSync(join(userCodex, 'auth.json'), personalAuth, 'utf8');

  // Seed shared runtime lease + auth.json, then run `pdd-codex logout`.
  const runtimeDir = sharedRuntimeDirPath({ env: sb.env, tmpRoot: sb.tmpRoot, uid: 504 });
  mkdirSync(runtimeDir, { recursive: true, mode: 0o700 });
  writeFileSync(join(runtimeDir, 'auth.json'), '{"tokens":{"access_token":"pddg_lse_x_y"}}\n', 'utf8');
  writeFileSync(join(runtimeDir, 'lease.json'), '{"lease_id":"lse_logout_1"}\n', 'utf8');

  const released = [];
  let logoutOut = '';
  const logoutRes = await runPddCodexCli(
    ['logout'],
    { cwd: sb.root, env: sb.env, stdout: { write(s) { logoutOut += s; } }, stderr: { write() {} } },
    {
      tmpRoot: sb.tmpRoot,
      uid: 504,
      releaseCloudLease: async id => { released.push(id); return { revoked: true }; },
    },
  );
  assert.equal(logoutRes.exitCode, 0);
  assert.match(logoutOut, /not touched/i);
  assert.deepEqual(released, ['lse_logout_1']);
  assert.equal(existsSync(join(runtimeDir, 'auth.json')), false);
  assert.equal(readFileSync(join(userCodex, 'auth.json'), 'utf8'), personalAuth, 'personal ~/.codex/auth.json untouched!');

  // `pdd-codex login` prints guidance and leaves personal auth untouched.
  let loginOut = '';
  const loginRes = await runPddCodexCli(
    ['login'],
    { cwd: sb.root, env: sb.env, stdout: { write(s) { loginOut += s; } }, stderr: { write() {} } },
    { tmpRoot: sb.tmpRoot, uid: 504 },
  );
  assert.equal(loginRes.exitCode, 0);
  assert.match(loginOut, /pdd accounts add --provider codex/);
  assert.equal(readFileSync(join(userCodex, 'auth.json'), 'utf8'), personalAuth);

  // `pdd-codex mcp add` symlinks config.toml -> ~/.codex/config.toml and requires 0 cloud lease calls.
  let leaseCalledForMcp = false;
  let mcpSawSymlink = false;
  const mcpRes = await runPddCodexCli(
    ['mcp', 'add', 'demo', '--', 'echo', 'hi'],
    { cwd: sb.root, env: sb.env, stdout: { write() {} }, stderr: { write() {} } },
    {
      tmpRoot: sb.tmpRoot,
      uid: 504,
      leaseCloudAccount: async () => { leaseCalledForMcp = true; throw new Error('should not lease'); },
      spawnCodex: async (_bin, args, opts) => {
        assert.deepEqual(args, ['mcp', 'add', 'demo', '--', 'echo', 'hi']);
        mcpSawSymlink = lstatSync(join(opts.env.CODEX_HOME, 'config.toml')).isSymbolicLink();
        return { code: 0 };
      },
    },
  );
  assert.equal(mcpRes.exitCode, 0);
  assert.equal(leaseCalledForMcp, false);
  assert.equal(mcpSawSymlink, true);
});

test('background heartbeat refreshes lease TTL while running and stops cleanly on exit', async t => {
  const sb = makeSandbox(t);
  const heartbeats = [];
  const extendedExpiry = new Date(Date.now() + 14 * 24 * 60 * 60 * 1000).toISOString();
  let observedLeaseMetaAfterHb = null;

  const res = await runPddCodexCli(
    ['exec', 'long-task'],
    { cwd: sb.root, env: sb.env, stdout: { write() {} }, stderr: { write() {} } },
    {
      tmpRoot: sb.tmpRoot,
      uid: 505,
      pid: 50_001,
      isPidAlive: pid => pid === 50_001,
      heartbeatIntervalMs: 20,
      spawnSync: () => ({ status: 0 }),
      leaseCloudAccount: async () => makeLeaseReply({ leaseId: 'lse_hb_1' }),
      releaseCloudLease: async () => ({ revoked: true }),
      heartbeatCloudLease: async id => {
        heartbeats.push(id);
        return { lease_id: id, expires_at: extendedExpiry, group_verified: true };
      },
      spawnCodex: async (_bin, _args, opts) => {
        await new Promise(r => setTimeout(r, 75));
        observedLeaseMetaAfterHb = JSON.parse(readFileSync(join(opts.env.CODEX_HOME, 'lease.json'), 'utf8'));
        return { code: 0 };
      },
    },
  );
  assert.equal(res.exitCode, 0);
  assert.ok(heartbeats.length >= 1, `expected >=1 heartbeat, got ${heartbeats.length}`);
  assert.equal(heartbeats[0], 'lse_hb_1');
  assert.equal(observedLeaseMetaAfterHb?.expires_at, extendedExpiry);
  const countAtExit = heartbeats.length;
  await new Promise(r => setTimeout(r, 60));
  assert.equal(heartbeats.length, countAtExit, 'heartbeat timer stopped on child exit');
});

test('materializeLocalCodexAuth and createCodexStepOverlay enable native /backend-api WebSockets when lease includes codex_backend_api_url', t => {
  const sb = makeSandbox(t);
  const lease = {
    delivery_mode: 'gateway_grant',
    plan_type: 'pro',
    codex_gateway_url: 'https://api.promptdriven.ai/v1/codex-gateway',
    codex_backend_api_url: 'https://api.promptdriven.ai/v1/codex-gateway/backend-api',
    codex_gateway_token: 'pddg_lse_wsnative1_secret123',
  };

  const mat = materializeLocalCodexAuth(lease, { env: sb.env }, { spawnSync: () => ({ status: 0 }) });
  const managedCfg = parseToml(readFileSync(mat.configPath, 'utf8'));
  assert.equal(managedCfg.chatgpt_base_url, 'https://api.promptdriven.ai/v1/codex-gateway/backend-api');
  assert.equal(managedCfg.openai_base_url, 'https://api.promptdriven.ai/v1/codex-gateway/backend-api/codex');
  assert.equal(managedCfg.sqlite_home, join(sb.home, '.codex'));
  assert.equal(managedCfg.features?.daemon_auto_start, false);
  assert.equal(managedCfg.features?.responses_websockets, undefined);
  assert.equal(managedCfg.model_providers?.pdd_codex_gateway?.supports_websockets, undefined);
  assert.equal(managedCfg.model_providers?.pdd_codex_gateway?.base_url, 'https://api.promptdriven.ai/v1/codex-gateway/backend-api/codex');

  const overlay = createCodexStepOverlay(lease, { env: sb.env, tmpRoot: sb.tmpRoot });
  try {
    const stepCfg = parseToml(readFileSync(overlay.configPath, 'utf8'));
    assert.equal(stepCfg.chatgpt_base_url, 'https://api.promptdriven.ai/v1/codex-gateway/backend-api');
    assert.equal(stepCfg.openai_base_url, 'https://api.promptdriven.ai/v1/codex-gateway/backend-api/codex');
    assert.equal(stepCfg.sqlite_home, resolve(join(sb.home, '.codex')));
    assert.equal(stepCfg.features?.daemon_auto_start, false);
    assert.equal(stepCfg.features?.shell_snapshot, false);
    assert.equal(stepCfg.features?.responses_websockets, undefined);
    assert.equal(stepCfg.model_providers?.pdd_codex_gateway?.supports_websockets, undefined);
    assert.equal(stepCfg.shell_environment_policy?.set?.CODEX_HOME, join(overlay.overlayDir, 'empty-subshell'));
  } finally {
    overlay.cleanup();
  }
});

