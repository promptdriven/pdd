import test from 'node:test';
import assert from 'node:assert/strict';
import {
  chmodSync,
  existsSync,
  lstatSync,
  mkdirSync,
  mkdtempSync,
  readdirSync,
  readFileSync,
  readlinkSync,
  realpathSync,
  renameSync,
  rmSync,
  statSync,
  symlinkSync,
  unlinkSync,
  utimesSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import {
  acquirePinnedRuntimeSession,
  acquireSharedRuntimeSession,
  parsePddCodexArgs,
  releaseSharedRuntimeSession,
  runPddCodexCli,
  sharedRuntimeDirPath,
} from '../src/pdd-codex.mjs';
import {
  registerProcessCleanupHooks,
  startLeaseHeartbeat,
} from '../src/accounts/runtime-session.mjs';
import {
  buildCodexGatewayCliArgs,
  buildCodexHomeMirrorCliArgs,
  CloudAccountsError,
  createCodexStepOverlay,
  localCodexHome,
  materializeLocalCodexAuth,
  normalizeCodexConfigWriteback,
  REQUIRED_CODEX_SUBSHELL_EXCLUDES,
  resolveCodexGatewayEndpoints,
  resolveEffectiveSqliteHome,
  stopCodexAppServerDaemon,
  writeCloudAccountsState,
} from '../src/login-pool.mjs';
import { parse as parseToml } from '../src/shared/toml/parse.js';

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

test('sharedRuntimeDirPath defaults under ~/.local/state/pdd/codex-runtime (never /tmp) and honors state/runtime env overrides', () => {
  const defaultDir = sharedRuntimeDirPath({ env: { HOME: '/home/alice' }, uid: 1002 });
  assert.equal(defaultDir, resolve('/home/alice/.local/state/pdd/codex-runtime/pdd-codex-1002'));
  assert.ok(!defaultDir.startsWith(resolve(tmpdir())), 'default runtime dir must not live under /tmp');

  assert.equal(
    sharedRuntimeDirPath({ env: { HOME: '/home/alice', XDG_STATE_HOME: '/var/state/alice' }, uid: 1002 }),
    resolve('/var/state/alice/pdd/codex-runtime/pdd-codex-1002'),
  );
  assert.equal(
    sharedRuntimeDirPath({ env: { HOME: '/home/alice', PDD_STATE_DIR: '/srv/pdd-state' }, uid: 1002 }),
    resolve('/srv/pdd-state/codex-runtime/pdd-codex-1002'),
  );
  assert.equal(
    sharedRuntimeDirPath({ env: { HOME: '/home/alice', PDD_CODEX_RUNTIME_ROOT: '/custom/runtime' }, uid: 1002 }),
    resolve('/custom/runtime/pdd-codex-1002'),
  );
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
    CODEX_CONNECTORS_TOKEN: 'dirty-personal-connectors-token',
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
          // Verify dirty env vars stripped, CODEX_CONNECTORS_TOKEN receives revocable pddg_* grant, and CODEX_HOME points to shared runtime dir.
          assert.equal(opts.env.OPENAI_API_KEY, undefined);
          assert.equal(opts.env.CODEX_API_KEY, undefined);
          assert.equal(opts.env.CODEX_ACCESS_TOKEN, undefined);
          assert.equal(opts.env.OPENAI_BASE_URL, undefined);
          assert.equal(opts.env.PDD_CODEX_GATEWAY_GRANT, undefined);
          assert.equal(opts.env.CODEX_CONNECTORS_TOKEN, 'pddg_lse_shared_001_secretval');
          assert.equal(opts.env.CODEX_HOME, sharedRuntimeDirPath({ env: sb.env, tmpRoot: sb.tmpRoot, uid: 501 }));
          // Verify native /backend-api + /codex CLI flags & zero responses_websockets=false!
          assert.ok(args.includes('chatgpt_base_url="https://api.promptdriven.ai/v1/codex-gateway/backend-api"'));
          assert.ok(args.includes('openai_base_url="https://api.promptdriven.ai/v1/codex-gateway/backend-api/codex"'));
          assert.ok(args.includes(`sqlite_home=${JSON.stringify(join(sb.home, '.codex'))}`));
          assert.ok(args.includes('features.daemon_auto_start=false'));
          assert.ok(args.includes('features.shell_snapshot=false'));
          assert.ok(args.includes('allow_symlinked_codex_home=true'));
          assert.ok(!args.some(a => a.startsWith('shell_environment_policy.set.CODEX_HOME=')));
          const filtersInline = args.find(a => a.startsWith('shell_environment_policy.filters={'));
          assert.ok(filtersInline, 'filters must use a single TOML inline table so "PDD_*" is parsed cleanly');
          assert.ok(filtersInline.includes('"PDD_*" = "exclude"'));
          assert.ok(filtersInline.includes('CODEX_CONNECTORS_TOKEN = "exclude"'));
          assert.ok(filtersInline.includes('OPENAI_API_KEY = "exclude"'));
          assert.ok(filtersInline.includes('CODEX_HOME = "exclude"'));
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
    { cwd: sb.root, env: { ...sb.env, CODEX_CONNECTORS_TOKEN: 'dirty-connectors-tok' }, stdout: { write() {} }, stderr: { write() {} } },
    {
      tmpRoot: sb.tmpRoot,
      uid: 504,
      leaseCloudAccount: async () => { leaseCalledForMcp = true; throw new Error('should not lease'); },
      spawnCodex: async (_bin, args, opts) => {
        assert.equal(args.includes(`sqlite_home=${JSON.stringify(userCodex)}`), true);
        assert.equal(args.includes('allow_symlinked_codex_home=true'), true);
        assert.deepEqual(args.slice(-6), ['mcp', 'add', 'demo', '--', 'echo', 'hi']);
        assert.equal(opts.env.CODEX_CONNECTORS_TOKEN, undefined);
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
    assert.equal(stepCfg.shell_environment_policy?.set?.CODEX_HOME, undefined);
    assert.equal(existsSync(join(overlay.overlayDir, 'empty-subshell')), false);
    for (const key of REQUIRED_CODEX_SUBSHELL_EXCLUDES) {
      assert.equal(stepCfg.shell_environment_policy?.filters?.[key], 'exclude', `overlay must exclude ${key}`);
    }
  } finally {
    overlay.cleanup();
  }
});

test('review regressions: shell_environment_policy merge/filters, nested CODEX_HOME guard, atomic config symlink, dead-lock recovery, heartbeat dedupe & revocation, and rolling-deploy fallback', async t => {
  const sb = makeSandbox(t);
  const runtimeDir = sharedRuntimeDirPath({ env: sb.env, tmpRoot: sb.tmpRoot, uid: 707 });
  const emptySubshell = join(runtimeDir, 'empty-subshell');

  // 1. Nested CODEX_HOME inside runtime dir (or empty-subshell) falls back to ~/.codex.
  const nestedEnv = { ...sb.env, CODEX_HOME: emptySubshell };
  assert.equal(localCodexHome(nestedEnv), join(sb.home, '.codex'));
  assert.equal(localCodexHome({ ...sb.env, CODEX_HOME: runtimeDir }), join(sb.home, '.codex'));

  // 2. shell_environment_policy preserves user [filters] via inline table AND merges legacy exclude without clobbering.
  const filtersArgs = buildCodexGatewayCliArgs({
    backendApiUrl: 'https://api.promptdriven.ai/v1/codex-gateway/backend-api',
    userCodexHome: join(sb.home, '.codex'),
    emptySubshellCodexHome: emptySubshell,
    userConfigText: '[shell_environment_policy.filters]\nMY_CUSTOM = "exclude"\n',
  });
  const filtersInline = filtersArgs.find(a => a.startsWith('shell_environment_policy.filters={'));
  assert.ok(filtersInline && filtersInline.includes('"PDD_*" = "exclude"') && filtersInline.includes('CODEX_CONNECTORS_TOKEN = "exclude"') && filtersInline.includes('CODEX_HOME = "exclude"'));
  assert.ok(!filtersArgs.some(a => a.startsWith('shell_environment_policy.exclude=')));

  const legacyExcludeArgs = buildCodexGatewayCliArgs({
    backendApiUrl: 'https://api.promptdriven.ai/v1/codex-gateway/backend-api',
    userCodexHome: join(sb.home, '.codex'),
    emptySubshellCodexHome: emptySubshell,
    userConfigText: '[shell_environment_policy]\nexclude = ["AWS_*", "MY_SECRET"]\n',
  });
  const excludeEntry = legacyExcludeArgs.find(a => a.startsWith('shell_environment_policy.exclude='));
  assert.ok(excludeEntry, 'legacy exclude should merge instead of switching to filters');
  assert.ok(excludeEntry.includes('"AWS_*"') && excludeEntry.includes('"MY_SECRET"') && excludeEntry.includes('"CODEX_CONNECTORS_TOKEN"'));

  // 3. Rolling-deploy fallback disables responses_websockets when server omits codex_backend_api_url.
  const legacyServerArgs = buildCodexGatewayCliArgs({
    backendApiUrl: 'https://api.promptdriven.ai/v1/codex-gateway/backend-api',
    userCodexHome: join(sb.home, '.codex'),
    emptySubshellCodexHome: emptySubshell,
    nativeBackendApi: false,
  });
  assert.ok(legacyServerArgs.includes('features.responses_websockets=false'));

  // 4. Bare `pdd-codex mcp` passes through without taking a cloud lease.
  let leaseCalledForMcp = false;
  const mcpRes = await runPddCodexCli(
    ['mcp'],
    { cwd: sb.root, env: sb.env, stdout: { write() {} }, stderr: { write() {} } },
    {
      leaseCloudAccount: async () => { leaseCalledForMcp = true; return makeLeaseReply(); },
      spawnCodex: async (_bin, args) => {
        assert.deepEqual(args, ['mcp']);
        return { code: 0 };
      },
    },
  );
  assert.equal(mcpRes.exitCode, 0);
  assert.equal(leaseCalledForMcp, false);

  // 5. Dead lock owner in `<runtimeDir>/lock` recovers rapidly, nested CODEX_HOME launches safely,
  // and 401 heartbeat revokes cached lease+auth.
  const lockDir = join(runtimeDir, 'lock');
  mkdirSync(lockDir, { recursive: true, mode: 0o700 });
  const pastMs = Date.now() - 5_000;
  writeFileSync(join(lockDir, 'owner.json'), JSON.stringify({
    pid: 99_999,
    acquired_at: pastMs,
  }), { mode: 0o600 });
  const pastDate = new Date(pastMs);
  utimesSync(lockDir, pastDate, pastDate);

  let observedConfigTarget = null;
  let observedLeaseAfter401 = true;
  let observedAuthAfter401 = true;
  const res = await runPddCodexCli(
    ['exec', 'nested-check'],
    { cwd: sb.root, env: nestedEnv, stdout: { write() {} }, stderr: { write() {} } },
    {
      tmpRoot: sb.tmpRoot,
      uid: 707,
      pid: 70_001,
      isPidAlive: candidate => candidate === 70_001,
      heartbeatIntervalMs: 20,
      spawnSync: () => ({ status: 0 }),
      leaseCloudAccount: async () => makeLeaseReply({ leaseId: 'lse_rev_401' }),
      heartbeatCloudLease: async () => {
        const err = new Error('revoked');
        err.status = 401;
        throw err;
      },
      releaseCloudLease: async () => ({ revoked: true }),
      spawnCodex: async (_bin, _args, opts) => {
        observedConfigTarget = readlinkSync(join(opts.env.CODEX_HOME, 'config.toml'));
        await new Promise(r => setTimeout(r, 90));
        observedLeaseAfter401 = existsSync(join(opts.env.CODEX_HOME, 'lease.json'));
        observedAuthAfter401 = existsSync(join(opts.env.CODEX_HOME, 'auth.json'));
        return { code: 0 };
      },
    },
  );
  assert.equal(res.exitCode, 0);
  assert.equal(resolve(observedConfigTarget), resolve(join(sb.home, '.codex', 'config.toml')));
  assert.equal(observedLeaseAfter401, false, '401 heartbeat should invalidate cached lease.json');
  assert.equal(observedAuthAfter401, false, '401 heartbeat should invalidate cached auth.json');
});

test('home parity: .tmp marketplaces mirror, unquoted openai-bundled source override, hooks.state remap, and local mcp list', async t => {
  const sb = makeSandbox(t);
  const userCodex = join(sb.home, '.codex');
  const bundledDir = join(userCodex, '.tmp', 'bundled-marketplaces', 'openai-bundled');
  const marketplacesDir = join(userCodex, '.tmp', 'marketplaces', 'claude-plugins-official');
  const pluginsRepoDir = join(userCodex, '.tmp', 'plugins');
  mkdirSync(bundledDir, { recursive: true });
  mkdirSync(marketplacesDir, { recursive: true });
  mkdirSync(pluginsRepoDir, { recursive: true });
  writeFileSync(join(userCodex, '.tmp', 'plugins.sha'), 'abc123\n');
  mkdirSync(join(userCodex, '.tmp', 'git-temp-clone'), { recursive: true });
  writeFileSync(join(userCodex, '.tmp', 'plugins.sync.lock'), '');
  writeFileSync(join(userCodex, 'hooks.json'), '{"hooks":{"SessionStart":[]}}\n');

  const userConfigText = [
    'model = "gpt-6.2-sol"',
    '',
    '[marketplaces.openai-bundled]',
    'source_type = "local"',
    `source = ${JSON.stringify(bundledDir)}`,
    '',
    '[marketplaces.external-cache]',
    'source_type = "local"',
    'source = "/opt/external/marketplace"',
    '',
    '[marketplaces.isolated-tmp-leak]',
    'source_type = "local"',
    `source = ${JSON.stringify(join(userCodex, '.tmp', 'git-temp-clone'))}`,
    '',
    `[hooks.state.${JSON.stringify(`${userCodex}/hooks.json:session_start:0:0`)}]`,
    'trusted_hash = "sha256:aaa111"',
    '',
    '[hooks.state."gitkraken-hooks@gitkraken:hooks/hooks.json:session_start:0:0"]',
    'trusted_hash = "sha256:bbb222"',
    '',
  ].join('\n');
  writeFileSync(join(userCodex, 'config.toml'), userConfigText, { mode: 0o600 });

  // Pre-seed a stale real directory at <runtime>/.tmp/marketplaces to verify auto-healing to symlink.
  const runtimeDir = sharedRuntimeDirPath({ env: sb.env, tmpRoot: sb.tmpRoot, uid: 555 });
  mkdirSync(join(runtimeDir, '.tmp', 'marketplaces', 'stale'), { recursive: true });

  // 1. Main pdd-codex launch mirrors safe .tmp entries and emits canonical -c overrides.
  let observedArgs = null;
  let observedTmpState = null;
  const runRes = await runPddCodexCli(
    ['exec', 'check parity'],
    { env: sb.env, stdout: { write() {} }, stderr: { write() {} } },
    {
      tmpRoot: sb.tmpRoot,
      uid: 555,
      pid: 99100,
      isPidAlive: () => true,
      leaseCloudAccount: async () => makeLeaseReply({ leaseId: 'lse_parity_1' }),
      releaseCloudLease: async () => ({ revoked: true }),
      spawnCodex: async (_bin, args, opts) => {
        observedArgs = args;
        const rt = opts.env.CODEX_HOME;
        observedTmpState = {
          tmpIsDir: lstatSync(join(rt, '.tmp')).isDirectory() && !lstatSync(join(rt, '.tmp')).isSymbolicLink(),
          bundledLink: lstatSync(join(rt, '.tmp', 'bundled-marketplaces')).isSymbolicLink(),
          marketplacesLink: lstatSync(join(rt, '.tmp', 'marketplaces')).isSymbolicLink(),
          pluginsLink: lstatSync(join(rt, '.tmp', 'plugins')).isSymbolicLink(),
          pluginsShaLink: lstatSync(join(rt, '.tmp', 'plugins.sha')).isSymbolicLink(),
          gitTempAbsent: !existsSync(join(rt, '.tmp', 'git-temp-clone')),
          lockAbsent: !existsSync(join(rt, '.tmp', 'plugins.sync.lock')),
        };
        return { code: 0 };
      },
    },
  );
  assert.equal(runRes.exitCode, 0);
  assert.deepEqual(observedTmpState, {
    tmpIsDir: true,
    bundledLink: true,
    marketplacesLink: true,
    pluginsLink: true,
    pluginsShaLink: true,
    gitTempAbsent: true,
    lockAbsent: true,
  });

  const realRt = realpathSync(runtimeDir);
  const expectedBundledOverride = `marketplaces.openai-bundled.source=${JSON.stringify(join(realRt, '.tmp', 'bundled-marketplaces', 'openai-bundled'))}`;
  assert.equal(observedArgs.includes(expectedBundledOverride), true, 'bare marketplace key must be unquoted and canonical');
  assert.equal(
    observedArgs.some(a => a.includes('marketplaces.external-cache') || a.includes('marketplaces.isolated-tmp-leak')),
    false,
    'external and isolated .tmp paths must not be rewritten',
  );
  const hooksArg = observedArgs.find(a => a.startsWith('hooks.state={'));
  assert.ok(hooksArg, 'hooks.state inline table override should be emitted');
  assert.equal(hooksArg.includes(JSON.stringify(`${realRt}/hooks.json:session_start:0:0`)), true);
  assert.equal(hooksArg.includes('trusted_hash = "sha256:aaa111"'), true);
  assert.equal(hooksArg.includes('gitkraken-hooks'), false, 'plugin hook state must stay untouched in user config');

  // 2. Local `pdd-codex mcp list` also mirrors .tmp and passes mirror -c overrides without leasing.
  let mcpLeased = false;
  let mcpObservedArgs = null;
  let mcpBundledPresent = false;
  const mcpRes = await runPddCodexCli(
    ['mcp', 'list'],
    { env: sb.env, stdout: { write() {} }, stderr: { write() {} } },
    {
      tmpRoot: sb.tmpRoot,
      leaseCloudAccount: async () => { mcpLeased = true; return makeLeaseReply(); },
      spawnCodex: async (_bin, args, opts) => {
        mcpObservedArgs = args;
        mcpBundledPresent = lstatSync(join(opts.env.CODEX_HOME, '.tmp', 'bundled-marketplaces')).isSymbolicLink();
        return { code: 0 };
      },
    },
  );
  assert.equal(mcpRes.exitCode, 0);
  assert.equal(mcpLeased, false, 'mcp list must remain offline without cloud lease');
  assert.equal(mcpBundledPresent, true, 'mcp list temp dir must mirror .tmp/bundled-marketplaces');
  assert.equal(
    mcpObservedArgs.some(a => a.startsWith('marketplaces.openai-bundled.source=')),
    true,
    'mcp list must pass marketplace override so plugin-contributed MCP servers (cua_repl, codex_app) appear',
  );

  // 3. Unsafe symlink inside ~/.codex/.tmp pointing to auth.json is rejected.
  writeFileSync(join(userCodex, 'auth.json'), '{"secret":true}\n', { mode: 0o600 });
  rmSync(join(userCodex, '.tmp', 'plugins.sha'), { force: true });
  symlinkSync(join(userCodex, 'auth.json'), join(userCodex, '.tmp', 'plugins.sha'));
  const directArgs = buildCodexHomeMirrorCliArgs({
    userCodexHome: userCodex,
    runtimeCodexHome: runtimeDir,
    userConfigText,
  });
  assert.equal(directArgs.includes(expectedBundledOverride), true);
  const res2 = await runPddCodexCli(
    ['exec', 'check unsafe tmp symlink'],
    { env: sb.env, stdout: { write() {} }, stderr: { write() {} } },
    {
      tmpRoot: sb.tmpRoot,
      uid: 555,
      pid: 99101,
      isPidAlive: () => true,
      leaseCloudAccount: async () => makeLeaseReply({ leaseId: 'lse_parity_2' }),
      releaseCloudLease: async () => ({ revoked: true }),
      spawnCodex: async (_bin, _args, opts) => {
        assert.equal(existsSync(join(opts.env.CODEX_HOME, '.tmp', 'plugins.sha')), false, 'unsafe auth.json symlink in .tmp must be pruned');
        return { code: 0 };
      },
    },
  );
  assert.equal(res2.exitCode, 0);

  // 4. Managed home (materializeLocalCodexAuth) and step overlays (createCodexStepOverlay)
  // mirror .tmp/bundled-marketplaces and remap marketplace source + hooks.state in their
  // materialized config.toml without altering ~/.codex/config.toml.
  const leaseSpec = {
    delivery_mode: 'gateway_grant',
    codex_gateway_url: 'http://127.0.0.1:41999/v1/codex-gateway/lse_parity_mat',
    codex_backend_api_url: 'http://127.0.0.1:41999/v1/codex-backend-api/lse_parity_mat',
    codex_gateway_token: 'pddg_lse_parity_mat_tok',
    plan_type: 'pro',
  };
  const materialized = materializeLocalCodexAuth(leaseSpec, { env: sb.env });
  const realManaged = realpathSync(materialized.codexHome);
  const managedCfgText = readFileSync(materialized.configPath, 'utf8');
  assert.equal(lstatSync(join(materialized.codexHome, '.tmp', 'bundled-marketplaces')).isSymbolicLink(), true);
  assert.equal(managedCfgText.includes(join(realManaged, '.tmp', 'bundled-marketplaces', 'openai-bundled')), true);
  assert.equal(managedCfgText.includes(`${join(realManaged, 'hooks.json')}:session_start:0:0`), true);

  const overlay = createCodexStepOverlay(leaseSpec, { env: sb.env, tmpRoot: sb.tmpRoot });
  try {
    const realOverlay = realpathSync(overlay.overlayDir);
    const overlayCfgText = readFileSync(overlay.configPath, 'utf8');
    assert.equal(lstatSync(join(overlay.overlayDir, '.tmp', 'bundled-marketplaces')).isSymbolicLink(), true);
    assert.equal(overlayCfgText.includes(join(realOverlay, '.tmp', 'bundled-marketplaces', 'openai-bundled')), true);
    assert.equal(overlayCfgText.includes(`${join(realOverlay, 'hooks.json')}:session_start:0:0`), true);
  } finally {
    overlay.cleanup();
  }
  assert.equal(readFileSync(join(userCodex, 'config.toml'), 'utf8'), userConfigText);
});

test('adversarial parity regressions: inline PDD_* filters, cross-layer exclude, sqlite_home preservation, writeback normalization, CLI guards, and daemon stop', async t => {
  const sb = makeSandbox(t);
  const userCodex = join(sb.home, '.codex');
  const repoDir = join(sb.root, 'repo');
  mkdirSync(join(repoDir, '.codex'), { recursive: true });

  // 1. parsePddCodexArgs preserves leading `--` when no PDD flags precede it.
  const leadingDashDash = parsePddCodexArgs(['--', '-prompt-like-flag']);
  assert.deepEqual(leadingDashDash.codexArgs, ['--', '-prompt-like-flag']);

  // 2. Leading global Codex flags cannot bypass `logout` or `login`, and `--help` / `features` need zero lease.
  let leaseCalls = 0;
  let spawnedCalls = [];
  const noLeasePorts = {
    tmpRoot: sb.tmpRoot,
    uid: 777,
    pid: 99201,
    leaseCloudAccount: async () => {
      leaseCalls += 1;
      return makeLeaseReply({ leaseId: 'lse_should_not_run' });
    },
    spawnCodex: async (bin, args, opts) => {
      spawnedCalls.push({ bin, args, env: opts.env });
      return { code: 0 };
    },
  };
  let loginOut = '';
  const rLogin = await runPddCodexCli(
    ['--no-daemon', 'login'],
    { env: sb.env, stdout: { write(s) { loginOut += s; } }, stderr: { write() {} } },
    noLeasePorts,
  );
  assert.equal(rLogin.exitCode, 0);
  assert.match(loginOut, /never touches your personal/);
  assert.equal(leaseCalls, 0);
  assert.equal(spawnedCalls.length, 0);

  let logoutOut = '';
  const rLogout = await runPddCodexCli(
    ['-c', 'model="gpt-6.2-sol"', 'logout'],
    { env: sb.env, stdout: { write(s) { logoutOut += s; } }, stderr: { write() {} } },
    noLeasePorts,
  );
  assert.equal(rLogout.exitCode, 0);
  assert.match(logoutOut, /Cleared PDD Codex/);
  assert.equal(leaseCalls, 0);
  assert.equal(spawnedCalls.length, 0);

  const rHelp = await runPddCodexCli(
    ['exec', '--help'],
    { env: sb.env, stdout: { write() {} }, stderr: { write() {} } },
    noLeasePorts,
  );
  assert.equal(rHelp.exitCode, 0);
  assert.equal(leaseCalls, 0);
  assert.equal(spawnedCalls.length, 1);

  // `features list` runs locally (no lease, no daemon_auto_start=false distortion, passes sqlite_home + allow_symlinked_codex_home,
  // and ensures fresh ~/.codex/.tmp/{bundled-marketplaces,marketplaces,plugins} baseline exists).
  const rFeat = await runPddCodexCli(
    ['features', 'list'],
    { env: sb.env, stdout: { write() {} }, stderr: { write() {} } },
    noLeasePorts,
  );
  assert.equal(rFeat.exitCode, 0);
  assert.equal(leaseCalls, 0);
  const featArgs = spawnedCalls[1].args;
  assert.ok(featArgs.includes(`sqlite_home=${JSON.stringify(userCodex)}`));
  assert.ok(featArgs.includes('allow_symlinked_codex_home=true'));
  assert.ok(!featArgs.includes('features.daemon_auto_start=false'));
  assert.equal(existsSync(join(userCodex, '.tmp', 'bundled-marketplaces')), true);
  assert.equal(existsSync(join(userCodex, '.tmp', 'marketplaces')), true);
  assert.equal(existsSync(join(userCodex, '.tmp', 'plugins')), true);

  // 3. resolveEffectiveSqliteHome preserves explicit user sqlite_home and CODEX_SQLITE_HOME.
  assert.equal(resolveEffectiveSqliteHome({ userCodexHome: userCodex, userConfigText: 'sqlite_home = "/fast-ssd/codex"\n', env: sb.env }), null);
  assert.equal(resolveEffectiveSqliteHome({ userCodexHome: userCodex, userConfigText: '', env: { ...sb.env, CODEX_SQLITE_HOME: '/fast-ssd/env' } }), null);
  assert.equal(resolveEffectiveSqliteHome({ userCodexHome: userCodex, userConfigText: 'model = "gpt-6.2-sol"\n', env: sb.env }), userCodex);

  // 4. Mirror mappings handle .tmp plugin hooks, `~/` marketplace sources, non-bare names, and non-existent macOS paths.
  const futureRt = join(sb.tmpRoot, 'future-not-yet-created-rt');
  const realFutureRt = join(realpathSync(sb.tmpRoot), 'future-not-yet-created-rt');
  const complexCfg = [
    'model_provider = "openrouter"',
    'sqlite_home = "/custom/sqlite"',
    '',
    '[marketplaces."team.dotted"]',
    'source_type = "local"',
    'source = "~/.codex/.tmp/bundled-marketplaces/team-bundled"',
    '',
    `[hooks.state.${JSON.stringify(`${join(userCodex, '.tmp', 'bundled-marketplaces', 'p', 'hooks.json')}:session_start:0:0`)}]`,
    'trusted_hash = "sha256:tmp_plugin_hook"',
    'extra_tags = ["a", "b"]',
    '',
  ].join('\n');
  const mirrorArgs = buildCodexHomeMirrorCliArgs({
    userCodexHome: userCodex,
    runtimeCodexHome: futureRt,
    userConfigText: complexCfg,
    env: sb.env,
  });
  assert.ok(mirrorArgs.includes('allow_symlinked_codex_home=true'));
  assert.ok(mirrorArgs.some(a => a.startsWith('marketplaces={') && a.includes('"team.dotted"') && a.includes(join(realFutureRt, '.tmp', 'bundled-marketplaces', 'team-bundled'))));
  assert.ok(mirrorArgs.some(a => a.startsWith('hooks.state={') && a.includes(`${join(realFutureRt, '.tmp', 'bundled-marketplaces', 'p', 'hooks.json')}:session_start:0:0`) && a.includes('extra_tags = ["a", "b"]')));

  // 5. model_provider="openai" override respects --oss, and cross-layer repo `.codex/config.toml` legacy exclude avoids filters clash.
  writeFileSync(join(repoDir, '.codex', 'config.toml'), '[shell_environment_policy]\nexclude = ["REPO_SECRET_*"]\n');
  const gwArgs = buildCodexGatewayCliArgs({
    backendApiUrl: 'https://api.promptdriven.ai/v1/codex-gateway/backend-api',
    userCodexHome: userCodex,
    runtimeCodexHome: futureRt,
    userConfigText: complexCfg,
    cwd: repoDir,
    env: sb.env,
  });
  assert.ok(gwArgs.includes('model_provider="openai"'), 'custom user model_provider must be overridden to native openai for PDD pool');
  assert.ok(!gwArgs.some(a => a.startsWith('sqlite_home=')), 'explicit user sqlite_home must not be clobbered');
  const repoExcludeArg = gwArgs.find(a => a.startsWith('shell_environment_policy.exclude='));
  assert.ok(repoExcludeArg && repoExcludeArg.includes('"REPO_SECRET_*"') && repoExcludeArg.includes('"PDD_*"') && repoExcludeArg.includes('"CODEX_HOME"'));
  assert.ok(!gwArgs.some(a => a.startsWith('shell_environment_policy.filters=')), 'must not mix filters with repo legacy exclude');

  const ossArgs = buildCodexGatewayCliArgs({
    backendApiUrl: 'https://api.promptdriven.ai/v1/codex-gateway/backend-api',
    userCodexHome: userCodex,
    runtimeCodexHome: futureRt,
    userConfigText: complexCfg,
    codexArgs: ['--oss'],
    env: sb.env,
  });
  assert.ok(!ossArgs.includes('model_provider="openai"'), '--oss should not be overridden with model_provider=openai');

  // 6. normalizeCodexConfigWriteback rewrites runtime-dir hook/marketplace paths back to ~/.codex only when changed.
  const cfgPath = join(userCodex, 'config.toml');
  const beforeCfg = 'model = "gpt-6.2-sol"\n';
  writeFileSync(cfgPath, beforeCfg, { mode: 0o600 });
  assert.equal(normalizeCodexConfigWriteback(undefined, {}), false);
  const rtDir = mkdtempSync(join(sb.tmpRoot, 'rt-writeback-'));
  const realRtDir = realpathSync(rtDir);
  assert.equal(
    normalizeCodexConfigWriteback(await import('node:fs'), {
      userCodexHome: userCodex,
      runtimeCodexHome: rtDir,
      userConfigPath: cfgPath,
      beforeContent: beforeCfg,
    }),
    false,
    'unchanged config must not be rewritten',
  );
  const pollutedCfg = [
    'model = "gpt-6.2-sol"',
    '',
    '[marketplaces.openai-bundled]',
    'source_type = "local"',
    `source = ${JSON.stringify(join(realRtDir, '.tmp', 'bundled-marketplaces', 'openai-bundled'))}`,
    '',
    `[hooks.state.${JSON.stringify(`${join(realRtDir, 'hooks.json')}:session_start:0:0`)}]`,
    'trusted_hash = "sha256:new_trust"',
    '',
  ].join('\n');
  writeFileSync(cfgPath, pollutedCfg, { mode: 0o600 });
  const normalized = normalizeCodexConfigWriteback(await import('node:fs'), {
    userCodexHome: userCodex,
    runtimeCodexHome: rtDir,
    userConfigPath: cfgPath,
    beforeContent: beforeCfg,
  });
  assert.equal(normalized, true);
  const parsedAfter = parseToml(readFileSync(cfgPath, 'utf8'));
  assert.equal(parsedAfter.marketplaces['openai-bundled'].source, join(userCodex, '.tmp', 'bundled-marketplaces', 'openai-bundled'));
  assert.equal(parsedAfter.hooks.state[`${join(userCodex, 'hooks.json')}:session_start:0:0`]?.trusted_hash, 'sha256:new_trust');
  assert.equal(parsedAfter.hooks.state[`${join(realRtDir, 'hooks.json')}:session_start:0:0`], undefined);

  // 7. stopCodexAppServerDaemon honors PDD_CODEX_BIN.
  let seenBin = null;
  stopCodexAppServerDaemon(rtDir, {
    env: { ...sb.env, PDD_CODEX_BIN: '/custom/bin/codex-alt' },
    spawnSync: (bin) => { seenBin = bin; return { status: 0 }; },
  });
  assert.equal(seenBin, '/custom/bin/codex-alt');

  // 8. createCodexStepOverlay preserves allowlist semantics (`inherit = "none"`) when migrating include_only without filters or explicit inherit.
  writeFileSync(cfgPath, '[shell_environment_policy]\ninclude_only = ["PATH", "HOME"]\n', { mode: 0o600 });
  const ov = createCodexStepOverlay({
    delivery_mode: 'gateway_grant',
    codex_gateway_url: 'http://127.0.0.1:41999/v1/codex-gateway/lse_inc_only',
    codex_gateway_token: 'pddg_lse_inc_only_tok',
  }, { env: sb.env, tmpRoot: sb.tmpRoot });
  try {
    const ovCfg = parseToml(readFileSync(ov.configPath, 'utf8'));
    assert.equal(ovCfg.shell_environment_policy?.inherit, 'none');
    assert.equal(ovCfg.shell_environment_policy?.include_only, undefined);
    assert.equal(ovCfg.shell_environment_policy?.filters?.PATH, 'include');
    assert.equal(ovCfg.sqlite_home, userCodex, 'even non-backend-api step overlays must set sqlite_home');
    assert.equal(ovCfg.allow_symlinked_codex_home, true);
  } finally {
    ov.cleanup();
  }

  // 9. Heartbeat 404 invalidates stale shared auth.json + lease.json.
  let authAfter404 = true;
  let leaseAfter404 = true;
  const r404 = await runPddCodexCli(
    ['exec', 'check 404 heartbeat'],
    { env: sb.env, stdout: { write() {} }, stderr: { write() {} } },
    {
      tmpRoot: sb.tmpRoot,
      uid: 778,
      pid: 99202,
      isPidAlive: () => true,
      heartbeatIntervalMs: 25,
      leaseCloudAccount: async () => makeLeaseReply({ leaseId: 'lse_hb_404' }),
      releaseCloudLease: async () => ({ revoked: true }),
      heartbeatCloudLease: async () => {
        const err = new Error('not found');
        err.status = 404;
        throw err;
      },
      spawnCodex: async (_bin, _args, opts) => {
        await new Promise(r => setTimeout(r, 90));
        authAfter404 = existsSync(join(opts.env.CODEX_HOME, 'auth.json'));
        leaseAfter404 = existsSync(join(opts.env.CODEX_HOME, 'lease.json'));
        return { code: 0 };
      },
    },
  );
  assert.equal(r404.exitCode, 0);
  assert.equal(authAfter404, false, '404 heartbeat must unlink stale auth.json');
  assert.equal(leaseAfter404, false, '404 heartbeat must unlink stale lease.json');
});

test('re-review P1 & P2 regressions: symlink-safe writeback, logout --help safety, --account -- -prompt, ancestor .codex + CLI exclude merge, profile model_provider, and non-gateway sqlite_home', async t => {
  const sb = makeSandbox(t);
  const userCodex = join(sb.home, '.codex');
  mkdirSync(userCodex, { recursive: true });

  // 1. P1-1: dotfile-symlinked ~/.codex/config.toml is preserved (never replaced by regular file) on writeback normalization.
  const dotfileDir = join(sb.root, 'dotfiles');
  mkdirSync(dotfileDir, { recursive: true });
  const dotfileCfg = join(dotfileDir, 'codex-config.toml');
  writeFileSync(dotfileCfg, 'model = "gpt-5.4"\n', 'utf8');
  const userCfgLink = join(userCodex, 'config.toml');
  symlinkSync(dotfileCfg, userCfgLink);
  const fakeRuntime = join(sb.tmpRoot, 'pdd-codex-dotfile');
  mkdirSync(fakeRuntime, { recursive: true });
  const beforeCfg = readFileSync(dotfileCfg, 'utf8');
  writeFileSync(
    dotfileCfg,
    `model = "gpt-5.4"\n[marketplaces.openai-bundled]\nsource = ${JSON.stringify(join(fakeRuntime, '.tmp', 'bundled-marketplaces', 'openai-bundled'))}\n`,
    'utf8',
  );
  const normalizedDotfile = normalizeCodexConfigWriteback(
    { readFileSync, writeFileSync, renameSync, lstatSync, statSync, realpathSync, chmodSync, unlinkSync, mkdirSync },
    { userCodexHome: userCodex, runtimeCodexHome: fakeRuntime, userConfigPath: userCfgLink, beforeContent: beforeCfg },
  );
  assert.equal(normalizedDotfile, true);
  assert.equal(lstatSync(userCfgLink).isSymbolicLink(), true, 'dotfile symlink must stay a symlink');
  assert.equal(readlinkSync(userCfgLink), dotfileCfg);
  const normalizedTarget = readFileSync(dotfileCfg, 'utf8');
  assert.equal(normalizedTarget.includes(fakeRuntime), false, 'runtime path normalized in symlink target');
  assert.equal(normalizedTarget.includes(join(userCodex, '.tmp', 'bundled-marketplaces', 'openai-bundled')), true);

  // 2. P1-2: `pdd-codex logout --help`, `-h logout`, and `login --help` pass through without revoking shared leases.
  const sharedRt = sharedRuntimeDirPath({ tmpRoot: sb.tmpRoot, uid: 781 });
  mkdirSync(sharedRt, { recursive: true, mode: 0o700 });
  writeFileSync(join(sharedRt, 'auth.json'), '{"tokens":{"access_token":"keep-me"}}', { mode: 0o600 });
  writeFileSync(join(sharedRt, 'lease.json'), JSON.stringify({ lease_id: 'lse_keep_me', auto_rotate: true }), { mode: 0o600 });
  let helpRevoked = false;
  for (const argv of [['logout', '--help'], ['-h', 'logout'], ['login', '--help']]) {
    let sawSpawn = null;
    const res = await runPddCodexCli(
      argv,
      { env: sb.env, stdout: { write() {} }, stderr: { write() {} } },
      {
        tmpRoot: sb.tmpRoot,
        uid: 781,
        releaseCloudLease: async () => { helpRevoked = true; return { revoked: true }; },
        spawnCodex: async (_bin, args) => { sawSpawn = args; return { code: 0 }; },
      },
    );
    assert.equal(res.exitCode, 0);
    assert.deepEqual(sawSpawn, argv);
  }
  assert.equal(helpRevoked, false, 'logout/login --help must never revoke shared lease');
  assert.equal(existsSync(join(sharedRt, 'auth.json')), true, 'logout --help must keep auth.json');
  assert.equal(existsSync(join(sharedRt, 'lease.json')), true, 'logout --help must keep lease.json');

  // 3. P1-3: `pdd-codex --account acct1 -- -prompt` preserves `--` for positional dash prompt.
  const dashPrompt = parsePddCodexArgs(['--account', 'acct1', '--', '-prompt']);
  assert.equal(dashPrompt.preferredAccount, 'acct1');
  assert.deepEqual(dashPrompt.codexArgs, ['--', '-prompt']);

  // 4. P1-4a: ancestor `.codex/config.toml` discovery from nested subdir and via `-C <repo>` detects legacy exclude.
  const repoRoot = join(sb.root, 'monorepo');
  const nestedSubdir = join(repoRoot, 'packages', 'app');
  mkdirSync(join(repoRoot, '.git'), { recursive: true });
  mkdirSync(join(repoRoot, '.codex'), { recursive: true });
  mkdirSync(nestedSubdir, { recursive: true });
  writeFileSync(join(repoRoot, '.codex', 'config.toml'), '[shell_environment_policy]\nexclude = ["REPO_SECRET"]\n', 'utf8');
  for (const [args, cwd] of [[[], nestedSubdir], [['-C', nestedSubdir], sb.root]]) {
    const gwArgs = buildCodexGatewayCliArgs({
      backendApiUrl: 'https://api.promptdriven.ai/v1/codex-gateway/backend-api',
      userCodexHome: userCodex,
      runtimeCodexHome: fakeRuntime,
      userConfigText: 'model = "gpt-5.4"\n',
      codexArgs: args,
      cwd,
      env: sb.env,
    });
    const exFlag = gwArgs.find(a => a.startsWith('shell_environment_policy.exclude='));
    assert.ok(exFlag, `ancestor .codex/config.toml must trigger merged exclude for cwd=${cwd}`);
    assert.ok(exFlag.includes('"REPO_SECRET"') && exFlag.includes('"PDD_*"') && exFlag.includes('"CODEX_HOME"'));
    assert.equal(gwArgs.some(a => a.startsWith('shell_environment_policy.filters')), false);
  }

  // 5. P1-4b: user `-c shell_environment_policy.exclude=["FOO"]` is merged into gateway exclude and stripped so it cannot wipe out PDD_* / CODEX_HOME.
  let spawnedArgsForCliExclude = null;
  const cliExRes = await runPddCodexCli(
    ['-c', 'shell_environment_policy.exclude=["FOO"]', 'exec', 'test'],
    { env: sb.env, stdout: { write() {} }, stderr: { write() {} } },
    {
      tmpRoot: sb.tmpRoot,
      uid: 782,
      pid: 99301,
      isPidAlive: () => true,
      leaseCloudAccount: async () => makeLeaseReply({ leaseId: 'lse_cli_ex' }),
      releaseCloudLease: async () => ({ revoked: true }),
      spawnCodex: async (_bin, args) => { spawnedArgsForCliExclude = args; return { code: 0 }; },
    },
  );
  assert.equal(cliExRes.exitCode, 0);
  const excludeFlags = spawnedArgsForCliExclude.filter(a => a.startsWith('shell_environment_policy.exclude='));
  assert.equal(excludeFlags.length, 1, 'raw user -c shell_environment_policy.exclude must be stripped after merge');
  assert.ok(excludeFlags[0].includes('"FOO"') && excludeFlags[0].includes('"PDD_*"') && excludeFlags[0].includes('"CODEX_HOME"'));

  // 6. P2: `pdd-codex mcp -c foo=1 list` still runs offline without leasing, profile `model_provider` overrides to openai, and non-gateway overlay sets sqlite_home.
  let mcpFlagLeased = false;
  const mcpFlagRes = await runPddCodexCli(
    ['mcp', '-c', 'foo=1', 'list'],
    { env: sb.env, stdout: { write() {} }, stderr: { write() {} } },
    {
      tmpRoot: sb.tmpRoot,
      uid: 783,
      leaseCloudAccount: async () => { mcpFlagLeased = true; throw new Error('should not lease'); },
      spawnCodex: async () => ({ code: 0 }),
    },
  );
  assert.equal(mcpFlagRes.exitCode, 0);
  assert.equal(mcpFlagLeased, false, 'mcp -c foo=1 list must run locally without leasing');

  const profGw = buildCodexGatewayCliArgs({
    backendApiUrl: 'https://api.promptdriven.ai/v1/codex-gateway/backend-api',
    userCodexHome: userCodex,
    runtimeCodexHome: fakeRuntime,
    userConfigText: 'profile = "alt"\n[profiles.alt]\nmodel_provider = "openrouter"\n',
    env: sb.env,
  });
  assert.equal(profGw.includes('model_provider="openai"'), true, 'active profile custom model_provider must be overridden to openai');
});

test('SEC-2, REL-3, REL-4 & currentAccountId: dash --account= guard, ENOENT->127, bin entry hygiene, post-mkdir symlink check, heartbeat stopped race, exit cleanup, and seat persistence', async t => {
  const sb = makeSandbox(t);

  // 1. REL-4a: Reject dash-prefixed --account=-foo on `=` syntax just like space syntax.
  assert.throws(() => parsePddCodexArgs(['--account=-foo', 'exec', 'hi']), err => err.exitCode === 2);
  assert.throws(() => parsePddCodexArgs(['--account=--flag']), err => err.exitCode === 2);
  assert.throws(() => parsePddCodexArgs(['--account=']), err => err.exitCode === 2);

  // 2. REL-3: bin/pdd-codex.mjs and bin/pdd-claude.mjs use .then(...) + process.exitCode (no top-level await or hard process.exit).
  for (const binFile of ['bin/pdd-codex.mjs', 'bin/pdd-claude.mjs']) {
    const src = readFileSync(join(process.cwd(), binFile), 'utf8');
    assert.doesNotMatch(src, /^\s*await\s+/m, `${binFile} must not use top-level await`);
    assert.doesNotMatch(src, /\bprocess\.exit\s*\(/, `${binFile} must use process.exitCode instead of process.exit()`);
  }
  const helpRun = spawnSync(process.execPath, [join(process.cwd(), 'bin', 'pdd-codex.mjs'), '--pdd-help'], {
    env: sb.env,
    encoding: 'utf8',
  });
  assert.equal(helpRun.status, 0, helpRun.stderr);
  assert.match(helpRun.stdout, /pdd-codex/);

  // 3. REL-4c: ENOENT when spawning codex returns exit code 127.
  let errOut = '';
  const enoentRes = await runPddCodexCli(
    ['--version'],
    { env: { ...sb.env, PDD_CODEX_BIN: join(sb.root, 'definitely-missing-codex-bin') }, stdout: { write() {} }, stderr: { write: s => { errOut += s; } } },
  );
  assert.equal(enoentRes.exitCode, 127);
  assert.match(errOut, /Failed to start .*ENOENT/i);

  // 4. SEC-2: Reject symlinked runtime root AND post-mkdirSync symlink swap race.
  const symRoot = join(sb.root, 'symlink-runtime-root');
  symlinkSync(sb.tmpRoot, symRoot);
  await assert.rejects(
    () => acquireSharedRuntimeSession(
      { cwd: sb.root, env: { ...sb.env, PDD_CODEX_RUNTIME_ROOT: symRoot } },
      { uid: 790, leaseCloudAccount: async () => makeLeaseReply({ leaseId: 'lse_sym' }) },
    ),
    /Refusing unsafe PDD Codex runtime/,
  );

  const raceTarget = join(sb.root, 'race-real-target');
  mkdirSync(raceTarget, { recursive: true, mode: 0o700 });
  const raceDir = sharedRuntimeDirPath({ env: sb.env, tmpRoot: sb.tmpRoot, uid: 791 });
  const nativeFs = await import('node:fs');
  const raceFs = {
    ...nativeFs,
    mkdirSync(p, opts) {
      if (resolve(p) === resolve(raceDir)) {
        nativeFs.symlinkSync(raceTarget, p);
        return undefined;
      }
      return nativeFs.mkdirSync(p, opts);
    },
  };
  await assert.rejects(
    () => acquireSharedRuntimeSession(
      { cwd: sb.root, env: sb.env },
      { fs: raceFs, uid: 791, leaseCloudAccount: async () => makeLeaseReply({ leaseId: 'lse_race' }) },
    ),
    /Refusing unsafe PDD Codex runtime/,
  );
  rmSync(raceDir, { force: true });

  // 5. REL-4d: startLeaseHeartbeat guards `if (stopped) return;` inside the lock on 401/403/404.
  const hbDir = join(sb.root, 'hb-stop-race');
  mkdirSync(hbDir, { recursive: true, mode: 0o700 });
  const hbLeasePath = join(hbDir, 'lease.json');
  writeFileSync(hbLeasePath, JSON.stringify({ lease_id: 'lse_hb_1', expires_at: new Date(Date.now() + 3600_000).toISOString() }), { mode: 0o600 });
  let rejectBeat = null;
  let clearedCount = 0;
  const stopHb = startLeaseHeartbeat({
    initialLeaseId: 'lse_hb_1',
    leasePath: hbLeasePath,
    runtimeDir: hbDir,
    shared: true,
    intervalMs: 10,
    heartbeatFn: () => new Promise((_res, rej) => { rejectBeat = rej; }),
    onInvalidated: () => { clearedCount += 1; },
  });
  await new Promise(r => setTimeout(r, 30));
  assert.equal(typeof rejectBeat, 'function', 'heartbeat request started');
  stopHb();
  rejectBeat(new CloudAccountsError('gone', { status: 404 }));
  await new Promise(r => setTimeout(r, 30));
  assert.equal(clearedCount, 0, '404 arriving after stop() must not run onInvalidated cleanup');
  assert.equal(existsSync(hbLeasePath), true);

  // 6. REL-4b: registerProcessCleanupHooks cleans up synchronously on process exit event.
  const pinFile = join(sb.root, 'exit-pin-file');
  writeFileSync(pinFile, '1', { mode: 0o600 });
  const fakeProc = new (await import('node:events')).EventEmitter();
  const unregister = registerProcessCleanupHooks({
    onEmergencyExit: () => { rmSync(pinFile, { force: true }); },
    onSignal: () => {},
    proc: fakeProc,
  });
  fakeProc.emit('exit', 0);
  assert.equal(existsSync(pinFile), false, 'emergency exit hook removed tracked runtime artifact');
  unregister();

  // 7. currentAccountId propagation: shared session forwards active ready Codex seat from accounts-state.json
  //    and refreshes an unreferenced stale seat after `use`/`next`, while pinned mode sends currentAccountId: null.
  const seatEnv = { ...sb.env, PDD_STATE_DIR: join(sb.root, 'state-seat') };
  writeCloudAccountsState({
    enrolled: true,
    providers: ['codex'],
    active: { codex: { account_id: 'acc_seat_A', label: 'seat-a', provider: 'codex', state: 'ready' } },
  }, { env: seatEnv });

  const seenCurrentIds = [];
  const sessA = await acquireSharedRuntimeSession(
    { cwd: sb.root, env: seatEnv },
    {
      tmpRoot: sb.tmpRoot,
      uid: 792,
      pid: 44101,
      isPidAlive: p => p === 44101,
      leaseCloudAccount: async req => {
        seenCurrentIds.push(req.currentAccountId);
        return {
          ...makeLeaseReply({ leaseId: `lse_${req.currentAccountId ?? 'none'}` }),
          account: { account_id: req.currentAccountId ?? 'acc_default', label: 'seat-a', provider: 'codex', plan_type: 'pro' },
        };
      },
    },
  );
  assert.equal(seenCurrentIds[0], 'acc_seat_A', 'shared lease must propagate active ready seat from accounts-state.json');

  // Simulate user switching seat via `pdd accounts use seat-b` while previous session crashed (dead PID 44101).
  writeCloudAccountsState({
    enrolled: true,
    providers: ['codex'],
    active: { codex: { account_id: 'acc_seat_B', label: 'seat-b', provider: 'codex', state: 'ready' } },
  }, { env: seatEnv });

  const sessB = await acquireSharedRuntimeSession(
    { cwd: sb.root, env: seatEnv },
    {
      tmpRoot: sb.tmpRoot,
      uid: 792,
      pid: 44102,
      isPidAlive: p => p === 44102,
      leaseCloudAccount: async req => {
        seenCurrentIds.push(req.currentAccountId);
        return {
          ...makeLeaseReply({ leaseId: `lse_${req.currentAccountId ?? 'none'}` }),
          account: { account_id: req.currentAccountId ?? 'acc_default', label: 'seat-b', provider: 'codex', plan_type: 'pro' },
        };
      },
    },
  );
  assert.equal(seenCurrentIds[1], 'acc_seat_B', 'unreferenced stale lease from another seat must re-lease the newly selected active seat');
  assert.equal(sessB.reused, false);
  await releaseSharedRuntimeSession(sessB.runtimeDir, { cwd: sb.root, env: seatEnv }, {
    pid: 44102,
    isPidAlive: () => false,
    releaseCloudLease: async () => ({ revoked: true }),
    spawnSync: () => ({ status: 0 }),
  });
  assert.ok(sessA.runtimeDir === sessB.runtimeDir);

  let pinnedCurrentId = 'unset';
  const pinnedSess = await acquirePinnedRuntimeSession('seat-a', { cwd: sb.root, env: seatEnv }, {
    tmpRoot: sb.tmpRoot,
    uid: 792,
    leaseCloudAccount: async req => {
      pinnedCurrentId = req.currentAccountId;
      return makeLeaseReply({ leaseId: 'lse_pin_seat', autoRotate: false });
    },
  });
  assert.equal(pinnedCurrentId, null, 'pinned session must pass currentAccountId: null');
  rmSync(pinnedSess.runtimeDir, { recursive: true, force: true });
});

test('PDD_CODEX_AUTO_FAIL_OPEN=1 matches pdd-claude fail-open contract, strips PDD_* in child env, and consolidates #3531 gateway endpoints', async t => {
  const sb = makeSandbox(t);
  const stateDir = join(sb.root, 'state');
  mkdirSync(stateDir, { recursive: true, mode: 0o700 });
  const autoEnv = {
    ...sb.env,
    PDD_STATE_DIR: stateDir,
    PDD_CODEX_AUTO_FAIL_OPEN: '1',
    PDD_TOKEN: 'pdd_secret_token_should_strip',
    PDD_CUSTOM_VAR: 'custom_secret_should_strip',
  };

  const calls = [];
  const captureSpawn = async (bin, args, opts) => {
    calls.push({ bin, args, env: opts.env });
    return { exitCode: 0 };
  };
  const quietStreams = { stdout: { write() {} }, stderr: { write() {} } };

  // 1. Unenrolled/inactive pool -> passes straight to stock codex with ALL PDD_* vars stripped.
  const rUnenrolled = await runPddCodexCli(['exec', 'hello'], { cwd: sb.root, env: autoEnv, ...quietStreams }, {
    spawnCodex: captureSpawn,
  });
  assert.equal(rUnenrolled.exitCode, 0);
  assert.deepEqual(calls.at(-1).args, ['exec', 'hello']);
  assert.deepEqual(Object.keys(calls.at(-1).env).filter(k => k.startsWith('PDD_')), [], 'unenrolled fail-open must strip ALL PDD_* vars');

  // 1b. Pass-through commands (--version) also strip ALL PDD_* vars even when autoFailOpen is false!
  const rVersion = await runPddCodexCli(['--version'], { cwd: sb.root, env: { ...autoEnv, PDD_CODEX_AUTO_FAIL_OPEN: '0' }, ...quietStreams }, {
    spawnCodex: captureSpawn,
  });
  assert.equal(rVersion.exitCode, 0);
  assert.deepEqual(Object.keys(calls.at(-1).env).filter(k => k.startsWith('PDD_')), [], 'pass-through must strip ALL PDD_* vars');

  // 2. logout / login (without status) under auto-wrapper -> passes straight to stock codex with ALL PDD_* stripped.
  const rLogout = await runPddCodexCli(['logout'], { cwd: sb.root, env: autoEnv, ...quietStreams }, {
    spawnCodex: captureSpawn,
  });
  assert.equal(rLogout.exitCode, 0);
  assert.deepEqual(calls.at(-1).args, ['logout']);
  assert.deepEqual(Object.keys(calls.at(-1).env).filter(k => k.startsWith('PDD_')), []);

  const rLogin = await runPddCodexCli(['login', '--device-auth'], { cwd: sb.root, env: autoEnv, ...quietStreams }, {
    spawnCodex: captureSpawn,
  });
  assert.equal(rLogin.exitCode, 0);
  assert.deepEqual(calls.at(-1).args, ['login', '--device-auth']);
  assert.deepEqual(Object.keys(calls.at(-1).env).filter(k => k.startsWith('PDD_')), []);

  // 3. Transient / 401 / 503 / all_cooling / network fetch errors under auto-wrapper -> fail open cleanly,
  //    strip ALL PDD_* vars, AND never touch/create ~/.codex baseline on a fresh HOME!
  const freshFailOpenHome = join(sb.root, 'fresh-fo-home');
  mkdirSync(freshFailOpenHome, { recursive: true, mode: 0o700 });
  const freshAutoEnv = { ...autoEnv, HOME: freshFailOpenHome };
  const fetchErr = new TypeError('fetch failed');
  fetchErr.cause = { code: 'ECONNREFUSED' };
  for (const err of [
    new CloudAccountsError('network down', { code: 'network_error', status: 0 }),
    new CloudAccountsError('expired gh auth', { code: 'unauthorized', status: 401 }),
    new CloudAccountsError('gateway 503', { code: 'service_unavailable', status: 503 }),
    new CloudAccountsError('all cooling', { code: 'all_cooling', status: 429 }),
    fetchErr,
  ]) {
    const rErr = await runPddCodexCli(['exec', 'fallback'], { cwd: sb.root, env: freshAutoEnv, ...quietStreams }, {
      tmpRoot: sb.tmpRoot,
      uid: 793,
      spawnCodex: captureSpawn,
      leaseCloudAccount: async () => { throw err; },
    });
    assert.equal(rErr.exitCode, 0);
    assert.deepEqual(calls.at(-1).args, ['exec', 'fallback']);
    assert.deepEqual(Object.keys(calls.at(-1).env).filter(k => k.startsWith('PDD_')), [], 'fail-open spawn must strip ALL PDD_* vars');
  }
  assert.equal(existsSync(join(freshFailOpenHome, '.codex')), false, 'fail-open lease failure must never create or mutate ~/.codex baseline');

  // 4. Explicit --account <label> disables auto fail-open; real production security/config codes,
  //    reauth_required Cloud replies, AND plain uncoded Error ALWAYS fail closed!
  let errOut = '';
  const rPinnedErr = await runPddCodexCli(
    ['--account', 'work', 'exec', 'strict'],
    { cwd: sb.root, env: autoEnv, stdout: { write() {} }, stderr: { write: s => { errOut += s; } } },
    {
      tmpRoot: sb.tmpRoot,
      uid: 793,
      spawnCodex: captureSpawn,
      leaseCloudAccount: async () => { throw new CloudAccountsError('offline', { code: 'network_error', status: 0 }); },
    },
  );
  assert.equal(rPinnedErr.exitCode, 1);
  assert.match(errOut, /offline/);

  const callsBeforeClosed = calls.length;
  for (const closedErr of [
    new CloudAccountsError('unsafe runtime dir', { code: 'unsafe_runtime_dir' }),
    new CloudAccountsError('symlink refused', { code: 'symlink_refused' }),
    new CloudAccountsError('invalid settings', { code: 'invalid_settings' }),
    new CloudAccountsError('invalid lease', { code: 'invalid_lease' }),
    new CloudAccountsError('reauth required', { code: 'reauth_required' }),
    new Error('uncoded state-dir error'),
  ]) {
    const rClosed = await runPddCodexCli(['exec', 'must-fail-closed'], { cwd: sb.root, env: autoEnv, ...quietStreams }, {
      tmpRoot: sb.tmpRoot,
      uid: 793,
      spawnCodex: captureSpawn,
      leaseCloudAccount: async () => { throw closedErr; },
    });
    assert.equal(rClosed.exitCode, 1, `fail-closed error (${closedErr.code || closedErr.message}) must NEVER fail open`);
  }

  // Cloud lease reply reporting state: 'reauth_required' (or reauth_required account) fails closed and is NOT collapsed into no_account_available!
  let reauthErrText = '';
  const rReauthReply = await runPddCodexCli(
    ['exec', 'reauth-reply'],
    { cwd: sb.root, env: autoEnv, stdout: { write() {} }, stderr: { write: s => { reauthErrText += s; } } },
    {
      tmpRoot: sb.tmpRoot,
      uid: 793,
      spawnCodex: captureSpawn,
      leaseCloudAccount: async () => ({ state: 'reauth_required', account: { label: 'work-codex', state: 'reauth_required' } }),
    },
  );
  assert.equal(rReauthReply.exitCode, 1);
  assert.match(reauthErrText, /requires re-authentication/i);
  assert.equal(calls.length, callsBeforeClosed, 'fail-closed cases must never spawn stock codex');

  // 5. Normal leased child env strips ALL PDD_* variables!
  const rLeased = await runPddCodexCli(['exec', 'clean-env'], { cwd: sb.root, env: autoEnv, ...quietStreams }, {
    tmpRoot: sb.tmpRoot,
    uid: 793,
    pid: 45101,
    isPidAlive: p => p === 45101,
    heartbeatIntervalMs: 0,
    spawnSync: () => ({ status: 0 }),
    spawnCodex: captureSpawn,
    leaseCloudAccount: async () => makeLeaseReply({ leaseId: 'lse_clean_env' }),
    releaseCloudLease: async () => ({ revoked: true }),
  });
  assert.equal(rLeased.exitCode, 0);
  const childEnvKeys = Object.keys(calls.at(-1).env);
  assert.deepEqual(childEnvKeys.filter(k => k.startsWith('PDD_')), [], 'child env must contain zero PDD_* vars');

  // 6. Consolidated #3531 endpoint builder handles native /backend-api and legacy fallback identically.
  const nativeEp = resolveCodexGatewayEndpoints({
    codex_gateway_url: 'https://api.promptdriven.ai/v1/codex-gateway/lse_abc',
    codex_backend_api_url: 'https://api.promptdriven.ai/v1/codex-gateway/backend-api/',
    codex_gateway_token: 'pddg_lse_abc_secret',
  });
  assert.equal(nativeEp.nativeBackendApi, true);
  assert.equal(nativeEp.backendApiUrl, 'https://api.promptdriven.ai/v1/codex-gateway/backend-api');
  assert.equal(nativeEp.codexApiUrl, 'https://api.promptdriven.ai/v1/codex-gateway/backend-api/codex');
  assert.equal(nativeEp.embeddedLeaseGrant, true);

  const legacyEp = resolveCodexGatewayEndpoints({
    codex_gateway_url: 'https://api.promptdriven.ai/v1/codex-gateway/lse_abc/',
    codex_gateway_token: 'pddg_lse_abc_secret',
  });
  assert.equal(legacyEp.nativeBackendApi, false);
  assert.equal(legacyEp.backendApiUrl, 'https://api.promptdriven.ai/v1/codex-gateway');
  assert.equal(legacyEp.codexApiUrl, 'https://api.promptdriven.ai/v1/codex-gateway');

  // 7. Direct import of src/accounts/toml-codec.mjs without parser registration throws loudly (never swallows as null).
  const unreg = spawnSync(process.execPath, [
    '--input-type=module',
    '-e',
    "import { parseCodexTomlQuiet } from './src/accounts/toml-codec.mjs'; try { parseCodexTomlQuiet('model = \"x\"'); process.exit(1); } catch (e) { process.exit(e?.code === 'toml_parser_unregistered' ? 0 : 2); }",
  ], { cwd: process.cwd(), encoding: 'utf8' });
  assert.equal(unreg.status, 0, `expected toml_parser_unregistered throw, got status=${unreg.status} stderr=${unreg.stderr}`);
});





