import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { EventEmitter } from 'node:events';
import { spawnSync } from 'node:child_process';
import {
  existsSync,
  lstatSync,
  mkdirSync,
  mkdtempSync,
  readdirSync,
  readFileSync,
  rmSync,
  statSync,
  symlinkSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import {
  acquirePinnedClaudeRuntimeSession,
  acquireSharedClaudeRuntimeSession,
  buildPddClaudeChildEnv,
  extractAndParseUserClaudeSettings,
  injectClaudeSettingsArg,
  inspectClaudeInvocation,
  logoutSharedClaudeRuntime,
  parsePddClaudeArgs,
  releasePinnedClaudeRuntimeSession,
  releaseSharedClaudeRuntimeSession,
  runPddClaudeCli,
  sharedClaudeRuntimeDir,
  spliceClaudeExtraArgs,
  startClaudeLeaseHeartbeat,
  withClaudeRuntimeLock,
} from '../src/pdd-claude.mjs';
import { renderAutoSwitchBlock } from '../src/accounts-cli.mjs';
import {
  buildClaudeGatewaySettingsOverlay,
  buildClaudeStepEnv,
  CloudAccountsError,
  claudeTokenFingerprint,
  isAuthFailureMessage,
  isReauthRequiredAccount,
  isReauthRequiredFailure,
  managedClaudeSettingsPath,
  materializeLocalClaudeAuth,
  prepareCloudStepExecution,
  restoreLocalClaudeGatewayConfig,
  writeCloudAccountsState,
} from '../src/login-pool.mjs';

function makeSandbox() {
  const root = mkdtempSync(join(tmpdir(), 'pdd-claude-test-'));
  const home = join(root, 'home');
  const state = join(root, 'state');
  const runtime = join(root, 'runtime');
  mkdirSync(home, { recursive: true });
  mkdirSync(state, { recursive: true });
  return {
    root,
    home,
    state,
    runtime,
    env: {
      HOME: home,
      PATH: process.env.PATH || '',
      PDD_STATE_DIR: state,
      PDD_CLAUDE_RUNTIME_ROOT: runtime,
    },
    cleanup() {
      rmSync(root, { recursive: true, force: true });
    },
  };
}

function makeFakeLeaseReply({
  leaseId = 'lse_cl_shared_001',
  accountId = 'acc_cl_1',
  label = 'cl-1',
  grant = 'pddg_lse_cl_shared_001_secret_token_value',
  autoRotate = true,
  expiresAt = new Date(Date.now() + 60 * 60 * 1000).toISOString(),
} = {}) {
  return {
    state: 'leased',
    account: { account_id: accountId, label, provider: 'claude', state: 'ready' },
    lease: {
      lease_id: leaseId,
      delivery_mode: 'gateway_grant',
      anthropic_base_url: `https://api.example.test/v1/claude-gateway/${leaseId}`,
      claude_oauth_token: grant,
      gateway_bearer_token: grant,
      expires_at: expiresAt,
      auto_rotate: autoRotate,
    },
  };
}

function fakeSpawnSuccess(capture) {
  return (cmd, args, opts) => {
    const entry = { cmd, args: [...args], env: { ...opts.env }, cwd: opts.cwd };
    const idx = args.indexOf('--settings');
    if (idx !== -1 && args[idx + 1] && existsSync(args[idx + 1])) {
      entry.settingsMode = statSync(args[idx + 1]).mode & 0o777;
      entry.settingsContent = JSON.parse(readFileSync(args[idx + 1], 'utf8'));
    }
    capture.push(entry);
    const child = new EventEmitter();
    queueMicrotask(() => child.emit('close', 0, null));
    return child;
  };
}

test('parsePddClaudeArgs & inspectClaudeInvocation handle flags, -- prompts, offline subcommands, and auth hints', () => {
  assert.deepEqual(parsePddClaudeArgs(['--account', 'cl-1', '-p', 'hi']), {
    preferredAccount: 'cl-1',
    showPddHelp: false,
    claudeArgs: ['-p', 'hi'],
  });
  assert.deepEqual(parsePddClaudeArgs(['--account=cl-2', '--', '-prompt-with-dash']), {
    preferredAccount: 'cl-2',
    showPddHelp: false,
    claudeArgs: ['--', '-prompt-with-dash'],
  });
  assert.deepEqual(parsePddClaudeArgs(['--', '-prompt']), {
    preferredAccount: null,
    showPddHelp: false,
    claudeArgs: ['--', '-prompt'],
  });
  assert.deepEqual(parsePddClaudeArgs(['--account', 'cl-1', '--', '--model', 'opus']), {
    preferredAccount: 'cl-1',
    showPddHelp: false,
    claudeArgs: ['--model', 'opus'],
  });
  assert.throws(() => parsePddClaudeArgs(['--account']), /Missing value for --account/);

  assert.equal(inspectClaudeInvocation(['--help']).mode, 'pass_through');
  assert.equal(inspectClaudeInvocation(['-v']).mode, 'pass_through');
  assert.equal(inspectClaudeInvocation(['logout', '--help']).mode, 'pass_through');
  assert.equal(inspectClaudeInvocation(['logout']).mode, 'logout');
  assert.equal(inspectClaudeInvocation(['login']).mode, 'login_hint');
  assert.equal(inspectClaudeInvocation(['setup-token']).mode, 'login_hint');
  assert.equal(inspectClaudeInvocation(['auth', 'login']).mode, 'login_hint');
  assert.equal(inspectClaudeInvocation(['auth', 'logout']).mode, 'login_hint');
  assert.equal(inspectClaudeInvocation(['auth', 'status']).mode, 'pass_through');
  assert.equal(inspectClaudeInvocation(['mcp', 'list']).mode, 'pass_through');
  assert.equal(inspectClaudeInvocation(['plugin', 'list']).mode, 'pass_through');
  assert.equal(inspectClaudeInvocation(['doctor']).mode, 'pass_through');
  assert.equal(inspectClaudeInvocation(['--model', 'sonnet', '-p', 'hello']).mode, 'leased');
  assert.equal(inspectClaudeInvocation(['-r', '--model', 'opus']).mode, 'leased');
  assert.equal(inspectClaudeInvocation(['--bare', '-p', 'hello']).hasBareFlag, true);
});

test('extractAndParseUserClaudeSettings merges last user --settings (file or inline) and refuses invalid JSON', () => {
  const sb = makeSandbox();
  try {
    const file1 = join(sb.root, 's1.json');
    const file2 = join(sb.root, 's2.json');
    writeFileSync(file1, JSON.stringify({ model: 'haiku', env: { FROM_1: '1' } }));
    writeFileSync(file2, JSON.stringify({ model: 'opus', env: { FROM_2: '2', ANTHROPIC_API_KEY: 'bad' } }));

    const merged = extractAndParseUserClaudeSettings(
      ['--settings', file1, '--model', 'sonnet', `--settings=${file2}`, '--', '--settings', 'ignored'],
      { cwd: sb.root },
    );
    assert.deepEqual(merged.strippedArgs, ['--model', 'sonnet', '--', '--settings', 'ignored']);
    assert.deepEqual(merged.userSettings, { model: 'opus', env: { FROM_2: '2', ANTHROPIC_API_KEY: 'bad' } });

    const inline = extractAndParseUserClaudeSettings(['--settings', '{"effortLevel":"high"}', '-p', 'hi'], { cwd: sb.root });
    assert.deepEqual(inline.strippedArgs, ['-p', 'hi']);
    assert.deepEqual(inline.userSettings, { effortLevel: 'high' });

    assert.deepEqual(injectClaudeSettingsArg(['-p', 'hi', '--', '-dash'], '/tmp/s.json'), ['--settings', '/tmp/s.json', '-p', 'hi', '--', '-dash']);
    assert.throws(() => extractAndParseUserClaudeSettings(['--settings', join(sb.root, 'missing.json')], { cwd: sb.root }), /Could not read --settings/);
    assert.throws(() => extractAndParseUserClaudeSettings(['--settings', '{not-json'], { cwd: sb.root }), /Invalid JSON/);
    assert.throws(() => extractAndParseUserClaudeSettings(['--settings', '[]'], { cwd: sb.root }), /JSON object/);
  } finally {
    sb.cleanup();
  }
});

test('buildPddClaudeChildEnv strips PDD_* and Anthropic auth vars without setting CLAUDE_CODE_SUBPROCESS_ENV_SCRUB', () => {
  const childEnv = buildPddClaudeChildEnv({
    HOME: '/tmp/h',
    PATH: '/usr/bin',
    MY_USER_VAR: 'keep-me',
    CLAUDE_CONFIG_DIR: '/tmp/custom-claude',
    PDD_API_KEY: 'secret',
    PDD_CLAUDE_RUNTIME_ROOT: '/tmp/rt',
    CLAUDE_CODE_OAUTH_TOKEN: 'stale',
    ANTHROPIC_API_KEY: 'sk-ant-api03-stale',
    ANTHROPIC_AUTH_TOKEN: 'stale-auth',
    ANTHROPIC_BASE_URL: 'https://stale.example',
    CLAUDE_CODE_USE_BEDROCK: '1',
    CLAUDE_CODE_USE_VERTEX: '1',
    CLAUDE_CODE_USE_FOUNDRY: '1',
  });
  assert.equal(childEnv.HOME, '/tmp/h');
  assert.equal(childEnv.MY_USER_VAR, 'keep-me');
  assert.equal(childEnv.CLAUDE_CONFIG_DIR, '/tmp/custom-claude');
  assert.equal(childEnv.PDD_API_KEY, undefined);
  assert.equal(childEnv.PDD_CLAUDE_RUNTIME_ROOT, undefined);
  assert.equal(childEnv.CLAUDE_CODE_OAUTH_TOKEN, undefined);
  assert.equal(childEnv.ANTHROPIC_API_KEY, undefined);
  assert.equal(childEnv.ANTHROPIC_AUTH_TOKEN, undefined);
  assert.equal(childEnv.ANTHROPIC_BASE_URL, undefined);
  assert.equal(childEnv.CLAUDE_CODE_USE_BEDROCK, undefined);
  assert.equal(childEnv.CLAUDE_CODE_SUBPROCESS_ENV_SCRUB, undefined);
});

test('shared pdd-claude sessions reuse 1 lease across concurrent windows, clean up on last exit, and never mutate ~/.claude/settings.json', async () => {
  const sb = makeSandbox();
  try {
    mkdirSync(join(sb.home, '.claude'), { recursive: true });
    const personalSettingsPath = join(sb.home, '.claude', 'settings.json');
    writeFileSync(personalSettingsPath, JSON.stringify({
      theme: 'dark',
      apiKeyHelper: 'echo personal-key',
      env: {
        CUSTOM_USER_VAR: 'keep',
        CLAUDE_CODE_OAUTH_TOKEN: 'sk-ant-oat01-user-personal-untouched',
        CLAUDE_CODE_USE_BEDROCK: '1',
      },
    }, null, 2));
    const beforePersonal = readFileSync(personalSettingsPath, 'utf8');

    let leaseCalls = 0;
    const released = [];
    const alivePids = new Set([5001, 5002]);
    const ports = {
      uid: 1000,
      isPidAlive: pid => alivePids.has(pid),
      leaseCloudAccount: async req => {
        leaseCalls += 1;
        assert.equal(req.provider, 'claude');
        assert.equal(req.autoRotate, true);
        return makeFakeLeaseReply();
      },
      releaseCloudLease: async id => {
        released.push(id);
      },
    };

    const s1 = await acquireSharedClaudeRuntimeSession({ cwd: sb.root, env: sb.env, pid: 5001, userSettings: { model: 'opus' } }, ports);
    const s2 = await acquireSharedClaudeRuntimeSession({ cwd: sb.root, env: sb.env, pid: 5002, userSettings: { model: 'sonnet' } }, ports);
    assert.equal(leaseCalls, 1, 'concurrent pdd-claude sessions share 1 lease');
    assert.equal(s1.reused, false);
    assert.equal(s2.reused, true);
    assert.notEqual(s1.settingsPath, s2.settingsPath, 'each session gets its own merged 0600 settings file');
    assert.equal(statSync(s1.settingsPath).mode & 0o777, 0o600);
    const cfg1 = JSON.parse(readFileSync(s1.settingsPath, 'utf8'));
    assert.equal(cfg1.model, 'opus');
    assert.equal(cfg1.apiKeyHelper, '');
    assert.equal(cfg1.env.CLAUDE_CODE_OAUTH_TOKEN, 'pddg_lse_cl_shared_001_secret_token_value');
    assert.equal(cfg1.env.ANTHROPIC_API_KEY, '');
    assert.equal(cfg1.env.CLAUDE_CODE_USE_BEDROCK, '0');

    // Personal ~/.claude/settings.json is 100% untouched!
    assert.equal(readFileSync(personalSettingsPath, 'utf8'), beforePersonal);

    // First session exits -> removes its settings file only, lease stays alive for s2.
    alivePids.delete(5001);
    const r1 = await releaseSharedClaudeRuntimeSession(s1, { cwd: sb.root, env: sb.env }, ports);
    assert.equal(r1.releasedLeaseId, null);
    assert.equal(existsSync(s1.settingsPath), false);
    assert.equal(existsSync(s1.leasePath), true);
    assert.deepEqual(released, []);

    // Last session exits -> removes lease.json + settings file and revokes cloud lease.
    alivePids.delete(5002);
    const r2 = await releaseSharedClaudeRuntimeSession(s2, { cwd: sb.root, env: sb.env }, ports);
    assert.equal(r2.releasedLeaseId, 'lse_cl_shared_001');
    assert.equal(existsSync(s2.settingsPath), false);
    assert.equal(existsSync(s2.leasePath), false);
    assert.deepEqual(released, ['lse_cl_shared_001']);
    assert.equal(readFileSync(personalSettingsPath, 'utf8'), beforePersonal);
  } finally {
    sb.cleanup();
  }
});

test('pinned --account, logout, heartbeat 404 cleanup, stale lock recovery, and symlink rejection work safely', async () => {
  const sb = makeSandbox();
  try {
    const released = [];
    const pinned = await acquirePinnedClaudeRuntimeSession({
      preferredAccount: 'team-claude',
      cwd: sb.root,
      env: sb.env,
      pid: 6001,
    }, {
      leaseCloudAccount: async req => {
        assert.equal(req.preferredLabel, 'team-claude');
        assert.equal(req.autoRotate, false);
        return makeFakeLeaseReply({ leaseId: 'lse_pin_99', autoRotate: false });
      },
    });
    assert.equal(pinned.lease.auto_rotate, false);
    assert.equal(existsSync(pinned.settingsPath), true);
    await releasePinnedClaudeRuntimeSession(pinned, { cwd: sb.root, env: sb.env }, {
      releaseCloudLease: async id => released.push(id),
    });
    assert.equal(existsSync(pinned.runtimeDir), false);
    assert.deepEqual(released, ['lse_pin_99']);

    // Shared logout cleans lease.json + legacy pddg_* from ~/.claude/settings.json without touching personal keys.
    mkdirSync(join(sb.home, '.claude'), { recursive: true });
    const personalPath = join(sb.home, '.claude', 'settings.json');
    writeFileSync(personalPath, JSON.stringify({
      theme: 'light',
      env: {
        CLAUDE_CODE_OAUTH_TOKEN: 'pddg_legacy_token',
        ANTHROPIC_BASE_URL: 'https://pdd-byok-api-c437voydwa-uc.a.run.app/v1/claude-gateway/lse_old',
      },
    }, null, 2));
    const shared = await acquireSharedClaudeRuntimeSession({ cwd: sb.root, env: sb.env, pid: process.pid }, {
      uid: 1000,
      leaseCloudAccount: async () => makeFakeLeaseReply({ leaseId: 'lse_shared_logout' }),
    });
    // Acquisition itself already cleaned legacy pddg_* from ~/.claude/settings.json!
    const afterAcquire = JSON.parse(readFileSync(personalPath, 'utf8'));
    assert.equal(afterAcquire.theme, 'light');
    assert.equal(afterAcquire.env, undefined);

    const logoutRes = await logoutSharedClaudeRuntime({ cwd: sb.root, env: sb.env }, {
      uid: 1000,
      releaseCloudLease: async id => released.push(id),
    });
    assert.equal(logoutRes.revokedLeaseId, 'lse_shared_logout');
    assert.equal(existsSync(shared.leasePath), false);
    assert.ok(released.includes('lse_shared_logout'));

    // Heartbeat 404 clears dead lease.json cleanly.
    const hbSess = await acquireSharedClaudeRuntimeSession({ cwd: sb.root, env: sb.env, pid: process.pid }, {
      uid: 1000,
      leaseCloudAccount: async () => makeFakeLeaseReply({ leaseId: 'lse_hb_404' }),
    });
    let beatCount = 0;
    const stopHb = startClaudeLeaseHeartbeat(hbSess, { cwd: sb.root, env: sb.env }, {
      heartbeatIntervalMs: 15,
      now: () => Date.now() + 60 * 60 * 1000,
      heartbeatCloudLease: async () => {
        beatCount += 1;
        const err = new Error('not found');
        err.status = 404;
        throw err;
      },
    });
    await new Promise(r => setTimeout(r, 80));
    stopHb();
    assert.equal(beatCount, 1);
    assert.equal(existsSync(hbSess.leasePath), false);

    // Dead-owner stale lock recovery works cleanly.
    const rtDir = sharedClaudeRuntimeDir(sb.env, 1000);
    const lockDir = join(rtDir, '.lock');
    mkdirSync(lockDir, { recursive: true });
    writeFileSync(join(lockDir, 'owner.json'), JSON.stringify({ pid: 999999, lockToken: 'dead', acquiredAt: Date.now() - 5000 }));
    let ranUnderLock = false;
    await withClaudeRuntimeLock(rtDir, async () => {
      ranUnderLock = true;
    }, { isPidAlive: () => false });
    assert.equal(ranUnderLock, true);
    assert.equal(existsSync(lockDir), false);

    // Symlinked runtime directory is refused.
    const symlinkRoot = join(sb.root, 'sym-runtime');
    symlinkSync(sb.state, symlinkRoot);
    await assert.rejects(
      () => acquireSharedClaudeRuntimeSession({ cwd: sb.root, env: { ...sb.env, PDD_CLAUDE_RUNTIME_ROOT: symlinkRoot } }, {
        uid: 1000,
        leaseCloudAccount: async () => makeFakeLeaseReply(),
      }),
      /Refusing unsafe pdd-claude runtime path/,
    );
  } finally {
    sb.cleanup();
  }
});

test('runPddClaudeCli end-to-end: merges --settings, routes offline commands without lease, and cleans session file', async () => {
  const sb = makeSandbox();
  try {
    const userSettingsFile = join(sb.root, 'custom.json');
    writeFileSync(userSettingsFile, JSON.stringify({ model: 'opus', env: { CUSTOM_KEY: 'yes' } }));
    const spawned = [];
    let leaseCalls = 0;
    const released = [];
    let out = '';
    let err = '';

    const ports = {
      uid: 1000,
      spawn: fakeSpawnSuccess(spawned),
      leaseCloudAccount: async () => {
        leaseCalls += 1;
        return makeFakeLeaseReply({ leaseId: 'lse_e2e_1' });
      },
      releaseCloudLease: async id => released.push(id),
    };
    const io = {
      cwd: sb.root,
      env: { ...sb.env, PDD_API_KEY: 'should-strip', USER_OK: 'keep' },
      stdout: { write: s => { out += s; } },
      stderr: { write: s => { err += s; } },
    };

    // Offline subcommand passes through without leasing or --settings
    const mcpRes = await runPddClaudeCli(['mcp', 'list'], io, ports);
    assert.equal(mcpRes.exitCode, 0);
    assert.equal(leaseCalls, 0);
    assert.deepEqual(spawned[0].args, ['mcp', 'list']);

    // Leased invocation merges user --settings and deletes temp settings file on exit
    const runRes = await runPddClaudeCli(['--settings', userSettingsFile, '-p', 'say hi'], io, ports);
    assert.equal(runRes.exitCode, 0, err);
    assert.equal(leaseCalls, 1);
    assert.equal(spawned[1].args[0], '--settings');
    const usedSettingsPath = spawned[1].args[1];
    assert.equal(existsSync(usedSettingsPath), false, 'session settings file deleted immediately on exit');
    assert.equal(spawned[1].settingsMode, 0o600);
    assert.equal(spawned[1].settingsContent.model, 'opus');
    assert.equal(spawned[1].settingsContent.env.CUSTOM_KEY, 'yes');
    assert.equal(spawned[1].settingsContent.env.CLAUDE_CODE_OAUTH_TOKEN, 'pddg_lse_cl_shared_001_secret_token_value');
    assert.equal(spawned[1].env.PDD_API_KEY, undefined);
    assert.equal(spawned[1].env.USER_OK, 'keep');
    assert.deepEqual(released, ['lse_e2e_1']);
    assert.equal(out, '');

    // Real bin/pdd-claude.mjs --pdd-help smoke check
    const binRes = spawnSync(process.execPath, [join(process.cwd(), 'bin', 'pdd-claude.mjs'), '--pdd-help'], {
      env: sb.env,
      encoding: 'utf8',
    });
    assert.equal(binRes.status, 0, binRes.stderr);
    assert.match(binRes.stdout, /pdd-claude — Launch Claude Code/);
  } finally {
    sb.cleanup();
  }
});

test('#3570 invariants: fingerprinted direct_oauth cleanup, isolated Claude step --settings overlay, and oauth_not_allowed_for_organization classification', () => {
  const sb = makeSandbox();
  try {
    mkdirSync(join(sb.home, '.claude'), { recursive: true });
    const personalPath = join(sb.home, '.claude', 'settings.json');
    const trackedDirectTok = 'sk-ant-oat01-pdd-written-legacy-direct-token-12345';
    const userDirectTok = 'sk-ant-oat01-genuinely-user-owned-token-99999';

    // 1. Tracked direct_oauth hash in accounts-state.json allows restoreLocalClaudeGatewayConfig to clean sk-ant-oat* and prune empty env!
    writeCloudAccountsState({
      enrolled: true,
      providers: ['claude'],
      active: {},
      cooling: {},
      managed_claude_token_hashes: [claudeTokenFingerprint(trackedDirectTok)],
    }, { env: sb.env });
    writeFileSync(personalPath, JSON.stringify({
      theme: 'dark',
      env: { CLAUDE_CODE_OAUTH_TOKEN: trackedDirectTok },
    }, null, 2));
    const res1 = restoreLocalClaudeGatewayConfig({ env: sb.env });
    assert.equal(res1.restoredSettings, true);
    const cleaned = JSON.parse(readFileSync(personalPath, 'utf8'));
    assert.equal(cleaned.theme, 'dark');
    assert.equal(cleaned.env, undefined, 'empty env object pruned cleanly');

    // 2. Untracked personal sk-ant-oat* token is NEVER deleted!
    writeFileSync(personalPath, JSON.stringify({
      env: { CLAUDE_CODE_OAUTH_TOKEN: userDirectTok },
    }, null, 2));
    const res2 = restoreLocalClaudeGatewayConfig({ env: sb.env });
    assert.equal(res2.restoredSettings, false);
    assert.equal(JSON.parse(readFileSync(personalPath, 'utf8')).env.CLAUDE_CODE_OAUTH_TOKEN, userDirectTok);

    // 3. prepareCloudStepExecution for claude returns disposable 0600 --settings overlay overriding ~/.claude/settings.json!
    const step = prepareCloudStepExecution(makeFakeLeaseReply(), sb.env, { tmpRoot: sb.root });
    try {
      assert.equal(step.extraArgs[0], '--settings');
      assert.equal(existsSync(step.settingsPath), true);
      assert.equal(statSync(step.settingsPath).mode & 0o777, 0o600);
      const overlay = JSON.parse(readFileSync(step.settingsPath, 'utf8'));
      assert.equal(overlay.env.CLAUDE_CODE_OAUTH_TOKEN, 'pddg_lse_cl_shared_001_secret_token_value');
      assert.equal(overlay.env.ANTHROPIC_API_KEY, '');
      assert.equal(overlay.apiKeyHelper, '');
    } finally {
      step.cleanup();
    }
    assert.equal(existsSync(step.settingsPath), false, 'step overlay cleaned up in finally');

    // 4. materializeLocalClaudeAuth writes ONLY to managedClaudeSettingsPath and never touches ~/.claude/settings.json!
    const beforeMat = readFileSync(personalPath, 'utf8');
    materializeLocalClaudeAuth(makeFakeLeaseReply().lease, { env: sb.env });
    assert.equal(readFileSync(personalPath, 'utf8'), beforeMat);
    assert.equal(existsSync(managedClaudeSettingsPath(sb.env)), true);

    // 5. oauth_not_allowed_for_organization / oauth_org_not_allowed classification in login-pool.mjs!
    assert.equal(isAuthFailureMessage('API Error: 403 oauth_not_allowed_for_organization'), true);
    assert.equal(isAuthFailureMessage('oauth_org_not_allowed'), true);
    assert.equal(isAuthFailureMessage('Your organization has disabled Claude subscription access for Claude Code'), true);
    assert.equal(isReauthRequiredFailure('oauth_not_allowed_for_organization'), true);
    assert.equal(isReauthRequiredFailure('Your organization has disabled Claude subscription access for Claude Code'), true);
    assert.equal(
      isReauthRequiredAccount({ last_refresh_error: 'Your organization has disabled Claude subscription access for Claude Code' }),
      true,
    );
    assert.equal(
      isReauthRequiredFailure(new CloudAccountsError('Your organization has disabled Claude subscription access for Claude Code', { status: 403 })),
      true,
    );
  } finally {
    sb.cleanup();
  }
});

test('adversarial P0/P1 regressions: auto fail-open, gateway URL & proxy isolation, symlink guards, CLI flag parsing, heartbeat 404 race, and read-only cleanup', async () => {
  const sb = makeSandbox();
  const makeBufStream = () => {
    const chunks = [];
    return { write: s => { chunks.push(String(s)); }, text: () => chunks.join('') };
  };
  try {
    // P0-1: auto shell wrapper bypasses auth/version/help/CLAUDE_CONFIG_DIR and passes PDD_CLAUDE_AUTO_FAIL_OPEN=1.
    const shBlock = renderAutoSwitchBlock('sh');
    const fishBlock = renderAutoSwitchBlock('fish');
    assert.match(shBlock, /CLAUDE_CONFIG_DIR/);
    assert.match(shBlock, /auth\|login\|logout\|setup-token/);
    assert.match(shBlock, /PDD_CLAUDE_AUTO_FAIL_OPEN=1 command pdd-claude/);
    assert.match(fishBlock, /PDD_CLAUDE_AUTO_FAIL_OPEN=1 command pdd-claude/);

    const failOpenCalls = [];
    const fakeSpawn = (bin, args, opts) => {
      failOpenCalls.push({ bin, args, env: opts.env });
      const child = new EventEmitter();
      process.nextTick(() => child.emit('close', 0, null));
      return child;
    };
    const autoEnv = { ...sb.env, PDD_CLAUDE_AUTO_FAIL_OPEN: '1' };
    // Unenrolled user with PDD_CLAUDE_AUTO_FAIL_OPEN=1 fails open cleanly to stock claude!
    const rUnenrolled = await runPddClaudeCli(['-p', 'hello'], { cwd: sb.root, env: autoEnv, stdout: makeBufStream(), stderr: makeBufStream() }, { spawn: fakeSpawn });
    assert.equal(rUnenrolled.exitCode, 0);
    assert.deepEqual(failOpenCalls.at(-1).args, ['-p', 'hello']);
    // Auth commands under auto-wrapper pass straight to stock claude without printing hint or revoking PDD lease!
    const rAutoAuth = await runPddClaudeCli(['--debug', 'auth', 'login'], { cwd: sb.root, env: autoEnv, stdout: makeBufStream(), stderr: makeBufStream() }, { spawn: fakeSpawn });
    assert.equal(rAutoAuth.exitCode, 0);
    assert.deepEqual(failOpenCalls.at(-1).args, ['--debug', 'auth', 'login']);
    // Lease failure under auto-wrapper fails open cleanly!
    const rLeaseErr = await runPddClaudeCli(['-p', 'hi'], { cwd: sb.root, env: autoEnv, stdout: makeBufStream(), stderr: makeBufStream() }, {
      spawn: fakeSpawn,
      leaseCloudAccount: async () => { throw new CloudAccountsError('offline', { code: 'network_error', status: 0 }); },
    });
    assert.equal(rLeaseErr.exitCode, 0);
    assert.deepEqual(failOpenCalls.at(-1).args, ['-p', 'hi']);

    // P0-2: gateway_grant validates anthropic_base_url; direct_oauth blocks third-party proxy leakage!
    assert.throws(
      () => buildClaudeGatewaySettingsOverlay({ delivery_mode: 'gateway_grant', gateway_bearer_token: 'pddg_tok', anthropic_base_url: '' }, { env: sb.env }),
      { code: 'invalid_lease' },
    );
    assert.throws(
      () => buildClaudeGatewaySettingsOverlay({ delivery_mode: 'gateway_grant', gateway_bearer_token: 'pddg_tok', anthropic_base_url: 'http://evil.example/v1' }, { env: sb.env }),
      { code: 'invalid_lease' },
    );
    assert.throws(
      () => buildClaudeGatewaySettingsOverlay({ delivery_mode: 'gateway_grant', gateway_bearer_token: 'pddg_tok', anthropic_base_url: 'https://user:pass@proxy.example/v1' }, { env: sb.env }),
      { code: 'invalid_lease' },
    );
    mkdirSync(join(sb.home, '.claude'), { recursive: true });
    writeFileSync(join(sb.home, '.claude', 'settings.json'), JSON.stringify({
      env: { ANTHROPIC_BASE_URL: 'https://third-party-proxy.example/anthropic' },
    }, null, 2));
    const directOverlay = buildClaudeGatewaySettingsOverlay(
      { delivery_mode: 'direct_oauth', claude_oauth_token: 'sk-ant-oat01-direct-lease-tok' },
      { env: sb.env, userSettings: { env: { ANTHROPIC_BASE_URL: 'https://other-proxy.example' } } },
    );
    assert.equal(directOverlay.settings.env.ANTHROPIC_BASE_URL, 'https://api.anthropic.com');
    const directStepEnv = buildClaudeStepEnv(
      { ...sb.env, ANTHROPIC_BASE_URL: 'https://ambient-proxy.example' },
      { delivery_mode: 'direct_oauth', claude_oauth_token: 'sk-ant-oat01-direct-lease-tok' },
    );
    assert.equal(directStepEnv.ANTHROPIC_BASE_URL, 'https://api.anthropic.com');

    // P0-3: logoutSharedClaudeRuntime rejects symlinked runtime root without modifying target!
    const victimDir = join(sb.root, 'victim');
    mkdirSync(join(victimDir, 'pdd-claude-1000'), { recursive: true });
    const victimFile = join(victimDir, 'pdd-claude-1000', 'lease.json');
    writeFileSync(victimFile, JSON.stringify({ lease_id: 'lse_keep' }));
    const linkRoot = join(sb.root, 'symlink-rt');
    symlinkSync(victimDir, linkRoot);
    await assert.rejects(
      () => logoutSharedClaudeRuntime({ cwd: sb.root, env: { ...sb.env, PDD_CLAUDE_RUNTIME_ROOT: linkRoot } }, { uid: 1000 }),
      { code: 'unsafe_runtime_dir' },
    );
    assert.equal(existsSync(victimFile), true, 'symlink target must remain untouched');

    // P1-1: prompt words after session flags, variadic flags, flag values after prompts, missing flags, whitespace --account, --bg!
    for (const argv of [
      ['-p', 'logout'],
      ['-p', 'doctor'],
      ['-p', 'login'],
      ['-r', 'sess-123', 'update'],
      ['-w', 'branch', 'doctor'],
      ['--add-dir', 'src', 'logs', '-p', 'check logs'],
      ['-p', 'hello', '--system-prompt', '-v'],
      ['hi', '--name', '-h'],
      ['-p', 'hello', '--system-prompt', '--bare'],
      ['--remote-control', 'doctor'],
    ]) {
      const insp = inspectClaudeInvocation(argv);
      assert.equal(insp.mode, 'leased', `expected leased for ${JSON.stringify(argv)}, got ${insp.mode}`);
      assert.equal(insp.hasBareFlag, false, `expected hasBareFlag=false for ${JSON.stringify(argv)}`);
    }
    assert.deepEqual(
      parsePddClaudeArgs(['--account', 'team-a', '--', '--safe-mode', '-p', 'hi']),
      { preferredAccount: 'team-a', showPddHelp: false, claudeArgs: ['--safe-mode', '-p', 'hi'] },
    );
    assert.throws(() => parsePddClaudeArgs(['--account', '   ', '-p', 'hi']), { code: 'invalid_args' });
    assert.throws(() => parsePddClaudeArgs(['--account=-bad', '-p', 'hi']), { code: 'invalid_args' });
    const bgErr = makeBufStream();
    const bgRes = await runPddClaudeCli(['--bg', '-p', 'hi'], { cwd: sb.root, env: sb.env, stdout: makeBufStream(), stderr: bgErr });
    assert.equal(bgRes.exitCode, 2);
    assert.match(bgErr.text(), /--bg/);

    // P1-2: --settings as value of another flag is NOT stripped; flag-aware -- scan!
    const extOther = extractAndParseUserClaudeSettings(['--system-prompt', '--settings', '-p', 'hi'], { cwd: sb.root });
    assert.equal(extOther.userSettings, null);
    assert.deepEqual(extOther.strippedArgs, ['--system-prompt', '--settings', '-p', 'hi']);
    assert.deepEqual(
      spliceClaudeExtraArgs(['--append-system-prompt', '--', '-p', 'hi'], ['--settings', '/tmp/ov.json']),
      ['--append-system-prompt', '--', '-p', 'hi', '--settings', '/tmp/ov.json'],
    );
    assert.deepEqual(
      spliceClaudeExtraArgs(['-p', '--', 'literal'], ['--settings', '/tmp/ov.json']),
      ['-p', '--settings', '/tmp/ov.json', '--', 'literal'],
    );

    // P1-3: heartbeat 404 on lse_OLD must NOT delete newer concurrent lse_NEW in lease.json!
    const hbRt = join(sb.root, 'hb-race');
    mkdirSync(hbRt, { recursive: true });
    const hbLeasePath = join(hbRt, 'lease.json');
    writeFileSync(hbLeasePath, JSON.stringify({ lease_id: 'lse_OLD', last_heartbeat_at: '2020-01-01T00:00:00Z' }));
    let beatStarted;
    const beatStartedP = new Promise(r => { beatStarted = r; });
    let failBeat;
    const stopRaceHb = startClaudeLeaseHeartbeat(
      { mode: 'shared', runtimeDir: hbRt, leasePath: hbLeasePath, pid: 7001, lease: { lease_id: 'lse_OLD' } },
      { cwd: sb.root, env: sb.env },
      {
        heartbeatIntervalMs: 10,
        heartbeatCloudLease: async id => {
          assert.equal(id, 'lse_OLD');
          beatStarted();
          await new Promise((_, rej) => { failBeat = rej; });
        },
      },
    );
    const keepAlive = setTimeout(() => {}, 5000);
    try {
      await beatStartedP;
    } finally {
      clearTimeout(keepAlive);
    }
    // Newer window replaces lease.json with lse_NEW while lse_OLD heartbeat is in flight!
    writeFileSync(hbLeasePath, JSON.stringify({ lease_id: 'lse_NEW', last_heartbeat_at: new Date().toISOString() }));
    failBeat(new CloudAccountsError('gone', { status: 404 }));
    await new Promise(r => setTimeout(r, 40));
    stopRaceHb();
    assert.equal(JSON.parse(readFileSync(hbLeasePath, 'utf8')).lease_id, 'lse_NEW', '404 for lse_OLD must never delete lse_NEW');

    // P1-4: read-only ~/.claude/settings.json fails soft on EROFS & dangling managed symlink is removed!
    const managedPath = managedClaudeSettingsPath(sb.env);
    mkdirSync(join(sb.state, 'claude-home'), { recursive: true });
    symlinkSync(join(sb.root, 'does-not-exist-target'), managedPath);
    assert.equal(lstatSync(managedPath).isSymbolicLink(), true);
    writeFileSync(join(sb.home, '.claude', 'settings.json'), JSON.stringify({
      env: { CLAUDE_CODE_OAUTH_TOKEN: 'pddg_ro_legacy' },
    }));
    const roFs = {
      ...await import('node:fs'),
      writeFileSync: () => { const e = new Error('EROFS'); e.code = 'EROFS'; throw e; },
    };
    const roRes = restoreLocalClaudeGatewayConfig({ env: sb.env }, { fs: roFs });
    assert.equal(roRes.removedManagedSettings, true, 'dangling managed symlink removed');
    assert.equal(roRes.restoredSettings, false, 'EROFS fails soft without throwing');

    // P1-6: pinned mode passes currentAccountId: null and fails fast on reauth_required!
    await assert.rejects(
      () => acquirePinnedClaudeRuntimeSession(
        { preferredAccount: 'broken-seat', cwd: sb.root, env: sb.env, pid: 7002 },
        {
          leaseCloudAccount: async req => {
            assert.equal(req.currentAccountId, null);
            return {
              ...makeFakeLeaseReply({ leaseId: 'lse_reauth', autoRotate: false }),
              account: { account_id: 'acc_bad', label: 'broken-seat', provider: 'claude', state: 'reauth_required' },
            };
          },
        },
      ),
      { code: 'reauth_required' },
    );
  } finally {
    sb.cleanup();
  }
});
