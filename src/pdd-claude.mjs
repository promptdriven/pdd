// Generated from prompts/cli/pdd-claude.prompt.md.
// Dedicated PDD Claude launcher: keeps ~/.claude/settings.json and CLAUDE_CONFIG_DIR untouched,
// passes PDD Cloud gateway auth via a per-session 0600 --settings file, shares one PID-refcounted
// cloud lease across concurrent windows, and revokes + cleans up on exit.
import { randomBytes } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import {
  CLAUDE_BOOL_FLAGS,
  CLAUDE_OPTIONAL_VALUE_FLAGS,
  CLAUDE_SESSION_ONLY_FLAGS,
  CLAUDE_VALUE_FLAGS,
  CLAUDE_VARIADIC_VALUE_FLAGS,
  extractAndParseUserClaudeSettings,
  findClaudeDoubleDashIndex,
  injectClaudeSettingsArg,
  spliceClaudeExtraArgs,
} from './accounts/claude-args.mjs';
import {
  assertSafeRuntimeDir,
  DEFAULT_HEARTBEAT_INTERVAL_MS,
  defaultIsPidAlive,
  MIN_REUSABLE_LEASE_REMAINING_MS,
  parseWrapperLeadingArgs,
  readJsonObjectQuiet,
  registerProcessCleanupHooks,
  signalToExitCode,
  spawnWrappedBinary,
  startLeaseHeartbeat,
  sweepLivePids,
  unlinkQuiet,
  withRuntimeDirLock,
  writeAtomicPrivate,
} from './accounts/runtime-session.mjs';
import {
  buildClaudeGatewaySettingsOverlay,
  CloudAccountsError,
  heartbeatCloudLease,
  isCloudAccountsActive,
  isReauthRequiredAccount,
  leaseCloudAccount,
  releaseCloudLease,
  resolvePddStateBase,
  restoreLocalClaudeGatewayConfig,
} from './login-pool.mjs';
import { redactSecrets, rememberSecrets } from './secret-redaction.mjs';

export {
  extractAndParseUserClaudeSettings,
  findClaudeDoubleDashIndex,
  injectClaudeSettingsArg,
  spliceClaudeExtraArgs,
};

const STRIPPED_CLAUDE_ENV_VARS = new Set([
  'CLAUDE_CODE_OAUTH_TOKEN',
  'ANTHROPIC_API_KEY',
  'ANTHROPIC_AUTH_TOKEN',
  'ANTHROPIC_BASE_URL',
  'CLAUDE_CODE_USE_BEDROCK',
  'CLAUDE_CODE_USE_VERTEX',
  'CLAUDE_CODE_USE_FOUNDRY',
]);

const NO_LEASE_TOP_FLAGS = new Set(['--version', '-v', '--help', '-h']);
const PASS_THROUGH_SUBCOMMANDS = new Set([
  'mcp',
  'plugin',
  'plugins',
  'doctor',
  'auto-mode',
  'update',
  'upgrade',
  'install',
  'import',
  'purge',
  'agents',
  'attach',
  'logs',
  'stop',
  'kill',
  'rm',
  'respawn',
  'gateway',
]);

const PDD_CLAUDE_HELP_TEXT = [
  'pdd-claude — Launch Claude Code through your PDD Cloud shared account pool.',
  '',
  'Usage:',
  '  pdd-claude [CLAUDE_ARGS...]',
  '  pdd-claude --account <label> [CLAUDE_ARGS...]',
  '  pdd-claude logout',
  '  pdd-claude --pdd-help',
  '',
  'Behavior:',
  '  - Never modifies your personal ~/.claude/settings.json, ~/.claude.json, or stock `claude` login.',
  '  - Keeps all your chats, plugins, skills, hooks, CLAUDE.md, MCP servers, and Claude in Chrome.',
  '  - Injects a private 0600 temporary --settings file per session and deletes it immediately on exit.',
  '  - Shares one PDD Cloud lease across concurrent windows and revokes it when the last window exits.',
  '  - Automatically rotates accounts server-side when quota or auth fails (unless --account is set).',
  '',
].join('\n');

function isKnownClaudeOrWrapperOption(token) {
  if (typeof token !== 'string' || !token) return false;
  if (token === '--' || token === '--account' || token.startsWith('--account=') || token === '--pdd-help') {
    return true;
  }
  const flagName = token.startsWith('--') && token.includes('=')
    ? token.slice(0, token.indexOf('='))
    : token;
  return NO_LEASE_TOP_FLAGS.has(flagName)
    || CLAUDE_VALUE_FLAGS.has(flagName)
    || CLAUDE_OPTIONAL_VALUE_FLAGS.has(flagName)
    || CLAUDE_BOOL_FLAGS.has(flagName);
}

/**
 * Parse optional leading `pdd-claude` wrapper flags (`--account`, `--pdd-help`) without
 * disturbing stock Claude Code flags or user prompt arguments.
 */
export function parsePddClaudeArgs(argv = []) {
  const usageMsg = 'Missing value for --account. Usage: pdd-claude --account <label> [CLAUDE_ARGS...]';
  const { preferredAccount, showPddHelp, restArgs } = parseWrapperLeadingArgs(argv, {
    isKnownOption: isKnownClaudeOrWrapperOption,
    missingMessage: usageMsg,
    missingEqMessage: usageMsg,
    missingCode: 'invalid_args',
    exitCode: 2,
  });
  return {
    preferredAccount,
    showPddHelp,
    claudeArgs: restArgs,
  };
}

/**
 * Classify Claude Code CLI arguments so help, version, offline subcommands, and auth
 * commands route cleanly without waiting on a Cloud lease or injecting `--settings`.
 */
export function inspectClaudeInvocation(claudeArgs = []) {
  const args = Array.isArray(claudeArgs) ? claudeArgs.map(String) : [];
  let subcommand = null;
  let subcommandArg = null;
  let hasHelpOrVersion = false;
  let hasBareFlag = false;
  let hasBackgroundFlag = false;
  let hasSessionOnlyFlag = false;

  const isReservedSubcommand = name => (
    name === 'logout'
    || name === 'login'
    || name === 'setup-token'
    || name === 'auth'
    || (Boolean(name) && PASS_THROUGH_SUBCOMMANDS.has(name))
  );

  for (let i = 0; i < args.length; i += 1) {
    const token = args[i];
    if (token === '--') break;
    if (NO_LEASE_TOP_FLAGS.has(token)) {
      hasHelpOrVersion = true;
      continue;
    }
    if (token === '--bare') {
      if (subcommand === null) hasSessionOnlyFlag = true;
      if (!isReservedSubcommand(subcommand)) hasBareFlag = true;
      continue;
    }
    if (token === '--bg' || token === '--background') {
      if (subcommand === null) hasSessionOnlyFlag = true;
      if (!isReservedSubcommand(subcommand)) hasBackgroundFlag = true;
      continue;
    }
    if (token.startsWith('--') && token.includes('=')) {
      const flagName = token.slice(0, token.indexOf('='));
      if (subcommand === null && CLAUDE_SESSION_ONLY_FLAGS.has(flagName)) {
        hasSessionOnlyFlag = true;
      }
      continue;
    }
    if (subcommand === null && CLAUDE_SESSION_ONLY_FLAGS.has(token)) {
      hasSessionOnlyFlag = true;
    }
    if (CLAUDE_VARIADIC_VALUE_FLAGS.has(token)) {
      if (i + 1 < args.length) {
        i += 1;
        while (i + 1 < args.length && args[i + 1] !== '--' && !args[i + 1].startsWith('-')) {
          i += 1;
        }
      }
      continue;
    }
    if (CLAUDE_VALUE_FLAGS.has(token)) {
      i += 1;
      continue;
    }
    if (CLAUDE_OPTIONAL_VALUE_FLAGS.has(token)) {
      const next = args[i + 1];
      if (next && next !== '--' && !next.startsWith('-')) {
        i += 1;
      }
      continue;
    }
    if (CLAUDE_BOOL_FLAGS.has(token) || token.startsWith('-')) {
      continue;
    }
    if (subcommand === null) {
      subcommand = token;
      continue;
    }
    if (subcommandArg === null) {
      subcommandArg = token;
    }
  }

  if (hasHelpOrVersion) {
    return { mode: 'pass_through', subcommand, subcommandArg, hasBareFlag, hasBackgroundFlag };
  }
  if (!hasSessionOnlyFlag && subcommand === 'logout') {
    return { mode: 'logout', subcommand, subcommandArg, hasBareFlag, hasBackgroundFlag };
  }
  if (
    !hasSessionOnlyFlag
    && (
      subcommand === 'login'
      || subcommand === 'setup-token'
      || (subcommand === 'auth' && (subcommandArg === 'login' || subcommandArg === 'logout'))
    )
  ) {
    return { mode: 'login_hint', subcommand, subcommandArg, hasBareFlag, hasBackgroundFlag };
  }
  if (!hasSessionOnlyFlag && (subcommand === 'auth' || (subcommand && PASS_THROUGH_SUBCOMMANDS.has(subcommand)))) {
    return { mode: 'pass_through', subcommand, subcommandArg, hasBareFlag, hasBackgroundFlag };
  }
  return { mode: 'leased', subcommand, subcommandArg, hasBareFlag, hasBackgroundFlag };
}

export function buildPddClaudeChildEnv(baseEnv = process.env) {
  const out = {};
  for (const [k, v] of Object.entries(baseEnv ?? {})) {
    if (typeof v !== 'string') continue;
    if (k.startsWith('PDD_')) continue;
    if (STRIPPED_CLAUDE_ENV_VARS.has(k)) continue;
    out[k] = v;
  }
  return out;
}

export function resolveClaudeRuntimeRoot(env = process.env) {
  const override = typeof env?.PDD_CLAUDE_RUNTIME_ROOT === 'string' && env.PDD_CLAUDE_RUNTIME_ROOT.trim();
  if (override) return resolve(override);
  return join(resolvePddStateBase(env), 'claude-runtime');
}

export function sharedClaudeRuntimeDir(env = process.env, uid = typeof process.getuid === 'function' ? process.getuid() : 'user') {
  return join(resolveClaudeRuntimeRoot(env), `pdd-claude-${uid}`);
}

export async function withClaudeRuntimeLock(runtimeDir, fn, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  assertSafeRuntimeDir(fs, runtimeDir, { label: 'pdd-claude runtime' });
  return withRuntimeDirLock(fs, runtimeDir, fn, {
    lockName: '.lock',
    timeoutCode: 'runtime_lock_timeout',
    label: 'pdd-claude runtime',
    ports,
  });
}

function sweepStaleSessionFiles(fs, sessionsDir, livePids) {
  const liveSet = new Set(livePids);
  let entries = [];
  try { entries = fs.readdirSync(sessionsDir); } catch { return; }
  for (const name of entries) {
    const match = /^settings-(\d+)-[a-f0-9]+\.json$/.exec(name);
    if (!match || !liveSet.has(Number(match[1]))) {
      unlinkQuiet(fs, join(sessionsDir, name));
    }
  }
}

function isReusableClaudeLease(meta, nowMs) {
  if (!meta || typeof meta !== 'object') return false;
  if (meta.auto_rotate !== true) return false;
  if (typeof meta.lease_id !== 'string' || !meta.lease_id.trim()) return false;
  const token = String(meta.claude_oauth_token || meta.gateway_bearer_token || '').trim();
  if (!token) return false;
  const expiresMs = Date.parse(String(meta.expires_at ?? ''));
  if (!Number.isFinite(expiresMs)) return false;
  return (expiresMs - nowMs) > MIN_REUSABLE_LEASE_REMAINING_MS;
}

function writeSessionSettingsFile(fs, sessionsDir, pid, lease, { env, userSettings }, ports) {
  assertSafeRuntimeDir(fs, sessionsDir, { checkAncestors: false, label: 'pdd-claude sessions' });
  const { settings } = buildClaudeGatewaySettingsOverlay(lease, { env, userSettings }, ports);
  const fileName = `settings-${pid}-${randomBytes(6).toString('hex')}.json`;
  const settingsPath = join(sessionsDir, fileName);
  writeAtomicPrivate(fs, settingsPath, `${JSON.stringify(settings, null, 2)}\n`);
  return settingsPath;
}

function normalizeLeaseRecord(reply, nowMs) {
  const lease = reply?.lease ?? {};
  const token = String(lease.claude_oauth_token || lease.gateway_bearer_token || '').trim();
  if (!token) {
    throw new CloudAccountsError('PDD Cloud Claude lease did not include a gateway grant token.', {
      code: 'invalid_lease',
    });
  }
  rememberSecrets(token);
  return {
    lease_id: lease.lease_id ?? null,
    account_id: reply?.account?.account_id ?? null,
    label: reply?.account?.label ?? null,
    delivery_mode: lease.delivery_mode ?? 'gateway_grant',
    anthropic_base_url: lease.anthropic_base_url ?? null,
    claude_oauth_token: token,
    gateway_bearer_token: token,
    expires_at: lease.expires_at ?? null,
    auto_rotate: lease.auto_rotate !== false,
    created_at: new Date(nowMs).toISOString(),
    last_heartbeat_at: new Date(nowMs).toISOString(),
  };
}

function assertAccountNotReauthRequired(account, fallbackLabel = null) {
  if (!account || !isReauthRequiredAccount(account)) return;
  const label = account.label || fallbackLabel || 'your Claude account';
  throw new CloudAccountsError(
    `PDD Cloud Claude account "${label}" requires re-authentication. Run \`pdd accounts add --provider claude --label ${label}\` or pick another account.`,
    { code: 'reauth_required', exitCode: 1 },
  );
}

export async function acquireSharedClaudeRuntimeSession({
  cwd = process.cwd(),
  env = process.env,
  pid = process.pid,
  userSettings = null,
} = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const now = ports.now ?? Date.now;
  const isPidAlive = ports.isPidAlive ?? defaultIsPidAlive;
  const leaseFn = ports.leaseCloudAccount ?? leaseCloudAccount;

  const runtimeRoot = resolveClaudeRuntimeRoot(env);
  assertSafeRuntimeDir(fs, runtimeRoot, { label: 'pdd-claude runtime' });
  const runtimeDir = sharedClaudeRuntimeDir(env, ports.uid);
  const pidsDir = join(runtimeDir, 'pids');
  const sessionsDir = join(runtimeDir, 'sessions');
  const leasePath = join(runtimeDir, 'lease.json');

  try {
    restoreLocalClaudeGatewayConfig({ env, removeManagedFile: false }, ports);
  } catch {}

  return await withClaudeRuntimeLock(runtimeDir, async () => {
    assertSafeRuntimeDir(fs, pidsDir, { checkAncestors: false, label: 'pdd-claude pids' });
    assertSafeRuntimeDir(fs, sessionsDir, { checkAncestors: false, label: 'pdd-claude sessions' });
    const livePids = sweepLivePids(fs, pidsDir, isPidAlive);
    sweepStaleSessionFiles(fs, sessionsDir, livePids);

    let leaseMeta = readJsonObjectQuiet(fs, leasePath);
    let reused = true;
    if (!isReusableClaudeLease(leaseMeta, now())) {
      reused = false;
      const reply = await leaseFn({
        provider: 'claude',
        holderId: 'pdd-claude-shared',
        autoRotate: true,
        updateState: false,
      }, { cwd, env }, ports);
      if (reply?.state !== 'leased' || !reply?.lease) {
        const wake = reply?.wake_at ? ` Next ready at ${reply.wake_at}.` : '';
        throw new CloudAccountsError(
          `No ready PDD Cloud Claude account is available (${reply?.state || 'unavailable'}).${wake} Run \`pdd accounts list\` to inspect your pool.`,
          { code: 'no_ready_account', exitCode: 1 },
        );
      }
      assertAccountNotReauthRequired(reply.account);
      leaseMeta = normalizeLeaseRecord(reply, now());
      buildClaudeGatewaySettingsOverlay(leaseMeta, { env, userSettings }, ports);
      writeAtomicPrivate(fs, leasePath, `${JSON.stringify(leaseMeta, null, 2)}\n`);
    } else {
      rememberSecrets(leaseMeta.claude_oauth_token, leaseMeta.gateway_bearer_token);
    }

    const settingsPath = writeSessionSettingsFile(fs, sessionsDir, pid, leaseMeta, { env, userSettings }, ports);
    writeAtomicPrivate(fs, join(pidsDir, String(pid)), `${JSON.stringify({ pid, startedAt: now() })}\n`);

    return {
      mode: 'shared',
      runtimeDir,
      leasePath,
      settingsPath,
      pid,
      reused,
      lease: leaseMeta,
    };
  }, { ...ports, pid });
}

export async function releaseSharedClaudeRuntimeSession(session, { cwd = process.cwd(), env = process.env } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  // SEC-7: Always unlink the 0600 session settings token file FIRST before any directory check
  // or lock acquisition so a failed safety check can never leave token material on disk.
  unlinkQuiet(fs, session?.settingsPath);
  if (!session?.runtimeDir) return { releasedLeaseId: null };
  const isPidAlive = ports.isPidAlive ?? defaultIsPidAlive;
  const releaseFn = ports.releaseCloudLease ?? releaseCloudLease;
  const pidsDir = join(session.runtimeDir, 'pids');
  const sessionsDir = join(session.runtimeDir, 'sessions');
  const leasePath = join(session.runtimeDir, 'lease.json');

  assertSafeRuntimeDir(fs, dirname(session.runtimeDir), { label: 'pdd-claude runtime' });

  let leaseIdToRevoke = null;
  try {
    await withClaudeRuntimeLock(session.runtimeDir, async () => {
      unlinkQuiet(fs, join(pidsDir, String(session.pid)));
      const remaining = sweepLivePids(fs, pidsDir, isPidAlive);
      sweepStaleSessionFiles(fs, sessionsDir, remaining);
      if (remaining.length === 0) {
        const meta = readJsonObjectQuiet(fs, leasePath);
        if (typeof meta?.lease_id === 'string' && meta.lease_id.trim()) {
          leaseIdToRevoke = meta.lease_id.trim();
        }
        unlinkQuiet(fs, leasePath);
      }
    }, { ...ports, pid: session.pid });
  } catch {
    unlinkQuiet(fs, join(pidsDir, String(session.pid)));
  }

  if (leaseIdToRevoke) {
    try {
      await releaseFn(leaseIdToRevoke, { cwd, env }, ports);
    } catch {}
  }
  return { releasedLeaseId: leaseIdToRevoke };
}

export async function acquirePinnedClaudeRuntimeSession({
  preferredAccount,
  cwd = process.cwd(),
  env = process.env,
  pid = process.pid,
  userSettings = null,
} = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const now = ports.now ?? Date.now;
  const leaseFn = ports.leaseCloudAccount ?? leaseCloudAccount;

  const runtimeRoot = resolveClaudeRuntimeRoot(env);
  assertSafeRuntimeDir(fs, runtimeRoot, { label: 'pdd-claude runtime' });
  const runtimeDir = fs.mkdtempSync(join(runtimeRoot, 'pdd-claude-pin-'));
  try { fs.chmodSync?.(runtimeDir, 0o700); } catch {}

  try {
    restoreLocalClaudeGatewayConfig({ env, removeManagedFile: false }, ports);
  } catch {}

  try {
    const reply = await leaseFn({
      provider: 'claude',
      preferredLabel: preferredAccount,
      currentAccountId: null,
      holderId: `pdd-claude-pin-${pid}`,
      autoRotate: false,
      updateState: false,
    }, { cwd, env }, ports);
    if (reply?.state !== 'leased' || !reply?.lease) {
      const wake = reply?.wake_at ? ` Next ready at ${reply.wake_at}.` : '';
      throw new CloudAccountsError(
        `Could not lease PDD Cloud Claude account "${preferredAccount}" (${reply?.state || 'unavailable'}).${wake} Run \`pdd accounts list\` to inspect your pool.`,
        { code: 'no_ready_account', exitCode: 1 },
      );
    }
    assertAccountNotReauthRequired(reply.account, preferredAccount);
    const leaseMeta = { ...normalizeLeaseRecord(reply, now()), auto_rotate: false };
    const settingsPath = writeSessionSettingsFile(fs, join(runtimeDir, 'sessions'), pid, leaseMeta, { env, userSettings }, ports);
    const leasePath = join(runtimeDir, 'lease.json');
    writeAtomicPrivate(fs, leasePath, `${JSON.stringify(leaseMeta, null, 2)}\n`);
    return {
      mode: 'pinned',
      runtimeDir,
      leasePath,
      settingsPath,
      pid,
      reused: false,
      lease: leaseMeta,
    };
  } catch (err) {
    try { fs.rmSync(runtimeDir, { recursive: true, force: true }); } catch {}
    throw err;
  }
}

export async function releasePinnedClaudeRuntimeSession(session, { cwd = process.cwd(), env = process.env } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  unlinkQuiet(fs, session?.settingsPath);
  if (!session?.runtimeDir) return { releasedLeaseId: null };
  const releaseFn = ports.releaseCloudLease ?? releaseCloudLease;
  const leaseId = typeof session.lease?.lease_id === 'string' && session.lease.lease_id.trim()
    ? session.lease.lease_id.trim()
    : null;
  try { fs.rmSync(session.runtimeDir, { recursive: true, force: true }); } catch {}
  if (leaseId) {
    try {
      await releaseFn(leaseId, { cwd, env }, ports);
    } catch {}
  }
  return { releasedLeaseId: leaseId };
}

export function startClaudeLeaseHeartbeat(session, { cwd = process.cwd(), env = process.env } = {}, ports = {}) {
  if (!session?.lease?.lease_id) return () => {};
  const fs = ports.fs ?? nativeFs;
  const now = ports.now ?? Date.now;
  const heartbeatFn = ports.heartbeatCloudLease ?? heartbeatCloudLease;

  return startLeaseHeartbeat({
    initialLeaseId: session.lease.lease_id,
    leasePath: session.leasePath,
    runtimeDir: session.runtimeDir,
    shared: session.mode === 'shared',
    lockName: '.lock',
    lockLabel: 'pdd-claude runtime',
    timeoutCode: 'runtime_lock_timeout',
    intervalMs: ports.heartbeatIntervalMs ?? DEFAULT_HEARTBEAT_INTERVAL_MS,
    minSpacingRatio: 0.6,
    jitterCapMs: 30_000,
    jitterRatio: 0.15,
    heartbeatFn,
    onRefresh: async (leaseId, beat) => {
      const latest = readJsonObjectQuiet(fs, session.leasePath);
      if (!latest || latest.lease_id !== leaseId) return;
      const updated = {
        ...latest,
        expires_at: beat?.expires_at ?? latest.expires_at,
        account_id: beat?.account_id ?? latest.account_id,
        last_heartbeat_at: new Date(now()).toISOString(),
      };
      writeAtomicPrivate(fs, session.leasePath, `${JSON.stringify(updated, null, 2)}\n`);
    },
    onInvalidated: async failedLeaseId => {
      const latest = readJsonObjectQuiet(fs, session.leasePath);
      if (latest && failedLeaseId && latest.lease_id === failedLeaseId) {
        unlinkQuiet(fs, session.leasePath);
      }
    },
    cwd,
    env,
    fs,
    now,
    ports: { ...ports, pid: session.pid },
  });
}

export async function logoutSharedClaudeRuntime({ cwd = process.cwd(), env = process.env } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const releaseFn = ports.releaseCloudLease ?? releaseCloudLease;
  const runtimeRoot = resolveClaudeRuntimeRoot(env);
  const runtimeDir = sharedClaudeRuntimeDir(env, ports.uid);
  const leasePath = join(runtimeDir, 'lease.json');
  const sessionsDir = join(runtimeDir, 'sessions');

  let revokedLeaseId = null;
  let rootExists = false;
  try {
    fs.lstatSync(runtimeRoot);
    rootExists = true;
  } catch (err) {
    if (err?.code !== 'ENOENT') throw err;
  }
  if (rootExists) {
    assertSafeRuntimeDir(fs, runtimeRoot, { label: 'pdd-claude runtime' });
    if (fs.existsSync?.(runtimeDir)) {
      await withClaudeRuntimeLock(runtimeDir, async () => {
        const meta = readJsonObjectQuiet(fs, leasePath);
        if (typeof meta?.lease_id === 'string' && meta.lease_id.trim()) {
          revokedLeaseId = meta.lease_id.trim();
        }
        unlinkQuiet(fs, leasePath);
        try {
          for (const name of fs.readdirSync(sessionsDir)) {
            unlinkQuiet(fs, join(sessionsDir, name));
          }
        } catch {}
      }, ports);
    }
  }

  if (revokedLeaseId) {
    try {
      await releaseFn(revokedLeaseId, { cwd, env }, ports);
    } catch {}
  }

  const restored = restoreLocalClaudeGatewayConfig({ env }, ports);
  return { revokedLeaseId, restored };
}

function spawnClaudePassthrough(claudeBin, args, { cwd, env, onChild } = {}, ports = {}) {
  return spawnWrappedBinary(claudeBin, args, { cwd, env, onChild }, ports);
}

function stripAutoFailOpenEnv(env) {
  if (!env || typeof env !== 'object' || !('PDD_CLAUDE_AUTO_FAIL_OPEN' in env)) return env;
  const next = { ...env };
  delete next.PDD_CLAUDE_AUTO_FAIL_OPEN;
  return next;
}

function isAutoFailOpenLeaseError(err) {
  const code = String(err?.code ?? '');
  if (['unsafe_path', 'invalid_args', 'reauth_required'].includes(code)) return false;
  if (['timeout', 'network_error', 'missing_auth_token', 'no_ready_account', 'all_cooling'].includes(code)) {
    return true;
  }
  const status = Number(err?.status ?? 0);
  if (status === 401 || status === 403 || status >= 500) return true;
  if (status === 0 && !code) return true;
  return false;
}

export async function runPddClaudeCli(argv = [], {
  cwd = process.cwd(),
  env = process.env,
  stdout = process.stdout,
  stderr = process.stderr,
} = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const claudeBin = ports.claudeBin ?? (typeof env?.PDD_CLAUDE_BIN === 'string' && env.PDD_CLAUDE_BIN.trim() ? env.PDD_CLAUDE_BIN.trim() : 'claude');

  let parsed;
  try {
    parsed = parsePddClaudeArgs(argv);
  } catch (err) {
    stderr.write(`${redactSecrets(err?.message || String(err))}\n`);
    return { exitCode: err?.exitCode ?? 2 };
  }

  if (parsed.showPddHelp) {
    stdout.write(PDD_CLAUDE_HELP_TEXT);
    return { exitCode: 0 };
  }

  const autoFailOpen = env?.PDD_CLAUDE_AUTO_FAIL_OPEN === '1' && !parsed.preferredAccount;
  const passthroughEnv = autoFailOpen ? stripAutoFailOpenEnv(env) : env;
  const inspection = inspectClaudeInvocation(parsed.claudeArgs);

  if (autoFailOpen && (inspection.mode === 'logout' || inspection.mode === 'login_hint')) {
    const res = await spawnClaudePassthrough(claudeBin, parsed.claudeArgs, { cwd, env: passthroughEnv }, ports);
    if (res.error) {
      stderr.write(`Failed to launch "${claudeBin}": ${redactSecrets(res.error.message || String(res.error))}\n`);
    }
    return { exitCode: res.exitCode };
  }

  if (inspection.mode === 'logout') {
    try {
      const res = await logoutSharedClaudeRuntime({ cwd, env }, ports);
      if (res.revokedLeaseId) {
        stdout.write('Ended shared pdd-claude session and revoked its PDD Cloud lease. Your personal ~/.claude login was not modified.\n');
      } else {
        stdout.write('No active shared pdd-claude session found. Your personal ~/.claude login was not modified.\n');
      }
      return { exitCode: 0 };
    } catch (err) {
      stderr.write(`${redactSecrets(err?.message || String(err))}\n`);
      return { exitCode: err?.exitCode ?? 1 };
    }
  }

  if (inspection.mode === 'login_hint') {
    stdout.write(
      'pdd-claude uses your PDD Cloud shared account pool and never modifies your personal Claude login.\n'
      + '  - Enroll a Claude account into PDD Cloud: pdd accounts add --provider claude\n'
      + '  - End the shared pdd-claude session:      pdd-claude logout\n'
      + '  - Manage your personal Claude login:      command claude auth login / command claude auth logout\n',
    );
    return { exitCode: 0 };
  }

  if (inspection.mode === 'pass_through') {
    const res = await spawnClaudePassthrough(claudeBin, parsed.claudeArgs, { cwd, env: passthroughEnv }, ports);
    if (res.error) {
      stderr.write(`Failed to launch "${claudeBin}": ${redactSecrets(res.error.message || String(res.error))}\n`);
    }
    return { exitCode: res.exitCode };
  }

  if (autoFailOpen && !ports.leaseCloudAccount && !isCloudAccountsActive({ env, provider: 'claude' }, ports)) {
    const res = await spawnClaudePassthrough(claudeBin, parsed.claudeArgs, { cwd, env: passthroughEnv }, ports);
    if (res.error) {
      stderr.write(`Failed to launch "${claudeBin}": ${redactSecrets(res.error.message || String(res.error))}\n`);
    }
    return { exitCode: res.exitCode };
  }

  if (inspection.hasBackgroundFlag) {
    if (autoFailOpen) {
      const res = await spawnClaudePassthrough(claudeBin, parsed.claudeArgs, { cwd, env: passthroughEnv }, ports);
      if (res.error) {
        stderr.write(`Failed to launch "${claudeBin}": ${redactSecrets(res.error.message || String(res.error))}\n`);
      }
      return { exitCode: res.exitCode };
    }
    stderr.write('pdd-claude does not support `--bg` / `--background` because detached Claude exits immediately and revokes its leased session. Run without `--bg` or use `command claude`.\n');
    return { exitCode: 2 };
  }

  if (inspection.hasBareFlag) {
    stderr.write('Warning: `claude --bare` disables OAuth authentication in Claude Code; pdd-claude pool tokens require standard mode (without `--bare`).\n');
  }

  let extracted;
  try {
    extracted = extractAndParseUserClaudeSettings(parsed.claudeArgs, { cwd, fs });
  } catch (err) {
    stderr.write(`${redactSecrets(err?.message || String(err))}\n`);
    return { exitCode: err?.exitCode ?? 2 };
  }

  let session = null;
  let stopHeartbeat = () => {};
  let activeChild = null;
  let receivedSignal = null;
  let cleanedUp = false;

  const syncEmergencyCleanup = () => {
    if (cleanedUp || !session) return;
    cleanedUp = true;
    try {
      unlinkQuiet(fs, session.settingsPath);
      if (session.mode === 'pinned' && session.runtimeDir) {
        fs.rmSync(session.runtimeDir, { recursive: true, force: true });
      } else if (session.runtimeDir && session.pid) {
        unlinkQuiet(fs, join(session.runtimeDir, 'pids', String(session.pid)));
      }
    } catch {}
  };

  const detachHooks = registerProcessCleanupHooks({
    onEmergencyExit: syncEmergencyCleanup,
    onSignal: sig => {
      receivedSignal = sig;
      if (activeChild) {
        try { activeChild.kill?.(sig); } catch {}
      }
    },
  });

  try {
    try {
      session = parsed.preferredAccount
        ? await acquirePinnedClaudeRuntimeSession({
            preferredAccount: parsed.preferredAccount,
            cwd,
            env,
            pid: ports.pid ?? process.pid,
            userSettings: extracted.userSettings,
          }, ports)
        : await acquireSharedClaudeRuntimeSession({
            cwd,
            env,
            pid: ports.pid ?? process.pid,
            userSettings: extracted.userSettings,
          }, ports);
    } catch (err) {
      if (receivedSignal) {
        return { exitCode: signalToExitCode(receivedSignal) };
      }
      if (autoFailOpen && isAutoFailOpenLeaseError(err)) {
        const res = await spawnClaudePassthrough(claudeBin, parsed.claudeArgs, {
          cwd,
          env: passthroughEnv,
          onChild: child => { activeChild = child; },
        }, ports);
        if (res.error) {
          stderr.write(`Failed to launch "${claudeBin}": ${redactSecrets(res.error.message || String(res.error))}\n`);
        }
        return { exitCode: res.exitCode };
      }
      throw err;
    }

    if (receivedSignal) {
      return { exitCode: signalToExitCode(receivedSignal) };
    }

    stopHeartbeat = startClaudeLeaseHeartbeat(session, { cwd, env }, ports);

    const finalArgs = injectClaudeSettingsArg(extracted.strippedArgs, session.settingsPath);
    const childEnv = buildPddClaudeChildEnv(env);
    const res = await spawnClaudePassthrough(claudeBin, finalArgs, {
      cwd,
      env: childEnv,
      onChild: child => { activeChild = child; },
    }, ports);
    if (res.error) {
      stderr.write(`Failed to launch "${claudeBin}": ${redactSecrets(res.error.message || String(res.error))}\n`);
    }
    return { exitCode: res.exitCode };
  } catch (err) {
    stderr.write(`${redactSecrets(err?.message || String(err))}\n`);
    return { exitCode: err?.exitCode ?? 1 };
  } finally {
    stopHeartbeat();
    if (session) {
      // SEC-7: Unlink the private 0600 settings token file first before any async release work.
      unlinkQuiet(fs, session.settingsPath);
      try {
        if (session.mode === 'pinned') {
          await releasePinnedClaudeRuntimeSession(session, { cwd, env }, ports);
        } else {
          await releaseSharedClaudeRuntimeSession(session, { cwd, env }, ports);
        }
        cleanedUp = true;
      } catch {
        syncEmergencyCleanup();
      }
    }
    detachHooks();
  }
}
