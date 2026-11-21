// Generated from prompts/cli/pdd-codex.prompt.md.
// Dedicated PDD Codex launcher: shares one ~/.codex home + one PID-refcounted runtime dir
// per machine, passes gateway routing via -c flags, and cleans up auth.json + lease on last exit.
import { randomBytes } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { dirname, join, resolve, sep } from 'node:path';
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
  buildCodexGatewayCliArgs,
  buildCodexHomeMirrorCliArgs,
  buildGatewayAuthJson,
  CloudAccountsError,
  ensureUserCodexHomeBaseline,
  heartbeatCloudLease,
  leaseCloudAccount,
  localCodexHome,
  needsCodexConfigWritebackNormalization,
  normalizeCodexConfigWriteback,
  readCloudAccountsState,
  releaseCloudLease,
  resolveCodexBackendApiUrl,
  resolveEffectiveSqliteHome,
  resolvePddStateBase,
  stopCodexAppServerDaemon,
  stripCodexCliEnvExcludeArgs,
  syncManagedCodexHomeLinks,
} from './login-pool.mjs';
import { redactSecrets, rememberSecrets } from './secret-redaction.mjs';

const STRIPPED_PROVIDER_ENV_VARS = [
  'OPENAI_API_KEY',
  'CODEX_API_KEY',
  'CODEX_ACCESS_TOKEN',
  'OPENAI_BASE_URL',
  'PDD_CODEX_GATEWAY_GRANT',
  'CODEX_CONNECTORS_TOKEN',
];

const NO_LEASE_TOP_FLAGS = new Set(['--version', '-V', '--help', '-h']);
const NO_LEASE_SUBCOMMANDS = new Set(['help', 'completion']);
const LOCAL_MCP_SUBCOMMANDS = new Set(['add', 'remove', 'list', 'get']);
const LOCAL_OFFLINE_SUBCOMMANDS = new Set([
  'features',
  'apply',
  'a',
  'archive',
  'unarchive',
  'delete',
  'migrate-rollouts',
  'migrate-nfs-db',
]);
const CODEX_GLOBAL_VALUE_FLAGS = new Set([
  '-c', '--config',
  '--enable', '--disable',
  '--remote', '--remote-auth-token-env',
  '-i', '--image',
  '-m', '--model',
  '--local-provider',
  '-p', '--profile',
  '-s', '--sandbox',
  '-C', '--cd',
  '--add-dir',
  '-a', '--ask-for-approval',
]);
const CODEX_GLOBAL_BOOL_FLAGS = new Set([
  '--strict-config',
  '--oss',
  '--approve-for-me',
  '--dangerously-bypass-approvals-and-sandbox',
  '--dangerously-bypass-hook-trust',
  '--worktree',
  '--search',
  '--no-alt-screen',
  '--no-daemon',
  '--full-auto',
]);

const PDD_CODEX_HELP_TEXT = [
  'pdd-codex — Launch Codex through your PDD Cloud shared account pool.',
  '',
  'Usage:',
  '  pdd-codex [CODEX_ARGS...]',
  '  pdd-codex --account <label> [CODEX_ARGS...]',
  '  pdd-codex logout',
  '  pdd-codex --pdd-help',
  '',
  'Behavior:',
  '  - Never touches your personal ~/.codex/auth.json or stock `codex` command.',
  '  - Uses your real ~/.codex/config.toml, chats, skills, plugins, and MCP servers.',
  '  - Shares one temporary runtime folder and one PDD Cloud lease across concurrent sessions.',
  '  - Automatically rotates accounts server-side when quota is reached (unless --account is set).',
  '  - Deletes the temporary runtime auth.json and revokes the lease when the last session exits.',
  '',
].join('\n');

function isKnownCodexOrWrapperOption(token) {
  if (typeof token !== 'string' || !token) return false;
  if (token === '--' || token === '--account' || token.startsWith('--account=') || token === '--pdd-help') {
    return true;
  }
  const flagName = token.startsWith('--') && token.includes('=')
    ? token.slice(0, token.indexOf('='))
    : token;
  return NO_LEASE_TOP_FLAGS.has(flagName)
    || CODEX_GLOBAL_VALUE_FLAGS.has(flagName)
    || CODEX_GLOBAL_BOOL_FLAGS.has(flagName);
}

/**
 * Parse optional leading `pdd-codex` flags (`--account`, `--pdd-help`) without disturbing
 * stock Codex flags or user prompt arguments. Rejects blank or dash-prefixed labels on both
 * `--account <label>` and `--account=<label>`.
 */
export function parsePddCodexArgs(argv = []) {
  const { preferredAccount, showPddHelp, restArgs } = parseWrapperLeadingArgs(argv, {
    isKnownOption: isKnownCodexOrWrapperOption,
    missingMessage: 'Missing account label after --account.',
    missingEqMessage: 'Missing account label after --account=.',
    missingCode: 'invalid_argument',
    exitCode: 2,
  });
  return {
    preferredAccount,
    showPddHelp,
    codexArgs: restArgs,
  };
}

/**
 * Inspect `codexArgs` past leading global Codex flags to find the real subcommand and
 * detect `--help` / `--version` requests without being fooled by flags after `--`.
 */
function inspectCodexInvocation(codexArgs = []) {
  const args = Array.isArray(codexArgs) ? codexArgs.map(String) : [];
  let i = 0;
  let hasHelpOrVersion = false;
  let subcommand = '';
  let subArgs = [];

  while (i < args.length) {
    const token = args[i];
    if (token === '--') break;
    if (NO_LEASE_TOP_FLAGS.has(token)) {
      hasHelpOrVersion = true;
      i += 1;
      continue;
    }
    if (CODEX_GLOBAL_VALUE_FLAGS.has(token)) {
      i += 2;
      continue;
    }
    if (token.startsWith('--') && token.includes('=')) {
      const flagName = token.slice(0, token.indexOf('='));
      if (CODEX_GLOBAL_VALUE_FLAGS.has(flagName)) {
        i += 1;
        continue;
      }
    }
    if (CODEX_GLOBAL_BOOL_FLAGS.has(token)) {
      i += 1;
      continue;
    }
    if (token.startsWith('-')) {
      i += 1;
      continue;
    }
    subcommand = token;
    subArgs = args.slice(i + 1);
    break;
  }

  for (const token of subArgs) {
    if (token === '--') break;
    if (token === '--help' || token === '-h') {
      hasHelpOrVersion = true;
      break;
    }
  }

  return { subcommand, subArgs, hasHelpOrVersion };
}

/**
 * Resolve the per-user runtime root (`~/.local/state/pdd/codex-runtime` by default,
 * never `/tmp` so Linux stock Codex can create helper binaries cleanly).
 */
function resolveRuntimeRoot({ env = process.env, tmpRoot = null } = {}) {
  if (typeof tmpRoot === 'string' && tmpRoot.trim()) return tmpRoot.trim();
  if (typeof env?.PDD_CODEX_RUNTIME_ROOT === 'string' && env.PDD_CODEX_RUNTIME_ROOT.trim()) {
    return env.PDD_CODEX_RUNTIME_ROOT.trim();
  }
  return join(resolvePddStateBase(env), 'codex-runtime');
}

/**
 * Resolve the per-user shared machine runtime folder (`~/.local/state/pdd/codex-runtime/pdd-codex-<uid>`).
 */
export function sharedRuntimeDirPath({ env = process.env, tmpRoot = null, uid = null } = {}) {
  const root = resolveRuntimeRoot({ env, tmpRoot });
  const effectiveUid = uid !== null && uid !== undefined
    ? String(uid)
    : (typeof process.getuid === 'function' ? String(process.getuid()) : 'user');
  return join(resolve(root), `pdd-codex-${effectiveUid}`);
}

function withCodexRuntimeLock(fs, runtimeDir, fn, ports = {}) {
  return withRuntimeDirLock(fs, runtimeDir, fn, {
    lockName: 'lock',
    timeoutCode: 'lock_timeout',
    label: 'PDD Codex runtime',
    ports,
  });
}

function ensureConfigSymlinkAtomic(fs, userConfigPath, runtimeConfigPath) {
  const lstat = fs.lstatSync ?? nativeFs.lstatSync;
  let existingCfg = null;
  try { existingCfg = lstat.call(fs, runtimeConfigPath); } catch {}
  if (existingCfg) {
    let matches = existingCfg.isSymbolicLink();
    if (matches && typeof fs.readlinkSync === 'function') {
      try { matches = fs.readlinkSync(runtimeConfigPath) === userConfigPath; } catch { matches = false; }
    }
    if (matches) return;
    if (existingCfg.isDirectory() && !existingCfg.isSymbolicLink()) {
      fs.rmSync(runtimeConfigPath, { recursive: true, force: true });
      fs.symlinkSync(userConfigPath, runtimeConfigPath);
      return;
    }
    const tmpLink = `${runtimeConfigPath}.link-${process.pid}-${randomBytes(4).toString('hex')}`;
    try {
      fs.symlinkSync(userConfigPath, tmpLink);
      fs.renameSync(tmpLink, runtimeConfigPath);
    } catch {
      unlinkQuiet(fs, tmpLink);
      fs.rmSync(runtimeConfigPath, { recursive: true, force: true });
      fs.symlinkSync(userConfigPath, runtimeConfigPath);
    }
    return;
  }
  fs.symlinkSync(userConfigPath, runtimeConfigPath);
}

/**
 * Ensure `~/.codex/` baseline exists and symlink all user entries + `config.toml` into `runtimeDir`.
 */
export function prepareRuntimeCodexHome(fs, userCodexHome, runtimeDir) {
  const resolvedUserHome = resolve(userCodexHome);
  const resolvedRuntimeDir = resolve(runtimeDir);
  const realFn = fs?.realpathSync?.native ?? fs?.realpathSync ?? (fs === nativeFs ? nativeFs.realpathSync : null);
  let realUserHome = resolvedUserHome;
  let realRuntimeDir = resolvedRuntimeDir;
  if (typeof realFn === 'function') {
    try { realUserHome = String(realFn.call(fs, resolvedUserHome)); } catch {}
    try { realRuntimeDir = String(realFn.call(fs, resolvedRuntimeDir)); } catch {}
  }
  if (
    resolvedUserHome === resolvedRuntimeDir
    || resolvedUserHome.startsWith(`${resolvedRuntimeDir}${sep}`)
    || realUserHome === realRuntimeDir
    || realUserHome.startsWith(`${realRuntimeDir}${sep}`)
  ) {
    throw new CloudAccountsError(
      `Refusing to mirror Codex home inside runtime folder (${resolvedRuntimeDir}).`,
      { code: 'unsafe_runtime_dir' },
    );
  }
  const userConfigPath = ensureUserCodexHomeBaseline(fs, resolvedUserHome);

  syncManagedCodexHomeLinks(fs, resolvedUserHome, resolvedRuntimeDir, [], {
    preserveLinks: new Set(['config.toml']),
  });

  ensureConfigSymlinkAtomic(fs, userConfigPath, join(resolvedRuntimeDir, 'config.toml'));

  return {
    userCodexHome: resolvedUserHome,
    userConfigPath,
  };
}

function readReusableRuntimeLease(fs, runtimeDir, { now }) {
  const meta = readJsonObjectQuiet(fs, join(runtimeDir, 'lease.json'));
  const auth = readJsonObjectQuiet(fs, join(runtimeDir, 'auth.json'));
  if (!meta || !auth) return null;
  if (meta.auto_rotate !== true) return null;
  if (typeof meta.lease_id !== 'string' || !meta.lease_id.trim()) return null;
  if (typeof meta.backend_api_url !== 'string' || !meta.backend_api_url.trim()) return null;
  const grantToken = typeof auth?.tokens?.access_token === 'string' ? auth.tokens.access_token.trim() : '';
  if (!grantToken.startsWith('pddg_')) return null;
  const expiresMs = Date.parse(String(meta.expires_at ?? ''));
  if (!Number.isFinite(expiresMs) || expiresMs <= now() + MIN_REUSABLE_LEASE_REMAINING_MS) {
    return null;
  }
  rememberSecrets(grantToken);
  return {
    leaseId: meta.lease_id.trim(),
    accountId: meta.account_id ?? null,
    label: meta.label ?? null,
    backendApiUrl: meta.backend_api_url.trim(),
    nativeBackendApi: meta.native_backend_api !== false,
    expiresAt: meta.expires_at,
    grantToken,
  };
}

function writeLeaseFiles(fs, runtimeDir, leaseReply, { autoRotate, now }) {
  const lease = leaseReply?.lease;
  const account = leaseReply?.account ?? {};
  if (!lease || lease.delivery_mode !== 'gateway_grant') {
    throw new CloudAccountsError(
      'PDD Cloud returned a non-gateway Codex lease; upgrade PDD Cloud gateway support before running pdd-codex.',
      { code: 'invalid_lease' },
    );
  }
  const grantToken = String(lease.codex_gateway_token || lease.gateway_bearer_token || '').trim();
  if (!grantToken.startsWith('pddg_')) {
    throw new CloudAccountsError('PDD Cloud returned an invalid Codex gateway grant token.', { code: 'invalid_lease' });
  }
  rememberSecrets(grantToken);
  const hasExplicitBackendApi = typeof lease.codex_backend_api_url === 'string' && Boolean(lease.codex_backend_api_url.trim());
  const backendApiUrl = resolveCodexBackendApiUrl(lease, null, { preserveLegacyBase: !hasExplicitBackendApi });
  if (!backendApiUrl) {
    throw new CloudAccountsError('PDD Cloud lease did not include a Codex gateway URL.', { code: 'invalid_lease' });
  }
  const nowIso = new Date(now()).toISOString();
  const planType = lease.plan_type ?? account.plan_type ?? account.plan ?? null;
  const authPayload = buildGatewayAuthJson({ grantToken, planType, now });
  const metaPayload = {
    lease_id: lease.lease_id ?? null,
    account_id: account.account_id ?? null,
    label: account.label ?? null,
    backend_api_url: backendApiUrl,
    native_backend_api: hasExplicitBackendApi,
    expires_at: lease.expires_at ?? null,
    delivery_mode: lease.delivery_mode,
    plan_type: planType,
    auto_rotate: Boolean(autoRotate),
    obtained_at: nowIso,
    last_heartbeat_at: nowIso,
  };
  writeAtomicPrivate(fs, join(runtimeDir, 'auth.json'), `${JSON.stringify(authPayload, null, 2)}\n`);
  writeAtomicPrivate(fs, join(runtimeDir, 'lease.json'), `${JSON.stringify(metaPayload, null, 2)}\n`);
  return {
    leaseId: metaPayload.lease_id,
    accountId: metaPayload.account_id,
    label: metaPayload.label,
    backendApiUrl,
    nativeBackendApi: hasExplicitBackendApi,
    expiresAt: metaPayload.expires_at,
    grantToken,
  };
}

/**
 * Acquire a shared machine runtime session (PID-refcounted, 1 lease across N concurrent sessions).
 * Propagates the locally active `accounts-state.json` Codex seat (from `pdd accounts use`/`next`)
 * into `leaseCloudAccount` when acquiring a new shared lease.
 */
export async function acquireSharedRuntimeSession({ cwd = process.cwd(), env = process.env } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const nowFn = ports.now ?? Date.now;
  const isPidAlive = ports.isPidAlive ?? defaultIsPidAlive;
  const myPid = ports.pid ?? process.pid;
  const expectedUid = typeof process.getuid === 'function' ? process.getuid() : null;
  const runtimeDir = sharedRuntimeDirPath({ env, tmpRoot: ports.tmpRoot, uid: ports.uid });
  const userCodexHome = localCodexHome(env);

  assertSafeRuntimeDir(fs, dirname(runtimeDir), { expectedUid, label: 'PDD Codex runtime root' });
  assertSafeRuntimeDir(fs, runtimeDir, { expectedUid, label: 'PDD Codex runtime' });

  return withCodexRuntimeLock(fs, runtimeDir, async () => {
    const pidsDir = join(runtimeDir, 'pids');
    const existingLivePids = sweepLivePids(fs, pidsDir, isPidAlive, { createDir: true });
    const myPidFile = join(pidsDir, String(myPid));
    writeAtomicPrivate(fs, myPidFile, JSON.stringify({ pid: myPid, started_at: new Date(nowFn()).toISOString() }));

    try {
      const homeInfo = prepareRuntimeCodexHome(fs, userCodexHome, runtimeDir);
      const savedActiveCodex = readCloudAccountsState({ env }, { fs })?.active?.codex;
      const savedActiveId = typeof savedActiveCodex?.account_id === 'string' && savedActiveCodex.account_id
        && savedActiveCodex.state !== 'reauth_required'
        ? savedActiveCodex.account_id
        : null;
      const existing = readReusableRuntimeLease(fs, runtimeDir, { now: nowFn });
      const seatMatchesOrShared = existingLivePids.length > 0
        || !savedActiveId
        || !existing?.accountId
        || existing.accountId === savedActiveId;
      if (existing && seatMatchesOrShared) {
        return {
          reused: true,
          pinned: false,
          pid: myPid,
          runtimeDir,
          ...homeInfo,
          ...existing,
        };
      }

      const leaseReply = await (ports.leaseCloudAccount ?? leaseCloudAccount)({
        provider: 'codex',
        ...(savedActiveId ? { currentAccountId: savedActiveId } : {}),
        holderId: 'pdd-codex',
        updateState: false,
        autoRotate: true,
      }, { cwd, env, timeoutMs: ports.leaseTimeoutMs ?? 15_000, now: nowFn }, ports);

      if (leaseReply?.state === 'all_cooling') {
        const wakeAt = leaseReply.wake_at ? ` until ${leaseReply.wake_at}` : '';
        throw new CloudAccountsError(`All shared Codex accounts are cooling${wakeAt}.`, { code: 'all_cooling' });
      }
      if (!leaseReply || leaseReply.state !== 'leased') {
        throw new CloudAccountsError(
          'No ready Codex account is available in PDD Cloud. Run `gh auth login`, `pdd accounts add --provider codex`, or run stock `codex` for your personal account.',
          { code: 'no_account_available' },
        );
      }

      const leaseInfo = writeLeaseFiles(fs, runtimeDir, leaseReply, { autoRotate: true, now: nowFn });
      stopCodexAppServerDaemon(runtimeDir, { env, fs, spawnSync: ports.spawnSync, codexBin: ports.codexBin });
      return {
        reused: false,
        pinned: false,
        pid: myPid,
        runtimeDir,
        ...homeInfo,
        ...leaseInfo,
      };
    } catch (err) {
      unlinkQuiet(fs, myPidFile);
      throw err;
    }
  }, ports);
}

/**
 * Unregister this PID and delete `auth.json` + revoke the cloud lease when the last session exits.
 */
export async function releaseSharedRuntimeSession(runtimeDir, { cwd = process.cwd(), env = process.env } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const isPidAlive = ports.isPidAlive ?? defaultIsPidAlive;
  const myPid = ports.pid ?? process.pid;

  let cleanupOutcome = { isLastSession: false, leaseId: null };
  try {
    cleanupOutcome = await withCodexRuntimeLock(fs, runtimeDir, async () => {
      const pidsDir = join(runtimeDir, 'pids');
      unlinkQuiet(fs, join(pidsDir, String(myPid)));
      const remaining = sweepLivePids(fs, pidsDir, isPidAlive, { createDir: true });
      if (remaining.length > 0) {
        return { isLastSession: false, leaseId: null, remainingPids: remaining.length };
      }
      const meta = readJsonObjectQuiet(fs, join(runtimeDir, 'lease.json'));
      const leaseId = typeof meta?.lease_id === 'string' && meta.lease_id.trim() ? meta.lease_id.trim() : null;
      unlinkQuiet(fs, join(runtimeDir, 'auth.json'));
      unlinkQuiet(fs, join(runtimeDir, 'lease.json'));
      stopCodexAppServerDaemon(runtimeDir, { env, fs, spawnSync: ports.spawnSync, codexBin: ports.codexBin });
      return { isLastSession: true, leaseId, remainingPids: 0 };
    }, ports);
  } catch {
    unlinkQuiet(fs, join(runtimeDir, 'pids', String(myPid)));
    return cleanupOutcome;
  }

  if (cleanupOutcome.isLastSession && cleanupOutcome.leaseId) {
    await (ports.releaseCloudLease ?? releaseCloudLease)(
      cleanupOutcome.leaseId,
      { cwd, env, timeoutMs: ports.releaseTimeoutMs ?? 2500 },
      ports,
    ).catch(() => {});
  }
  return cleanupOutcome;
}

/**
 * Acquire an isolated temporary runtime session pinned to `--account <label>` (`auto_rotate: false`).
 */
export async function acquirePinnedRuntimeSession(preferredLabel, { cwd = process.cwd(), env = process.env } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const nowFn = ports.now ?? Date.now;
  const myPid = ports.pid ?? process.pid;
  const expectedUid = typeof process.getuid === 'function' ? process.getuid() : null;
  const root = resolveRuntimeRoot({ env, tmpRoot: ports.tmpRoot });
  assertSafeRuntimeDir(fs, root, { expectedUid, label: 'PDD Codex runtime root' });
  const pinDir = fs.mkdtempSync(join(resolve(root), 'pdd-codex-pin-'));
  try { fs.chmodSync?.(pinDir, 0o700); } catch {}

  try {
    const homeInfo = prepareRuntimeCodexHome(fs, localCodexHome(env), pinDir);
    const leaseReply = await (ports.leaseCloudAccount ?? leaseCloudAccount)({
      provider: 'codex',
      preferredLabel,
      currentAccountId: null,
      holderId: 'pdd-codex-pin',
      updateState: false,
      autoRotate: false,
    }, { cwd, env, timeoutMs: ports.leaseTimeoutMs ?? 15_000, now: nowFn }, ports);

    if (leaseReply?.state === 'all_cooling') {
      const wakeAt = leaseReply.wake_at ? ` until ${leaseReply.wake_at}` : '';
      throw new CloudAccountsError(`Pinned Codex account "${preferredLabel}" is cooling${wakeAt}.`, { code: 'all_cooling' });
    }
    if (!leaseReply || leaseReply.state !== 'leased') {
      throw new CloudAccountsError(`Codex account "${preferredLabel}" is not available in PDD Cloud.`, { code: 'no_account_available' });
    }

    const leaseInfo = writeLeaseFiles(fs, pinDir, leaseReply, { autoRotate: false, now: nowFn });
    return {
      reused: false,
      pinned: true,
      pid: myPid,
      runtimeDir: pinDir,
      ...homeInfo,
      ...leaseInfo,
    };
  } catch (err) {
    try { fs.rmSync(pinDir, { recursive: true, force: true }); } catch {}
    throw err;
  }
}

async function releasePinnedRuntimeSession(session, { cwd = process.cwd(), env = process.env } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  try { fs.rmSync(session.runtimeDir, { recursive: true, force: true }); } catch {}
  if (session.leaseId) {
    await (ports.releaseCloudLease ?? releaseCloudLease)(
      session.leaseId,
      { cwd, env, timeoutMs: ports.releaseTimeoutMs ?? 2500 },
      ports,
    ).catch(() => {});
  }
}

function buildCleanChildEnv(baseEnv, runtimeDir, { grantToken = null } = {}) {
  const next = {};
  for (const [key, val] of Object.entries(baseEnv ?? {})) {
    if (typeof val === 'string') next[key] = val;
  }
  for (const key of STRIPPED_PROVIDER_ENV_VARS) {
    delete next[key];
  }
  next.CODEX_HOME = runtimeDir;
  if (typeof grantToken === 'string' && grantToken.startsWith('pddg_')) {
    next.CODEX_CONNECTORS_TOKEN = grantToken;
  }
  return next;
}

function spawnCodexProcess(command, args, { cwd, env, onChild = null }, ports = {}) {
  return spawnWrappedBinary(
    command,
    args,
    { cwd, env, onChild, customSpawn: ports.spawnCodex },
    ports,
  );
}

function startBackgroundHeartbeat(session, { cwd, env }, ports = {}) {
  if (!session?.leaseId) return () => {};
  const fs = ports.fs ?? nativeFs;
  const nowFn = ports.now ?? Date.now;
  const metaPath = join(session.runtimeDir, 'lease.json');

  return startLeaseHeartbeat({
    initialLeaseId: session.leaseId,
    leasePath: metaPath,
    runtimeDir: session.runtimeDir,
    shared: !session.pinned,
    lockName: 'lock',
    lockLabel: 'PDD Codex runtime',
    timeoutCode: 'lock_timeout',
    intervalMs: ports.heartbeatIntervalMs ?? DEFAULT_HEARTBEAT_INTERVAL_MS,
    minSpacingRatio: 0.75,
    jitterCapMs: 30_000,
    jitterRatio: 0.2,
    heartbeatTimeoutMs: ports.heartbeatTimeoutMs ?? 5000,
    heartbeatFn: ports.heartbeatCloudLease ?? heartbeatCloudLease,
    onRefresh: async (targetLeaseId, reply) => {
      if (!reply?.expires_at || session.pinned) return;
      const currentMeta = readJsonObjectQuiet(fs, metaPath);
      if (currentMeta && currentMeta.lease_id === targetLeaseId) {
        currentMeta.expires_at = reply.expires_at;
        currentMeta.last_heartbeat_at = new Date(nowFn()).toISOString();
        writeAtomicPrivate(fs, metaPath, `${JSON.stringify(currentMeta, null, 2)}\n`);
      }
    },
    onInvalidated: async targetLeaseId => {
      if (session.pinned) return;
      const currentMeta = readJsonObjectQuiet(fs, metaPath);
      if (currentMeta && currentMeta.lease_id === targetLeaseId) {
        unlinkQuiet(fs, join(session.runtimeDir, 'auth.json'));
        unlinkQuiet(fs, metaPath);
        stopCodexAppServerDaemon(session.runtimeDir, { env, fs, spawnSync: ports.spawnSync, codexBin: ports.codexBin });
      }
    },
    cwd,
    env,
    fs,
    now: nowFn,
    ports,
  });
}

/**
 * Clear the shared PDD Codex runtime auth.json and revoke the lease without touching ~/.codex/auth.json.
 */
async function runPddCodexLogout({ cwd, env, stdout }, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const expectedUid = typeof process.getuid === 'function' ? process.getuid() : null;
  const runtimeDir = sharedRuntimeDirPath({ env, tmpRoot: ports.tmpRoot, uid: ports.uid });
  let leaseId = null;
  if (fs.existsSync?.(runtimeDir)) {
    assertSafeRuntimeDir(fs, dirname(runtimeDir), { expectedUid, label: 'PDD Codex runtime root' });
    assertSafeRuntimeDir(fs, runtimeDir, { expectedUid, label: 'PDD Codex runtime' });
    try {
      await withCodexRuntimeLock(fs, runtimeDir, async () => {
        const meta = readJsonObjectQuiet(fs, join(runtimeDir, 'lease.json'));
        leaseId = typeof meta?.lease_id === 'string' && meta.lease_id.trim() ? meta.lease_id.trim() : null;
        unlinkQuiet(fs, join(runtimeDir, 'auth.json'));
        unlinkQuiet(fs, join(runtimeDir, 'lease.json'));
        stopCodexAppServerDaemon(runtimeDir, { env, fs, spawnSync: ports.spawnSync, codexBin: ports.codexBin });
      }, ports);
    } catch {}
  }
  if (leaseId) {
    await (ports.releaseCloudLease ?? releaseCloudLease)(
      leaseId,
      { cwd, env, timeoutMs: ports.releaseTimeoutMs ?? 2500 },
      ports,
    ).catch(() => {});
  }
  stdout?.write?.('Cleared PDD Codex session lease (your personal ~/.codex/auth.json was not touched).\n');
  return { exitCode: 0 };
}

/**
 * Main entrypoint for the `pdd-codex` command.
 */
export async function runPddCodexCli(
  argv = process.argv.slice(2),
  { cwd = process.cwd(), env = process.env, stdout = process.stdout, stderr = process.stderr } = {},
  ports = {},
) {
  const fs = ports.fs ?? nativeFs;
  const expectedUid = typeof process.getuid === 'function' ? process.getuid() : null;
  const codexBin = (typeof env?.PDD_CODEX_BIN === 'string' && env.PDD_CODEX_BIN.trim())
    ? env.PDD_CODEX_BIN.trim()
    : 'codex';

  let parsed;
  try {
    parsed = parsePddCodexArgs(argv);
  } catch (err) {
    stderr?.write?.(`${redactSecrets(err?.message ?? String(err))}\n`);
    return { exitCode: 2 };
  }

  if (parsed.showPddHelp) {
    stdout?.write?.(PDD_CODEX_HELP_TEXT);
    return { exitCode: 0 };
  }

  const codexArgs = parsed.codexArgs;
  const invocation = inspectCodexInvocation(codexArgs);
  const { subcommand, subArgs, hasHelpOrVersion } = invocation;
  const mcpSubcommand = subcommand === 'mcp' ? inspectCodexInvocation(subArgs).subcommand : '';

  const isMcpHelp = subcommand === 'mcp' && (!mcpSubcommand || mcpSubcommand === 'help');
  if (hasHelpOrVersion || NO_LEASE_SUBCOMMANDS.has(subcommand) || isMcpHelp) {
    const res = await spawnCodexProcess(codexBin, codexArgs, { cwd, env }, ports);
    if (res?.error) {
      stderr?.write?.(`Failed to start "${codexBin}": ${redactSecrets(res.error.message)}\n`);
    }
    return { exitCode: res?.exitCode ?? res?.code ?? 1 };
  }

  if (subcommand === 'logout') {
    try {
      return await runPddCodexLogout({ cwd, env, stdout }, { ...ports, codexBin });
    } catch (err) {
      stderr?.write?.(`pdd-codex: ${redactSecrets(err?.message ?? String(err))}\n`);
      return { exitCode: 1 };
    }
  }
  if (subcommand === 'login') {
    stdout?.write?.(
      'pdd-codex uses PDD Cloud shared accounts and never touches your personal ~/.codex/auth.json.\n'
      + 'Run `pdd accounts add --provider codex` to enroll an account, or run `codex login` for your personal account.\n',
    );
    return { exitCode: 0 };
  }

  const normalizeWritebackUnderLock = async writebackOpts => {
    if (!needsCodexConfigWritebackNormalization(fs, writebackOpts)) return false;
    const lockRuntimeDir = sharedRuntimeDirPath({ env, tmpRoot: ports.tmpRoot, uid: ports.uid });
    try {
      assertSafeRuntimeDir(fs, lockRuntimeDir, { expectedUid, label: 'PDD Codex runtime' });
      return await withCodexRuntimeLock(
        fs,
        lockRuntimeDir,
        () => normalizeCodexConfigWriteback(fs, writebackOpts),
        ports,
      );
    } catch {
      return normalizeCodexConfigWriteback(fs, writebackOpts);
    }
  };

  const isLocalMcp = subcommand === 'mcp' && LOCAL_MCP_SUBCOMMANDS.has(mcpSubcommand);
  if (isLocalMcp || LOCAL_OFFLINE_SUBCOMMANDS.has(subcommand)) {
    const root = resolveRuntimeRoot({ env, tmpRoot: ports.tmpRoot });
    let localDir = null;
    try {
      assertSafeRuntimeDir(fs, root, { expectedUid, label: 'PDD Codex runtime root' });
      localDir = fs.mkdtempSync(join(resolve(root), 'pdd-codex-mcp-'));
      try { fs.chmodSync?.(localDir, 0o700); } catch {}
      const homeInfo = prepareRuntimeCodexHome(fs, localCodexHome(env), localDir);
      let userConfigText = '';
      try { userConfigText = fs.readFileSync(homeInfo.userConfigPath, 'utf8'); } catch {}
      const localFlags = [];
      const effectiveSqliteHome = resolveEffectiveSqliteHome({
        userCodexHome: homeInfo.userCodexHome,
        userConfigText,
        env,
      });
      if (effectiveSqliteHome) {
        localFlags.push('-c', `sqlite_home=${JSON.stringify(effectiveSqliteHome)}`);
      }
      localFlags.push(...buildCodexHomeMirrorCliArgs({
        userCodexHome: homeInfo.userCodexHome,
        runtimeCodexHome: localDir,
        userConfigText,
        env,
        fs,
      }));
      const childEnv = buildCleanChildEnv(env, localDir);
      const res = await spawnCodexProcess(codexBin, [...localFlags, ...codexArgs], { cwd, env: childEnv }, ports);
      await normalizeWritebackUnderLock({
        userCodexHome: homeInfo.userCodexHome,
        runtimeCodexHome: localDir,
        userConfigPath: homeInfo.userConfigPath,
        beforeContent: userConfigText,
      });
      if (res?.error) {
        stderr?.write?.(`Failed to start "${codexBin}": ${redactSecrets(res.error.message)}\n`);
      }
      return { exitCode: res?.exitCode ?? res?.code ?? 1 };
    } catch (err) {
      stderr?.write?.(`pdd-codex: ${redactSecrets(err?.message ?? String(err))}\n`);
      return { exitCode: 1 };
    } finally {
      if (localDir) {
        try { fs.rmSync(localDir, { recursive: true, force: true }); } catch {}
      }
    }
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
      if (session.pinned && session.runtimeDir) {
        fs.rmSync(session.runtimeDir, { recursive: true, force: true });
      } else if (session.runtimeDir) {
        const myPid = session.pid ?? ports.pid ?? process.pid;
        unlinkQuiet(fs, join(session.runtimeDir, 'pids', String(myPid)));
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
        ? await acquirePinnedRuntimeSession(parsed.preferredAccount, { cwd, env }, { ...ports, codexBin })
        : await acquireSharedRuntimeSession({ cwd, env }, { ...ports, codexBin });
    } catch (err) {
      if (receivedSignal) return { exitCode: signalToExitCode(receivedSignal) };
      stderr?.write?.(`pdd-codex: ${redactSecrets(err?.message ?? String(err))}\n`);
      return { exitCode: 1 };
    }

    if (receivedSignal) {
      return { exitCode: signalToExitCode(receivedSignal) };
    }

    stopHeartbeat = startBackgroundHeartbeat(session, { cwd, env }, { ...ports, codexBin });

    let userConfigText = '';
    try { userConfigText = fs.readFileSync(session.userConfigPath, 'utf8'); } catch {}
    const cliFlags = buildCodexGatewayCliArgs({
      backendApiUrl: session.backendApiUrl,
      userCodexHome: session.userCodexHome,
      runtimeCodexHome: session.runtimeDir,
      userConfigText,
      nativeBackendApi: session.nativeBackendApi !== false,
      codexArgs,
      cwd,
      env,
      fs,
    });
    const forwardedCodexArgs = stripCodexCliEnvExcludeArgs(codexArgs);
    const childEnv = buildCleanChildEnv(env, session.runtimeDir, { grantToken: session.grantToken });
    const res = await spawnCodexProcess(
      codexBin,
      [...cliFlags, ...forwardedCodexArgs],
      { cwd, env: childEnv, onChild: child => { activeChild = child; } },
      ports,
    );
    await normalizeWritebackUnderLock({
      userCodexHome: session.userCodexHome,
      runtimeCodexHome: session.runtimeDir,
      userConfigPath: session.userConfigPath,
      beforeContent: userConfigText,
    });
    if (res?.error) {
      stderr?.write?.(`Failed to start "${codexBin}": ${redactSecrets(res.error.message)}\n`);
    }
    return { exitCode: res?.exitCode ?? res?.code ?? 1 };
  } finally {
    stopHeartbeat();
    if (session) {
      try {
        if (session.pinned) {
          await releasePinnedRuntimeSession(session, { cwd, env }, { ...ports, codexBin });
        } else {
          await releaseSharedRuntimeSession(session.runtimeDir, { cwd, env }, { ...ports, codexBin });
        }
        cleanedUp = true;
      } catch {
        syncEmergencyCleanup();
      }
    }
    detachHooks();
  }
}
