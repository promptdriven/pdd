// Generated from prompts/cli/pdd-codex.prompt.md.
// Dedicated PDD Codex launcher: shares one ~/.codex home + one PID-refcounted runtime dir
// per machine, passes gateway routing via -c flags, and cleans up auth.json + lease on last exit.
import { spawn as nativeSpawn } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { dirname, join, resolve, sep } from 'node:path';
import {
  buildCodexGatewayCliArgs,
  buildGatewayAuthJson,
  CloudAccountsError,
  ensureUserCodexHomeBaseline,
  heartbeatCloudLease,
  leaseCloudAccount,
  localCodexHome,
  releaseCloudLease,
  resolveCodexBackendApiUrl,
  resolvePddStateBase,
  stopCodexAppServerDaemon,
  syncManagedCodexHomeLinks,
} from './login-pool.mjs';
import { redactSecrets, rememberSecrets } from './secret-redaction.mjs';

const DEFAULT_LOCK_TIMEOUT_MS = 25_000;
const DEFAULT_STALE_LOCK_MS = 30_000;
const DEAD_LOCK_GRACE_MS = 1_500;
const DEFAULT_HEARTBEAT_INTERVAL_MS = 10 * 60 * 1000;
const MIN_REUSABLE_LEASE_REMAINING_MS = 5 * 60 * 1000;

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

function sleepMs(ms) {
  return new Promise(resolveTimer => {
    setTimeout(resolveTimer, ms);
  });
}

function defaultIsPidAlive(pid) {
  if (!Number.isInteger(pid) || pid <= 0) return false;
  try {
    process.kill(pid, 0);
    return true;
  } catch {
    // Runtime directory is 0700 per-UID, so EPERM means a recycled PID owned by another OS user.
    return false;
  }
}

function writePrivateAtomic(fs, targetPath, content) {
  fs.mkdirSync(dirname(targetPath), { recursive: true, mode: 0o700 });
  const tmpPath = `${targetPath}.tmp-${process.pid}-${randomBytes(6).toString('hex')}`;
  try {
    fs.writeFileSync(tmpPath, content, { encoding: 'utf8', mode: 0o600 });
    try { fs.chmodSync?.(tmpPath, 0o600); } catch {}
    fs.renameSync(tmpPath, targetPath);
  } catch (err) {
    try { fs.unlinkSync(tmpPath); } catch {}
    throw err;
  }
}

function readJsonFileQuiet(fs, targetPath) {
  try {
    const parsed = JSON.parse(fs.readFileSync(targetPath, 'utf8'));
    return parsed && typeof parsed === 'object' && !Array.isArray(parsed) ? parsed : null;
  } catch {
    return null;
  }
}

function unlinkQuiet(fs, targetPath) {
  try {
    fs.unlinkSync(targetPath);
  } catch {}
}

/**
 * Parse optional leading `pdd-codex` flags (`--account`, `--pdd-help`) without disturbing
 * stock Codex flags or user prompt arguments.
 */
export function parsePddCodexArgs(argv = []) {
  const args = Array.isArray(argv) ? argv.map(String) : [];
  let preferredAccount = null;
  let showPddHelp = false;
  let idx = 0;

  while (idx < args.length) {
    const token = args[idx];
    if (token === '--') {
      idx += 1;
      break;
    }
    if (token === '--pdd-help') {
      showPddHelp = true;
      idx += 1;
      continue;
    }
    if (token === '--account') {
      const value = args[idx + 1];
      if (typeof value !== 'string' || !value.trim() || value.startsWith('-')) {
        throw new CloudAccountsError('Missing account label after --account.', { code: 'invalid_argument' });
      }
      preferredAccount = value.trim();
      idx += 2;
      continue;
    }
    if (token.startsWith('--account=')) {
      const value = token.slice('--account='.length).trim();
      if (!value) {
        throw new CloudAccountsError('Missing account label after --account=.', { code: 'invalid_argument' });
      }
      preferredAccount = value;
      idx += 1;
      continue;
    }
    break;
  }

  return {
    preferredAccount,
    showPddHelp,
    codexArgs: args.slice(idx),
  };
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

function ensureSecureDirectory(fs, dirPath, { expectedUid = null } = {}) {
  const lstat = fs.lstatSync ?? nativeFs.lstatSync;
  let stat = null;
  try {
    stat = lstat.call(fs, dirPath);
  } catch (err) {
    if (err?.code !== 'ENOENT') throw err;
  }
  if (stat) {
    if (stat.isSymbolicLink() || !stat.isDirectory()) {
      throw new CloudAccountsError(`Refusing unsafe PDD Codex runtime path at ${dirPath}.`, { code: 'unsafe_runtime_dir' });
    }
    if (expectedUid !== null && typeof stat.uid === 'number' && stat.uid !== expectedUid) {
      throw new CloudAccountsError(`PDD Codex runtime folder at ${dirPath} is owned by another user.`, { code: 'unsafe_runtime_dir' });
    }
  } else {
    fs.mkdirSync(dirPath, { recursive: true, mode: 0o700 });
  }
  try { fs.chmodSync?.(dirPath, 0o700); } catch {}
}

function tryBreakLockAtomically(fs, runtimeDir, lockDir) {
  const staleDir = join(runtimeDir, `.lock-stale-${process.pid}-${randomBytes(4).toString('hex')}`);
  try {
    fs.renameSync(lockDir, staleDir);
  } catch {
    return false;
  }
  try { fs.rmSync(staleDir, { recursive: true, force: true }); } catch {}
  return true;
}

/**
 * Acquire an atomic cross-process directory lock inside `runtimeDir` with dead-owner and stale-lock recovery.
 */
async function withRuntimeLock(fs, runtimeDir, fn, ports = {}) {
  const nowFn = ports.now ?? Date.now;
  const sleep = ports.sleep ?? sleepMs;
  const isPidAlive = ports.isPidAlive ?? defaultIsPidAlive;
  const ownerPid = ports.pid ?? process.pid;
  const lockTimeoutMs = ports.lockTimeoutMs ?? DEFAULT_LOCK_TIMEOUT_MS;
  const staleLockMs = ports.staleLockMs ?? DEFAULT_STALE_LOCK_MS;
  const lockDir = join(runtimeDir, 'lock');
  const ownerPath = join(lockDir, 'owner.json');
  const deadline = nowFn() + lockTimeoutMs;

  while (true) {
    try {
      fs.mkdirSync(lockDir, { mode: 0o700 });
      try {
        fs.writeFileSync(ownerPath, JSON.stringify({ pid: ownerPid, acquired_at: nowFn() }), { encoding: 'utf8', mode: 0o600 });
      } catch {}
      break;
    } catch (err) {
      if (err?.code !== 'EEXIST') throw err;
      try {
        const st = fs.statSync(lockDir);
        const ageMs = typeof st?.mtimeMs === 'number' ? (nowFn() - st.mtimeMs) : 0;
        const owner = readJsonFileQuiet(fs, ownerPath);
        const ownerDead = Number.isInteger(owner?.pid)
          && owner.pid > 0
          && !isPidAlive(owner.pid)
          && ageMs >= DEAD_LOCK_GRACE_MS;
        if (ownerDead || ageMs > staleLockMs) {
          if (tryBreakLockAtomically(fs, runtimeDir, lockDir)) continue;
        }
      } catch {}
      if (nowFn() >= deadline) {
        throw new CloudAccountsError('Timed out waiting for PDD Codex runtime lock.', { code: 'lock_timeout' });
      }
      await sleep(15 + Math.floor(Math.random() * 25));
    }
  }

  try {
    return await fn();
  } finally {
    try { fs.rmSync(lockDir, { recursive: true, force: true }); } catch {}
  }
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
    // Atomic rename avoids an ENOENT window for concurrent Codex processes reading config.toml.
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
  if (resolvedUserHome === resolvedRuntimeDir || resolvedUserHome.startsWith(`${resolvedRuntimeDir}${sep}`)) {
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

  const emptySubshellDir = join(resolvedRuntimeDir, 'empty-subshell');
  fs.mkdirSync(emptySubshellDir, { recursive: true, mode: 0o700 });
  try { fs.chmodSync?.(emptySubshellDir, 0o700); } catch {}

  return {
    userCodexHome: resolvedUserHome,
    userConfigPath,
    emptySubshellDir,
  };
}

function sweepAndListLivePids(fs, pidsDir, isPidAlive) {
  fs.mkdirSync(pidsDir, { recursive: true, mode: 0o700 });
  const live = [];
  let entries = [];
  try {
    entries = fs.readdirSync(pidsDir);
  } catch {
    return live;
  }
  for (const name of entries) {
    if (!/^\d+$/.test(name)) {
      unlinkQuiet(fs, join(pidsDir, name));
      continue;
    }
    const pidNum = Number(name);
    if (isPidAlive(pidNum)) {
      live.push(pidNum);
    } else {
      unlinkQuiet(fs, join(pidsDir, name));
    }
  }
  return live;
}

function readReusableRuntimeLease(fs, runtimeDir, { now }) {
  const meta = readJsonFileQuiet(fs, join(runtimeDir, 'lease.json'));
  const auth = readJsonFileQuiet(fs, join(runtimeDir, 'auth.json'));
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
  writePrivateAtomic(fs, join(runtimeDir, 'auth.json'), `${JSON.stringify(authPayload, null, 2)}\n`);
  writePrivateAtomic(fs, join(runtimeDir, 'lease.json'), `${JSON.stringify(metaPayload, null, 2)}\n`);
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
 */
export async function acquireSharedRuntimeSession({ cwd = process.cwd(), env = process.env } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const nowFn = ports.now ?? Date.now;
  const isPidAlive = ports.isPidAlive ?? defaultIsPidAlive;
  const myPid = ports.pid ?? process.pid;
  const expectedUid = typeof process.getuid === 'function' ? process.getuid() : null;
  const runtimeDir = sharedRuntimeDirPath({ env, tmpRoot: ports.tmpRoot, uid: ports.uid });
  const userCodexHome = localCodexHome(env);

  ensureSecureDirectory(fs, runtimeDir, { expectedUid });

  return withRuntimeLock(fs, runtimeDir, async () => {
    const pidsDir = join(runtimeDir, 'pids');
    sweepAndListLivePids(fs, pidsDir, isPidAlive);
    const myPidFile = join(pidsDir, String(myPid));
    writePrivateAtomic(fs, myPidFile, JSON.stringify({ pid: myPid, started_at: new Date(nowFn()).toISOString() }));

    try {
      const homeInfo = prepareRuntimeCodexHome(fs, userCodexHome, runtimeDir);
      const existing = readReusableRuntimeLease(fs, runtimeDir, { now: nowFn });
      if (existing) {
        return {
          reused: true,
          pinned: false,
          runtimeDir,
          ...homeInfo,
          ...existing,
        };
      }

      const leaseReply = await (ports.leaseCloudAccount ?? leaseCloudAccount)({
        provider: 'codex',
        currentAccountId: null,
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
      stopCodexAppServerDaemon(runtimeDir, { env, fs, spawnSync: ports.spawnSync });
      return {
        reused: false,
        pinned: false,
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
    cleanupOutcome = await withRuntimeLock(fs, runtimeDir, async () => {
      const pidsDir = join(runtimeDir, 'pids');
      unlinkQuiet(fs, join(pidsDir, String(myPid)));
      const remaining = sweepAndListLivePids(fs, pidsDir, isPidAlive);
      if (remaining.length > 0) {
        return { isLastSession: false, leaseId: null, remainingPids: remaining.length };
      }
      const meta = readJsonFileQuiet(fs, join(runtimeDir, 'lease.json'));
      const leaseId = typeof meta?.lease_id === 'string' && meta.lease_id.trim() ? meta.lease_id.trim() : null;
      unlinkQuiet(fs, join(runtimeDir, 'auth.json'));
      unlinkQuiet(fs, join(runtimeDir, 'lease.json'));
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
  const root = resolveRuntimeRoot({ env, tmpRoot: ports.tmpRoot });
  fs.mkdirSync(root, { recursive: true, mode: 0o700 });
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
  // Stock Codex's built-in `codex_apps` MCP client only attaches ChatGPT auth to chatgpt.com;
  // setting CODEX_CONNECTORS_TOKEN passes our revocable `pddg_*` grant to `{chatgpt_base_url}/ps/mcp`
  // while `shell_environment_policy.exclude` keeps it out of Codex subshells.
  if (typeof grantToken === 'string' && grantToken.startsWith('pddg_')) {
    next.CODEX_CONNECTORS_TOKEN = grantToken;
  }
  return next;
}

function spawnCodexProcess(command, args, { cwd, env }, ports = {}) {
  if (typeof ports.spawnCodex === 'function') {
    return Promise.resolve(ports.spawnCodex(command, args, { cwd, env }));
  }
  return new Promise(resolveExit => {
    const child = (ports.spawn ?? nativeSpawn)(command, args, {
      cwd,
      env,
      stdio: 'inherit',
    });
    const forward = sig => {
      try { child.kill(sig); } catch {}
    };
    const onSigInt = () => forward('SIGINT');
    const onSigTerm = () => forward('SIGTERM');
    const onSigHup = () => forward('SIGHUP');
    process.on('SIGINT', onSigInt);
    process.on('SIGTERM', onSigTerm);
    process.on('SIGHUP', onSigHup);

    const detach = () => {
      process.off('SIGINT', onSigInt);
      process.off('SIGTERM', onSigTerm);
      process.off('SIGHUP', onSigHup);
    };

    child.on('error', err => {
      detach();
      resolveExit({ code: 1, error: err });
    });
    child.on('close', (code, signal) => {
      detach();
      if (signal === 'SIGINT') return resolveExit({ code: 130 });
      if (signal === 'SIGTERM') return resolveExit({ code: 143 });
      if (signal === 'SIGHUP') return resolveExit({ code: 129 });
      resolveExit({ code: typeof code === 'number' ? code : 1 });
    });
  });
}

function startBackgroundHeartbeat(session, { cwd, env }, ports = {}) {
  if (!session?.leaseId) return () => {};
  const intervalMs = ports.heartbeatIntervalMs ?? DEFAULT_HEARTBEAT_INTERVAL_MS;
  if (!Number.isFinite(intervalMs) || intervalMs <= 0) return () => {};
  const fs = ports.fs ?? nativeFs;
  const nowFn = ports.now ?? Date.now;
  let stopped = false;
  let inFlight = false;
  let timer = null;

  const stop = () => {
    stopped = true;
    if (timer) clearTimeout(timer);
    timer = null;
  };

  const scheduleNext = () => {
    if (stopped) return;
    const jitterMs = intervalMs >= 1000 ? Math.floor(Math.random() * Math.min(30_000, intervalMs * 0.2)) : 0;
    timer = setTimeout(() => { void tick(); }, intervalMs + jitterMs);
    timer.unref?.();
  };

  const tick = async () => {
    if (stopped || inFlight) return;
    inFlight = true;
    let targetLeaseId = session.leaseId;
    try {
      if (!session.pinned) {
        const meta = readJsonFileQuiet(fs, join(session.runtimeDir, 'lease.json'));
        if (!meta || typeof meta.lease_id !== 'string' || !meta.lease_id.trim()) {
          stop();
          return;
        }
        targetLeaseId = meta.lease_id.trim();
        // Deduplicate heartbeats across concurrent sessions sharing one runtime lease.
        const lastHbMs = Date.parse(String(meta.last_heartbeat_at ?? ''));
        if (Number.isFinite(lastHbMs) && (nowFn() - lastHbMs) < Math.floor(intervalMs * 0.75)) {
          return;
        }
      }

      const reply = await (ports.heartbeatCloudLease ?? heartbeatCloudLease)(
        targetLeaseId,
        { cwd, env, timeoutMs: ports.heartbeatTimeoutMs ?? 5000 },
        ports,
      );
      if (stopped) return;
      if (reply?.expires_at && !session.pinned) {
        await withRuntimeLock(fs, session.runtimeDir, async () => {
          if (stopped) return;
          const metaPath = join(session.runtimeDir, 'lease.json');
          const currentMeta = readJsonFileQuiet(fs, metaPath);
          if (currentMeta && currentMeta.lease_id === targetLeaseId) {
            currentMeta.expires_at = reply.expires_at;
            currentMeta.last_heartbeat_at = new Date(nowFn()).toISOString();
            writePrivateAtomic(fs, metaPath, `${JSON.stringify(currentMeta, null, 2)}\n`);
          }
        }, ports).catch(() => {});
      }
    } catch (err) {
      if (err?.status === 401 || err?.status === 403) {
        if (!session.pinned) {
          await withRuntimeLock(fs, session.runtimeDir, async () => {
            const metaPath = join(session.runtimeDir, 'lease.json');
            const currentMeta = readJsonFileQuiet(fs, metaPath);
            if (currentMeta && currentMeta.lease_id === targetLeaseId) {
              unlinkQuiet(fs, join(session.runtimeDir, 'auth.json'));
              unlinkQuiet(fs, metaPath);
            }
          }, ports).catch(() => {});
        }
        stop();
      } else if (err?.status === 404) {
        stop();
      }
    } finally {
      inFlight = false;
      scheduleNext();
    }
  };

  scheduleNext();
  return stop;
}

/**
 * Clear the shared PDD Codex runtime auth.json and revoke the lease without touching ~/.codex/auth.json.
 */
async function runPddCodexLogout({ cwd, env, stdout }, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const runtimeDir = sharedRuntimeDirPath({ env, tmpRoot: ports.tmpRoot, uid: ports.uid });
  let leaseId = null;
  if (fs.existsSync?.(runtimeDir)) {
    try {
      await withRuntimeLock(fs, runtimeDir, async () => {
        const meta = readJsonFileQuiet(fs, join(runtimeDir, 'lease.json'));
        leaseId = typeof meta?.lease_id === 'string' && meta.lease_id.trim() ? meta.lease_id.trim() : null;
        unlinkQuiet(fs, join(runtimeDir, 'auth.json'));
        unlinkQuiet(fs, join(runtimeDir, 'lease.json'));
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
  const firstArg = codexArgs[0] ?? '';

  // Never let `pdd-codex logout` or `pdd-codex login` touch the user's personal ~/.codex/auth.json.
  if (firstArg === 'logout') {
    return runPddCodexLogout({ cwd, env, stdout }, ports);
  }
  if (firstArg === 'login') {
    stdout?.write?.(
      'pdd-codex uses PDD Cloud shared accounts and never touches your personal ~/.codex/auth.json.\n'
      + 'Run `pdd accounts add --provider codex` to enroll an account, or run `codex login` for your personal account.\n',
    );
    return { exitCode: 0 };
  }

  // Instant passthrough for purely local help/version/completion commands (no cloud lease needed).
  const isMcpHelp = firstArg === 'mcp' && (!codexArgs[1] || NO_LEASE_TOP_FLAGS.has(codexArgs[1]) || codexArgs[1] === 'help');
  if (NO_LEASE_TOP_FLAGS.has(firstArg) || NO_LEASE_SUBCOMMANDS.has(firstArg) || isMcpHelp) {
    const res = await spawnCodexProcess(codexBin, codexArgs, { cwd, env }, ports);
    if (res?.error) {
      stderr?.write?.(`Failed to start "${codexBin}": ${redactSecrets(res.error.message)}\n`);
    }
    return { exitCode: res?.code ?? 1 };
  }

  // Local `mcp add/remove/list/get` edits `~/.codex/config.toml` via symlink without needing a cloud lease.
  if (firstArg === 'mcp' && LOCAL_MCP_SUBCOMMANDS.has(codexArgs[1] ?? '')) {
    const root = resolveRuntimeRoot({ env, tmpRoot: ports.tmpRoot });
    fs.mkdirSync(root, { recursive: true, mode: 0o700 });
    const mcpDir = fs.mkdtempSync(join(resolve(root), 'pdd-codex-mcp-'));
    try { fs.chmodSync?.(mcpDir, 0o700); } catch {}
    try {
      prepareRuntimeCodexHome(fs, localCodexHome(env), mcpDir);
      const childEnv = buildCleanChildEnv(env, mcpDir);
      const res = await spawnCodexProcess(codexBin, codexArgs, { cwd, env: childEnv }, ports);
      if (res?.error) {
        stderr?.write?.(`Failed to start "${codexBin}": ${redactSecrets(res.error.message)}\n`);
      }
      return { exitCode: res?.code ?? 1 };
    } finally {
      try { fs.rmSync(mcpDir, { recursive: true, force: true }); } catch {}
    }
  }

  let session = null;
  try {
    session = parsed.preferredAccount
      ? await acquirePinnedRuntimeSession(parsed.preferredAccount, { cwd, env }, ports)
      : await acquireSharedRuntimeSession({ cwd, env }, ports);
  } catch (err) {
    stderr?.write?.(`pdd-codex: ${redactSecrets(err?.message ?? String(err))}\n`);
    return { exitCode: 1 };
  }

  const stopHeartbeat = startBackgroundHeartbeat(session, { cwd, env }, ports);
  try {
    let userConfigText = '';
    try {
      userConfigText = fs.readFileSync(session.userConfigPath, 'utf8');
    } catch {}
    const cliFlags = buildCodexGatewayCliArgs({
      backendApiUrl: session.backendApiUrl,
      userCodexHome: session.userCodexHome,
      emptySubshellCodexHome: session.emptySubshellDir,
      userConfigText,
      nativeBackendApi: session.nativeBackendApi !== false,
    });
    const childEnv = buildCleanChildEnv(env, session.runtimeDir, { grantToken: session.grantToken });
    const res = await spawnCodexProcess(codexBin, [...cliFlags, ...codexArgs], { cwd, env: childEnv }, ports);
    if (res?.error) {
      stderr?.write?.(`Failed to start "${codexBin}": ${redactSecrets(res.error.message)}\n`);
    }
    return { exitCode: res?.code ?? 1 };
  } finally {
    stopHeartbeat();
    if (session.pinned) {
      await releasePinnedRuntimeSession(session, { cwd, env }, ports);
    } else {
      await releaseSharedRuntimeSession(session.runtimeDir, { cwd, env }, ports);
    }
  }
}
