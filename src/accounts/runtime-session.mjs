// Generated from prompts/cli/pdd-codex.prompt.md.
// Layer-1 shared runtime session engine for `pdd-codex` and `pdd-claude`:
// ancestor-safe private dirs, unified arg parsing, directory locking, PID sweeping,
// guarded lease heartbeats, process exit/signal cleanup, and ENOENT->127 spawning.
import * as nativeFs from 'node:fs';
import { join, resolve } from 'node:path';
import {
  assertSafePrivateDir,
  readJsonObjectQuiet,
  unlinkQuiet,
  writeAtomicPrivate,
} from '../shared/atomic-fs.mjs';
import { defaultIsPidAlive, withDirectoryLock } from '../shared/file-lock.mjs';
import { resolvePddStateBase } from '../shared/state-dir.mjs';
import { signalToExitCode, spawnInheritedProcess } from '../shared/subprocess.mjs';
import { CloudAccountsError } from './cloud-error.mjs';

export const DEFAULT_HEARTBEAT_INTERVAL_MS = 10 * 60 * 1000;
export const MIN_REUSABLE_LEASE_REMAINING_MS = 5 * 60 * 1000;

export {
  defaultIsPidAlive,
  readJsonObjectQuiet,
  signalToExitCode,
  unlinkQuiet,
  writeAtomicPrivate,
};

/**
 * Validate and create a `0700` private runtime directory owned by the current OS user,
 * rejecting untrusted symlink ancestors, symlinked targets, and foreign ownership both
 * before and after `mkdirSync`.
 */
export function assertSafeRuntimeDir(
  fs,
  dirPath,
  {
    checkAncestors = true,
    expectedUid = typeof process.getuid === 'function' ? process.getuid() : null,
    label = 'PDD runtime',
  } = {},
) {
  return assertSafePrivateDir(fs, dirPath, {
    checkAncestors,
    expectedUid,
    label,
    errorFactory: message => new CloudAccountsError(message, { code: 'unsafe_runtime_dir' }),
  });
}

/**
 * Parse optional leading wrapper flags (`--account <label>` / `--account=<label>` and `--pdd-help`),
 * rejecting blank, `--`, or dash-prefixed labels on BOTH space and `=` forms, and preserving `--`
 * when followed by an unknown dash-prefixed positional prompt.
 */
export function parseWrapperLeadingArgs(
  argv = [],
  {
    isKnownOption = () => false,
    missingMessage = 'Missing account label after --account.',
    missingEqMessage = missingMessage,
    missingCode = 'invalid_argument',
    exitCode = 2,
  } = {},
) {
  const args = Array.isArray(argv) ? argv.map(String) : [];
  let preferredAccount = null;
  let showPddHelp = false;
  let idx = 0;

  while (idx < args.length) {
    const token = args[idx];
    if (token === '--') {
      const nextToken = args[idx + 1];
      const nextIsPositionalDashPrompt = typeof nextToken === 'string'
        && nextToken.startsWith('-')
        && !isKnownOption(nextToken);
      if (idx > 0 && !nextIsPositionalDashPrompt) {
        idx += 1;
      }
      break;
    }
    if (token === '--pdd-help') {
      showPddHelp = true;
      idx += 1;
      continue;
    }
    if (token === '--account') {
      const nextRaw = args[idx + 1];
      const value = typeof nextRaw === 'string' ? nextRaw.trim() : '';
      if (!value || value === '--' || value.startsWith('-')) {
        throw new CloudAccountsError(missingMessage, { code: missingCode, exitCode });
      }
      preferredAccount = value;
      idx += 2;
      continue;
    }
    if (token.startsWith('--account=')) {
      const value = token.slice('--account='.length).trim();
      if (!value || value === '--' || value.startsWith('-')) {
        throw new CloudAccountsError(missingEqMessage, { code: missingCode, exitCode });
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
    restArgs: args.slice(idx),
  };
}

/**
 * Acquire an atomic cross-process directory lock inside `runtimeDir` using `withDirectoryLock`,
 * converting lock timeouts to `CloudAccountsError`.
 */
export async function withRuntimeDirLock(
  fs,
  runtimeDir,
  fn,
  {
    lockName = 'lock',
    timeoutCode = 'lock_timeout',
    label = 'PDD runtime',
    ports = {},
  } = {},
) {
  return withDirectoryLock(fs ?? nativeFs, runtimeDir, fn, {
    lockName,
    now: ports.now ?? Date.now,
    sleep: ports.sleep,
    isPidAlive: ports.isPidAlive ?? defaultIsPidAlive,
    pid: ports.pid ?? process.pid,
    lockTimeoutMs: ports.lockTimeoutMs,
    staleLockMs: ports.staleLockMs,
    onTimeout: () => new CloudAccountsError(
      `Timed out waiting for ${label} lock in "${runtimeDir}".`,
      { code: timeoutCode },
    ),
  });
}

/**
 * Sweep invalid or dead PID marker files inside `pidsDir` (strict `/^\d+$/`) and return live PIDs.
 */
export function sweepLivePids(fs, pidsDir, isPidAlive = defaultIsPidAlive, { createDir = false } = {}) {
  const f = fs ?? nativeFs;
  if (createDir) {
    f.mkdirSync(pidsDir, { recursive: true, mode: 0o700 });
  }
  const live = [];
  let entries = [];
  try {
    entries = f.readdirSync(pidsDir);
  } catch {
    return live;
  }
  for (const name of entries) {
    const validPidName = /^\d+$/.test(name);
    const pidNum = validPidName ? Number(name) : NaN;
    const full = join(pidsDir, name);
    if (!validPidName || !Number.isSafeInteger(pidNum) || pidNum <= 0 || !isPidAlive(pidNum)) {
      unlinkQuiet(f, full);
    } else {
      live.push(pidNum);
    }
  }
  return live;
}

/**
 * Start a background lease heartbeat timer (`.unref()`'d) that deduplicates across concurrent
 * shared sessions, persists refreshed expiries under the runtime lock, and clears revoked
 * (`401`/`403`/`404`) leases under the runtime lock ONLY when `!stopped` and the lease ID still matches.
 */
export function startLeaseHeartbeat({
  initialLeaseId,
  leasePath,
  runtimeDir,
  shared = true,
  lockName = 'lock',
  lockLabel = 'PDD runtime',
  timeoutCode = 'lock_timeout',
  intervalMs = DEFAULT_HEARTBEAT_INTERVAL_MS,
  minSpacingRatio = 0.6,
  jitterCapMs = 30_000,
  jitterRatio = 0.15,
  heartbeatTimeoutMs = undefined,
  heartbeatFn,
  onRefresh,
  onInvalidated,
  cwd = process.cwd(),
  env = process.env,
  fs = nativeFs,
  now = Date.now,
  ports = {},
}) {
  if (!initialLeaseId || !Number.isFinite(intervalMs) || intervalMs <= 0) return () => {};
  const minSpacingMs = intervalMs >= 1000
    ? Math.max(1_000, Math.floor(intervalMs * minSpacingRatio))
    : Math.floor(intervalMs * minSpacingRatio);

  let stopped = false;
  let inFlight = false;
  let timer = null;

  const stop = () => {
    stopped = true;
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  };

  const scheduleNext = () => {
    if (stopped) return;
    const jitter = intervalMs >= 1000
      ? Math.floor(Math.random() * Math.min(jitterCapMs, Math.floor(intervalMs * jitterRatio)))
      : 0;
    timer = setTimeout(() => { void tick(); }, intervalMs + jitter);
    timer.unref?.();
  };

  const withLockIfShared = fn => (
    shared
      ? withRuntimeDirLock(fs, runtimeDir, fn, { lockName, label: lockLabel, timeoutCode, ports })
      : fn()
  );

  const tick = async () => {
    if (stopped || inFlight) return;
    inFlight = true;
    let targetLeaseId = initialLeaseId;
    try {
      if (shared || leasePath) {
        const meta = readJsonObjectQuiet(fs, leasePath);
        if (shared) {
          if (!meta || typeof meta.lease_id !== 'string' || !meta.lease_id.trim()) {
            stop();
            return;
          }
          targetLeaseId = meta.lease_id.trim();
          const lastBeatMs = Date.parse(String(meta.last_heartbeat_at ?? ''));
          if (Number.isFinite(lastBeatMs) && (now() - lastBeatMs) < minSpacingMs) {
            return;
          }
        } else if (meta && typeof meta.lease_id === 'string' && meta.lease_id.trim()) {
          targetLeaseId = meta.lease_id.trim();
          const lastBeatMs = Date.parse(String(meta.last_heartbeat_at ?? ''));
          if (Number.isFinite(lastBeatMs) && (now() - lastBeatMs) < minSpacingMs) {
            return;
          }
        }
      }

      const beat = await heartbeatFn(
        targetLeaseId,
        { cwd, env, ...(heartbeatTimeoutMs ? { timeoutMs: heartbeatTimeoutMs } : {}) },
        ports,
      );
      if (stopped) return;
      if (typeof onRefresh === 'function') {
        await withLockIfShared(async () => {
          if (stopped) return;
          await onRefresh(targetLeaseId, beat);
        }).catch(() => {});
      }
    } catch (err) {
      const status = err?.status ?? 0;
      if (status === 401 || status === 403 || status === 404) {
        if (!stopped && typeof onInvalidated === 'function') {
          await withLockIfShared(async () => {
            if (stopped) return;
            await onInvalidated(targetLeaseId);
          }).catch(() => {});
        }
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
 * Attach process `exit` emergency cleanup and `SIGINT`/`SIGTERM`/`SIGHUP` forwarding hooks,
 * returning a `detach()` function to unregister all listeners cleanly in `finally`.
 */
export function registerProcessCleanupHooks({ onEmergencyExit, onSignal, proc = process }) {
  const onSigInt = () => onSignal?.('SIGINT');
  const onSigTerm = () => onSignal?.('SIGTERM');
  const onSigHup = () => onSignal?.('SIGHUP');

  proc.on('exit', onEmergencyExit);
  proc.on('SIGINT', onSigInt);
  proc.on('SIGTERM', onSigTerm);
  proc.on('SIGHUP', onSigHup);

  return () => {
    proc.off('exit', onEmergencyExit);
    proc.off('SIGINT', onSigInt);
    proc.off('SIGTERM', onSigTerm);
    proc.off('SIGHUP', onSigHup);
  };
}

/**
 * Spawn a wrapped CLI binary (`codex` or `claude`) with `stdio: 'inherit'`, optional test port
 * override, signal forwarding, and standard `ENOENT -> 127` exit code mapping.
 */
export function spawnWrappedBinary(command, args, { cwd, env, onChild = null, customSpawn = null } = {}, ports = {}) {
  if (typeof customSpawn === 'function') {
    return Promise.resolve(customSpawn(command, args, { cwd, env })).then(res => {
      const hasNumericCode = typeof res?.exitCode === 'number' || typeof res?.code === 'number';
      const fallback = res?.error?.code === 'ENOENT' ? 127 : 1;
      const code = hasNumericCode ? (res.exitCode ?? res.code) : fallback;
      return { ...res, code, exitCode: code };
    });
  }
  return spawnInheritedProcess(command, args, { cwd, env, onChild, spawn: ports?.spawn });
}

/**
 * Resolve the per-user `pdd-codex` runtime root (`~/.local/state/pdd/codex-runtime` by default,
 * never `/tmp` so Linux stock Codex creates helper binaries cleanly).
 */
export function resolveCodexRuntimeRoot({ env = process.env, tmpRoot = null } = {}) {
  if (typeof tmpRoot === 'string' && tmpRoot.trim()) return tmpRoot.trim();
  if (typeof env?.PDD_CODEX_RUNTIME_ROOT === 'string' && env.PDD_CODEX_RUNTIME_ROOT.trim()) {
    return env.PDD_CODEX_RUNTIME_ROOT.trim();
  }
  return join(resolvePddStateBase(env), 'codex-runtime');
}

/**
 * Resolve the per-user shared machine runtime directory (`<runtimeRoot>/pdd-codex-<uid>`).
 */
export function sharedCodexRuntimeDirPath({ env = process.env, tmpRoot = null, uid = null } = {}) {
  const root = resolveCodexRuntimeRoot({ env, tmpRoot });
  const effectiveUid = uid !== null && uid !== undefined
    ? String(uid)
    : (typeof process.getuid === 'function' ? String(process.getuid()) : 'user');
  return join(resolve(root), `pdd-codex-${effectiveUid}`);
}

function isSafeReadableDir(fs, dirPath, expectedUid) {
  const lstat = fs.lstatSync ?? nativeFs.lstatSync;
  let st;
  try { st = lstat.call(fs, dirPath); } catch { return false; }
  if (!st || st.isSymbolicLink() || !st.isDirectory()) return false;
  if (expectedUid !== null && typeof st.uid === 'number' && st.uid !== expectedUid) return false;
  return true;
}

function readSafeJsonRegularFile(fs, filePath, expectedUid) {
  const lstat = fs.lstatSync ?? nativeFs.lstatSync;
  let st;
  try { st = lstat.call(fs, filePath); } catch { return null; }
  if (!st || st.isSymbolicLink() || !st.isFile()) return null;
  if (expectedUid !== null && typeof st.uid === 'number' && st.uid !== expectedUid) return null;
  return readJsonObjectQuiet(fs, filePath);
}

function listLivePidsReadOnly(fs, pidsDir, isPidAlive, expectedUid) {
  if (!isSafeReadableDir(fs, pidsDir, expectedUid)) return [];
  let entries = [];
  try { entries = fs.readdirSync(pidsDir); } catch { return []; }
  const seen = new Set();
  for (const name of entries) {
    if (!/^\d+$/.test(name)) continue;
    const pidNum = Number(name);
    if (!Number.isSafeInteger(pidNum) || pidNum <= 0) continue;
    if (isPidAlive(pidNum)) seen.add(pidNum);
  }
  return [...seen].sort((a, b) => a - b);
}

function buildRuntimeLeaseSnapshot(meta, { mode, pinned, liveSessions }) {
  return {
    mode,
    pinned,
    lease_id: typeof meta.lease_id === 'string' ? meta.lease_id : null,
    account_id: typeof meta.account_id === 'string' ? meta.account_id : null,
    label: typeof meta.label === 'string' ? meta.label : null,
    is_owner: typeof meta.is_owner === 'boolean' ? meta.is_owner : null,
    shared: typeof meta.shared === 'boolean' ? meta.shared : null,
    owner_login: typeof meta.owner_login === 'string' ? meta.owner_login : null,
    auto_rotate: typeof meta.auto_rotate === 'boolean' ? meta.auto_rotate : !pinned,
    expires_at: typeof meta.expires_at === 'string' ? meta.expires_at : null,
    live_sessions: liveSessions,
  };
}

/**
 * Strictly read-only inspection of live `pdd-codex` runtime leases (shared + pinned).
 * Never creates directories, acquires locks, mutates PID files, follows symlinks,
 * reads foreign-owned entries, or opens `auth.json`.
 */
export function readLiveCodexRuntimeLeases({ env = process.env, tmpRoot = null, uid = null } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const isPidAlive = ports.isPidAlive ?? defaultIsPidAlive;
  const expectedUid = ports.expectedUid !== undefined
    ? ports.expectedUid
    : (typeof process.getuid === 'function' ? process.getuid() : null);

  const root = resolve(resolveCodexRuntimeRoot({ env, tmpRoot }));
  if (!isSafeReadableDir(fs, root, expectedUid)) return [];

  const results = [];
  const sharedDir = sharedCodexRuntimeDirPath({ env, tmpRoot, uid });
  if (isSafeReadableDir(fs, sharedDir, expectedUid)) {
    const meta = readSafeJsonRegularFile(fs, join(sharedDir, 'lease.json'), expectedUid);
    if (meta) {
      const livePids = listLivePidsReadOnly(fs, join(sharedDir, 'pids'), isPidAlive, expectedUid);
      if (livePids.length > 0) {
        results.push(buildRuntimeLeaseSnapshot(meta, {
          mode: 'shared',
          pinned: false,
          liveSessions: livePids.length,
        }));
      }
    }
  }

  let rootEntries = [];
  try { rootEntries = fs.readdirSync(root); } catch { rootEntries = []; }
  for (const name of rootEntries) {
    if (!name.startsWith('pdd-codex-pin-')) continue;
    const pinDir = join(root, name);
    if (!isSafeReadableDir(fs, pinDir, expectedUid)) continue;
    const meta = readSafeJsonRegularFile(fs, join(pinDir, 'lease.json'), expectedUid);
    if (!meta) continue;
    const pidsFromDir = listLivePidsReadOnly(fs, join(pinDir, 'pids'), isPidAlive, expectedUid);
    let liveSessions = pidsFromDir.length;
    if (liveSessions === 0 && Number.isSafeInteger(meta.pid) && meta.pid > 0 && isPidAlive(meta.pid)) {
      liveSessions = 1;
    }
    if (liveSessions > 0) {
      results.push(buildRuntimeLeaseSnapshot(meta, {
        mode: 'pinned',
        pinned: true,
        liveSessions,
      }));
    }
  }

  return results;
}
