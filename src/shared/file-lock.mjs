// Layer-0 cross-process file and directory locking primitives.
import { randomBytes, randomUUID } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { join } from 'node:path';
import { readJsonObjectQuiet } from './atomic-fs.mjs';

const DEFAULT_LOCK_TIMEOUT_MS = 25_000;
const DEFAULT_STALE_LOCK_MS = 30_000;
const DEAD_LOCK_GRACE_MS = 1_500;

const VALID_LOCK_TOKEN = value => typeof value === 'string' && /^[A-Za-z0-9._-]{1,128}$/.test(value);

function sleepMs(ms) {
  return new Promise(resolveTimer => {
    setTimeout(resolveTimer, ms);
  });
}

/**
 * Check whether an OS process owned by the current user is alive.
 * Runtime dirs are `0700` per-UID, so `EPERM` indicates a recycled PID owned by another OS user.
 */
export function defaultIsPidAlive(pid) {
  if (!Number.isInteger(pid) || pid <= 0) return false;
  try {
    process.kill(pid, 0);
    return true;
  } catch {
    return false;
  }
}

function lockProblem(cause) {
  const detail = cause?.code ? ` (${cause.code})` : '';
  const err = new Error(
    `Run lock is currently held by another active process${detail}. `
    + 'Wait for the other pdd command to finish or remove a stale lock after verifying its PID is dead, then rerun.',
  );
  err.code = 'run_busy';
  return err;
}

function readExclusiveLock(fs, lockPath) {
  const flags = (fs.constants?.O_RDONLY ?? 0)
    | (fs.constants?.O_NOFOLLOW ?? 0)
    | (fs.constants?.O_NONBLOCK ?? 0);
  const fd = fs.openSync(lockPath, flags);
  try {
    const value = JSON.parse(fs.readFileSync(fd, 'utf8'));
    if (
      !value || typeof value !== 'object' || Array.isArray(value)
      || Object.keys(value).some(key => !['pid', 'token'].includes(key))
      || !Number.isSafeInteger(value.pid) || value.pid < 1
      || !VALID_LOCK_TOKEN(value.token)
    ) {
      throw lockProblem();
    }
    return value;
  } finally {
    fs.closeSync(fd);
  }
}

function isOwnerDeadStrict(owner) {
  try {
    process.kill(owner.pid, 0);
    return false;
  } catch (error) {
    if (error?.code === 'ESRCH') return true;
    throw lockProblem();
  }
}

/**
 * Acquire an exclusive file lock inside `runDir` using `wx` + `fsyncSync`, with atomic
 * dead-PID recovery via a `.claim` file and owner-verified release.
 */
export function acquireRunLock(runDir, filename = 'chat-replacement.lock', { fs = nativeFs } = {}) {
  const lockPath = join(runDir, filename);
  const claimPath = `${lockPath}.claim`;
  const owner = { pid: process.pid, token: randomUUID() };
  const sameOwner = (a, b) => a.pid === b.pid && a.token === b.token;

  const create = () => {
    const fd = fs.openSync(lockPath, 'wx', 0o600);
    try {
      fs.writeFileSync(fd, JSON.stringify(owner));
      fs.fsyncSync?.(fd);
    } finally {
      fs.closeSync(fd);
    }
  };

  try {
    create();
  } catch (error) {
    if (error?.code !== 'EEXIST') throw lockProblem(error);
    let prior;
    let claimFd;
    try {
      prior = readExclusiveLock(fs, lockPath);
      if (!isOwnerDeadStrict(prior)) throw lockProblem();
      claimFd = fs.openSync(claimPath, 'wx', 0o600);
      if (!sameOwner(prior, readExclusiveLock(fs, lockPath)) || !isOwnerDeadStrict(prior)) {
        throw lockProblem();
      }
      fs.unlinkSync(lockPath);
      create();
    } catch {
      throw lockProblem();
    } finally {
      if (claimFd !== undefined) {
        try { fs.closeSync(claimFd); } catch {}
        try { fs.unlinkSync(claimPath); } catch {}
      }
    }
  }

  return () => {
    try {
      if (sameOwner(owner, readExclusiveLock(fs, lockPath))) {
        fs.unlinkSync(lockPath);
      }
    } catch {
      // Never remove another or unreadable owner's lock.
    }
  };
}

function tryBreakDirLockAtomically(fs, runtimeDir, lockDir, ownerPid) {
  const staleDir = join(runtimeDir, `.lock-stale-${ownerPid}-${randomBytes(4).toString('hex')}`);
  try {
    fs.renameSync(lockDir, staleDir);
  } catch {
    return false;
  }
  try { fs.rmSync(staleDir, { recursive: true, force: true }); } catch {}
  return true;
}

/**
 * Acquire an atomic `mkdir` directory lock inside `runtimeDir` with dead-owner grace recovery,
 * atomic stale-lock rename-and-remove recovery, jittered backoff, and owner-token-verified unlock.
 */
export async function withDirectoryLock(
  fs,
  runtimeDir,
  fn,
  {
    lockName = 'lock',
    now = Date.now,
    sleep = sleepMs,
    isPidAlive = defaultIsPidAlive,
    pid = process.pid,
    lockTimeoutMs = DEFAULT_LOCK_TIMEOUT_MS,
    staleLockMs = DEFAULT_STALE_LOCK_MS,
    onTimeout = null,
  } = {},
) {
  const f = fs ?? nativeFs;
  const lockDir = join(runtimeDir, lockName);
  const ownerPath = join(lockDir, 'owner.json');
  const lockToken = randomBytes(12).toString('hex');
  const deadline = now() + lockTimeoutMs;
  let acquired = false;
  let wroteOwner = false;

  while (true) {
    try {
      f.mkdirSync(lockDir, { mode: 0o700 });
      acquired = true;
      try {
        const acquiredAt = now();
        f.writeFileSync(
          ownerPath,
          JSON.stringify({ pid, token: lockToken, lockToken, acquired_at: acquiredAt, acquiredAt }),
          { encoding: 'utf8', mode: 0o600 },
        );
        wroteOwner = true;
      } catch {}
      break;
    } catch (err) {
      if (err?.code !== 'EEXIST') throw err;
      try {
        const statFn = f.lstatSync ?? f.statSync;
        const st = statFn.call(f, lockDir);
        const owner = readJsonObjectQuiet(f, ownerPath);
        const acquiredAt = typeof owner?.acquiredAt === 'number'
          ? owner.acquiredAt
          : (typeof owner?.acquired_at === 'number' ? owner.acquired_at : st?.mtimeMs);
        const ageMs = typeof acquiredAt === 'number' ? (now() - acquiredAt) : 0;
        const ownerDead = Number.isInteger(owner?.pid)
          && owner.pid > 0
          && !isPidAlive(owner.pid)
          && ageMs >= DEAD_LOCK_GRACE_MS;
        if (ownerDead || ageMs >= staleLockMs) {
          if (tryBreakDirLockAtomically(f, runtimeDir, lockDir, pid)) continue;
        }
      } catch {}
      if (now() >= deadline) break;
      await sleep(15 + Math.floor(Math.random() * 25));
    }
  }

  if (!acquired) {
    if (typeof onTimeout === 'function') throw onTimeout(lockDir);
    const err = new Error(
      `Timed out waiting for directory lock at "${lockDir}". `
      + 'Check for a hung PDD process holding this lock or remove the stale lock directory, then rerun.',
    );
    err.code = 'lock_timeout';
    throw err;
  }

  try {
    return await fn();
  } finally {
    try {
      const currentOwner = readJsonObjectQuiet(f, ownerPath);
      const currentToken = currentOwner?.token ?? currentOwner?.lockToken;
      const ownsLock = wroteOwner
        ? currentToken === lockToken
        : currentOwner === null;
      if (ownsLock) {
        f.rmSync(lockDir, { recursive: true, force: true });
      }
    } catch {}
  }
}
