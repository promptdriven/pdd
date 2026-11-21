// Layer-0 atomic private filesystem and symlink-safety primitives.
import { randomBytes, randomUUID } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { dirname, resolve, sep } from 'node:path';

/**
 * Atomically write a private file (`0600` by default) into a `0700` parent directory,
 * cleaning up the temporary sibling file if write or rename fails.
 */
export function writeAtomicPrivate(fs, targetPath, content, dirMode = 0o700, fileMode = 0o600) {
  const f = fs ?? nativeFs;
  f.mkdirSync(dirname(targetPath), { recursive: true, mode: dirMode });
  const tmpPath = `${targetPath}.${process.pid}.${randomUUID()}.tmp`;
  try {
    f.writeFileSync(tmpPath, content, { encoding: 'utf8', mode: fileMode });
    try { f.chmodSync?.(tmpPath, fileMode); } catch {}
    f.renameSync(tmpPath, targetPath);
    try { f.chmodSync?.(targetPath, fileMode); } catch {}
  } catch (err) {
    try { f.unlinkSync?.(tmpPath); } catch {}
    throw err;
  }
}

/**
 * Quietly parse a JSON object from disk, returning `null` if missing, unreadable,
 * invalid JSON, or not a plain object.
 */
export function readJsonObjectQuiet(fs, targetPath) {
  const f = fs ?? nativeFs;
  try {
    const parsed = JSON.parse(f.readFileSync(targetPath, 'utf8'));
    return parsed !== null && typeof parsed === 'object' && !Array.isArray(parsed) ? parsed : null;
  } catch {
    return null;
  }
}

/**
 * Best-effort unlink that swallows missing-file or permission errors.
 */
export function unlinkQuiet(fs, targetPath) {
  if (!targetPath) return;
  const f = fs ?? nativeFs;
  try {
    f.unlinkSync(targetPath);
  } catch {}
}

/**
 * Check whether `candidatePath` equals or lies inside `rootPath`, both lexically
 * and after resolving canonical paths through `fs.realpathSync`.
 */
export function isPathAtOrInside(candidatePath, rootPath, fs = nativeFs) {
  const resolvedCandidate = resolve(candidatePath);
  const resolvedRoot = resolve(rootPath);
  if (
    resolvedCandidate === resolvedRoot
    || resolvedCandidate.startsWith(`${resolvedRoot}${sep}`)
    || resolvedCandidate.startsWith(`${resolvedRoot}/`)
  ) {
    return true;
  }
  const f = fs ?? nativeFs;
  const realFn = f?.realpathSync?.native ?? f?.realpathSync ?? (f === nativeFs ? nativeFs.realpathSync : null);
  if (typeof realFn !== 'function') return false;
  try {
    const realCandidate = String(realFn.call(f, resolvedCandidate));
    const realRoot = String(realFn.call(f, resolvedRoot));
    return (
      realCandidate === realRoot
      || realCandidate.startsWith(`${realRoot}${sep}`)
      || realCandidate.startsWith(`${realRoot}/`)
    );
  } catch {
    return false;
  }
}

/**
 * Ensure `dirPath` is a private `0700` real directory owned by the current OS user:
 * 1. Walks existing ancestor directories before `mkdirSync` and refuses any symlink owned
 *    by a non-root, non-self user (allowing root-owned OS symlinks like `/var -> /private/var`).
 * 2. Refuses an existing symlink, non-directory, or foreign-owned target before `mkdirSync`.
 * 3. Re-checks via `lstatSync` AFTER `mkdirSync` to eliminate TOCTOU races, then enforces `0700`.
 */
export function assertSafePrivateDir(
  fs,
  dirPath,
  {
    checkAncestors = true,
    expectedUid = typeof process.getuid === 'function' ? process.getuid() : null,
    label = 'PDD private runtime',
    errorFactory = null,
  } = {},
) {
  const f = fs ?? nativeFs;
  const lstat = typeof f.lstatSync === 'function' ? f.lstatSync.bind(f) : nativeFs.lstatSync;
  const target = resolve(dirPath);

  const fail = (reason, fixHint) => {
    const msg = `${label} path "${dirPath}": ${reason} ${fixHint}`;
    if (typeof errorFactory === 'function') throw errorFactory(msg);
    const err = new Error(msg);
    err.code = 'unsafe_runtime_dir';
    throw err;
  };

  if (checkAncestors) {
    const chain = [];
    let cursor = dirname(target);
    while (cursor && cursor !== dirname(cursor)) {
      chain.push(cursor);
      cursor = dirname(cursor);
    }
    for (const ancestor of chain) {
      let aStat;
      try {
        aStat = lstat(ancestor);
      } catch (err) {
        if (err?.code === 'ENOENT') continue;
        throw err;
      }
      if (aStat?.isSymbolicLink?.()) {
        if (expectedUid !== null && typeof aStat.uid === 'number' && aStat.uid !== 0 && aStat.uid !== expectedUid) {
          fail(
            `refusing untrusted symlink ancestor "${ancestor}" (owned by uid ${aStat.uid}).`,
            'Remove the untrusted symlink or point PDD_STATE_DIR to a user-owned directory, then rerun.',
          );
        }
      }
    }
  }

  let preStat = null;
  try {
    preStat = lstat(target);
  } catch (err) {
    if (err?.code !== 'ENOENT') throw err;
  }
  if (preStat) {
    if (preStat.isSymbolicLink() || !preStat.isDirectory()) {
      fail(
        'target must be a real directory (not a symlink or file).',
        `Remove "${dirPath}" or set a clean PDD state directory, then rerun.`,
      );
    }
    if (expectedUid !== null && typeof preStat.uid === 'number' && preStat.uid !== expectedUid) {
      fail(
        `directory is owned by another user (uid ${preStat.uid}, expected ${expectedUid}).`,
        `Use a directory owned by uid ${expectedUid}, then rerun.`,
      );
    }
  } else {
    f.mkdirSync(target, { recursive: true, mode: 0o700 });
  }

  const postStat = lstat(target);
  if (postStat.isSymbolicLink() || !postStat.isDirectory()) {
    fail(
      'target must remain a real directory after creation (not a symlink or file).',
      `Remove "${dirPath}" or set a clean PDD state directory, then rerun.`,
    );
  }
  if (expectedUid !== null && typeof postStat.uid === 'number' && postStat.uid !== expectedUid) {
    fail(
      `directory is owned by another user after creation (uid ${postStat.uid}, expected ${expectedUid}).`,
      `Use a directory owned by uid ${expectedUid}, then rerun.`,
    );
  }
  try { f.chmodSync?.(target, 0o700); } catch {}
  return target;
}

/**
 * Atomically update a user shell profile file while preserving dotfiles symlinks
 * (Stow/chezmoi) by resolving the symlink target before atomic write+rename, and
 * preserving existing file mode bits (defaulting to `0o644` for newly created files).
 */
export function writeAtomicPreservingSymlinkAndMode(
  fs,
  targetPath,
  content,
  { defaultMode = 0o644 } = {},
) {
  const f = fs ?? nativeFs;
  let writePath = targetPath;
  let mode = defaultMode;
  try {
    const lstat = typeof f.lstatSync === 'function' ? f.lstatSync(targetPath) : null;
    if (lstat?.isSymbolicLink?.()) {
      const realFn = f.realpathSync?.native ?? f.realpathSync;
      if (typeof realFn === 'function') {
        writePath = String(realFn.call(f, targetPath));
      }
    }
    const st = typeof f.statSync === 'function' ? f.statSync(writePath) : lstat;
    if (typeof st?.mode === 'number' && (st.mode & 0o777) !== 0) {
      mode = st.mode & 0o777;
    }
  } catch {}

  f.mkdirSync?.(dirname(writePath), { recursive: true });
  if (typeof f.renameSync === 'function') {
    const tmpPath = `${writePath}.pdd-tmp-${process.pid}-${randomBytes(6).toString('hex')}`;
    try {
      f.writeFileSync(tmpPath, content, { encoding: 'utf8', mode });
      try { f.chmodSync?.(tmpPath, mode); } catch {}
      f.renameSync(tmpPath, writePath);
      try { f.chmodSync?.(writePath, mode); } catch {}
      return { writePath, mode };
    } catch (err) {
      try { f.unlinkSync?.(tmpPath); } catch {}
      throw err;
    }
  }
  f.writeFileSync(writePath, content, { encoding: 'utf8', mode });
  try { f.chmodSync?.(writePath, mode); } catch {}
  return { writePath, mode };
}
