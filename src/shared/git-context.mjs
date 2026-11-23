// Layer-0 Git repository context and file listing primitives.
import { execFile as execFileCallback, spawnSync } from 'node:child_process';
import { realpathSync } from 'node:fs';
import { promisify } from 'node:util';

const execFileAsync = promisify(execFileCallback);

/**
 * Resolve `{ toplevel, commonDir }` (canonicalized via `realpathSync`) for the Git checkout at `cwd`,
 * or return `null` when `cwd` is outside a Git repository.
 */
export async function gitContext(cwd, ports = {}) {
  const exec = ports.execFile ?? ((file, args, options) => execFileAsync(file, args, { ...options, encoding: 'utf8' }));
  try {
    const read = async args => String((await exec('git', args, { cwd })).stdout ?? '').trim();
    return {
      toplevel: realpathSync(await read(['rev-parse', '--show-toplevel'])),
      commonDir: realpathSync(await read(['rev-parse', '--path-format=absolute', '--git-common-dir'])),
    };
  } catch {
    return null;
  }
}

/**
 * Resolve the canonical Git repository top-level directory for `cwd`, or `null` if unavailable.
 */
export async function resolveRepoRoot(cwd, ports = {}) {
  const ctx = await gitContext(cwd, ports);
  return ctx?.toplevel ?? null;
}

/**
 * Synchronously list all Git-tracked and non-ignored untracked files under `root`, sorted uniquely.
 * Throws an error with `name = 'PreflightError'` and `exitCode = 5` if Git listing fails.
 */
export function gitFiles(root) {
  const listed = spawnSync('git', ['ls-files', '-z', '-co', '--exclude-standard'], {
    cwd: root,
    maxBuffer: 512 * 1024 * 1024,
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  if (listed.status !== 0) {
    const err = new Error('pdd could not list the Git files of this repository.');
    err.name = 'PreflightError';
    err.exitCode = 5;
    throw err;
  }
  return [...new Set(listed.stdout.toString('utf8').split('\0').filter(Boolean))].sort();
}
