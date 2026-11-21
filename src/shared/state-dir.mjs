// Layer-0 state directory, hash, and home-expansion primitives.
import { createHash } from 'node:crypto';
import { homedir } from 'node:os';
import { join } from 'node:path';

/**
 * Resolve PDD's machine-local state root:
 * `PDD_STATE_DIR` > `join(XDG_STATE_HOME, 'pdd')` > `join(HOME || homedir(), '.local', 'state', 'pdd')`.
 */
export function resolvePddStateBase(env = process.env) {
  const home = (typeof env?.HOME === 'string' && env.HOME.trim()) ? env.HOME.trim() : homedir();
  if (typeof env?.PDD_STATE_DIR === 'string' && env.PDD_STATE_DIR.trim()) {
    return env.PDD_STATE_DIR.trim();
  }
  if (typeof env?.XDG_STATE_HOME === 'string' && env.XDG_STATE_HOME.trim()) {
    return join(env.XDG_STATE_HOME.trim(), 'pdd');
  }
  return join(home, '.local', 'state', 'pdd');
}

/**
 * Resolve Autopilot's state root (`<stateBase>/autopilot`), honoring explicit `stateDir`,
 * `PDD_STATE_DIR`, `XDG_STATE_HOME`, and `HOME` / `home`.
 */
export function autopilotStateRoot({ stateDir, env = process.env, home } = {}) {
  if (typeof stateDir === 'string' && stateDir.trim()) {
    return join(stateDir.trim(), 'autopilot');
  }
  const effectiveEnv = home && !(typeof env?.HOME === 'string' && env.HOME.trim())
    ? { ...env, HOME: home }
    : env;
  return join(resolvePddStateBase(effectiveEnv), 'autopilot');
}

/**
 * Deterministic 20-hex-char SHA-256 prefix used for repository ledger and state file names.
 */
export function shortHash(value) {
  return createHash('sha256').update(String(value ?? '')).digest('hex').slice(0, 20);
}

/**
 * Expand a leading `~` or `~/` using an explicit home string or env object (`HOME` / `homedir()`).
 * Pass `{ requireHome: true }` to throw when `HOME` is missing on a tilde path.
 */
export function expandHome(value, envOrHome = process.env, { requireHome = false } = {}) {
  if (typeof value !== 'string') return '';
  if (value !== '~' && !value.startsWith('~/') && !value.startsWith('~\\')) return value;
  const home = typeof envOrHome === 'string'
    ? envOrHome
    : (typeof envOrHome?.HOME === 'string' && envOrHome.HOME ? envOrHome.HOME : (requireHome ? '' : homedir()));
  if (!home) {
    if (requireHome) {
      throw new Error(
        `expandHome(${JSON.stringify(value)}): HOME is required to expand tilde paths. `
        + 'Set HOME in the environment or pass an absolute path, then rerun the command.',
      );
    }
    return value;
  }
  return value === '~' ? home : join(home, value.slice(2));
}
