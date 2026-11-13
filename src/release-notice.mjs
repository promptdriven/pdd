// Generated from prompts/cli/release-notice.prompt.md (sha256: 60de2cb79dced07b6253a422453b2142e10a1b68099a2218ebd092b78547bd32).
import * as nativeFs from 'node:fs';
import { homedir } from 'node:os';
import { dirname, join } from 'node:path';

const DAY_MS = 24 * 60 * 60 * 1000;
const ERROR_BACKOFF_MS = 23 * 60 * 60 * 1000;
const RELEASE_URL = 'https://api.github.com/repos/promptdriven/pdd/releases/latest';

export function parseReleaseVersion(value) {
  if (typeof value !== 'string') return null;
  const match = /^(?:alpha-v|v)?(\d+)\.(\d+)\.(\d+)(?:[-+][\w.-]+)?$/.exec(value.trim());
  if (!match) return null;
  return `${Number(match[1])}.${Number(match[2])}.${Number(match[3])}`;
}

export function isNewerRelease(candidate, current) {
  const next = parseReleaseVersion(candidate), base = parseReleaseVersion(current);
  if (!next || !base) return false;
  const [a, b] = [next.split('.').map(Number), base.split('.').map(Number)];
  for (let i = 0; i < 3; i++) if (a[i] !== b[i]) return a[i] > b[i];
  return false;
}

function readCache(file, fs) {
  try {
    const parsed = JSON.parse(fs.readFileSync(file, 'utf8'));
    return parsed && typeof parsed === 'object' && !Array.isArray(parsed) ? parsed : null;
  } catch { return null; }
}

function writeCache(file, data, fs) {
  try {
    const dir = dirname(file);
    fs.mkdirSync(dir, { recursive: true, mode: 0o700 });
    const tmp = `${file}.${process.pid}.${Date.now()}.tmp`;
    fs.writeFileSync(tmp, `${JSON.stringify(data)}\n`, { mode: 0o600 });
    fs.renameSync(tmp, file);
  } catch { /* Read-only state folders never disrupt CLI execution. */ }
}

async function defaultFetchLatestRelease() {
  const response = await fetch(RELEASE_URL, {
    headers: { Accept: 'application/vnd.github+json', 'User-Agent': 'pdd-cli' },
    signal: AbortSignal.timeout(1000),
  });
  if (!response.ok) throw Error(`HTTP ${response.status}`);
  return response.json();
}

export async function checkReleaseNotice({ currentVersion, isVersionCommand = false, interactive = false, env = process.env } = {}, ports = {}) {
  const baseVersion = parseReleaseVersion(currentVersion);
  if (!baseVersion) return null;
  if (env.PDD_NO_UPDATE_CHECK === '1' || env.PDD_PATH_PROBE === '1' || env.CI || env.PDD_AGENT_SESSION || env.PDD_AUTOPILOT_CONTEXT) return null;
  const fs = ports.fs ?? nativeFs;
  const now = (ports.now ?? Date.now)();
  const home = env.HOME || (ports.homedir ?? homedir)();
  const stateHome = ports.stateHome ?? (env.XDG_STATE_HOME || (home ? join(home, '.local', 'state') : null));
  if (!stateHome) return null;
  const cacheFile = join(stateHome, 'pdd', 'release-check.json');
  let cache = readCache(cacheFile, fs);
  const staleCache = !cache || !Number.isFinite(cache.checkedAt) || now - cache.checkedAt >= DAY_MS;
  const mayFetch = typeof ports.fetchLatestRelease === 'function' || (interactive === true && !env.NODE_TEST_CONTEXT);
  if (staleCache && mayFetch) {
    try {
      const release = await (ports.fetchLatestRelease ?? defaultFetchLatestRelease)();
      const tag = release && release.draft !== true && typeof release.tag_name === 'string' ? release.tag_name.trim() : null;
      const latestVersion = parseReleaseVersion(tag);
      if (!latestVersion) throw Error('Invalid release tag');
      cache = { checkedAt: now, latestTag: tag, latestVersion, notifiedAt: cache?.notifiedAt ?? null };
      writeCache(cacheFile, cache, fs);
    } catch {
      cache = { ...(cache ?? {}), checkedAt: now - ERROR_BACKOFF_MS };
      writeCache(cacheFile, cache, fs);
    }
  }
  const latestVersion = parseReleaseVersion(cache?.latestVersion);
  if (!latestVersion || !isNewerRelease(latestVersion, baseVersion)) return null;
  const message = `A newer PDD release is available (${baseVersion} -> ${latestVersion}). To update, run: npm install -g github:promptdriven/pdd && pdd setup`;
  if (isVersionCommand) return message;
  if (!interactive) return null;
  if (Number.isFinite(cache?.notifiedAt) && now - cache.notifiedAt < DAY_MS) return null;
  writeCache(cacheFile, { ...(cache ?? {}), notifiedAt: now }, fs);
  return message;
}
