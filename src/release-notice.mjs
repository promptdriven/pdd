// Generated from prompts/cli/release-notice.prompt.md (sha256: 294a463aab7b4aa81a94e58070578e5e1ca03ce8d7f510483d5b7092f364c340).
import * as nativeFs from 'node:fs';
import { homedir } from 'node:os';
import { dirname, join } from 'node:path';

const DAY_MS = 24 * 60 * 60 * 1000;
const ERROR_BACKOFF_MS = 23 * 60 * 60 * 1000;
const RELEASE_URL = 'https://api.github.com/repos/promptdriven/pdd/releases?per_page=10';

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

export function pickLatestRelease(payload) {
  const list = Array.isArray(payload) ? payload : (payload && typeof payload === 'object' ? [payload] : []);
  const valid = list
    .filter(item => item && item.draft !== true && typeof item.tag_name === 'string' && parseReleaseVersion(item.tag_name))
    .sort((a, b) => (Date.parse(b.published_at || '') || 0) - (Date.parse(a.published_at || '') || 0));
  if (!valid.length) return null;
  const tag = valid[0].tag_name.trim();
  return { tag, version: parseReleaseVersion(tag) };
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
      const picked = pickLatestRelease(release);
      if (!picked) throw Error('Invalid release tag');
      cache = { checkedAt: now, latestTag: picked.tag, latestVersion: picked.version, notifiedAt: cache?.notifiedAt ?? null };
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
