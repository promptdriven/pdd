// Prompt: prompts/cli/release-notice.prompt.md
import * as nativeFs from 'node:fs';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { writeAtomicPrivate } from './shared/atomic-fs.mjs';
import { resolvePddStateBase } from './shared/state-dir.mjs';

const DAY_MS = 24 * 60 * 60 * 1000;
const ERROR_BACKOFF_MS = 23 * 60 * 60 * 1000;
const RELEASE_URL = 'https://api.github.com/repos/promptdriven/pdd/releases?per_page=10';

export function parseReleaseVersion(value) {
  if (typeof value !== 'string') return null;
  const match = /^(?:alpha-v|v)?(\d+)\.(\d+)\.(\d+)(?:[-+][\w.-]+)?$/.exec(value.trim());
  if (!match) return null;
  return `${Number(match[1])}.${Number(match[2])}.${Number(match[3])}`;
}

function compareSemverDesc(aVersion, bVersion) {
  const a = aVersion.split('.').map(Number);
  const b = bVersion.split('.').map(Number);
  for (let i = 0; i < 3; i++) if (a[i] !== b[i]) return b[i] - a[i];
  return 0;
}

export function isNewerRelease(candidate, current) {
  const next = parseReleaseVersion(candidate), base = parseReleaseVersion(current);
  if (!next || !base) return false;
  return compareSemverDesc(base, next) > 0;
}

function isSemverPrereleaseTag(tag) {
  return /^(?:v)?\d+\.\d+\.\d+-[\w.-]+$/.test(String(tag ?? '').trim());
}

export function pickLatestRelease(payload) {
  const list = Array.isArray(payload) ? payload : (payload && typeof payload === 'object' ? [payload] : []);
  const nonDraft = list
    .filter(item => item && item.draft !== true && typeof item.tag_name === 'string' && parseReleaseVersion(item.tag_name));
  if (!nonDraft.length) return null;
  // Filter prereleases whenever stable releases exist; fall back to prerelease-only repos (e.g. alpha-v*).
  const stable = nonDraft.filter(item => item.prerelease !== true && !isSemverPrereleaseTag(item.tag_name));
  const pool = stable.length ? stable : nonDraft;
  const sorted = [...pool].sort((a, b) => {
    const cmp = compareSemverDesc(parseReleaseVersion(a.tag_name), parseReleaseVersion(b.tag_name));
    if (cmp !== 0) return cmp;
    return (Date.parse(b.published_at || '') || 0) - (Date.parse(a.published_at || '') || 0);
  });
  const tag = sorted[0].tag_name.trim();
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
    writeAtomicPrivate(fs, file, `${JSON.stringify(data)}\n`, 0o700, 0o600);
  } catch { /* Read-only state folders never disrupt CLI execution. */ }
}

async function defaultFetchLatestRelease() {
  const response = await fetch(RELEASE_URL, {
    headers: { Accept: 'application/vnd.github+json', 'User-Agent': 'pdd-cli' },
    signal: AbortSignal.timeout(1000),
  });
  if (!response.ok) throw new Error(`HTTP ${response.status}`);
  return response.json();
}

export async function checkReleaseNotice({ currentVersion, isVersionCommand = false, interactive = false, env = process.env } = {}, ports = {}) {
  const baseVersion = parseReleaseVersion(currentVersion);
  if (!baseVersion) return null;
  if (env.PDD_NO_UPDATE_CHECK === '1' || env.PDD_PATH_PROBE === '1' || env.CI || env.PDD_AGENT_SESSION || env.PDD_AUTOPILOT_CONTEXT) return null;
  const fs = ports.fs ?? nativeFs;
  const now = (ports.now ?? Date.now)();
  const resolvedHome = env.HOME || (ports.homedir ?? homedir)();
  const effectiveEnv = resolvedHome ? { ...env, HOME: resolvedHome } : env;
  const stateDir = ports.stateHome ? join(ports.stateHome, 'pdd') : resolvePddStateBase(effectiveEnv);
  if (!stateDir) return null;
  const cacheFile = join(stateDir, 'release-check.json');
  let cache = readCache(cacheFile, fs);
  const staleCache = !cache || !Number.isFinite(cache.checkedAt) || now - cache.checkedAt >= DAY_MS;
  const mayFetch = typeof ports.fetchLatestRelease === 'function' || (interactive === true && !env.NODE_TEST_CONTEXT);
  if (staleCache && mayFetch) {
    try {
      const release = await (ports.fetchLatestRelease ?? defaultFetchLatestRelease)();
      const picked = pickLatestRelease(release);
      if (!picked) throw new Error('Invalid release tag');
      cache = { checkedAt: now, latestTag: picked.tag, latestVersion: picked.version, notifiedAt: cache?.notifiedAt ?? null };
      writeCache(cacheFile, cache, fs);
    } catch {
      cache = { ...(cache ?? {}), checkedAt: now - ERROR_BACKOFF_MS };
      writeCache(cacheFile, cache, fs);
    }
  }
  const latestVersion = parseReleaseVersion(cache?.latestVersion);
  if (!latestVersion || !isNewerRelease(latestVersion, baseVersion)) return null;
  const message = `A newer PDD release is available (${baseVersion} -> ${latestVersion}). To update, run: pdd upgrade`;
  if (isVersionCommand) return message;
  if (!interactive) return null;
  if (Number.isFinite(cache?.notifiedAt) && now - cache.notifiedAt < DAY_MS) return null;
  writeCache(cacheFile, { ...(cache ?? {}), notifiedAt: now }, fs);
  return message;
}
