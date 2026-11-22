// Universal G2 Feature Map (`verify.test`, `verify.paths[]`) schema parser, glob matcher, and open capability prober.
import { spawnSync } from 'node:child_process';
import { existsSync, realpathSync } from 'node:fs';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { isTestOwnedPath } from '../file-owner.mjs';
import { canonicalRepoPath, readSafeUtf8 } from './lint/diagnostics.mjs';
import { compileGlobMatcher } from './lint/regex-safety.mjs';

const MAX_VERIFY_PATHS = 100;
const PATH_ID_RE = /^[A-Za-z0-9][A-Za-z0-9_.:-]{0,63}$/;
const CAPABILITY_RE = /^[A-Za-z0-9][A-Za-z0-9_.:-]{0,63}$/;
const NON_SURFACE_PATH_RE = /(?:^|\/)(?:docs?|user_stories|pdd\/stories|__pycache__|\.pytest_cache|node_modules)\/|\.prompt\.md$|\.(?:md|mdx|txt|rst|pyc|pyo)$|(?:^|\/)\.DS_Store$/i;

export const isProductionSurfaceFile = filePath =>
  canonicalRepoPath(filePath) && !isTestOwnedPath(filePath) && !NON_SURFACE_PATH_RE.test(filePath);

export function parseVerifyConfig(raw, { sourcePath = 'pdd.json' } = {}) {
  const empty = { configured: false, source: sourcePath, test: null, report: null, paths: [], errors: [] };
  if (raw === undefined || raw === null) return empty;
  const section = raw && typeof raw === 'object' && !Array.isArray(raw) && Object.hasOwn(raw, 'verify') ? raw.verify : raw;
  if (section === undefined || section === null) return empty;
  if (typeof section !== 'object' || Array.isArray(section)) {
    return { ...empty, configured: true, errors: [`${sourcePath}: "verify" must be a JSON object.`] };
  }

  const errors = [];
  let test = null;
  if (section.test !== undefined) {
    if (typeof section.test !== 'string' || !section.test.trim()) errors.push(`${sourcePath}: "verify.test" must be a nonblank command string.`);
    else test = section.test.trim();
  }
  let report = null;
  if (section.report !== undefined) {
    if (typeof section.report !== 'string' || !canonicalRepoPath(section.report.trim())) errors.push(`${sourcePath}: "verify.report" must be a repository-relative file path.`);
    else report = section.report.trim();
  }

  const paths = [];
  const seenIds = new Set();
  if (section.paths !== undefined) {
    if (!Array.isArray(section.paths)) errors.push(`${sourcePath}: "verify.paths" must be an array of path recipe objects.`);
    else if (section.paths.length > MAX_VERIFY_PATHS) errors.push(`${sourcePath}: "verify.paths" exceeds the maximum of ${MAX_VERIFY_PATHS} entries.`);
    else {
      for (let i = 0; i < section.paths.length; i++) {
        const item = section.paths[i];
        if (!item || typeof item !== 'object' || Array.isArray(item)) { errors.push(`${sourcePath}: verify.paths[${i}] must be an object.`); continue; }
        const id = typeof item.id === 'string' ? item.id.trim() : '';
        if (!PATH_ID_RE.test(id)) { errors.push(`${sourcePath}: verify.paths[${i}].id must be a valid identifier.`); continue; }
        if (seenIds.has(id)) { errors.push(`${sourcePath}: duplicate verify.paths id "${id}".`); continue; }
        seenIds.add(id);

        const name = typeof item.name === 'string' && item.name.trim() ? item.name.trim() : id;
        const rawWhen = typeof item.when === 'string' ? [item.when] : item.when;
        if (!Array.isArray(rawWhen) || !rawWhen.length || rawWhen.some(g => typeof g !== 'string')) {
          errors.push(`${sourcePath}: verify.paths["${id}"].when must be a non-empty glob or array of globs.`);
          continue;
        }
        const matchers = rawWhen.map(compileGlobMatcher);
        if (matchers.some(m => m === null)) { errors.push(`${sourcePath}: verify.paths["${id}"].when contains an invalid or oversized glob.`); continue; }
        const run = typeof item.run === 'string' ? item.run.trim() : '';
        if (!run) { errors.push(`${sourcePath}: verify.paths["${id}"].run must be a nonblank command string.`); continue; }

        let needs = [];
        if (item.needs !== undefined) {
          const rawNeeds = typeof item.needs === 'string' ? [item.needs] : item.needs;
          if (!Array.isArray(rawNeeds) || rawNeeds.some(c => typeof c !== 'string' || !CAPABILITY_RE.test(c.trim()))) {
            errors.push(`${sourcePath}: verify.paths["${id}"].needs must be an array of capability identifiers.`);
            continue;
          }
          needs = [...new Set(rawNeeds.map(c => c.trim()))];
        }
        paths.push({ id, name, when: rawWhen, matchers, run, needs });
      }
    }
  }
  return { configured: Boolean(test || report || paths.length || errors.length), source: sourcePath, test, report, paths, errors };
}

export function loadVerifyConfig(rootOrObject, { gitRef } = {}) {
  if (!rootOrObject) return parseVerifyConfig(null);
  if (typeof rootOrObject === 'object') return parseVerifyConfig(rootOrObject, { sourcePath: 'pdd.json' });
  let realRoot;
  try { realRoot = realpathSync(rootOrObject); } catch { return parseVerifyConfig(null); }

  let rawText = null;
  let sourcePath = 'pdd.json';
  if (gitRef) {
    const res = spawnSync('git', ['show', `${gitRef}:pdd.json`], { cwd: realRoot, encoding: 'utf8', maxBuffer: 2 * 1024 * 1024, stdio: ['ignore', 'pipe', 'ignore'] });
    if (res.status === 0 && typeof res.stdout === 'string') { rawText = res.stdout; sourcePath = `${gitRef}:pdd.json`; }
  } else {
    rawText = readSafeUtf8(realRoot, 'pdd.json');
  }
  if (rawText === null) return parseVerifyConfig(null, { sourcePath });
  try { return parseVerifyConfig(JSON.parse(rawText), { sourcePath }); }
  catch { return { configured: true, source: sourcePath, test: null, report: null, paths: [], errors: [`${sourcePath}: invalid JSON.`] }; }
}

export function matchVerifyPaths(verifyConfig, touchedFiles = []) {
  const cleanFiles = [...new Set((touchedFiles ?? []).filter(f => typeof f === 'string' && f.trim()).map(f => f.replace(/^\.\//, '')))].sort();
  const matched = [];
  const coveredFiles = new Set();
  for (const recipe of verifyConfig?.paths ?? []) {
    const matchedFiles = cleanFiles.filter(f => recipe.matchers.some(m => m.test(f)));
    if (matchedFiles.length > 0) {
      matched.push({ ...recipe, matchedFiles });
      for (const f of matchedFiles) coveredFiles.add(f);
    }
  }
  const changedSurfaces = cleanFiles.filter(isProductionSurfaceFile);
  return { matched, changedSurfaces, unmappedSurfaces: changedSurfaces.filter(f => !coveredFiles.has(f)) };
}

function defaultProbeCapability(cap, { env = process.env, isTTY } = {}) {
  if (cap === 'tty') return typeof isTTY === 'boolean' ? isTTY : Boolean(process.stdout?.isTTY || process.stdin?.isTTY);
  if (cap === 'docker') return spawnSync('docker', ['info', '--format', '{{.ServerVersion}}'], { encoding: 'utf8', timeout: 3000, stdio: ['ignore', 'pipe', 'ignore'] }).status === 0;
  if (cap === 'browser') {
    if (env.CHROME_PATH && existsSync(env.CHROME_PATH)) return true;
    if (env.PLAYWRIGHT_BROWSERS_PATH && existsSync(env.PLAYWRIGHT_BROWSERS_PATH)) return true;
    return ['/Applications/Google Chrome.app/Contents/MacOS/Google Chrome', '/usr/bin/google-chrome', '/usr/bin/chromium', '/usr/bin/chromium-browser'].some(existsSync);
  }
  if (cap === 'ios-simulator') {
    return process.platform === 'darwin' && spawnSync('xcrun', ['simctl', 'list', 'devices'], { encoding: 'utf8', timeout: 3000, stdio: ['ignore', 'pipe', 'ignore'] }).status === 0;
  }
  if (cap.startsWith('account:')) {
    const dir = join(env.HOME || homedir(), '.config', 'pdd');
    const raw = readSafeUtf8(dir, 'autopilot-test-env.json');
    if (!raw) return false;
    try {
      const parsed = JSON.parse(raw);
      const acct = cap.slice('account:'.length);
      return Boolean(parsed && typeof parsed === 'object' && (Object.hasOwn(parsed, acct) || Object.hasOwn(parsed, cap)));
    } catch { return false; }
  }
  return false;
}

export function detectHostCapabilities(requiredNeeds = [], { env = process.env, capabilities, probe, isTTY } = {}) {
  const available = new Set();
  const explicitFalse = new Set();
  if (typeof env?.PDD_CAPABILITIES === 'string' && env.PDD_CAPABILITIES.trim()) {
    for (const part of env.PDD_CAPABILITIES.split(',').map(s => s.trim()).filter(Boolean)) {
      if (part.startsWith('!')) {
        const cap = part.slice(1);
        available.delete(cap);
        explicitFalse.add(cap);
      } else {
        explicitFalse.delete(part);
        available.add(part);
      }
    }
  }
  if (Array.isArray(capabilities) || capabilities instanceof Set) {
    for (const cap of capabilities) {
      if (typeof cap === 'string' && cap.trim()) {
        const c = cap.trim();
        explicitFalse.delete(c);
        available.add(c);
      }
    }
  } else if (capabilities && typeof capabilities === 'object') {
    for (const [k, v] of Object.entries(capabilities)) {
      if (v) {
        explicitFalse.delete(k);
        available.add(k);
      } else {
        available.delete(k);
        explicitFalse.add(k);
      }
    }
  }

  const probeFn = typeof probe === 'function' ? probe : (cap => defaultProbeCapability(cap, { env, isTTY }));
  const checked = {};
  for (const cap of new Set(requiredNeeds)) {
    if (explicitFalse.has(cap)) { checked[cap] = false; continue; }
    if (available.has(cap)) { checked[cap] = true; continue; }
    const found = (capabilities !== undefined && typeof probe !== 'function') ? false : Boolean(probeFn(cap));
    checked[cap] = found;
    if (found) available.add(cap);
  }
  return { available, checked };
}

export function matchCapabilities(needs = [], capabilityState) {
  const avail = capabilityState?.available instanceof Set ? capabilityState.available : new Set(capabilityState ?? []);
  const missing = needs.filter(cap => !avail.has(cap));
  return { satisfied: missing.length === 0, missing };
}
