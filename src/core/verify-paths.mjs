// Universal G2 Feature Map (`verify.test`, `verify.paths[]`) schema parser, glob matcher, and open capability prober.
import { spawnSync } from 'node:child_process';
import { existsSync, realpathSync } from 'node:fs';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { isTestOwnedPath } from '../file-owner.mjs';
import { canonicalRepoPath, formatTeachingDetail, readSafeUtf8 } from './lint/diagnostics.mjs';
import { compileGlobMatcher } from './lint/regex-safety.mjs';
import { SHARED_SURFACE_COLS, csv, rowsWithMeta } from './product/markdown-utils.mjs';

const MAX_VERIFY_PATHS = 100;
const PATH_ID_RE = /^[A-Za-z0-9][A-Za-z0-9_.:-]{0,63}$/;
const CAPABILITY_RE = /^[A-Za-z0-9][A-Za-z0-9_.:-]{0,63}$/;
const NON_SURFACE_PATH_RE = /^(?:docs|prompts|user_stories|pdd\/stories)\/|\.prompt\.md$|\.mdx?$|^(?:README|CHANGELOG|LICENSE)(?:\.[^/]+)?$|(?:^|\/)(?:__pycache__|\.pytest_cache|node_modules)\/|\.(?:pyc|pyo)$|(?:^|\/)\.DS_Store$/i;

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

        let scope = null;
        if (item.scope !== undefined) {
          if (typeof item.scope !== 'string' || !PATH_ID_RE.test(item.scope.trim())) {
            errors.push(`${sourcePath}: verify.paths["${id}"].scope must be a valid identifier.`);
            continue;
          }
          scope = item.scope.trim().toLowerCase();
        }
        let needs = [];
        if (item.needs !== undefined) {
          const rawNeeds = typeof item.needs === 'string' ? [item.needs] : item.needs;
          if (!Array.isArray(rawNeeds) || rawNeeds.some(c => typeof c !== 'string' || !CAPABILITY_RE.test(c.trim()))) {
            errors.push(`${sourcePath}: verify.paths["${id}"].needs must be an array of capability identifiers.`);
            continue;
          }
          needs = [...new Set(rawNeeds.map(c => c.trim()))];
        }
        paths.push({ id, name, ...(scope ? { scope } : {}), when: rawWhen, matchers, run, needs });
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

const INTEGRATION_SCOPE_RE = /^(?:integration|cross[-_]?part|journey|e2e|end[-_]?to[-_]?end)$/i;
const INTEGRATION_LABEL_RE = /\b(?:integration|cross[-_\s]?part|journey|end[-_\s]?to[-_\s]?end|e2e)\b/i;
const IGNORED_PART_NAMES = new Set(['', '-', '*', 'all']);
const escapeRegex = s => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');

function extractProductPartsFromPlan(planText, mapText = '') {
  const partSet = new Set();
  const folderByPart = new Map();
  const addPart = (raw, folder = '') => {
    const name = String(raw ?? '').trim();
    if (!name || IGNORED_PART_NAMES.has(name.toLowerCase())) return;
    partSet.add(name);
    const cleanFolder = String(folder ?? '').trim().replace(/^\.\//, '').replace(/\/+$/, '');
    if (cleanFolder && !folderByPart.has(name)) folderByPart.set(name, cleanFolder);
  };

  for (const [text, file] of [[mapText, 'product/map.md'], [planText, 'product/plan.md']]) {
    if (!text) continue;
    const partsMeta = rowsWithMeta(text, 'Parts', file, { required: false });
    for (const row of partsMeta.rows) addPart(row.values.Part, row.values.Folder);
  }
  const runsMeta = rowsWithMeta(planText, 'Runs', 'product/plan.md', { required: false });
  const sharedCol = (runsMeta.heading ?? []).find(col => SHARED_SURFACE_COLS.has(col.toLowerCase()));
  for (const row of runsMeta.rows) {
    for (const token of csv(row.values.Part)) addPart(token);
    if (sharedCol) for (const token of csv(row.values[sharedCol])) addPart(token);
  }
  const promptsMeta = rowsWithMeta(planText, 'Prompts', 'product/plan.md', { required: false });
  for (const row of promptsMeta.rows) addPart(row.values.Part);

  return { parts: [...partSet].sort(), folderByPart };
}

function recipeCoversCrossPartIntegration(recipe, parts, folderByPart) {
  if (!recipe || typeof recipe !== 'object') return false;
  if (typeof recipe.scope === 'string' && INTEGRATION_SCOPE_RE.test(recipe.scope.trim())) return true;
  if (INTEGRATION_LABEL_RE.test(`${recipe.id ?? ''} ${recipe.name ?? ''}`)) return true;
  const globs = Array.isArray(recipe.when) ? recipe.when : [];
  if (globs.some(g => /(?:^|\/)product\/(?:plan\.md|\*+)/i.test(String(g ?? '').trim()))) return true;
  const coveredParts = new Set();
  for (const part of parts) {
    const folder = folderByPart.get(part) || '';
    const partSegRe = new RegExp(`(?:^|/)${escapeRegex(part)}(?:/|$)`, 'i');
    const folderRe = folder ? new RegExp(`(?:^|/)${escapeRegex(folder)}(?:/|$)`, 'i') : null;
    if (globs.some(g => {
      const cleanGlob = String(g ?? '').trim().replace(/^\.\//, '');
      return partSegRe.test(cleanGlob) || (folderRe && folderRe.test(cleanGlob));
    })) {
      coveredParts.add(part);
    }
  }
  return coveredParts.size >= 2;
}

/**
 * #3575 Multi-part integration guard: when product/plan.md defines >=2 distinct product parts
 * and pdd.json verify.paths declares no unmocked cross-part integration recipe, emit a 4-part Not proved reason.
 */
export function inspectMultiPartIntegrationGuard(root, verifyConfig) {
  const clean = { applicable: false, parts: [], covered: true, reason: null };
  if (!root || typeof root !== 'string') return clean;
  let realRoot;
  try { realRoot = realpathSync(root); } catch { return clean; }
  const planText = readSafeUtf8(realRoot, 'product/plan.md');
  if (!planText || !planText.trim()) return clean;
  const mapText = readSafeUtf8(realRoot, 'product/map.md') ?? '';
  const { parts, folderByPart } = extractProductPartsFromPlan(planText, mapText);
  if (parts.length < 2) return { applicable: false, parts, covered: true, reason: null };
  const recipes = Array.isArray(verifyConfig?.paths) ? verifyConfig.paths : [];
  const covered = recipes.some(recipe => recipeCoversCrossPartIntegration(recipe, parts, folderByPart));
  if (covered) return { applicable: true, parts, covered: true, reason: null };
  const detail = formatTeachingDetail({
    invariant: `multi-part product has >=2 parts in product/plan.md (${parts.join(', ')}) but no unmocked cross-part integration recipe in pdd.json verify.paths`,
    fix: `Add a verify.paths recipe in pdd.json with "scope": "integration" (covering ${parts.slice(0, 2).join(' and ')} or product/plan.md) that runs an unmocked cross-part integration test`,
    rerun: 'pdd prove',
  });
  return {
    applicable: true,
    parts,
    covered: false,
    reason: `pdd.json:1 [multi-part-integration-missing] ${detail}`,
  };
}
