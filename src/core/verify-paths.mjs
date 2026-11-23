// Prompt: prompts/cli/prove.prompt.md

// Universal G2 Feature Map (`verify.test`, `verify.paths[]`) schema parser, glob matcher, and open capability prober.
import { spawnSync } from 'node:child_process';
import { existsSync, lstatSync, readdirSync, realpathSync } from 'node:fs';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { isTestOwnedPath } from '../file-owner.mjs';
import { canonicalRepoPath, formatTeachingDetail, readSafeUtf8 } from './lint/diagnostics.mjs';
import { compileGlobMatcher } from './lint/regex-safety.mjs';
import { SHARED_SURFACE_COLS, clean, csv, findSectionLines, isSeparatorRow, tableCells } from './product/markdown-utils.mjs';

const MAX_VERIFY_PATHS = 100;
const PATH_ID_RE = /^[A-Za-z0-9][A-Za-z0-9_.:-]{0,63}$/;
const CAPABILITY_RE = /^[A-Za-z0-9][A-Za-z0-9_.:-]{0,63}$/;
const NON_SURFACE_PATH_RE = /^(?:docs|prompts|user_stories|pdd\/stories|contracts)\/|\.prompt\.md$|\.mdx?$|^(?:README|CHANGELOG|LICENSE|AGENTS|CLAUDE)(?:\.[^/]+)?$|^(?:pdd|pdd-workspace|pdd-bindings)\.json$|(?:^|\/)(?:__pycache__|\.pytest_cache|node_modules)\/|\.(?:pyc|pyo)$|(?:^|\/)\.DS_Store$/i;

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
  if (rawText === null) return parseVerifyConfig(null, { sourcePath: null });
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
const PLAN_PART_COLS = new Set(['part', 'service', 'app', 'component', 'module']);
const PLAN_FOLDER_COLS = new Set(['folder', 'path', 'dir', 'directory', 'root']);
const PLAN_FROM_COLS = new Set(['from', 'consumer']);
const PLAN_TO_COLS = new Set(['to', 'provider']);
const escapeRegex = s => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');

function parseSectionTableRows(text, sectionName) {
  const sec = findSectionLines(text, sectionName, { caseInsensitive: true });
  if (!sec) return { heading: null, rows: [], section: null };
  const tableLines = sec.lines
    .filter(item => /^\s*\|/.test(item.text))
    .map(item => tableCells(item.text));
  const heading = tableLines.shift() ?? null;
  const rows = heading
    ? tableLines.filter(cells => !isSeparatorRow(cells))
    : [];
  return { heading, rows, section: sec };
}

function extractProductPartsFromPlan(planText, mapText = '') {
  const partSet = new Set();
  const folderByPart = new Map();
  const addPart = (raw, folder = '') => {
    const name = clean(raw);
    if (!name || IGNORED_PART_NAMES.has(name.toLowerCase())) return;
    partSet.add(name);
    const cleanFolder = clean(folder).replace(/^\.\//, '').replace(/\/+$/, '');
    if (cleanFolder && !folderByPart.has(name)) folderByPart.set(name, cleanFolder);
  };

  for (const text of [mapText, planText]) {
    if (!text) continue;
    const partsTable = parseSectionTableRows(text, 'Parts');
    if (partsTable.heading) {
      const pIdx = partsTable.heading.findIndex(c => PLAN_PART_COLS.has(c.toLowerCase()));
      const fIdx = partsTable.heading.findIndex(c => PLAN_FOLDER_COLS.has(c.toLowerCase()));
      if (pIdx >= 0) {
        for (const cells of partsTable.rows) addPart(cells[pIdx], fIdx >= 0 ? cells[fIdx] : '');
      }
    }
    if (partsTable.section) {
      for (const item of partsTable.section.lines) {
        const bm = /^[ \t]*(?:[-*+]|\d+[.)])[ \t]+(.+)$/.exec(item.text);
        if (!bm) continue;
        const body = bm[1].trim();
        const lead = /^(?:\*\*`?([a-zA-Z0-9][a-zA-Z0-9_-]*)`?\*\*|`([a-zA-Z0-9][a-zA-Z0-9_-]*)`)/.exec(body);
        if (!lead) continue;
        const partName = lead[1] ?? lead[2];
        const rest = body.slice(lead[0].length);
        const folderMatch = /^\s*\(\s*`?([^)`\r\n]+?)`?\s*\)/.exec(rest);
        addPart(partName, folderMatch ? folderMatch[1] : '');
      }
    }
  }

  const runsTable = parseSectionTableRows(planText, 'Runs');
  if (runsTable.heading) {
    const pIdx = runsTable.heading.findIndex(c => PLAN_PART_COLS.has(c.toLowerCase()));
    const sharedIdx = runsTable.heading.findIndex(c => SHARED_SURFACE_COLS.has(c.toLowerCase()));
    for (const cells of runsTable.rows) {
      if (pIdx >= 0) for (const token of csv(cells[pIdx])) addPart(token);
      if (sharedIdx >= 0) for (const token of csv(cells[sharedIdx])) addPart(token);
    }
  }

  const promptsTable = parseSectionTableRows(planText, 'Prompts');
  if (promptsTable.heading) {
    const pIdx = promptsTable.heading.findIndex(c => PLAN_PART_COLS.has(c.toLowerCase()));
    if (pIdx >= 0) {
      for (const cells of promptsTable.rows) addPart(cells[pIdx]);
    }
  }

  if (partSet.size === 0) {
    const boundariesTable = parseSectionTableRows(planText, 'Boundaries');
    if (boundariesTable.heading) {
      const fromIdx = boundariesTable.heading.findIndex(c => PLAN_FROM_COLS.has(c.toLowerCase()));
      const toIdx = boundariesTable.heading.findIndex(c => PLAN_TO_COLS.has(c.toLowerCase()));
      for (const cells of boundariesTable.rows) {
        if (fromIdx >= 0) for (const token of csv(cells[fromIdx])) addPart(token);
        if (toIdx >= 0) for (const token of csv(cells[toIdx])) addPart(token);
      }
    }
  }

  return { parts: [...partSet].sort(), folderByPart };
}

function hasContractMarkdownFiles(realRoot) {
  const contractsDir = join(realRoot, 'contracts');
  try {
    const st = lstatSync(contractsDir);
    if (st.isSymbolicLink() || !st.isDirectory()) return false;
    const walk = (dir, depth) => {
      if (depth > 3) return false;
      for (const entry of readdirSync(dir, { withFileTypes: true })) {
        if (entry.isSymbolicLink() || entry.name.startsWith('.')) continue;
        if (entry.isFile() && /\.md$/i.test(entry.name)) return true;
        if (entry.isDirectory() && walk(join(dir, entry.name), depth + 1)) return true;
      }
      return false;
    };
    return walk(contractsDir, 0);
  } catch {
    return false;
  }
}

function listMultiPartCandidateSubdirs(realRoot) {
  const found = [];
  for (const base of ['prompts', 'src', 'services']) {
    const abs = join(realRoot, base);
    try {
      const st = lstatSync(abs);
      if (st.isSymbolicLink() || !st.isDirectory()) continue;
      const subs = [];
      for (const entry of readdirSync(abs, { withFileTypes: true })) {
        if (entry.isSymbolicLink() || !entry.isDirectory() || entry.name.startsWith('.') || entry.name === '__pycache__') continue;
        subs.push(`${base}/${entry.name}`);
      }
      if (subs.length >= 2) return subs.sort();
      found.push(...subs);
    } catch {
      // absent
    }
  }
  return [];
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
 * Also fails closed when product/plan.md + (product/map.md or contracts/*.md) exist alongside >=2 subdirs
 * under prompts/, src/, or services/ yet fewer than 2 parts could be parsed.
 */
export function inspectMultiPartIntegrationGuard(root, verifyConfig, { executedPathResults = null, changedSurfaces = null } = {}) {
  const cleanRes = { applicable: false, parts: [], covered: true, reason: null };
  if (!root || typeof root !== 'string') return cleanRes;
  let realRoot;
  try { realRoot = realpathSync(root); } catch { return cleanRes; }
  const planText = readSafeUtf8(realRoot, 'product/plan.md');
  if (!planText || !planText.trim()) return cleanRes;
  const mapText = readSafeUtf8(realRoot, 'product/map.md') ?? '';
  const { parts, folderByPart } = extractProductPartsFromPlan(planText, mapText);
  if (parts.length < 2) {
    const hasMap = Boolean(mapText.trim());
    const hasContracts = hasContractMarkdownFiles(realRoot);
    const subdirs = listMultiPartCandidateSubdirs(realRoot);
    if (subdirs.length >= 2 && (parts.length === 0 || hasMap || hasContracts)) {
      const detail = formatTeachingDetail({
        invariant: `product/plan.md exists alongside >=2 subdirectories (${subdirs.slice(0, 4).join(', ')}), yet only ${parts.length} product part(s) could be parsed`,
        fix: 'Format product/map.md "## Parts" as a "| Part | Folder | What it is |" table (or bullet list) and product/plan.md "## Runs" with a "Part" column so multi-part integration checks can verify wiring',
        rerun: 'pdd prove',
      });
      return {
        applicable: true,
        parts,
        covered: false,
        reason: `product/plan.md:1 [multi-part-plan-unparseable] ${detail}`,
      };
    }
    return { applicable: false, parts, covered: true, reason: null };
  }
  const recipes = Array.isArray(verifyConfig?.paths) ? verifyConfig.paths : [];
  const integrationRecipes = recipes.filter(recipe => recipeCoversCrossPartIntegration(recipe, parts, folderByPart));
  if (integrationRecipes.length === 0) {
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
  if (Array.isArray(executedPathResults) && Array.isArray(changedSurfaces) && changedSurfaces.length > 0) {
    const integrationIds = new Set(integrationRecipes.map(r => r.id));
    const ranIntegration = executedPathResults.some(r => integrationIds.has(r.id) && r.status === 'proved');
    if (!ranIntegration) {
      const detail = formatTeachingDetail({
        invariant: `multi-part product (${parts.join(', ')}) changed production surfaces (${changedSurfaces.join(', ')}) without executing a passing cross-part integration recipe (${[...integrationIds].join(', ')})`,
        fix: 'Expand the cross-part integration recipe `when` globs in pdd.json so it executes for touched product surfaces',
        rerun: 'pdd prove',
      });
      return {
        applicable: true,
        parts,
        covered: false,
        reason: `pdd.json:1 [multi-part-integration-not-executed] ${detail}`,
      };
    }
  }
  return { applicable: true, parts, covered: true, reason: null };
}
