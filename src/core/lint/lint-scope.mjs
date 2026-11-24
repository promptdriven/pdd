// Prompt: prompts/cli/repo-hygiene-lint.prompt.md

// Single upfront reporting-scope resolver for `pdd lint`, `pdd lint <targets...>`, and `pdd lint --diff [BASE]`.
// Separates the full-repository lookup index (what exists) from the reporting scope (what is checked/reported).
import { realpathSync } from 'node:fs';
import { posix, relative, resolve, sep } from 'node:path';
import { headerEntries, isTestOwnedPath } from '../../file-owner.mjs';
import { isLintableStoryPath } from '../../story-lint.mjs';
import { isSecretPath } from '../../shared/safe-read.mjs';
import { workspace } from '../../shared/workspace-policy.mjs';
import { HEAD_BYTES, canonicalRepoPath, readSafeHeadUtf8, readSafeUtf8 } from './diagnostics.mjs';
import { extractDependencyLinks, isNativeOnlyPrompt } from './prompt-metadata.mjs';

export const CODE_FILE_EXT = /\.(?:mjs|cjs|js|ts|tsx|jsx|py|rs|go|rb|java|kt|cs|swift|c|cc|cpp|h|hpp|php|scala|lua|sh)$/i;
export const TEST_CODE_EXT = /\.(?:mjs|cjs|js|ts|tsx|jsx|py|rs|go|rb|java|kt|cs|swift)$/i;
export const FIXTURE_DIR = /(?:^|\/)fixtures(?:\/|$)/i;
export const EXAMPLE_DIR = /(?:^|\/)examples(?:\/|$)/i;
export const NON_CODE_DIR = /^(?:user_stories|docs?|\.github)\//i;
export const SCENARIO_JSON_RE = /(?:^|\/)(?:tests?|__tests__)\/.*\.json$/i;
export const APP_MAP_PATH_RE = /(?:^|\/)(?:app-map\.json|app\/maps\/[^/]+\.json)$/i;

export const isContractDocPath = p => /(?:^|\/)contracts\/.+\.md$/i.test(p) && !p.endsWith('.prompt.md');
export const isEligibleProductionCodeFile = p => canonicalRepoPath(p) && CODE_FILE_EXT.test(p) && !p.endsWith('.prompt.md') && !isTestOwnedPath(p) && !FIXTURE_DIR.test(p) && !EXAMPLE_DIR.test(p) && !NON_CODE_DIR.test(p);
export const isCustomRuleTestFile = p => canonicalRepoPath(p) && isTestOwnedPath(p) && TEST_CODE_EXT.test(p) && !/(?:^|\/)(?:fixtures|helpers)\//i.test(p);

export function scenarioPromptRefs(doc) {
  if (!doc || typeof doc !== 'object') return [];
  const refs = [];
  if (typeof doc.entry_path === 'string') refs.push(doc.entry_path.replace(/^\.\//, ''));
  for (const p of Array.isArray(doc.entry_paths) ? doc.entry_paths : []) if (typeof p === 'string') refs.push(p.replace(/^\.\//, ''));
  for (const s of Array.isArray(doc.steps) ? doc.steps : []) if (typeof s?.entry_path === 'string') refs.push(s.entry_path.replace(/^\.\//, ''));
  for (const c of Array.isArray(doc.context) ? doc.context : []) {
    if (typeof c === 'string') refs.push(c.replace(/^\.\//, ''));
    else if (c && typeof c === 'object') {
      if (typeof c.prompt_path === 'string') refs.push(c.prompt_path.replace(/^\.\//, ''));
      for (const cp of Array.isArray(c.paths) ? c.paths : []) if (typeof cp === 'string') refs.push(cp.replace(/^\.\//, ''));
    }
  }
  return [...new Set(refs.filter(Boolean))];
}

export function extractBoundModules(rawBindings) {
  const entries = [];
  if (typeof rawBindings !== 'string' || !rawBindings.trim()) return entries;
  try {
    const doc = JSON.parse(rawBindings);
    if (!doc || typeof doc !== 'object' || doc.schema_version !== 'pdd.bindings.v1' || !Array.isArray(doc.modules)) return entries;
    for (const item of doc.modules) {
      if (!item || typeof item !== 'object') continue;
      const mod = typeof item.module === 'string' ? item.module.replace(/^\.\//, '') : '';
      const prompt = typeof item.prompt === 'string' ? item.prompt.replace(/^\.\//, '') : '';
      if (mod && canonicalRepoPath(mod)) entries.push({ module: mod, prompt: prompt && canonicalRepoPath(prompt) ? prompt : '' });
    }
  } catch {
    // malformed bindings handled by resolveOwners / config checks
  }
  return entries;
}

function appMapPromptRefs(doc) {
  if (!doc || typeof doc !== 'object' || Array.isArray(doc)) return [];
  const refs = [];
  for (const s of Array.isArray(doc.screens) ? doc.screens : []) {
    if (typeof s?.prompt_path === 'string' && s.prompt_path.trim()) refs.push(s.prompt_path.trim().replace(/^\.\//, ''));
  }
  for (const h of Array.isArray(doc.handlers) ? doc.handlers : []) {
    if (typeof h?.handler?.prompt_path === 'string' && h.handler.prompt_path.trim()) refs.push(h.handler.prompt_path.trim().replace(/^\.\//, ''));
  }
  for (const t of Array.isArray(doc.timers) ? doc.timers : []) {
    if (typeof t?.handler?.prompt_path === 'string' && t.handler.prompt_path.trim()) refs.push(t.handler.prompt_path.trim().replace(/^\.\//, ''));
  }
  return [...new Set(refs)];
}

const REF_LABEL_NORM = s => String(s ?? '').trim().replace(/\s+/g, ' ').toLowerCase();

function extractPromptSvgTargets(promptText, promptPath) {
  if (typeof promptText !== 'string' || !/\.ui\.svg/i.test(promptText)) return [];
  const baseDir = posix.dirname(promptPath);
  const targets = new Set();
  const addRaw = rawLink => {
    const raw = String(rawLink ?? '').split('#')[0].split('?')[0].trim();
    if (!raw || /^(?:[a-z][a-z\d+.-]*:|\/\/|#)/i.test(raw) || !/\.ui\.svg$/i.test(raw)) return;
    let decoded = raw;
    try { decoded = decodeURIComponent(raw); } catch { decoded = raw; }
    const resolved = posix.normalize(baseDir === '.' ? decoded : posix.join(baseDir, decoded));
    if (canonicalRepoPath(resolved)) targets.add(resolved);
  };

  // Reference-style definitions: [label]: path/to/file.ui.svg
  const refDefs = new Map();
  const refDefRe = /^[ \t]*\[([^\[\]\r\n]+)\]:[ \t]*<?([^\s>\r\n]+)>?(?:[ \t]+(?:"[^"\r\n]*"|'[^'\r\n]*'|\([^)\r\n]*\)))?[ \t]*$/gm;
  let m;
  while ((m = refDefRe.exec(promptText)) !== null) {
    refDefs.set(REF_LABEL_NORM(m[1]), m[2]);
  }
  // Inline Markdown links/images (linear character class — zero quadratic backtracking).
  const inlineRe = /!?\[[^\[\]\r\n]*\]\(\s*(?:<([^>\r\n]+)>|([^\s)\r\n]+))(?:\s+["'][^)\r\n]*)?\)/g;
  while ((m = inlineRe.exec(promptText)) !== null) {
    addRaw(m[1] || m[2]);
  }
  // Full and collapsed/shortcut reference links: ![alt][ref], [text][ref], ![ref]
  if (refDefs.size > 0) {
    const refUseRe = /!?\[([^\[\]\r\n]*)\]\[([^\[\]\r\n]*)\]/g;
    while ((m = refUseRe.exec(promptText)) !== null) {
      const target = refDefs.get(REF_LABEL_NORM(m[2] || m[1]));
      if (target) addRaw(target);
    }
    const shortRefRe = /!?\[([^\[\]\r\n]+)\](?![\[(:])/g;
    while ((m = shortRefRe.exec(promptText)) !== null) {
      const target = refDefs.get(REF_LABEL_NORM(m[1]));
      if (target) addRaw(target);
    }
  }
  return [...targets];
}

const NON_SCENARIO_JSON_NAME_RE =
  /^(?:\..+|cases|.*-cases|tsconfig(?:\.[^/]+)?|jsconfig|package(?:-lock)?|npm-shrinkwrap|composer|biome|deno|jsr|eslint|prettier|vitest|jest|babel|firebase|firestore\.indexes|vercel|netlify|wrangler)\.json$/i;

function buildStoryInferrer(storyPaths) {
  const byStem = new Map();
  for (const f of storyPaths) {
    const stem = posix.basename(f).replace(/\.md$/i, '');
    if (!byStem.has(stem)) byStem.set(stem, []);
    byStem.get(stem).push(f);
  }
  return (doc, scenarioPath) => {
    if (doc && typeof doc === 'object' && !Array.isArray(doc) && typeof doc.story_path === 'string' && doc.story_path.trim()) {
      return doc.story_path.trim().replace(/^\.\//, '');
    }
    const fileName = posix.basename(scenarioPath);
    if (NON_SCENARIO_JSON_NAME_RE.test(fileName)) return null;
    const base = fileName.replace(/\.json$/i, '');
    const owners = byStem.has(base) ? [base] : [];
    for (let at = base.lastIndexOf('.'); at > 0; at = base.lastIndexOf('.', at - 1)) {
      if (byStem.has(base.slice(0, at))) owners.push(base.slice(0, at));
    }
    return owners.length === 1 && (byStem.get(owners[0]) ?? []).length === 1 ? byStem.get(owners[0])[0] : null;
  };
}

function matchTargetWords(words, { realRoot, realCwd, allowedFiles, allowedSet }) {
  const matched = new Set();
  const unmatched = [];
  const nonFixtureAllowed = allowedFiles.filter(f => !FIXTURE_DIR.test(f));

  for (const raw of words) {
    const word = String(raw ?? '').trim();
    if (!word) {
      unmatched.push(String(raw ?? ''));
      continue;
    }
    const stripped = word.replace(/^\.\//, '').replace(/\/+$/, '');
    const relFromCwd = relative(realRoot, resolve(realCwd, word)).split(sep).join('/').replace(/^\.\//, '').replace(/\/+$/, '');

    // Repo root target (`.` or `./` from repo root, or `..` resolving to repo root).
    if (relFromCwd === '' && (word === '.' || word === './' || stripped === '' || stripped === '.' || resolve(realCwd, word) === realRoot)) {
      for (const f of nonFixtureAllowed) matched.add(f);
      continue;
    }

    const candidates = [...new Set([stripped, relFromCwd].filter(canonicalRepoPath))];
    let found = false;

    for (const cand of candidates) {
      if (allowedSet.has(cand)) {
        matched.add(cand);
        found = true;
      }
    }
    if (!found) {
      for (const cand of candidates) {
        const dirPrefix = `${cand}/`;
        const pool = FIXTURE_DIR.test(dirPrefix) ? allowedFiles : nonFixtureAllowed;
        const under = pool.filter(f => f.startsWith(dirPrefix));
        if (under.length) {
          for (const f of under) matched.add(f);
          found = true;
        }
      }
    }
    if (!found && !stripped.includes('/')) {
      const hasPromptExt = /\.prompt\.md$/i.test(stripped);
      const hasMdExt = !hasPromptExt && /\.md$/i.test(stripped);
      const hasJsonExt = /\.json$/i.test(stripped);
      const allowStory = !hasPromptExt && !hasJsonExt;
      const allowScenario = !hasPromptExt && !hasMdExt;
      const allowPrompt = !hasMdExt && !hasJsonExt;
      const slug = stripped.replace(/\.prompt\.md$/i, '').replace(/\.md$/i, '').replace(/\.json$/i, '');
      for (const f of nonFixtureAllowed) {
        const base = posix.basename(f);
        if (allowStory && isLintableStoryPath(f) && base.replace(/\.md$/i, '') === slug) { matched.add(f); found = true; }
        else if (allowScenario && SCENARIO_JSON_RE.test(f) && base.replace(/\.json$/i, '') === slug) { matched.add(f); found = true; }
        else if (allowPrompt && f.endsWith('.prompt.md') && base.replace(/\.prompt\.md$/i, '') === slug) { matched.add(f); found = true; }
      }
    }
    if (!found) unmatched.push(word);
  }
  return { matched, unmatched };
}

/**
 * Resolve one upfront LintScope separating:
 * - Lookup index (`allowedFiles`, `scopedFiles`): ALWAYS the full live repository so unchanged links/headers resolve cleanly.
 * - Reporting scope (`prompts`, `stories`, `scenarios`, `codeFiles`, `testFiles`, `appMaps`, `productPlan`): strictly what is reported.
 */
export function resolveLintScope({
  root,
  cwd = root,
  files = [],
  words = [],
  diffEntries = null,
  touchedFiles = null,
  extraDeletedPaths = null,
  workspaceRoot,
  workspacePolicy,
} = {}) {
  const realRoot = realpathSync(root);
  let realCwd = realRoot;
  try { realCwd = realpathSync(cwd); } catch { realCwd = realRoot; }
  const policy = workspacePolicy ?? workspace.policy({ root: typeof workspaceRoot === 'string' && workspaceRoot.trim() ? realpathSync(workspaceRoot) : realRoot });

  const hasWords = Array.isArray(words) && words.length > 0;
  const isDiffMode = Array.isArray(diffEntries) || Array.isArray(touchedFiles);

  // Compute deleted and renamed old paths from git diff entries so live lookup index reflects working-tree deletions
  // and reverse references to old paths are followed into scope.
  const deletedPaths = new Set();
  const deletedOrRenamedOldPaths = new Set();
  const diffDirectCandidates = new Set();

  if (Array.isArray(extraDeletedPaths)) {
    for (const p of extraDeletedPaths) {
      if (typeof p === 'string' && p.trim()) {
        const clean = p.replace(/^\.\//, '');
        deletedPaths.add(clean);
      }
    }
  }

  if (Array.isArray(diffEntries)) {
    const presentNewPaths = new Set(
      diffEntries
        .map(e => (typeof e?.newPath === 'string' ? e.newPath.replace(/^\.\//, '') : ''))
        .filter(Boolean),
    );
    for (const entry of diffEntries) {
      if (!entry || typeof entry !== 'object') continue;
      const status = String(entry.status ?? '');
      const oldP = typeof entry.oldPath === 'string' ? entry.oldPath.replace(/^\.\//, '') : '';
      const newP = typeof entry.newPath === 'string' ? entry.newPath.replace(/^\.\//, '') : '';
      if (newP) diffDirectCandidates.add(newP);
      if (oldP) diffDirectCandidates.add(oldP);
      if (oldP && (status === 'D' || (status.startsWith('R') && oldP !== newP))) {
        deletedOrRenamedOldPaths.add(oldP);
        if (!presentNewPaths.has(oldP)) deletedPaths.add(oldP);
      }
    }
  } else if (Array.isArray(touchedFiles)) {
    for (const raw of touchedFiles) {
      if (typeof raw !== 'string') continue;
      const clean = raw.replace(/^\.\//, '');
      if (clean) diffDirectCandidates.add(clean);
    }
  }

  const liveRawFiles = deletedPaths.size ? files.filter(f => !deletedPaths.has(f)) : files;
  const allowedFiles = [...new Set(liveRawFiles)]
    .filter(p => canonicalRepoPath(p) && !isSecretPath(p) && workspace.allows(policy, p))
    .sort();
  const allowedSet = new Set(allowedFiles);

  if (!hasWords && !isDiffMode) {
    const scopedFiles = allowedFiles.filter(p => !FIXTURE_DIR.test(p));
    return {
      fullRepo: true,
      mode: 'full',
      effectiveFiles: allowedFiles,
      allowedFiles,
      scopedFiles,
      directFiles: new Set(),
      deletedPaths,
      deletedOrRenamedOldPaths,
      prompts: new Set(),
      stories: new Set(),
      scenarios: new Set(),
      codeFiles: new Set(),
      testFiles: new Set(),
      appMaps: new Set(),
      productPlan: true,
      unmatched: [],
      caches: null,
    };
  }

  const directFiles = new Set();
  const unmatched = [];
  if (hasWords) {
    const res = matchTargetWords(words, { realRoot, realCwd, allowedFiles, allowedSet });
    for (const m of res.matched) directFiles.add(m);
    unmatched.push(...res.unmatched);
    if (unmatched.length > 0) {
      return {
        fullRepo: false,
        mode: 'targets',
        effectiveFiles: allowedFiles,
        allowedFiles,
        scopedFiles: allowedFiles.filter(p => !FIXTURE_DIR.test(p)),
        directFiles,
        deletedPaths,
        deletedOrRenamedOldPaths,
        prompts: new Set(),
        stories: new Set(),
        scenarios: new Set(),
        codeFiles: new Set(),
        testFiles: new Set(),
        appMaps: new Set(),
        productPlan: false,
        unmatched,
        caches: null,
      };
    }
  } else {
    for (const p of diffDirectCandidates) {
      if (!canonicalRepoPath(p) || isSecretPath(p) || !workspace.allows(policy, p)) continue;
      directFiles.add(p);
      if (!allowedSet.has(p)) deletedOrRenamedOldPaths.add(p);
    }
  }

  const includeFixtures = [...directFiles, ...deletedOrRenamedOldPaths].some(p => FIXTURE_DIR.test(p));
  const scopedFiles = includeFixtures ? allowedFiles : allowedFiles.filter(p => !FIXTURE_DIR.test(p));
  const scopedSet = new Set(scopedFiles);

  // Shared single-pass read caches reused by lintRepoProject (zero duplicate file reads).
  const promptCache = new Map(), headCache = new Map(), fullCache = new Map();
  const getPrompt = p => (promptCache.has(p) ? promptCache.get(p) : (promptCache.set(p, readSafeUtf8(realRoot, p)), promptCache.get(p)));
  const getHead = p => (headCache.has(p) ? headCache.get(p) : (headCache.set(p, readSafeHeadUtf8(realRoot, p, HEAD_BYTES + 1)), headCache.get(p)));
  const getFull = p => (fullCache.has(p) ? fullCache.get(p) : (fullCache.set(p, readSafeUtf8(realRoot, p)), fullCache.get(p)));

  const allPrompts = scopedFiles.filter(p => p.endsWith('.prompt.md'));
  const allStories = scopedFiles.filter(isLintableStoryPath);
  const allScenarios = scopedFiles.filter(p => SCENARIO_JSON_RE.test(p));
  const prodCodePaths = scopedFiles.filter(isEligibleProductionCodeFile);

  const rawBindings = scopedSet.has('pdd-bindings.json') ? getFull('pdd-bindings.json') : null;
  const boundEntries = extractBoundModules(rawBindings);
  const bindingsByModule = new Map();
  const modulesByBoundPrompt = new Map();
  for (const { module: mod, prompt } of boundEntries) {
    if (!bindingsByModule.has(mod)) bindingsByModule.set(mod, new Set());
    if (prompt) {
      bindingsByModule.get(mod).add(prompt);
      if (!modulesByBoundPrompt.has(prompt)) modulesByBoundPrompt.set(prompt, new Set());
      modulesByBoundPrompt.get(prompt).add(mod);
    }
  }

  // Index 4 KiB headers of eligible production code files (also reused by project-lint).
  const headerTargetsByCode = new Map();
  const codeByHeaderPrompt = new Map();
  for (const codePath of prodCodePaths) {
    const head = getHead(codePath);
    if (typeof head !== 'string') continue;
    const refs = headerEntries(head).map(e => e.prompt);
    if (!refs.length) continue;
    headerTargetsByCode.set(codePath, refs);
    for (const ref of refs) {
      if (!codeByHeaderPrompt.has(ref)) codeByHeaderPrompt.set(ref, new Set());
      codeByHeaderPrompt.get(ref).add(codePath);
    }
  }

  // Index scenario JSONs -> Story / prompts / app_maps (including custom-path app maps declared in scenario `app_maps`).
  const inferStory = buildStoryInferrer(allStories);
  const scenarioIndex = [];
  const scenarioByPath = new Map();
  const discoveredAppMapPaths = new Set(scopedFiles.filter(p => APP_MAP_PATH_RE.test(p)));
  for (const sc of allScenarios) {
    const raw = getFull(sc);
    if (typeof raw !== 'string') continue;
    let doc = null;
    try { doc = JSON.parse(raw); } catch { doc = null; }
    const explicitStory = typeof doc?.story_path === 'string' && doc.story_path.trim()
      ? doc.story_path.trim().replace(/^\.\//, '')
      : null;
    const story = inferStory(doc, sc);
    const promptRefs = doc ? scenarioPromptRefs(doc) : [];
    const appMaps = Array.isArray(doc?.app_maps)
      ? doc.app_maps.filter(m => typeof m === 'string' && m.trim()).map(m => m.trim().replace(/^\.\//, ''))
      : [];
    for (const m of appMaps) {
      if (scopedSet.has(m)) discoveredAppMapPaths.add(m);
    }
    const baseStem = posix.basename(sc).replace(/\.json$/i, '');
    const rec = { path: sc, baseStem, story, explicitStory, promptRefs, appMaps };
    scenarioIndex.push(rec);
    scenarioByPath.set(sc, rec);
  }

  // Index all default + custom-path app-map JSON files -> referenced prompts.
  const appMapIndex = [];
  const appMapByPath = new Map();
  for (const mapPath of [...discoveredAppMapPaths].sort()) {
    const raw = getFull(mapPath);
    let doc = null;
    if (typeof raw === 'string') {
      try { doc = JSON.parse(raw); } catch { doc = null; }
    }
    const rec = { path: mapPath, promptRefs: appMapPromptRefs(doc) };
    appMapIndex.push(rec);
    appMapByPath.set(mapPath, rec);
  }

  // Build reverse dependency & SVG index only when prompts, contracts, SVGs, or deleted/renamed paths are involved.
  const needsReverseDeps = deletedOrRenamedOldPaths.size > 0
    || [...directFiles].some(p => p.endsWith('.prompt.md') || isContractDocPath(p) || /\.ui\.svg$/i.test(p));
  const reverseDepPrompts = new Map();
  const reverseSvgPrompts = new Map();
  const liveDirSet = new Set();
  if (needsReverseDeps) {
    for (const f of allowedFiles) {
      let idx = f.indexOf('/');
      while (idx > 0) {
        liveDirSet.add(f.slice(0, idx));
        idx = f.indexOf('/', idx + 1);
      }
    }
    for (const p of allPrompts) {
      const text = getPrompt(p);
      if (typeof text !== 'string') continue;
      for (const link of extractDependencyLinks(text, p)) {
        if (!link.canonical) continue;
        const target = link.target.replace(/\/+$/, '');
        if (!reverseDepPrompts.has(target)) reverseDepPrompts.set(target, new Set());
        reverseDepPrompts.get(target).add(p);
      }
      for (const svgTarget of extractPromptSvgTargets(text, p)) {
        if (!reverseSvgPrompts.has(svgTarget)) reverseSvgPrompts.set(svgTarget, new Set());
        reverseSvgPrompts.get(svgTarget).add(p);
      }
    }
  }

  const prompts = new Set();
  const stories = new Set();
  const scenarios = new Set();
  const codeFiles = new Set();
  const testFiles = new Set();
  const appMaps = new Set();
  let productPlan = false;

  const addPrompt = p => { if (scopedSet.has(p) && p.endsWith('.prompt.md')) prompts.add(p); };
  const addStory = s => { if (scopedSet.has(s) && isLintableStoryPath(s)) stories.add(s); };
  const addScenario = sc => { if (scopedSet.has(sc)) scenarios.add(sc); };
  const addCode = c => { if (scopedSet.has(c) && !isTestOwnedPath(c)) codeFiles.add(c); };
  const addAppMap = m => { if (scopedSet.has(m)) appMaps.add(m); };
  const addOwnedCodeOfPrompt = promptPath => {
    for (const c of codeByHeaderPrompt.get(promptPath) ?? []) addCode(c);
    for (const c of modulesByBoundPrompt.get(promptPath) ?? []) addCode(c);
  };
  const addAppMapsForPrompt = promptPath => {
    for (const am of appMapIndex) {
      if (am.promptRefs.includes(promptPath)) addAppMap(am.path);
    }
  };

  for (const seed of directFiles) {
    if (seed === 'product/plan.md' || seed === 'product/map.md') {
      productPlan = true;
    }
    if (seed === 'pdd-bindings.json') {
      for (const { module: mod, prompt } of boundEntries) {
        addCode(mod);
        if (prompt) addPrompt(prompt);
      }
      continue;
    }
    if (isLintableStoryPath(seed)) {
      addStory(seed);
      for (const rec of scenarioIndex) {
        if (rec.story !== seed && rec.explicitStory !== seed) continue;
        addScenario(rec.path);
        for (const m of rec.appMaps) addAppMap(m);
        for (const ref of rec.promptRefs) {
          addPrompt(ref);
          addOwnedCodeOfPrompt(ref);
          if (rec.appMaps.length === 0) addAppMapsForPrompt(ref);
        }
      }
      continue;
    }
    if (SCENARIO_JSON_RE.test(seed)) {
      addScenario(seed);
      const rec = scenarioByPath.get(seed);
      if (rec) {
        if (rec.story) addStory(rec.story);
        for (const m of rec.appMaps) addAppMap(m);
        for (const ref of rec.promptRefs) {
          addPrompt(ref);
          addOwnedCodeOfPrompt(ref);
          if (rec.appMaps.length === 0) addAppMapsForPrompt(ref);
        }
      }
      continue;
    }
    if (seed.endsWith('.prompt.md')) {
      addPrompt(seed);
      addOwnedCodeOfPrompt(seed);
      addAppMapsForPrompt(seed);
      for (const rec of scenarioIndex) {
        if (!rec.promptRefs.includes(seed)) continue;
        addScenario(rec.path);
        if (rec.story) addStory(rec.story);
        for (const m of rec.appMaps) addAppMap(m);
      }
      // On live modified prompts, pull in `kind: native-only` dependents (whose port parity can break),
      // while avoiding pre-existing warning noise from unrelated checkable prompts linking a hub prompt.
      // (Deleted/renamed prompts pull ALL reverse dependents below so broken-dependency-link always fires.)
      for (const caller of reverseDepPrompts.get(seed) ?? []) {
        const callerText = getPrompt(caller);
        if (typeof callerText === 'string' && isNativeOnlyPrompt(callerText)) addPrompt(caller);
      }
      continue;
    }
    if (APP_MAP_PATH_RE.test(seed) || appMapByPath.has(seed)) {
      addAppMap(seed);
      const rec = appMapByPath.get(seed);
      for (const ref of rec?.promptRefs ?? []) addPrompt(ref);
      continue;
    }
    if (/\.ui\.svg$/i.test(seed)) {
      for (const caller of reverseSvgPrompts.get(seed) ?? []) {
        addPrompt(caller);
        addAppMapsForPrompt(caller);
      }
      for (const caller of reverseDepPrompts.get(seed) ?? []) addPrompt(caller);
      continue;
    }
    if (isContractDocPath(seed)) {
      for (const caller of reverseDepPrompts.get(seed) ?? []) {
        const callerText = getPrompt(caller);
        if (typeof callerText === 'string' && isNativeOnlyPrompt(callerText)) addPrompt(caller);
      }
      continue;
    }
    if (isCustomRuleTestFile(seed)) {
      if (scopedSet.has(seed)) testFiles.add(seed);
      continue;
    }
    if (isEligibleProductionCodeFile(seed) || bindingsByModule.has(seed)) {
      addCode(seed);
      for (const ref of headerTargetsByCode.get(seed) ?? []) addPrompt(ref);
      for (const ref of bindingsByModule.get(seed) ?? []) addPrompt(ref);
      continue;
    }
  }

  // Follow OLD paths on renames and deletions so callers/headers/bindings/dependencies/scenarios/app-maps referencing them are flagged.
  for (const oldPath of deletedOrRenamedOldPaths) {
    for (const c of codeByHeaderPrompt.get(oldPath) ?? []) addCode(c);
    for (const c of modulesByBoundPrompt.get(oldPath) ?? []) addCode(c);
    for (const caller of reverseDepPrompts.get(oldPath) ?? []) addPrompt(caller);
    for (const caller of reverseSvgPrompts.get(oldPath) ?? []) {
      addPrompt(caller);
      addAppMapsForPrompt(caller);
    }

    // If deleting oldPath emptied an ancestor directory that a prompt linked under ## Dependencies, include that prompt.
    let dir = posix.dirname(oldPath);
    while (dir && dir !== '.') {
      if (!liveDirSet.has(dir)) {
        for (const caller of reverseDepPrompts.get(dir) ?? []) addPrompt(caller);
      }
      const parent = posix.dirname(dir);
      if (parent === dir) break;
      dir = parent;
    }

    const oldStorySlug = isLintableStoryPath(oldPath) ? posix.basename(oldPath).replace(/\.md$/i, '') : null;
    for (const rec of scenarioIndex) {
      const stemMatch = Boolean(oldStorySlug && (rec.baseStem === oldStorySlug || rec.baseStem.startsWith(`${oldStorySlug}.`)));
      if (stemMatch || rec.explicitStory === oldPath || rec.promptRefs.includes(oldPath) || rec.appMaps.includes(oldPath)) {
        addScenario(rec.path);
        if (rec.story) addStory(rec.story);
      }
    }
    for (const am of appMapIndex) {
      if (am.promptRefs.includes(oldPath)) addAppMap(am.path);
    }
  }

  return {
    fullRepo: false,
    mode: hasWords ? 'targets' : 'diff',
    effectiveFiles: allowedFiles,
    allowedFiles,
    scopedFiles,
    directFiles,
    deletedPaths,
    deletedOrRenamedOldPaths,
    prompts,
    stories,
    scenarios,
    codeFiles,
    testFiles,
    appMaps,
    productPlan,
    unmatched: [],
    caches: { promptCache, headCache, fullCache },
  };
}
