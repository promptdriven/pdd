// Prompt: prompts/cli/test-selection.prompt.md
import { execFileSync } from 'node:child_process';
import { readdirSync, readFileSync } from 'node:fs';
import { basename, join, posix } from 'node:path';

const AC_HEADING = /(?<![^\n])##[ \t]+Acceptance(?:[ \t]+Criteria)?[ \t]*(?![^\n])/i;
const storyName = path => basename(path).replace(/\.md$/, '');
const folders = path => path.split('/').slice(0, -1);

// The test name rule (one owner): the tests of Story S (user_stories/**/S.md) are S.json and S.<variant>.json in a
// folder named test or tests, at any depth. It uses names only, so no size or content can hide a test.
export const isStoryPath = path =>
  path.endsWith('.md') && folders(path).includes('user_stories') && !/^(?:plan|readme)\.md$/i.test(basename(path));

export const hasAcceptance = text => AC_HEADING.test(text);

const isTestFolderJson = path => path.endsWith('.json') && folders(path).some(part => part === 'test' || part === 'tests');
const byText = (a, b) => (a < b ? -1 : a > b ? 1 : 0);
const listed = items => (items.length < 3 ? items.join(' and ') : `${items.slice(0, -1).join(', ')} and ${items.at(-1)}`);

export function expectedTestPath(storyPath) {
  const parts = folders(storyPath);
  return [...parts.slice(0, parts.lastIndexOf('user_stories')), 'tests', `${storyName(storyPath)}.json`].join('/');
}

// The Story names that a test file name fits: N for N.json, and each S where N is S.<variant>.
function ownerNames(name, names) {
  const fits = names.has(name) ? [name] : [];
  for (let at = name.lastIndexOf('.'); at > 0; at = name.lastIndexOf('.', at - 1)) {
    if (names.has(name.slice(0, at))) fits.push(name.slice(0, at));
  }
  return fits;
}

export function matchTests(storyPaths, files) {
  const groups = new Map(), names = new Set();
  for (const path of [...new Set(storyPaths)].sort(byText)) {
    const name = storyName(path);
    names.add(name);
    if (!groups.has(name)) groups.set(name, { stories: [], files: new Map() });
    groups.get(name).stories.push(path);
  }
  const tests = [], untested = [], orphans = [], claimed = new Set();
  for (const path of [...new Set(files)].sort(byText)) {
    if (!isTestFolderJson(path)) continue;
    const base = basename(path, '.json'), owners = ownerNames(base, names);
    if (!owners.length) {
      orphans.push({ path, line: `${path} matches no Story (user_stories/**/${base}.md).` });
      continue;
    }
    if (owners.length > 1) {
      // A file name that fits two Story names (tests/a.b.json with Stories a and a.b): pdd never picks one.
      const stories = owners.flatMap(name => groups.get(name).stories).sort(byText);
      for (const name of owners) claimed.add(name);
      tests.push({
        path,
        files: [path],
        story: base,
        storyPath: null,
        storyPaths: stories,
        problem: `${path} matches ${stories.length} Stories: ${listed(stories)}. Rename one.`,
      });
      continue;
    }
    const same = groups.get(owners[0]).files;
    same.set(base, [...(same.get(base) ?? []), path]);
  }
  for (const [story, { stories, files: byName }] of groups) {
    if (!byName.size) {
      if (!claimed.has(story)) {
        untested.push(
          ...stories.map(storyPath => ({
            story,
            storyPath,
            line: `${storyPath} has no test: expected ${expectedTestPath(storyPath)} (or ${story}.json in any test or tests folder).`,
          })),
        );
      }
      continue;
    }
    const entry = (found, problem) => ({
      path: found[0],
      files: found,
      story,
      storyPath: stories.length === 1 ? stories[0] : null,
      storyPaths: stories,
      problem,
    });
    if (stories.length > 1) {
      const found = [...byName.values()].flat().sort(byText);
      tests.push(
        entry(found, `${listed(found)} ${found.length > 1 ? 'match' : 'matches'} ${stories.length} Stories: ${listed(stories)}. Rename one.`),
      );
      continue;
    }
    for (const [base, found] of byName) {
      tests.push(entry(found, found.length > 1 ? `${stories[0]} has ${found.length} files named ${base}.json: ${listed(found)}. Keep one.` : null));
    }
  }
  const sorted = (items, key) => items.sort((a, b) => byText(a[key], b[key]));
  return { tests: sorted(tests, 'path'), untested: sorted(untested, 'storyPath'), orphans: sorted(orphans, 'path') };
}

// One line for the JSON files in test folders that match no Story; `pdd test --files` and --json list each one.
export const orphanSummary = orphans =>
  orphans.length === 1
    ? `Warning: ${orphans[0].line}`
    : `Warning: ${orphans.length} JSON files in test folders match no Story (the tests of user_stories/**/S.md are S.json and S.<variant>.json). pdd test --files lists them.`;

// STORY words, by the test name rule: a test path, a story path, a story name or a test file name.
// Returns {selected, unknown, untested}: untested holds the line of each named Story that has no test.
export function selectTests(found, words = [], { native = false, captureSource } = {}) {
  if (!words.length) return { selected: [...found.tests], unknown: [], untested: [] };
  const selected = new Set(), unknown = [], untested = [], nativeSelections = new Map();
  for (const raw of words) {
    const word = raw.replace(/^\.\//, '');
    const hits = found.tests.filter(
      test =>
        test.path === word ||
        test.files?.includes(word) ||
        test.storyPath === word ||
        test.storyPaths?.includes(word) ||
        test.story === word ||
        word === '.' ||
        (!word.startsWith('../') &&
          word !== '..' &&
          [test.path, ...(test.files ?? []), ...(test.storyPaths ?? []), test.storyPath].some(path =>
            path?.startsWith(word.replace(/\/$/, '') + '/'),
          )) ||
        basename(test.path, '.json') === word ||
        test.storyPaths?.some(path => storyName(path) === word),
    );
    const nativeHits = native
      ? (found.nativeSelections ?? []).filter(
          item =>
            item.storyPath === word ||
            item.story === word ||
            word === '.' ||
            (!word.startsWith('../') && word !== '..' && item.storyPath.startsWith(word.replace(/\/$/, '') + '/')),
        )
      : [];
    for (const item of nativeHits) nativeSelections.set(item.storyPath, item);
    const missing = hits.length || nativeHits.length ? [] : (found.untested ?? []).filter(item => item.storyPath === word || item.story === word);
    if (missing.length) untested.push(...missing.map(item => item.line));
    else if (!hits.length && !nativeHits.length) unknown.push(raw);
    for (const hit of hits) selected.add(hit);
  }
  const descriptors = [...nativeSelections.values()].map(item => {
    const links = [...item.section.matchAll(/\[[^\]]*\]\(([^)\s]+)#native-validation-profile-([^)\s]+)\)/g)];
    if (links.length !== 1) return { storyPath: item.storyPath, profileId: null, promptPath: null, reason: 'Native Story owner link is missing or ambiguous.' };
    const promptPath = posix.normalize(posix.join(posix.dirname(item.storyPath), links[0][1]));
    try {
      if (!promptPath.endsWith('.prompt.md')) throw Error('Native owner must be a module prompt.');
      if (typeof captureSource !== 'function') {
        throw Object.assign(new Error('Test selection port (captureSource) is not bound.'), { unboundPort: true });
      }
      const captured = captureSource(found.root, { tests: [item.storyPath, promptPath] });
      return { storyPath: item.storyPath, promptPath, profileId: links[0][2], sourceReferences: captured.files };
    } catch (error) {
      // Workspace/source boundary and unbound-port failures retain their ordinary throw.
      if (error?.unboundPort || error?.name === 'PreflightError' || typeof error?.exitCode === 'number') throw error;
      return { storyPath: item.storyPath, promptPath, profileId: links[0][2], reason: error.message };
    }
  });
  return { selected: found.tests.filter(test => selected.has(test)), nativeSelections: descriptors, unknown, untested };
}

export const NO_TESTS = 'No tests found. The test of Story user_stories/S.md is S.json in a test or tests folder. See RUNBOOK.md §2.';

// Why a repo has no tests, by the test name rule (it opens no JSON file): Stories with no test, test-folder JSON
// that matches no Story, and *.prompt names.
export function whyNoTests(root, visible, found, ports = {}) {
  if (typeof ports?.allowsPath !== 'function') {
    throw new Error('Empty-repository explanation port (allowsPath) is not bound.');
  }
  if (found === undefined) {
    if (typeof ports?.discoverTests !== 'function') {
      throw new Error('Empty-repository explanation port (discoverTests) is not bound.');
    }
    found = ports.discoverTests(root, [...visible]);
  }
  const files = [...visible].filter(path => ports.allowsPath(root, path)).sort();
  const why = [...(found.untested ?? []), ...(found.orphans ?? [])].map(item => item.line);
  for (const path of files.filter(file => file.endsWith('.prompt'))) {
    why.push(`PDD prompts must end in .prompt.md: rename ${path} to ${path}.md.`);
  }
  return why.length > 5 ? [...why.slice(0, 5), `…and ${why.length - 5} more`] : why;
}

// --- Affected native test selection (#3065) ---

const SKIP_WALK_DIRS = new Set(['.git', 'node_modules', 'dist', 'build', 'coverage', '.next', '.cache', 'vendor']);
const EXCLUDED_TEST_DIRS = new Set(['src', 'node_modules', '.git', 'dist', 'build', 'coverage', 'vendor', 'fixtures', 'helpers', 'examples']);
const CODE_EXTENSIONS = /\.(?:m?js|cjs|jsx|m?ts|cts|tsx)$/i;
const RUNNABLE_TEST_RE = /\.(?:test|spec)\.(?:m?js|cjs|jsx|m?ts|cts|tsx)$/i;
const PROMPT_HEADER_RE = /^\s*(?:(?:\/\/+|#+|--|;+|\/\*+|\*+|<!--|"""|''')?\s*Generated from|(?:\/\/+|#+|--|;+|\/\*+|\*+|<!--|"""|''')\s*Prompt:)\s+(\S+\.prompt\.md)\b/m;
const REPO_REF_PREFIX_RE = /^(?:docs|skills|user_stories|prompts|\.github)\/[A-Za-z0-9_@+~./-]+$|^(?:README|RUNBOOK|AGENTS|CLAUDE)\.md$/;

function normalizeRepoPath(value) {
  if (typeof value !== 'string') return '';
  return value.trim().replace(/^(?:\.\/)+/, '').replace(/\/+$/, '');
}

function isSafeRepoPath(path) {
  if (typeof path !== 'string' || !path.length || path.length > 1000) return false;
  if (path.startsWith('/') || path.includes('\\') || /[\x00-\x1f\x7f]/.test(path)) return false;
  return path.split('/').every(part => part && part !== '.' && part !== '..' && part.toLowerCase() !== '.git');
}

export function isRunnableTestPath(rawPath) {
  const path = normalizeRepoPath(rawPath);
  if (!isSafeRepoPath(path) || !RUNNABLE_TEST_RE.test(basename(path))) return false;
  const dirParts = folders(path);
  return dirParts.length > 0 && !dirParts.some(part => EXCLUDED_TEST_DIRS.has(part.toLowerCase()));
}

export function classifyGlobalSuiteTrigger(changedFiles, { coreInfrastructure = [] } = {}) {
  if (!Array.isArray(changedFiles)) {
    return { fallback: true, category: 'changed-files-unavailable', file: null, reason: 'changed files could not be determined safely' };
  }
  const customCore = new Set(coreInfrastructure.map(normalizeRepoPath).filter(Boolean));
  for (const raw of changedFiles) {
    if (typeof raw !== 'string') {
      return { fallback: true, category: 'unsafe-path', file: String(raw), reason: 'changed file entry is not a path string' };
    }
    const trimmed = raw.trim();
    if (!trimmed) continue;
    const stripped = trimmed.replace(/^(?:\.\/)+/, '');
    if (!isSafeRepoPath(stripped)) {
      return { fallback: true, category: 'unsafe-path', file: trimmed, reason: `unsafe changed path (${trimmed})` };
    }
    const file = normalizeRepoPath(stripped);
    if (
      /^(?:test|tests|__tests__)\/(?:helpers|fixtures)(?:\/|$)/i.test(file) ||
      /^(?:test|tests|__tests__)\/(?:setup|preload|register|global-setup)\.[^/]+$/i.test(file)
    ) {
      return { fallback: true, category: 'global-test-helper', file, reason: `global test helper changed (${file})` };
    }
    if (
      /^(?:package\.json|package-lock\.json|npm-shrinkwrap\.json|pnpm-lock\.yaml|yarn\.lock|bun\.lockb?|pdd\.json|pdd-bindings\.json|tsconfig(?:\.[^/]+)?\.json|jsconfig\.json|\.npmrc|\.nvmrc|\.node-version)$/i.test(file) ||
      /(?:^|\/)(?:vitest|jest|ava|mocha)\.config\.[^/]+$/i.test(file)
    ) {
      return { fallback: true, category: 'package-config', file, reason: `package or runner configuration changed (${file})` };
    }
    if (
      /^bin\//.test(file) ||
      /^src\/test-suite-[^/]+\.mjs$/.test(file) ||
      /^prompts\/cli\/test-suite-[^/]+\.prompt\.md$/.test(file) ||
      file === 'src/runtime-seam.mjs' ||
      file === 'prompts/cli/runtime-seam.prompt.md' ||
      customCore.has(file)
    ) {
      return { fallback: true, category: 'core-shared-infrastructure', file, reason: `core shared infrastructure changed (${file})` };
    }
  }
  return { fallback: false, category: null, file: null, reason: null };
}

// Single-pass lexical scanner over JS/TS source: ignores comments and string-interior fake imports,
// collects real relative module/URL specifiers and repo-relative file references inside test literals.
function scanModuleSource(source, collectRefs = false) {
  const specifiers = [], refs = [];
  if (typeof source !== 'string' || !source) return { specifiers, refs };
  const len = source.length;
  let i = 0, codeTail = '';
  const pushTail = chunk => {
    codeTail += chunk;
    if (codeTail.length > 128) codeTail = codeTail.slice(-48);
  };
  const isSpecifierContext = () =>
    /(?:^|[^\w$])(?:from|import)\s*$/.test(codeTail) ||
    /(?:^|[^\w$])(?:import|require|req)\s*\(\s*$/.test(codeTail) ||
    /new\s+URL\s*\(\s*$/.test(codeTail);
  const checkLiteral = (literal, afterIndex) => {
    if ((literal.startsWith('./') || literal.startsWith('../')) && isSpecifierContext()) {
      if (/new\s+URL\s*\(\s*$/.test(codeTail)) {
        const rest = source.slice(afterIndex, afterIndex + 64);
        if (/^\s*,\s*import\.meta\.url\b/.test(rest)) specifiers.push(literal);
      } else {
        specifiers.push(literal);
      }
    }
    if (collectRefs) {
      const cleaned = literal.replace(/^(?:\.\/)+/, '').replace(/^(?:\.\.\/)+/, '');
      if (REPO_REF_PREFIX_RE.test(cleaned) && isSafeRepoPath(cleaned)) refs.push(cleaned);
    }
  };

  while (i < len) {
    const ch = source[i], next = source[i + 1];
    if (ch === '/' && next === '/') {
      i += 2;
      while (i < len && source[i] !== '\n') i++;
      pushTail(' ');
      continue;
    }
    if (ch === '/' && next === '*') {
      i += 2;
      while (i < len && !(source[i] === '*' && source[i + 1] === '/')) i++;
      i += 2;
      pushTail(' ');
      continue;
    }
    if (ch === "'" || ch === '"' || ch === '`') {
      const quote = ch;
      i++;
      let value = '', hasInterpolation = false;
      while (i < len && source[i] !== quote) {
        if (source[i] === '\\') {
          value += source.slice(i, i + 2);
          i += 2;
          continue;
        }
        if (quote === '`' && source[i] === '$' && source[i + 1] === '{') hasInterpolation = true;
        value += source[i++];
      }
      i++;
      if (!hasInterpolation) checkLiteral(value, i);
      pushTail('""');
      continue;
    }
    pushTail(ch);
    i++;
  }
  return { specifiers, refs };
}

function resolveRelativeTarget(fromFile, specifier, fileSet) {
  const cleanSpec = specifier.split(/[?#]/)[0];
  if (!cleanSpec) return null;
  const joined = posix.normalize(posix.join(posix.dirname(fromFile), cleanSpec));
  if (!isSafeRepoPath(joined)) return null;
  if (fileSet.has(joined)) return joined;
  const swapped = joined.endsWith('.js')
    ? [joined.slice(0, -3) + '.ts', joined.slice(0, -3) + '.tsx', joined.slice(0, -3) + '.mjs']
    : joined.endsWith('.mjs')
      ? [joined.slice(0, -4) + '.mts']
      : [];
  for (const candidate of swapped) {
    if (fileSet.has(candidate)) return candidate;
  }
  const extensions = ['.mjs', '.js', '.ts', '.mts', '.cjs', '.jsx', '.tsx', '/index.mjs', '/index.js', '/index.ts'];
  for (const ext of extensions) {
    if (fileSet.has(joined + ext)) return joined + ext;
  }
  // Keep explicit-extension relative paths so deleted modules still map back to existing importers.
  return posix.extname(basename(joined)) ? joined : null;
}

const escapeRegExp = value => value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');

function extractExportedSymbols(source) {
  const symbols = new Set();
  for (const match of source.matchAll(/\bexport\s+(?:async\s+)?(?:function|const|let|var|class)\s+([A-Za-z_$][A-Za-z0-9_$]*)/g)) {
    if (match[1].length >= 2) symbols.add(match[1]);
  }
  for (const match of source.matchAll(/\bexport\s*\{([^}]+)\}/g)) {
    for (const part of match[1].split(',')) {
      const exported = part.trim().split(/\s+as\s+/).pop()?.trim();
      if (exported && /^[A-Za-z_$][A-Za-z0-9_$]*$/.test(exported) && exported.length >= 2) symbols.add(exported);
    }
  }
  return symbols;
}

function extractStem(filePath) {
  const base = basename(filePath);
  if (base.endsWith('.prompt.md')) return base.slice(0, -'.prompt.md'.length);
  if (RUNNABLE_TEST_RE.test(base)) {
    return base
      .replace(/\.(?:test|spec)\.[^.]+$/i, '')
      .replace(/\.(?:vectors|formal|integration|e2e|unit)$/i, '');
  }
  const dot = base.lastIndexOf('.');
  return dot > 0 ? base.slice(0, dot) : base;
}

function stemVariants(stem) {
  if (!stem) return [];
  return [...new Set([stem, stem.replaceAll('_', '-'), stem.replaceAll('-', '_')])];
}

function matchTestsByStem(stem, allTests) {
  const variants = stemVariants(stem);
  if (!variants.length) return [];
  return allTests.filter(testPath => {
    const base = basename(testPath);
    return variants.some(v => base.startsWith(`${v}.`) || base.startsWith(`${v}-`));
  });
}

function defaultListFiles(root) {
  const out = [];
  const walk = relDir => {
    let entries;
    try {
      entries = readdirSync(relDir ? join(root, relDir) : root, { withFileTypes: true });
    } catch {
      return;
    }
    for (const entry of entries) {
      if (entry.isSymbolicLink()) continue;
      const relPath = relDir ? `${relDir}/${entry.name}` : entry.name;
      if (entry.isDirectory()) {
        if (!SKIP_WALK_DIRS.has(entry.name)) walk(relPath);
      } else if (entry.isFile()) {
        out.push(relPath);
      }
    }
  };
  walk('');
  return out.sort(byText);
}

function defaultReadFile(root, relPath) {
  try {
    return readFileSync(join(root, relPath), 'utf8');
  } catch {
    return null;
  }
}

function defaultReadChangedFiles({ root, baseRef = 'origin/main' }) {
  try {
    const git = args =>
      execFileSync('git', args, { cwd: root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'], maxBuffer: 16 * 1024 * 1024 });
    let baseCommit = null;
    for (const candidate of [baseRef, baseRef.replace(/^origin\//, ''), 'HEAD'].filter(Boolean)) {
      try {
        const resolved = git(['merge-base', 'HEAD', candidate]).trim();
        if (resolved) {
          baseCommit = resolved;
          break;
        }
      } catch {
        continue;
      }
    }
    const paths = new Set();
    const collect = args => {
      for (const item of git(args).split('\0')) {
        if (item) paths.add(item);
      }
    };
    if (baseCommit) collect(['diff', '--no-color', '--no-renames', '--name-only', '-z', baseCommit]);
    collect(['diff', '--no-color', '--no-renames', '--cached', '--name-only', '-z']);
    collect(['diff', '--no-color', '--no-renames', '--name-only', '-z']);
    collect(['ls-files', '--others', '--exclude-standard', '-z']);
    return [...paths].sort(byText);
  } catch {
    return null;
  }
}

export function formatAffectedTestsSummary(plan) {
  const total = plan?.totalCount ?? plan?.totalTests?.length ?? 0;
  const selected = plan?.selectedCount ?? plan?.selectedTests?.length ?? 0;
  if (plan?.mode === 'full') {
    const why = plan.fallbackReason || 'global infrastructure change';
    return `Affected tests: running full suite (${total} of ${total} test files; fallback: ${why}).`;
  }
  if (selected === 0) {
    const detail = plan?.changedFiles?.length ? 'no matching tests for changed files' : 'no changed files';
    return `Affected tests: selected 0 of ${total} test files (${detail}).`;
  }
  const names = (plan.selectedTests ?? []).slice(0, 5);
  const rest = selected > names.length ? `, +${selected - names.length} more` : '';
  return `Affected tests: selected ${selected} of ${total} test files (${names.join(', ')}${rest}).`;
}

export function selectAffectedTests(options = {}, ports = {}) {
  const root = options.root ?? process.cwd();
  const baseRef = options.baseRef ?? 'origin/main';
  const dispatcherImportThreshold = options.dispatcherImportThreshold ?? 12;
  const listFiles = ports.listFiles ?? defaultListFiles;
  const readFile = ports.readFile ?? (relPath => defaultReadFile(root, relPath));
  const readContent = relPath => (ports.readFile ? ports.readFile(relPath, root) : readFile(relPath));

  const allFiles = (options.files ? [...options.files] : listFiles(root))
    .map(normalizeRepoPath)
    .filter(isSafeRepoPath)
    .sort(byText);
  const fileSet = new Set(allFiles);
  const totalTests = allFiles.filter(isRunnableTestPath);
  const totalTestSet = new Set(totalTests);

  const rawChanged =
    options.changedFiles !== undefined && options.changedFiles !== null
      ? options.changedFiles
      : (ports.readChangedFiles ?? defaultReadChangedFiles)({ root, baseRef });

  const globalCheck = classifyGlobalSuiteTrigger(rawChanged, { coreInfrastructure: options.coreInfrastructure });
  if (globalCheck.fallback) {
    const normalizedChanged = Array.isArray(rawChanged)
      ? [...new Set(rawChanged.filter(x => typeof x === 'string').map(normalizeRepoPath).filter(Boolean))].sort(byText)
      : [];
    const reasons = Object.fromEntries(totalTests.map(t => [t, [`fallback:${globalCheck.category}`]]));
    const plan = {
      mode: 'full',
      selectedTests: [...totalTests],
      totalTests,
      selectedCount: totalTests.length,
      totalCount: totalTests.length,
      changedFiles: normalizedChanged,
      smokeTests: [],
      fallbackReason: globalCheck.reason,
      fallbackCategory: globalCheck.category,
      reasons,
    };
    return { ...plan, summary: formatAffectedTestsSummary(plan) };
  }

  const changedFiles = [...new Set(rawChanged.map(normalizeRepoPath).filter(Boolean))].sort(byText);
  const smokeTests = [...new Set((options.smokeTests ?? []).map(normalizeRepoPath).filter(p => totalTestSet.has(p)))].sort(byText);
  const reasonsMap = new Map();
  const addTest = (testPath, reason) => {
    if (!totalTestSet.has(testPath)) return;
    if (!reasonsMap.has(testPath)) reasonsMap.set(testPath, new Set());
    reasonsMap.get(testPath).add(reason);
  };
  for (const smoke of smokeTests) addTest(smoke, 'smoke');

  if (!changedFiles.length) {
    const selectedTests = [...reasonsMap.keys()].sort(byText);
    const reasons = Object.fromEntries(selectedTests.map(t => [t, [...reasonsMap.get(t)].sort(byText)]));
    const plan = {
      mode: 'affected',
      selectedTests,
      totalTests,
      selectedCount: selectedTests.length,
      totalCount: totalTests.length,
      changedFiles,
      smokeTests,
      fallbackReason: null,
      fallbackCategory: null,
      reasons,
    };
    return { ...plan, summary: formatAffectedTestsSummary(plan) };
  }

  // Scan code and non-helper test modules once to build the reverse-import graph, prompt ownership map, and literal path references.
  const reverseImporters = new Map();
  const outgoingSrcImports = new Map();
  const exportedSymbols = new Map();
  const testSources = new Map();
  const promptToOwnedCode = new Map();
  const pathToRefTests = new Map();
  const addReverseEdge = (target, importer) => {
    if (!reverseImporters.has(target)) reverseImporters.set(target, new Set());
    reverseImporters.get(target).add(importer);
  };
  const addPromptOwner = (promptPath, codePath) => {
    if (!promptToOwnedCode.has(promptPath)) promptToOwnedCode.set(promptPath, new Set());
    promptToOwnedCode.get(promptPath).add(codePath);
  };
  const addRefTest = (refPath, testPath) => {
    if (!pathToRefTests.has(refPath)) pathToRefTests.set(refPath, new Set());
    pathToRefTests.get(refPath).add(testPath);
  };

  const isGraphCodeFile = path => {
    if (!CODE_EXTENSIONS.test(basename(path))) return false;
    const parts = folders(path);
    if (parts.some(p => SKIP_WALK_DIRS.has(p) || p === 'fixtures' || p === 'helpers' || p === 'examples')) return false;
    return /^(?:src|lib|app|test|tests|__tests__)\//.test(path);
  };
  const isProductionCodeFile = path => /^(?:src|lib|app)\//.test(path) && CODE_EXTENSIONS.test(basename(path));

  if (fileSet.has('pdd-bindings.json')) {
    try {
      const bindings = JSON.parse(readContent('pdd-bindings.json') ?? '');
      for (const item of bindings?.modules ?? []) {
        if (typeof item?.prompt === 'string' && typeof item?.module === 'string') {
          addPromptOwner(normalizeRepoPath(item.prompt), normalizeRepoPath(item.module));
        }
      }
    } catch {
      // Malformed bindings are handled by local lint; ignore here.
    }
  }

  for (const file of allFiles) {
    if (!isGraphCodeFile(file)) continue;
    const content = readContent(file);
    if (typeof content !== 'string') continue;
    const isTestEntry = totalTestSet.has(file);
    const isProd = isProductionCodeFile(file);

    if (isProd) {
      exportedSymbols.set(file, extractExportedSymbols(content));
      const headerMatch = PROMPT_HEADER_RE.exec(content.slice(0, 4096));
      if (headerMatch && isSafeRepoPath(headerMatch[1])) {
        addPromptOwner(normalizeRepoPath(headerMatch[1]), file);
      }
    } else if (isTestEntry) {
      testSources.set(file, content);
    }

    const { specifiers, refs } = scanModuleSource(content, isTestEntry);
    const srcDeps = isProd ? new Set() : null;
    for (const spec of specifiers) {
      const resolved = resolveRelativeTarget(file, spec, fileSet);
      if (!resolved) continue;
      addReverseEdge(resolved, file);
      if (isProd && isProductionCodeFile(resolved) && resolved !== file) srcDeps.add(resolved);
      if (isTestEntry && !CODE_EXTENSIONS.test(basename(resolved))) addRefTest(resolved, file);
    }
    if (srcDeps) outgoingSrcImports.set(file, srcDeps);
    if (isTestEntry) {
      for (const ref of refs) addRefTest(ref, file);
    }
  }

  // Lazy scenario JSON inspection only when prompts, Stories, or scenario JSON files changed.
  const needsScenarioLinks = changedFiles.some(
    f => f.endsWith('.prompt.md') || isStoryPath(f) || isTestFolderJson(f),
  );
  const promptToScenarios = new Map();
  const storyToScenarios = new Map();
  if (needsScenarioLinks) {
    for (const file of allFiles) {
      if (!isTestFolderJson(file) || folders(file).includes('fixtures')) continue;
      const raw = readContent(file);
      if (typeof raw !== 'string') continue;
      let doc;
      try {
        doc = JSON.parse(raw);
      } catch {
        continue;
      }
      if (!doc || typeof doc !== 'object') continue;
      if (typeof doc.story_path === 'string') {
        const sp = normalizeRepoPath(doc.story_path);
        if (!storyToScenarios.has(sp)) storyToScenarios.set(sp, new Set());
        storyToScenarios.get(sp).add(file);
      }
      for (const step of Array.isArray(doc.steps) ? doc.steps : []) {
        if (typeof step?.entry_path === 'string') {
          const ep = normalizeRepoPath(step.entry_path);
          if (!promptToScenarios.has(ep)) promptToScenarios.set(ep, new Set());
          promptToScenarios.get(ep).add(file);
        }
      }
    }
  }

  const dispatcherHubs = new Set(
    [...outgoingSrcImports.entries()]
      .filter(([, deps]) => deps.size >= dispatcherImportThreshold)
      .map(([file]) => file),
  );

  const seedModules = new Map();
  const addSeedModule = (modPath, reason) => {
    if (!seedModules.has(modPath)) seedModules.set(modPath, reason);
  };

  let touchedPrompts = false, touchedStories = false, touchedDocs = false, touchedSkills = false;

  for (const file of changedFiles) {
    // Any test literally referencing this changed file path (e.g. docs/cli.md, .github/workflows/ci.yml).
    for (const refTest of pathToRefTests.get(file) ?? []) {
      addTest(refTest, `references:${file}`);
    }

    if (totalTestSet.has(file)) {
      addTest(file, 'direct');
      continue;
    }

    if (isRunnableTestPath(file)) {
      // Deleted runnable test file: do not pass missing path to test runner.
      continue;
    }

    if (/^(?:test|tests|__tests__)\//.test(file) && CODE_EXTENSIONS.test(basename(file))) {
      addSeedModule(file, `test-module:${file}`);
      continue;
    }

    if (isProductionCodeFile(file)) {
      addSeedModule(file, `reverse-import:${file}`);
      for (const hit of matchTestsByStem(extractStem(file), totalTests)) {
        addTest(hit, `stem:${file}`);
      }
      continue;
    }

    if (file.endsWith('.prompt.md') || file.endsWith('.prompt')) {
      touchedPrompts = true;
      const stem = extractStem(file);
      for (const hit of matchTestsByStem(stem, totalTests)) {
        addTest(hit, `prompt-stem:${file}`);
      }
      for (const owned of promptToOwnedCode.get(file) ?? []) {
        const ownedCheck = classifyGlobalSuiteTrigger([owned], { coreInfrastructure: options.coreInfrastructure });
        if (ownedCheck.fallback) {
          const reasons = Object.fromEntries(totalTests.map(t => [t, [`fallback:${ownedCheck.category}`]]));
          const plan = {
            mode: 'full',
            selectedTests: [...totalTests],
            totalTests,
            selectedCount: totalTests.length,
            totalCount: totalTests.length,
            changedFiles,
            smokeTests,
            fallbackReason: `${ownedCheck.reason} via ${file}`,
            fallbackCategory: ownedCheck.category,
            reasons,
          };
          return { ...plan, summary: formatAffectedTestsSummary(plan) };
        }
        addSeedModule(owned, `prompt-owner:${file}`);
        for (const hit of matchTestsByStem(extractStem(owned), totalTests)) {
          addTest(hit, `prompt-owner-stem:${owned}`);
        }
      }
      // Also match conventional src/**/<stem>.* modules when headerless or newly paired.
      for (const candidate of allFiles) {
        if (isProductionCodeFile(candidate) && stemVariants(stem).includes(extractStem(candidate))) {
          addSeedModule(candidate, `prompt-stem-code:${file}`);
        }
      }
      for (const scenarioFile of promptToScenarios.get(file) ?? []) {
        for (const hit of matchTestsByStem(extractStem(scenarioFile), totalTests)) {
          addTest(hit, `prompt-scenario:${scenarioFile}`);
        }
      }
      continue;
    }

    if (isStoryPath(file)) {
      touchedStories = true;
      const stem = extractStem(file);
      for (const hit of matchTestsByStem(stem, totalTests)) {
        addTest(hit, `story-stem:${file}`);
      }
      for (const scenarioFile of storyToScenarios.get(file) ?? []) {
        for (const hit of matchTestsByStem(extractStem(scenarioFile), totalTests)) {
          addTest(hit, `story-scenario:${scenarioFile}`);
        }
      }
      continue;
    }

    if (isTestFolderJson(file)) {
      touchedStories = true;
      for (const hit of matchTestsByStem(extractStem(file), totalTests)) {
        addTest(hit, `scenario:${file}`);
      }
      continue;
    }

    if (/^skills\//.test(file)) {
      touchedSkills = true;
      const skillFolder = file.split('/').slice(0, 2).join('/');
      for (const [refPath, tests] of pathToRefTests.entries()) {
        if (refPath === skillFolder || refPath.startsWith(`${skillFolder}/`)) {
          for (const t of tests) addTest(t, `skill-ref:${file}`);
        }
      }
      continue;
    }

    if (/^docs\//.test(file) || /^(?:README|RUNBOOK|AGENTS|CLAUDE)\.md$/i.test(file)) {
      touchedDocs = true;
      continue;
    }
  }

  // Reverse-import BFS across src/ -> src/ -> test/ (bounded at untouched high-fanout dispatcher hubs,
  // while bridging re-exported symbols through hubs to tests that consume them).
  const visitedModules = new Set(seedModules.keys());
  const queue = [...seedModules.entries()];
  while (queue.length) {
    const [current, originReason] = queue.shift();
    const curExports = exportedSymbols.get(current);
    for (const importer of reverseImporters.get(current) ?? []) {
      if (totalTestSet.has(importer)) {
        addTest(importer, originReason);
        continue;
      }
      if (visitedModules.has(importer)) continue;
      if (!seedModules.has(importer) && dispatcherHubs.has(importer)) {
        const hubExports = exportedSymbols.get(importer);
        if (curExports?.size && hubExports?.size) {
          const reexported = [...curExports].filter(sym => hubExports.has(sym));
          if (reexported.length) {
            const symRe = new RegExp(`(?<![A-Za-z0-9_$])(?:${reexported.map(escapeRegExp).join('|')})(?![A-Za-z0-9_$])`);
            for (const hubImporter of reverseImporters.get(importer) ?? []) {
              if (totalTestSet.has(hubImporter) && symRe.test(testSources.get(hubImporter) ?? '')) {
                addTest(hubImporter, `${originReason}->${importer}`);
              }
            }
          }
        }
        continue;
      }
      visitedModules.add(importer);
      queue.push([importer, originReason]);
    }
  }

  // Contract test suites for prompts, Stories, docs, and skills (filtered to existing tests in repository).
  if (touchedPrompts) {
    for (const testPath of totalTests) {
      if (
        /^(?:test|tests)\/(?:plain-prompts-and-frontmatter|prompt-approve|repo-hygiene-lint|file-owner|story-quality-lint|authoring-lint-parity|skills)\.(?:test|spec)\./.test(testPath) ||
        /^(?:test|tests)\/.*prompt.*contract.*\.(?:test|spec)\./i.test(testPath)
      ) {
        addTest(testPath, 'prompt-contract');
      }
    }
  }

  if (touchedStories) {
    for (const testPath of totalTests) {
      if (
        /^(?:test|tests)\/(?:story-quality-lint|repo-hygiene-lint|authoring-lint-parity|tests-found-by-name)\.(?:test|spec)\./.test(testPath) ||
        /^(?:test|tests)\/.*story.*(?:lint|contract).*\.(?:test|spec)\./i.test(testPath)
      ) {
        addTest(testPath, 'story-contract');
      }
    }
  }

  if (touchedDocs) {
    for (const testPath of totalTests) {
      if (
        /^(?:test|tests)\/(?:docs(?:[-.].*)?|runbook(?:[-.].*)?|skills|authoring-lint-parity|help-teaches-pdd|cli-help-words)\.(?:test|spec)\./.test(testPath) ||
        /^(?:test|tests)\/.*docs?.*contract.*\.(?:test|spec)\./i.test(testPath)
      ) {
        addTest(testPath, 'docs-contract');
      }
    }
  }

  if (touchedSkills) {
    for (const testPath of totalTests) {
      if (
        /^(?:test|tests)\/(?:.*skill.*|runbook(?:[-.].*)?|authoring-lint-parity|setup|setup-defaults)\.(?:test|spec)\./i.test(testPath)
      ) {
        addTest(testPath, 'skills-contract');
      }
    }
  }

  const selectedTests = [...reasonsMap.keys()].sort(byText);
  const reasons = Object.fromEntries(selectedTests.map(t => [t, [...reasonsMap.get(t)].sort(byText)]));
  const plan = {
    mode: 'affected',
    selectedTests,
    totalTests,
    selectedCount: selectedTests.length,
    totalCount: totalTests.length,
    changedFiles,
    smokeTests,
    fallbackReason: null,
    fallbackCategory: null,
    reasons,
  };
  return { ...plan, summary: formatAffectedTestsSummary(plan) };
}
