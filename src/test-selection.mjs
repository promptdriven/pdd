// Generated from prompts/cli/test-selection.prompt.md (sha256: cc8e71acdec3a69af1f81fa4f25af00916bface4ad2116ff1d2ec4819d2159bd).
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
const PROMPT_HEADER_RE = /^\s*(?:(?:\/\/+|#+|--|;+|\/\*+|\*+|<!--|"""|''')?\s*Generated from|(?:\/\/+|#+|--|;+|\/\*+|\*+|<!--|"""|''')\s*(?:Prompt|Implements):)\s+(\S+\.prompt\.md)\b/m;
const REPO_REF_PREFIX_RE = /^(?:docs|skills|user_stories|prompts|\.github)\/[A-Za-z0-9_@+~./-]+$|^(?:README|RUNBOOK|AGENTS|CLAUDE)\.md$/;
const REGEX_PRECEDING_KEYWORDS = new Set([
  'return', 'throw', 'case', 'delete', 'void', 'typeof', 'in', 'instanceof', 'of', 'new', 'await', 'yield', 'else', 'do', 'export', 'default',
]);
const COND_KEYWORDS = new Set(['if', 'while', 'for', 'with', 'catch']);
const GENERIC_STEM_PARTS = new Set([
  'test', 'tests', 'spec', 'specs', 'core', 'util', 'utils', 'helper', 'helpers', 'common', 'shared', 'index', 'main', 'base', 'types', 'model', 'models', 'data', 'info',
]);

function normalizeRepoPath(value) {
  if (typeof value !== 'string') return '';
  return value.trim().replaceAll('\\', '/').replace(/^(?:\.\/)+/, '').replace(/\/+$/, '');
}

function isSafeRepoPath(path) {
  if (typeof path !== 'string' || !path.length || path.length > 1000) return false;
  if (path.startsWith('/') || /^[A-Za-z]:(?:\/|$)/.test(path) || path.includes('\\') || /[\x00-\x1f\x7f]/.test(path)) return false;
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
    const stripped = trimmed.replaceAll('\\', '/').replace(/^(?:\.\/)+/, '');
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

function tryScanRegexLiteral(source, start) {
  const len = source.length;
  let j = start + 1;
  if (j >= len || source[j] === '\n' || source[j] === '\r') return -1;
  let inClass = false;
  while (j < len) {
    const c = source[j];
    if (c === '\n' || c === '\r') return -1;
    if (c === '\\') {
      if (j + 1 >= len || source[j + 1] === '\n' || source[j + 1] === '\r') return -1;
      j += 2;
      continue;
    }
    if (c === '[') {
      inClass = true;
      j++;
      continue;
    }
    if (c === ']' && inClass) {
      inClass = false;
      j++;
      continue;
    }
    if (c === '/' && !inClass) {
      j++;
      while (j < len && /[A-Za-z]/.test(source[j])) j++;
      return j;
    }
    j++;
  }
  return -1;
}

// Single-pass JS/TS lexer: handles // and /* */ comments, /.../ regex literals (including [...] classes),
// '...' and "..." strings, and nested `...${...}...` template interpolations.
function scanModuleSource(source, collectRefs = false) {
  const specifiers = [], refs = [];
  let stripped = '';
  if (typeof source !== 'string' || !source) return { specifiers, refs, stripped };
  const len = source.length;
  let i = 0, codeTail = '', prevToken = null, wantCondParen = false;
  const parenStack = [], templateStack = [];
  const pushTail = chunk => {
    codeTail += chunk;
    if (codeTail.length > 128) codeTail = codeTail.slice(-48);
  };
  const isSpecifierContext = () =>
    /(?:^|[^\w$])(?:from|import)\s*$/.test(codeTail) ||
    /(?:^|[^\w$])(?:import|require|req)\s*\(\s*$/.test(codeTail) ||
    /new\s+URL\s*\(\s*$/.test(codeTail);
  const decodeEscChar = esc => (esc === 'n' ? '\n' : esc === 'r' ? '\r' : esc === 't' ? '\t' : esc);
  const collectLiteralRefs = decoded => {
    const cleaned = decoded.replaceAll('\\', '/').replace(/^(?:\.\/)+/, '').replace(/^(?:\.\.\/)+/, '');
    if (REPO_REF_PREFIX_RE.test(cleaned) && isSafeRepoPath(cleaned)) refs.push(cleaned);
  };
  const checkLiteral = (literal, afterIndex) => {
    if ((literal.startsWith('./') || literal.startsWith('../')) && isSpecifierContext()) {
      if (/new\s+URL\s*\(\s*$/.test(codeTail)) {
        const rest = source.slice(afterIndex, afterIndex + 64);
        if (/^\s*,\s*import\.meta\.url\b/.test(rest)) specifiers.push(literal);
      } else {
        specifiers.push(literal);
      }
    }
    if (collectRefs) collectLiteralRefs(literal);
  };
  const canStartRegex = () => {
    if (!prevToken) return true;
    if (prevToken.kind === 'ident') return REGEX_PRECEDING_KEYWORDS.has(prevToken.value);
    if (prevToken.kind === 'punct') return !['++', '--', ')', ']'].includes(prevToken.value);
    return false;
  };
  const consumeTemplateText = frame => {
    let chunk = '';
    while (i < len) {
      const c = source[i];
      if (c === '\\') {
        chunk += decodeEscChar(source[i + 1] ?? '');
        i += 2;
        continue;
      }
      if (c === '`') {
        i++;
        const isFrom = /(?:^|[^\w$])from\s*$/.test(codeTail);
        if (!frame.hadInterpolation) checkLiteral(chunk, i);
        else if (collectRefs && chunk) collectLiteralRefs(chunk);
        prevToken = { kind: 'template', value: '``' };
        wantCondParen = false;
        stripped += !frame.hadInterpolation && isFrom ? ` ${JSON.stringify(chunk)} ` : ' "" ';
        pushTail('""');
        return;
      }
      if (c === '$' && source[i + 1] === '{') {
        if (collectRefs && chunk) collectLiteralRefs(chunk);
        frame.hadInterpolation = true;
        frame.braceDepth = 0;
        templateStack.push(frame);
        i += 2;
        prevToken = { kind: 'punct', value: '${' };
        wantCondParen = false;
        stripped += ' ( ';
        pushTail('(');
        return;
      }
      chunk += c;
      i++;
    }
  };

  while (i < len) {
    const ch = source[i], next = source[i + 1];
    if (ch === '/' && next === '/') {
      i += 2;
      while (i < len && source[i] !== '\n') i++;
      pushTail(' ');
      stripped += ' ';
      continue;
    }
    if (ch === '/' && next === '*') {
      i += 2;
      while (i < len && !(source[i] === '*' && source[i + 1] === '/')) i++;
      i += 2;
      pushTail(' ');
      stripped += ' ';
      continue;
    }
    if (ch === '/' && canStartRegex()) {
      const regexEnd = tryScanRegexLiteral(source, i);
      if (regexEnd > i) {
        i = regexEnd;
        prevToken = { kind: 'regexp', value: '//' };
        wantCondParen = false;
        pushTail('0');
        stripped += ' 0 ';
        continue;
      }
    }
    if (ch === "'" || ch === '"') {
      const quote = ch;
      const isFrom = /(?:^|[^\w$])from\s*$/.test(codeTail);
      i++;
      let value = '';
      while (i < len && source[i] !== quote && source[i] !== '\n' && source[i] !== '\r') {
        if (source[i] === '\\') {
          value += decodeEscChar(source[i + 1] ?? '');
          i += 2;
          continue;
        }
        value += source[i++];
      }
      if (source[i] === quote) i++;
      checkLiteral(value, i);
      prevToken = { kind: 'string', value: '""' };
      wantCondParen = false;
      stripped += isFrom ? ` ${JSON.stringify(value)} ` : ' "" ';
      pushTail('""');
      continue;
    }
    if (ch === '`') {
      i++;
      consumeTemplateText({ braceDepth: 0, hadInterpolation: false });
      continue;
    }
    if (/\s/.test(ch)) {
      pushTail(ch === '\n' ? '\n' : ' ');
      stripped += ch === '\n' ? '\n' : ' ';
      i++;
      continue;
    }
    if (/[A-Za-z_$]/.test(ch)) {
      let end = i + 1;
      while (end < len && /[A-Za-z0-9_$]/.test(source[end])) end++;
      const word = source.slice(i, end);
      const prevWasDot = prevToken?.kind === 'punct' && (prevToken.value === '.' || prevToken.value === '?.');
      prevToken = { kind: prevWasDot ? 'prop' : 'ident', value: word };
      wantCondParen = !prevWasDot && COND_KEYWORDS.has(word);
      pushTail(word);
      stripped += word;
      i = end;
      continue;
    }
    if (/[0-9]/.test(ch)) {
      let end = i + 1;
      while (end < len && /[0-9A-Za-z_.]/.test(source[end])) end++;
      const num = source.slice(i, end);
      prevToken = { kind: 'number', value: num };
      wantCondParen = false;
      pushTail(num);
      stripped += num;
      i = end;
      continue;
    }
    if (ch === '(') {
      parenStack.push({ isCond: wantCondParen });
      wantCondParen = false;
      prevToken = { kind: 'punct', value: '(' };
      pushTail('(');
      stripped += '(';
      i++;
      continue;
    }
    if (ch === ')') {
      const top = parenStack.pop();
      wantCondParen = false;
      prevToken = { kind: 'punct', value: top?.isCond ? ')cond' : ')' };
      pushTail(')');
      stripped += ')';
      i++;
      continue;
    }
    if (ch === '{') {
      if (templateStack.length > 0) templateStack[templateStack.length - 1].braceDepth++;
      wantCondParen = false;
      prevToken = { kind: 'punct', value: '{' };
      pushTail('{');
      stripped += '{';
      i++;
      continue;
    }
    if (ch === '}') {
      if (templateStack.length > 0 && templateStack[templateStack.length - 1].braceDepth === 0) {
        const resumed = templateStack.pop();
        i++;
        consumeTemplateText(resumed);
        continue;
      }
      if (templateStack.length > 0) templateStack[templateStack.length - 1].braceDepth--;
      wantCondParen = false;
      prevToken = { kind: 'punct', value: '}' };
      pushTail('}');
      stripped += '}';
      i++;
      continue;
    }
    if ((ch === '+' && next === '+') || (ch === '-' && next === '-') || (ch === '?' && next === '.')) {
      const two = ch + next;
      wantCondParen = false;
      prevToken = { kind: 'punct', value: two };
      pushTail(two);
      stripped += two;
      i += 2;
      continue;
    }
    wantCondParen = false;
    prevToken = { kind: 'punct', value: ch };
    pushTail(ch);
    stripped += ch;
    i++;
  }
  return { specifiers, refs, stripped };
}

function resolveRelativeTarget(fromFile, specifier, fileSet) {
  const cleanSpec = specifier.replaceAll('\\', '/').split(/[?#]/)[0];
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
const IDENT_RE = /^[A-Za-z_$][A-Za-z0-9_$]*$/;

function extractModuleExports(stripped) {
  const ownExports = new Set();
  const wildcardSpecs = [];
  const namedFromSpecs = [];
  if (!stripped) return { ownExports, wildcardSpecs, namedFromSpecs };

  for (const match of stripped.matchAll(/\bexport\s+(?:default\s+)?(?:async\s+)?(?:function|class)\s+([A-Za-z_$][A-Za-z0-9_$]*)/g)) {
    ownExports.add(match[1]);
  }
  if (/\bexport\s+default\b/.test(stripped)) ownExports.add('default');

  for (const match of stripped.matchAll(/\bexport\s+(?:const|let|var)\s+([^;\n]+)/g)) {
    let depth = 0, current = '';
    const pushDecl = chunk => {
      const id = /^([A-Za-z_$][A-Za-z0-9_$]*)/.exec(chunk.trim());
      if (id) ownExports.add(id[1]);
    };
    for (const ch of match[1]) {
      if (ch === '(' || ch === '[' || ch === '{') depth++;
      else if (ch === ')' || ch === ']' || ch === '}') depth = Math.max(0, depth - 1);
      if (ch === ',' && depth === 0) {
        pushDecl(current);
        current = '';
      } else {
        current += ch;
      }
    }
    pushDecl(current);
  }

  for (const match of stripped.matchAll(/\bexport\s*\*\s+as\s+([A-Za-z_$][A-Za-z0-9_$]*)\s+from\s*"((?:\\.|[^"\\])*)"/g)) {
    try {
      const spec = JSON.parse(`"${match[2]}"`);
      ownExports.add(match[1]);
      namedFromSpecs.push({ spec, exported: [match[1]] });
    } catch {}
  }

  for (const match of stripped.matchAll(/\bexport\s*\*\s*from\s*"((?:\\.|[^"\\])*)"/g)) {
    try {
      wildcardSpecs.push(JSON.parse(`"${match[1]}"`));
    } catch {}
  }

  for (const match of stripped.matchAll(/\bexport\s*(?:type\s*)?\{([^}]*)\}\s*from\s*"((?:\\.|[^"\\])*)"/g)) {
    let spec;
    try {
      spec = JSON.parse(`"${match[2]}"`);
    } catch {
      continue;
    }
    const exported = [];
    for (const rawPart of match[1].split(',')) {
      const cleaned = rawPart.trim().replace(/^type\s+/, '');
      if (!cleaned) continue;
      const alias = cleaned.split(/\s+as\s+/).pop()?.trim();
      if (alias && IDENT_RE.test(alias)) {
        ownExports.add(alias);
        exported.push(alias);
      }
    }
    if (exported.length) namedFromSpecs.push({ spec, exported });
  }

  for (const match of stripped.matchAll(/\bexport\s*(?:type\s*)?\{([^}]*)\}(?!\s*from\b)/g)) {
    for (const rawPart of match[1].split(',')) {
      const cleaned = rawPart.trim().replace(/^type\s+/, '');
      if (!cleaned) continue;
      const alias = cleaned.split(/\s+as\s+/).pop()?.trim();
      if (alias && IDENT_RE.test(alias)) ownExports.add(alias);
    }
  }

  return { ownExports, wildcardSpecs, namedFromSpecs };
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
  const readContent = relPath =>
    ports.readFile ? (ports.readFile(relPath, root) ?? ports.readFile(relPath.replaceAll('/', '\\'), root)) : readFile(relPath);

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
  const ownExportsMap = new Map();
  const wildcardReexports = new Map();
  const namedReexports = new Map();
  const moduleSources = new Map();
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
  const addNamedReexport = (hubFile, targetFile, symbols) => {
    if (!namedReexports.has(hubFile)) namedReexports.set(hubFile, new Map());
    const byTarget = namedReexports.get(hubFile);
    if (!byTarget.has(targetFile)) byTarget.set(targetFile, new Set());
    const bucket = byTarget.get(targetFile);
    for (const sym of symbols) bucket.add(sym);
  };

  const isGraphCodeFile = path => {
    if (!CODE_EXTENSIONS.test(basename(path))) return false;
    const parts = folders(path);
    if (parts.some(p => SKIP_WALK_DIRS.has(p) || p === 'fixtures' || p === 'helpers' || p === 'examples')) return false;
    return /^(?:src|lib|app|test|tests|__tests__)\//.test(path);
  };
  const isProductionCodeFile = path => /^(?:src|lib|app)\//.test(path) && CODE_EXTENSIONS.test(basename(path));
  const isLocalTestHelper = path => !totalTestSet.has(path) && /^(?:test|tests|__tests__)\//.test(path) && isGraphCodeFile(path);

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
      const headerMatch = PROMPT_HEADER_RE.exec(content.slice(0, 4096));
      const ownerHeader = headerMatch ? normalizeRepoPath(headerMatch[1]) : '';
      if (ownerHeader && isSafeRepoPath(ownerHeader)) {
        addPromptOwner(ownerHeader, file);
      }
    } else {
      moduleSources.set(file, content);
    }

    const { specifiers, refs, stripped } = scanModuleSource(content, isTestEntry);
    if (isProd) {
      const { ownExports, wildcardSpecs, namedFromSpecs } = extractModuleExports(stripped);
      ownExportsMap.set(file, ownExports);
      for (const spec of wildcardSpecs) {
        const resolved = resolveRelativeTarget(file, spec, fileSet);
        if (resolved) {
          if (!wildcardReexports.has(file)) wildcardReexports.set(file, new Set());
          wildcardReexports.get(file).add(resolved);
        }
      }
      for (const { spec, exported } of namedFromSpecs) {
        const resolved = resolveRelativeTarget(file, spec, fileSet);
        if (resolved) addNamedReexport(file, resolved, exported);
      }
    }

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

  const effectiveExportsCache = new Map();
  const effectiveExports = (mod, visiting = new Set()) => {
    if (effectiveExportsCache.has(mod)) return effectiveExportsCache.get(mod);
    if (visiting.has(mod)) return ownExportsMap.get(mod) ?? new Set();
    visiting.add(mod);
    const merged = new Set(ownExportsMap.get(mod) ?? []);
    for (const target of wildcardReexports.get(mod) ?? []) {
      for (const sym of effectiveExports(target, visiting)) merged.add(sym);
    }
    visiting.delete(mod);
    effectiveExportsCache.set(mod, merged);
    return merged;
  };

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
  const prodModTests = new Map();
  const prodModHubs = new Map();
  const directProdChanges = new Set();
  const trackedProdMods = new Set();
  const recordProdModTest = (prodMod, testPath, reason) => {
    addTest(testPath, reason);
    if (totalTestSet.has(testPath)) {
      if (!prodModTests.has(prodMod)) prodModTests.set(prodMod, new Set());
      prodModTests.get(prodMod).add(testPath);
    }
  };
  const addSeedModule = (modPath, reason, prodOwner = null) => {
    if (!seedModules.has(modPath)) seedModules.set(modPath, { reason, prodOwners: new Set() });
    if (prodOwner) {
      trackedProdMods.add(prodOwner);
      seedModules.get(modPath).prodOwners.add(prodOwner);
    }
  };

  let touchedPrompts = false, touchedStories = false, touchedDocs = false, touchedSkills = false;

  for (const file of changedFiles) {
    // Any test literally referencing this changed file path (e.g. docs/cli.md, .github/workflows/ci.yml).
    for (const refTest of pathToRefTests.get(file) ?? []) {
      if (isProductionCodeFile(file)) recordProdModTest(file, refTest, `references:${file}`);
      else addTest(refTest, `references:${file}`);
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
      directProdChanges.add(file);
      addSeedModule(file, `reverse-import:${file}`, file);
      for (const hit of matchTestsByStem(extractStem(file), totalTests)) {
        recordProdModTest(file, hit, `stem:${file}`);
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
        addSeedModule(owned, `prompt-owner:${file}`, isProductionCodeFile(owned) ? owned : null);
        for (const hit of matchTestsByStem(extractStem(owned), totalTests)) {
          if (isProductionCodeFile(owned)) recordProdModTest(owned, hit, `prompt-owner-stem:${owned}`);
          else addTest(hit, `prompt-owner-stem:${owned}`);
        }
      }
      // Also match conventional src/**/<stem>.* modules when headerless or newly paired.
      for (const candidate of allFiles) {
        if (isProductionCodeFile(candidate) && stemVariants(stem).includes(extractStem(candidate))) {
          addSeedModule(candidate, `prompt-stem-code:${file}`, candidate);
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
  // while bridging export *, aliased re-exports, and shared symbols through hubs and local test helpers).
  const nodeState = new Map();
  const queue = [];
  const enqueueModule = (modPath, reason, prodOwners) => {
    let state = nodeState.get(modPath);
    if (!state) {
      state = { reason, prodOwners: new Set(prodOwners) };
      nodeState.set(modPath, state);
      queue.push(modPath);
      return;
    }
    let addedOwner = false;
    for (const owner of prodOwners) {
      if (!state.prodOwners.has(owner)) {
        state.prodOwners.add(owner);
        addedOwner = true;
      }
    }
    if (addedOwner) queue.push(modPath);
  };
  for (const [modPath, info] of seedModules.entries()) {
    enqueueModule(modPath, info.reason, info.prodOwners);
  }

  while (queue.length) {
    const current = queue.shift();
    const { reason: originReason, prodOwners } = nodeState.get(current);
    const curExports = effectiveExports(current);
    for (const importer of reverseImporters.get(current) ?? []) {
      if (totalTestSet.has(importer)) {
        addTest(importer, originReason);
        for (const owner of prodOwners) recordProdModTest(owner, importer, originReason);
        continue;
      }
      if (!seedModules.has(importer) && dispatcherHubs.has(importer)) {
        for (const owner of prodOwners) {
          if (!prodModHubs.has(owner)) prodModHubs.set(owner, new Set());
          prodModHubs.get(owner).add(importer);
        }
        const hubExports = effectiveExports(importer);
        const bridged = new Set();
        if (wildcardReexports.get(importer)?.has(current)) {
          for (const sym of curExports) bridged.add(sym);
        }
        for (const sym of namedReexports.get(importer)?.get(current) ?? []) {
          bridged.add(sym);
        }
        for (const sym of curExports) {
          if (hubExports.has(sym)) bridged.add(sym);
        }
        if (bridged.size > 0) {
          const symRe = new RegExp(`(?<![A-Za-z0-9_$])(?:${[...bridged].map(escapeRegExp).join('|')})(?![A-Za-z0-9_$])`);
          for (const hubImporter of reverseImporters.get(importer) ?? []) {
            const src = moduleSources.get(hubImporter) ?? '';
            if (!symRe.test(src)) continue;
            if (totalTestSet.has(hubImporter)) {
              const bridgeReason = `${originReason}->${importer}`;
              addTest(hubImporter, bridgeReason);
              for (const owner of prodOwners) recordProdModTest(owner, hubImporter, bridgeReason);
            } else if (isLocalTestHelper(hubImporter)) {
              enqueueModule(hubImporter, `${originReason}->${importer}`, prodOwners);
            }
          }
        }
        continue;
      }
      enqueueModule(importer, originReason, prodOwners);
    }
  }

  // Collect all runnable tests reachable from a dispatcher hub (directly or via local test helpers).
  const hubTestsCache = new Map();
  const collectHubTests = hub => {
    if (hubTestsCache.has(hub)) return hubTestsCache.get(hub);
    const tests = new Set();
    const seen = new Set([hub]);
    const work = [hub];
    while (work.length) {
      const cur = work.shift();
      for (const imp of reverseImporters.get(cur) ?? []) {
        if (totalTestSet.has(imp)) tests.add(imp);
        else if (isLocalTestHelper(imp) && !seen.has(imp)) {
          seen.add(imp);
          work.push(imp);
        }
      }
    }
    const sortedTests = [...tests].sort(byText);
    hubTestsCache.set(hub, sortedTests);
    return sortedTests;
  };

  // Never allow a changed production module to resolve to 0 tests: bridge through reached hubs or fall back safely.
  for (const prodMod of [...trackedProdMods].sort(byText)) {
    if ((prodModTests.get(prodMod)?.size ?? 0) > 0) continue;
    const stem = extractStem(prodMod);
    const fullVariants = stemVariants(stem).filter(Boolean);
    const specificParts = stem
      .split(/[-_.]/)
      .map(s => s.toLowerCase())
      .filter(s => s.length >= 4 && !GENERIC_STEM_PARTS.has(s));
    const hubs = [...(prodModHubs.get(prodMod) ?? [])];
    const hubTests = new Set(hubs.flatMap(collectHubTests));

    // Step A: match tests mentioning full stem variants, test filenames sharing specific stem parts, or hub tests quoting stem parts.
    const fullStemRe = fullVariants.length
      ? new RegExp(`(?<![A-Za-z0-9])(?:${fullVariants.map(escapeRegExp).join('|')})(?![A-Za-z0-9])`, 'i')
      : null;
    const quotedPartRe = specificParts.length
      ? new RegExp(`['"\`](?:${specificParts.map(escapeRegExp).join('|')})['"\`]`, 'i')
      : null;

    for (const testPath of totalTests) {
      const testStemParts = extractStem(testPath)
        .split(/[-_.]/)
        .map(s => s.toLowerCase());
      const src = moduleSources.get(testPath) ?? '';
      if (
        (fullStemRe && fullStemRe.test(src)) ||
        specificParts.some(part => testStemParts.includes(part)) ||
        (hubTests.has(testPath) && quotedPartRe && quotedPartRe.test(src))
      ) {
        recordProdModTest(prodMod, testPath, `hub-stem-bridge:${prodMod}`);
      }
    }

    // Step B: if still 0 tests and the module is dispatched by hub(s), select runnable tests importing those hub(s).
    if ((prodModTests.get(prodMod)?.size ?? 0) === 0 && hubTests.size > 0) {
      for (const testPath of hubTests) {
        recordProdModTest(prodMod, testPath, `hub-importers:${prodMod}`);
      }
    }

    // Step C: if a directly changed production code module still has 0 tests while runnable tests exist, fall back safely to full suite.
    if (directProdChanges.has(prodMod) && (prodModTests.get(prodMod)?.size ?? 0) === 0 && totalTests.length > 0) {
      const fallbackReason = `no isolated test mapping for changed code (${prodMod})`;
      const reasons = Object.fromEntries(totalTests.map(t => [t, ['fallback:unmapped-code-change']]));
      const plan = {
        mode: 'full',
        selectedTests: [...totalTests],
        totalTests,
        selectedCount: totalTests.length,
        totalCount: totalTests.length,
        changedFiles,
        smokeTests,
        fallbackReason,
        fallbackCategory: 'unmapped-code-change',
        reasons,
      };
      return { ...plan, summary: formatAffectedTestsSummary(plan) };
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
