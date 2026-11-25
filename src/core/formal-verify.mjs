// Prompt: prompts/cli/formal-verify.prompt.md

// Shared Layer-1 language-agnostic code-bound formal verification engine (#3151, #3561):
// discovery, static multi-language code-binding inspection, per-file subprocess isolation,
// tier classification (proved_solver_code | bounded | proved_spec_model | not-applicable | missing),
// and disposable-copy production-code mutation control.
import { spawn, spawnSync } from 'node:child_process';
import {
  cpSync,
  existsSync,
  lstatSync,
  mkdirSync,
  mkdtempSync,
  readdirSync,
  readFileSync,
  realpathSync,
  rmSync,
  symlinkSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, posix, relative, sep } from 'node:path';
import { isTestOwnedPath } from '../file-owner.mjs';
import { gitFiles } from '../shared/git-context.mjs';
import { causeText } from '../shared/safe-read.mjs';
import { TEST_DIR_WITH_SPEC_PATTERN } from '../shared/test-paths.mjs';
import { canonicalRepoPath, formatTeachingDetail, readSafeUtf8, scrubChildEnv } from './lint/diagnostics.mjs';
import {
  buildRunnerEnv,
  buildRunnerInvocation,
  detectTestRunner,
  extractTestCases,
  parseCargoReport,
  parseGoJsonReport,
  parseJunitXml,
  parsePytestVerboseReport,
  parseTapReport,
  parseTestSummaryOutput,
  parseVitestVerboseReport,
  resolvePytestBinary,
  resolvePythonBinary,
} from './polyglot-runners.mjs';

export { resolvePytestBinary, resolvePythonBinary };

export const FORMAL_TEST_FILE_RE = /(?:\.formal\.test\.[^/]+$|(?:^|\/)(?:test_formal_[^/]+|[^/]+_formal_test)\.py$|(?:^|\/)formal\/(?:test_[^/]+|[^/]+_test)\.py$|_formal_test\.go$|(?:^|\/)tests\/[^/]*formal[^/]*\.rs$)/i;
export const PRODUCTION_CODE_FILE_RE = /\.(?:mjs|cjs|js|ts|tsx|jsx|py|go|rs|java|kt|rb|c|cc|cpp|h|hpp|cs|swift|scala|php|sh)$/i;
export const NON_PRODUCTION_PROOF_PATH_RE = new RegExp(`(?:^(?:prompts|docs|user_stories|pdd/stories|contracts|specs?|models?|fixtures|examples)/|\\.prompt\\.md$|\\.mdx?$|^(?:${TEST_DIR_WITH_SPEC_PATTERN})/|\\.(?:test|spec)\\.[a-z0-9]+$|_test\\.(?:go|rs|py)$|(?:^|/)test_[^/]+\\.py$|(?:^|/)(?:__pycache__|\\.pytest_cache|node_modules)/)`, 'i');

const STORY_PATH_RE = /(?:^(?:user_stories|pdd\/stories)\/[^/].*\.md$)/i;
const INVARIANT_DOMAIN_KEYWORD_RE = /\b(?:invariant|state\s+transition|state\s+machine|parser|validator|serializer|deserializer|auth(?:entication|orization)?|permission|trust\s+boundar|money|minor\s+unit|rounding|metric|quota|lock(?:ing)?|dedup(?:licat)?|schedul(?:e|er|ing)|bound(?:ed|s)?|fail[- ]closed|monoton(?:ic|icity)|concurren(?:t|cy)|idempoten(?:t|cy)|conservation|ordering|precedence)\b/i;

const JS_EXT_RE = /\.(?:mjs|cjs|js|ts|tsx|jsx)$/i;
const JS_RESOLVE_EXTS = ['', '.mjs', '.js', '.cjs', '.ts', '.tsx', '.jsx', '/index.mjs', '/index.js', '/index.cjs', '/index.ts', '/index.tsx'];
const PY_EXT_RE = /\.py$/i;
const GO_EXT_RE = /\.go$/i;
const RS_EXT_RE = /\.rs$/i;

const PY_IGNORED_MODULES = new Set([
  'z3', 'cvc5', 'pysmt', 'ortools', 'pytest', 'unittest', 'hypothesis', 'hypothesis_crosshair', 'crosshair',
  'math', 'cmath', 'random', 'sys', 'os', 're', 'json', 'pathlib', 'typing', 'dataclasses', 'itertools',
  'functools', 'collections', 'decimal', 'fractions', 'datetime', 'time', 'subprocess', 'tempfile', 'shutil',
  'io', 'copy', 'enum', 'abc', 'inspect', 'importlib', 'contextlib', 'threading', 'multiprocessing', 'asyncio',
  'hashlib', 'hmac', 'base64', 'uuid', 'struct', 'statistics', 'operator', 'heapq', 'bisect', 'array', 'queue',
  'string', 'textwrap', 'warnings', 'logging', 'argparse', 'csv', 'sqlite3', 'http', 'urllib', 'socket', 'ssl',
  'email', 'html', 'xml', 'zlib', 'gzip', 'tarfile', 'zipfile', 'pickle', 'shelve', 'pprint', 'traceback',
  'gc', 'weakref', 'types', 'numbers', 'builtins', '__future__',
]);

const SOLVER_CODE_RE = /(?:(?:^|[\s;(])(?:import|from)\s+(?:z3|cvc5|pysmt|crosshair)\b|#\[\s*kani::proof\s*\]|\bkani::any\b)/m;
const SOLVER_SPEC_RE = /^(?:z3-solver|z3|smt|cvc5|pysmt|crosshair|hypothesis[-_]crosshair)$/i;
const CODE_BOUND_SOLVER_CODE_RE = /(?:(?:^|[\s;(])(?:import|from)\s+(?:crosshair|hypothesis_crosshair)\b|#\[\s*kani::proof\s*\]|\bkani::any\b)/m;
const CODE_BOUND_SOLVER_SPEC_RE = /^(?:crosshair|hypothesis[-_]crosshair)$/i;
const SOLVER_COMMAND_RE = /\b(?:crosshair|kani|dafny|quint|tlc)\b/i;
const PROPERTY_TESTING_CODE_RE = /(?:\bmulberry32\b|\bxorshift\b|\bproptest!\s*\{|for\s*\(\s*(?:let|var|const)\s+\w+\s*=|for\s+\w+\s+in\s+range\s*\(|(?:^|[\s;(])(?:import|from)\s+hypothesis\b|\brapid\.Check\b|\bquick\.Check\b)/im;
const PROPERTY_TESTING_SPEC_RE = /^(?:fast-check|hypothesis|proptest|quickcheck|pgrec\.net\/rapid|.*\/rapid)$/i;
const SYNTAX_CRASH_RE = /(?:^\s*(?:#\s*|E\s+|error:\s*)?(?:SyntaxError:|IndentationError:|TabError:|ImportError:|ModuleNotFoundError:|NameError:.*is not defined|ReferenceError:|ParseError:|Transform failed\b|Error\s*\[ERR_MODULE_NOT_FOUND\]:|Cannot find (?:module|package)\b|ERROR collecting\b|error\[E\d+\]:|failed to compile\b|could not compile\b)|\[build failed\]|"Action"\s*:\s*"build-fail"|syntax error\b)/im;
const MISSING_RUNNER_RE = /(?:ENOENT|command not found|not recognized as an internal|No such file or directory)/i;

const isPlainObj = v => v !== null && typeof v === 'object' && !Array.isArray(v);
const nonEmpty = v => typeof v === 'string' && v.trim().length > 0;

export function isProductionCodeFile(filePath) {
  return canonicalRepoPath(filePath)
    && PRODUCTION_CODE_FILE_RE.test(filePath)
    && !isTestOwnedPath(filePath)
    && !NON_PRODUCTION_PROOF_PATH_RE.test(filePath);
}

function listRepoFilesSafe(realRoot, providedFiles = null) {
  if (Array.isArray(providedFiles)) {
    return [...new Set(providedFiles.filter(canonicalRepoPath))].sort();
  }
  try {
    const tracked = gitFiles(realRoot);
    if (Array.isArray(tracked) && tracked.length > 0) {
      return [...new Set(tracked.filter(canonicalRepoPath))].sort();
    }
  } catch {
    // Fallback to safe bounded filesystem walk when not a git checkout.
  }
  const found = [];
  const walk = (absDir, relPrefix, depth) => {
    if (depth > 8 || found.length >= 10_000) return;
    let entries;
    try { entries = readdirSync(absDir, { withFileTypes: true }); } catch { return; }
    for (const entry of entries) {
      if (found.length >= 10_000) break;
      if (entry.isSymbolicLink()) continue;
      if (entry.name === '.git' || entry.name === 'node_modules' || entry.name === '.venv' || entry.name === 'venv' || entry.name === '__pycache__' || entry.name === 'target') continue;
      const rel = relPrefix ? `${relPrefix}/${entry.name}` : entry.name;
      if (entry.isDirectory()) walk(join(absDir, entry.name), rel, depth + 1);
      else if (entry.isFile() && canonicalRepoPath(rel)) found.push(rel);
    }
  };
  walk(realRoot, '', 0);
  return found.sort();
}

/**
 * Single-pass comment-stripping and string-isolating lexer for C-style languages (JS/TS, Go, Rust).
 * Handles Rust lifetimes (`'a` vs char literals `'a'`), Rust raw strings (`r#*"..."#*`),
 * Go raw backtick strings, and JS/TS quotes/template literals.
 * Returns `codeOnly` (all string interiors blanked) and `sentinelCode` (quoted literals replaced
 * by `__PDD_STR_<idx>__` placeholders pointing into `strings[]`) so strings/comments can never spoof imports.
 */
export function lexCStyleSource(source, { rust = false, go = false } = {}) {
  const s = String(source ?? '');
  const strings = [];
  let codeOnly = '';
  let sentinelCode = '';
  let i = 0;
  let prev = '';

  const canStartJsRegex = () => !prev || '(=:,[!&|?{};+*%<>^~'.includes(prev) || /^(?:return|throw|case|in|of|typeof|void|delete|await|yield)$/.test(prev);

  const pushString = (rawText, value, quote) => {
    const idx = strings.length;
    strings.push({ raw: rawText, value, quote });
    const nlMask = rawText.replace(/[^\n]/g, ' ');
    codeOnly += nlMask;
    // Only single-line quoted literals (`'` or `"`) are valid import specifiers; multiline/backtick strings get blanked.
    if ((quote === '\'' || quote === '"') && !rawText.includes('\n')) {
      sentinelCode += `__PDD_STR_${idx}__`;
    } else {
      sentinelCode += nlMask;
    }
    prev = 's';
  };

  while (i < s.length) {
    const ch = s[i], next = s[i + 1];
    if (ch === '/' && next === '/') {
      const end = s.indexOf('\n', i + 2);
      const slice = end < 0 ? s.slice(i) : s.slice(i, end);
      const pad = ' '.repeat(slice.length);
      codeOnly += pad + (end < 0 ? '' : '\n');
      sentinelCode += pad + (end < 0 ? '' : '\n');
      if (end < 0) break;
      i = end + 1;
      continue;
    }
    if (ch === '/' && next === '*') {
      const end = s.indexOf('*/', i + 2);
      const slice = end < 0 ? s.slice(i) : s.slice(i, end + 2);
      const nlMask = slice.replace(/[^\n]/g, ' ');
      codeOnly += nlMask;
      sentinelCode += nlMask;
      if (end < 0) break;
      i = end + 2;
      continue;
    }
    // JS/TS regex literal (handled before string quotes so `/['"]/` never desynchronizes string lexing).
    if (!rust && !go && ch === '/' && next !== '/' && next !== '*' && canStartJsRegex()) {
      let j = i + 1;
      let inClass = false;
      let closed = false;
      while (j < s.length && s[j] !== '\n') {
        if (s[j] === '\\') { j += 2; continue; }
        if (s[j] === '[') inClass = true;
        else if (s[j] === ']') inClass = false;
        else if (s[j] === '/' && !inClass) { closed = true; j += 1; break; }
        j += 1;
      }
      if (closed) {
        while (j < s.length && /[A-Za-z]/.test(s[j])) j += 1;
        const pad = ' '.repeat(j - i);
        codeOnly += pad;
        sentinelCode += pad;
        prev = 'r';
        i = j;
        continue;
      }
    }
    // Rust raw string literals: r"...", r#"..."#, br#"..."#, cr#"..."#
    if (rust && (ch === 'r' || ((ch === 'b' || ch === 'c') && next === 'r'))) {
      const rPos = ch === 'r' ? i : i + 1;
      const prevChar = i > 0 ? s[i - 1] : '';
      if (!/[A-Za-z0-9_]/.test(prevChar)) {
        let k = rPos + 1;
        while (k < s.length && s[k] === '#') k += 1;
        if (s[k] === '"') {
          const hashes = '#'.repeat(k - (rPos + 1));
          const closeSeq = `"${hashes}`;
          const endIdx = s.indexOf(closeSeq, k + 1);
          const stop = endIdx < 0 ? s.length : endIdx + closeSeq.length;
          const rawLit = s.slice(i, stop);
          pushString(rawLit, endIdx < 0 ? s.slice(k + 1) : s.slice(k + 1, endIdx), 'raw');
          i = stop;
          continue;
        }
      }
    }
    // Rust single quote: distinguish char literals ('a', '\n', '\x7f', '\u{1f}') from lifetimes ('a, 'static, '_).
    if (rust && ch === '\'') {
      const charM = /^'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F_]+\}|.)|[^'\\\n])'/.exec(s.slice(i, i + 16));
      if (charM) {
        const lit = charM[0];
        pushString(lit, lit.slice(1, -1), 'char');
        i += lit.length;
        continue;
      }
      codeOnly += ch;
      sentinelCode += ch;
      prev = ch;
      i += 1;
      continue;
    }
    if (ch === '\'' || ch === '"' || ch === '`') {
      let j = i + 1;
      while (j < s.length) {
        if (s[j] === '\\' && !(go && ch === '`')) {
          if (s[j + 1] === '\r' && s[j + 2] === '\n') { j += 3; continue; }
          j += 2;
          continue;
        }
        if (s[j] === '\n' && !rust && ch !== '`') break;
        if (s[j] === ch) { j += 1; break; }
        j += 1;
      }
      const rawLit = s.slice(i, j);
      const closed = j > i + 1 && s[j - 1] === ch;
      pushString(rawLit, closed ? rawLit.slice(1, -1) : rawLit.slice(1), ch);
      i = j;
      continue;
    }
    if (!rust && !go && /[A-Za-z_$]/.test(ch)) {
      let j = i + 1;
      while (j < s.length && /[A-Za-z0-9_$]/.test(s[j])) j += 1;
      const ident = s.slice(i, j);
      codeOnly += ident;
      sentinelCode += ident;
      prev = ident;
      i = j;
      continue;
    }
    codeOnly += ch;
    sentinelCode += ch;
    if (!/\s/.test(ch)) prev = ch;
    i += 1;
  }
  return { codeOnly, sentinelCode, strings };
}

/**
 * Single-pass comment-stripping and string-isolating lexer for Python.
 * Properly handles `#` comments, triple-quoted strings/docstrings, and backslash line-continued strings
 * so commented-out imports, docstrings, and string literals can never spoof imports.
 */
export function lexPythonSource(source) {
  const s = String(source ?? '');
  const strings = [];
  let codeOnly = '';
  let sentinelCode = '';
  let i = 0;

  const pushString = (rawText, value, singleLine) => {
    const idx = strings.length;
    strings.push({ raw: rawText, value });
    const nlMask = rawText.replace(/[^\n]/g, ' ');
    codeOnly += nlMask;
    sentinelCode += singleLine ? `__PDD_STR_${idx}__` : nlMask;
  };

  while (i < s.length) {
    const ch = s[i];
    if (ch === '#') {
      const end = s.indexOf('\n', i + 1);
      const slice = end < 0 ? s.slice(i) : s.slice(i, end);
      const pad = ' '.repeat(slice.length);
      codeOnly += pad + (end < 0 ? '' : '\n');
      sentinelCode += pad + (end < 0 ? '' : '\n');
      if (end < 0) break;
      i = end + 1;
      continue;
    }
    if ((ch === '"' || ch === '\'') && s[i + 1] === ch && s[i + 2] === ch) {
      const delim = ch.repeat(3);
      let j = i + 3;
      while (j < s.length) {
        if (s[j] === '\\') { j += 2; continue; }
        if (s.startsWith(delim, j)) { j += 3; break; }
        j += 1;
      }
      const block = s.slice(i, j);
      pushString(block, block.slice(3, block.endsWith(delim) ? -3 : undefined), false);
      i = j;
      continue;
    }
    if (ch === '\'' || ch === '"') {
      let j = i + 1;
      while (j < s.length) {
        if (s[j] === '\\') {
          if (s[j + 1] === '\r' && s[j + 2] === '\n') { j += 3; continue; }
          j += 2;
          continue;
        }
        if (s[j] === '\n') break;
        if (s[j] === ch) { j += 1; break; }
        j += 1;
      }
      const rawLit = s.slice(i, j);
      const closed = j > i + 1 && s[j - 1] === ch;
      const singleLine = closed && !rawLit.includes('\n');
      pushString(rawLit, closed ? rawLit.slice(1, -1) : rawLit.slice(1), singleLine);
      i = j;
      continue;
    }
    codeOnly += ch;
    sentinelCode += ch;
    i += 1;
  }
  return { codeOnly, sentinelCode, strings };
}

function detectLanguage(filePath) {
  if (JS_EXT_RE.test(filePath)) return 'javascript';
  if (PY_EXT_RE.test(filePath)) return 'python';
  if (GO_EXT_RE.test(filePath)) return 'go';
  if (RS_EXT_RE.test(filePath)) return 'rust';
  return 'other';
}

function resolveRelativeJsTarget(fromFile, rawSpec, repoSet) {
  if (!rawSpec || (!rawSpec.startsWith('./') && !rawSpec.startsWith('../'))) return null;
  const cleanSpec = rawSpec.split(/[?#]/)[0];
  const baseDir = posix.dirname(fromFile);
  const joined = posix.normalize(baseDir === '.' ? cleanSpec : `${baseDir}/${cleanSpec}`).replace(/^(?:\.\/)+/, '');
  if (!canonicalRepoPath(joined)) return null;
  for (const suffix of JS_RESOLVE_EXTS) {
    const cand = `${joined}${suffix}`;
    if (repoSet.has(cand)) return cand;
  }
  // Support TypeScript `.js` import specifiers pointing to `.ts`/`.tsx` source files.
  if (/\.[cm]?js$/i.test(joined)) {
    const stem = joined.replace(/\.[cm]?js$/i, '');
    for (const ext of ['.ts', '.tsx', '.mts', '.cts']) {
      if (repoSet.has(`${stem}${ext}`)) return `${stem}${ext}`;
    }
  }
  return null;
}

function extractJsSpecifiers(lexed) {
  const specs = new Set();
  const addByIndex = idxStr => {
    const s = lexed.strings[Number(idxStr)]?.value;
    if (typeof s === 'string' && s.trim()) specs.add(s.trim());
  };
  // Reject TypeScript `import type` / `export type` (erased at runtime, executes zero production code).
  for (const m of lexed.sentinelCode.matchAll(/(?:^|[;\n])\s*(import|export)\s+(?!type\b)(?:[^;\n]*?\s+from\s+)?__PDD_STR_(\d+)__/g)) {
    addByIndex(m[2]);
  }
  // Also handle multiline `import {\n  a,\n  b,\n} from '...'` (excluding `import type` / `export type`).
  for (const m of lexed.sentinelCode.matchAll(/(?:^|[;\n])\s*(?:import|export)\s+(?!type\b)\{[\s\S]*?\}\s*from\s+__PDD_STR_(\d+)__/g)) {
    addByIndex(m[1]);
  }
  for (const re of [
    /\bimport\s*\(\s*__PDD_STR_(\d+)__\s*\)/g,
    /(?<![.\w$])require\s*\(\s*__PDD_STR_(\d+)__\s*\)/g,
    /\bnew\s+URL\s*\(\s*__PDD_STR_(\d+)__\s*,\s*import\.meta\.url\s*\)/g,
  ]) {
    for (const m of lexed.sentinelCode.matchAll(re)) addByIndex(m[1]);
  }
  return [...specs];
}

function resolveJsProductionImports(realRoot, filePath, lexed, repoSet) {
  const prod = new Set();
  const visited = new Set([filePath]);
  const walk = (curFile, curLexed, depth) => {
    for (const spec of extractJsSpecifiers(curLexed)) {
      const target = resolveRelativeJsTarget(curFile, spec, repoSet);
      if (!target) continue;
      if (isProductionCodeFile(target)) {
        prod.add(target);
      } else if (depth > 0 && !visited.has(target) && visited.size < 40 && JS_EXT_RE.test(target)) {
        visited.add(target);
        const helperRaw = readSafeUtf8(realRoot, target);
        if (typeof helperRaw === 'string') walk(target, lexCStyleSource(helperRaw), depth - 1);
      }
    }
  };
  walk(filePath, lexed, 2);
  return [...prod].sort();
}

function resolvePythonModuleCandidates(modPath, fromFile, leadingDots, repoSet) {
  const matches = [];
  const tryBase = base => {
    if (!base) return;
    const norm = posix.normalize(base).replace(/^(?:\.\/)+/, '').replace(/\/+$/, '');
    if (!canonicalRepoPath(norm)) return;
    for (const cand of [`${norm}.py`, `${norm}/__init__.py`]) {
      if (repoSet.has(cand)) matches.push(cand);
    }
  };
  const relParts = modPath ? modPath.split('.').filter(Boolean) : [];
  if (leadingDots > 0) {
    let dir = posix.dirname(fromFile);
    for (let i = 1; i < leadingDots; i += 1) dir = posix.dirname(dir);
    if (dir === '.') dir = '';
    const joined = [dir, ...relParts].filter(Boolean).join('/');
    tryBase(joined);
  } else if (relParts.length > 0) {
    if (PY_IGNORED_MODULES.has(relParts[0])) return [];
    const rel = relParts.join('/');
    tryBase(rel);
    tryBase(`src/${rel}`);
    tryBase(`lib/${rel}`);
  }
  return [...new Set(matches)];
}

function resolvePythonProductionImports(realRoot, filePath, lexed, repoSet) {
  const prod = new Set();
  const visited = new Set([filePath]);
  const walk = (curFile, curLexed, depth) => {
    const candidates = new Set();
    const lines = curLexed.codeOnly.split(/\r?\n/);
    for (const rawLine of lines) {
      const line = rawLine.trim();
      if (!line) continue;
      const fromM = /^from\s+(\.*)([A-Za-z_][A-Za-z0-9_.]*)?\s+import\s+(.+)$/.exec(line);
      if (fromM) {
        const dots = fromM[1].length;
        const baseMod = fromM[2] ?? '';
        const importedList = fromM[3].replace(/[()]/g, '').split(',').map(s => s.trim().split(/\s+as\s+/)[0].trim()).filter(Boolean);
        for (const c of resolvePythonModuleCandidates(baseMod, curFile, dots, repoSet)) candidates.add(c);
        for (const sym of importedList) {
          if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(sym)) continue;
          const combined = baseMod ? `${baseMod}.${sym}` : sym;
          for (const c of resolvePythonModuleCandidates(combined, curFile, dots, repoSet)) candidates.add(c);
        }
        continue;
      }
      const impM = /^import\s+(.+)$/.exec(line);
      if (impM) {
        for (const seg of impM[1].split(',')) {
          const mod = seg.trim().split(/\s+as\s+/)[0].trim();
          if (/^[A-Za-z_][A-Za-z0-9_.]*$/.test(mod)) {
            for (const c of resolvePythonModuleCandidates(mod, curFile, 0, repoSet)) candidates.add(c);
          }
        }
        continue;
      }
    }
    for (const dynM of curLexed.sentinelCode.matchAll(/\bimportlib\.import_module\s*\(\s*__PDD_STR_(\d+)__\s*(?:,|\))/g)) {
      const rawMod = curLexed.strings[Number(dynM[1])]?.value ?? '';
      if (!/^[A-Za-z0-9_.]+$/.test(rawMod)) continue;
      const dotsMatch = /^(\.+)(.*)$/.exec(rawMod);
      const dots = dotsMatch ? dotsMatch[1].length : 0;
      const mod = dotsMatch ? dotsMatch[2] : rawMod;
      for (const c of resolvePythonModuleCandidates(mod, curFile, dots, repoSet)) candidates.add(c);
    }
    for (const target of candidates) {
      if (isProductionCodeFile(target)) {
        prod.add(target);
      } else if (depth > 0 && !visited.has(target) && visited.size < 20 && PY_EXT_RE.test(target)) {
        visited.add(target);
        const helperRaw = readSafeUtf8(realRoot, target);
        if (typeof helperRaw === 'string') walk(target, lexPythonSource(helperRaw), depth - 1);
      }
    }
  };
  walk(filePath, lexed, 1);
  return [...prod].sort();
}

function extractGoDeclaredSymbols(codeOnly) {
  const syms = new Set();
  for (const m of codeOnly.matchAll(/^\s*func\s+(?:\([^)]*\)\s*)?([A-Za-z_][A-Za-z0-9_]*)\s*(?:\[[^\]]*\])?\s*\(/gm)) {
    if (m[1] !== 'main' && m[1] !== 'init') syms.add(m[1]);
  }
  for (const m of codeOnly.matchAll(/^\s*(?:type|var|const)\s+([A-Za-z_][A-Za-z0-9_]*)\b/gm)) {
    // Exclude 1-char lowercase var/const/type identifiers (e.g., `var i int`) to avoid matching test loop variables.
    if (m[1].length >= 2 || /^[A-Z]/.test(m[1])) syms.add(m[1]);
  }
  return [...syms];
}

function extractGoImportedPackages(lexed) {
  const importedPkgs = [];
  for (const m of lexed.sentinelCode.matchAll(/^\s*import\s+(?:[A-Za-z_.]\w*\s+)?__PDD_STR_(\d+)__/gm)) {
    const pkg = lexed.strings[Number(m[1])]?.value;
    if (pkg) importedPkgs.push(pkg);
  }
  for (const block of lexed.sentinelCode.matchAll(/^\s*import\s*\(([\s\S]*?)\)/gm)) {
    for (const m of block[1].matchAll(/__PDD_STR_(\d+)__/g)) {
      const pkg = lexed.strings[Number(m[1])]?.value;
      if (pkg) importedPkgs.push(pkg);
    }
  }
  return importedPkgs;
}

function resolveGoProductionImports(realRoot, filePath, lexed, allRepoFiles) {
  const prod = new Set();
  const goMod = readSafeUtf8(realRoot, 'go.mod');
  const modPath = typeof goMod === 'string' ? /^\s*module\s+(\S+)/m.exec(goMod)?.[1]?.replace(/\/+$/, '') ?? null : null;

  const importedPkgs = extractGoImportedPackages(lexed);
  if (modPath) {
    for (const pkg of importedPkgs) {
      if (pkg !== modPath && !pkg.startsWith(`${modPath}/`)) continue;
      const relDir = pkg === modPath ? '' : pkg.slice(modPath.length + 1).replace(/\/+$/, '');
      for (const f of allRepoFiles) {
        if (!GO_EXT_RE.test(f) || !isProductionCodeFile(f)) continue;
        const dir = posix.dirname(f) === '.' ? '' : posix.dirname(f);
        if (dir === relDir) prod.add(f);
      }
    }
  }

  // Same-package Go tests (`package foo`, NOT `package foo_test`) must reference at least one symbol from sibling prod files.
  const pkgDecl = /^\s*package\s+([A-Za-z_][A-Za-z0-9_]*)/m.exec(lexed.codeOnly)?.[1] ?? '';
  if (pkgDecl && !pkgDecl.endsWith('_test')) {
    const fileDir = posix.dirname(filePath) === '.' ? '' : posix.dirname(filePath);
    const siblings = allRepoFiles.filter(f => {
      if (f === filePath || !GO_EXT_RE.test(f) || !isProductionCodeFile(f)) return false;
      const d = posix.dirname(f) === '.' ? '' : posix.dirname(f);
      return d === fileDir;
    });
    for (const sib of siblings) {
      const sibRaw = readSafeUtf8(realRoot, sib);
      if (typeof sibRaw !== 'string') continue;
      const syms = extractGoDeclaredSymbols(lexCStyleSource(sibRaw, { go: true }).codeOnly);
      for (const sym of syms) {
        if (new RegExp(`(?<![A-Za-z0-9_])${sym}(?![A-Za-z0-9_])`).test(lexed.codeOnly)) {
          prod.add(sib);
          break;
        }
      }
    }
  }
  return [...prod].sort();
}

function resolveRustProductionImports(realRoot, lexed, repoSet) {
  const prod = new Set();
  const cargoToml = readSafeUtf8(realRoot, 'Cargo.toml');
  const pkgName = typeof cargoToml === 'string'
    ? /^\s*name\s*=\s*"([^"]+)"/m.exec(cargoToml)?.[1]?.replace(/-/g, '_') ?? null
    : null;

  const addRustTarget = subMod => {
    if (subMod) {
      const clean = subMod.replace(/::/g, '/');
      for (const cand of [`src/${clean}.rs`, `src/${clean}/mod.rs`]) {
        if (repoSet.has(cand) && isProductionCodeFile(cand)) { prod.add(cand); return; }
      }
    }
    if (repoSet.has('src/lib.rs') && isProductionCodeFile('src/lib.rs')) prod.add('src/lib.rs');
    else if (repoSet.has('src/main.rs') && isProductionCodeFile('src/main.rs')) prod.add('src/main.rs');
  };

  for (const m of lexed.codeOnly.matchAll(/^\s*(?:pub\s+)?use\s+([A-Za-z_][A-Za-z0-9_]*)(?:::([A-Za-z_][A-Za-z0-9_:]*))?/gm)) {
    const rootIdent = m[1];
    const sub = m[2] ? m[2].split('::')[0] : null;
    if (rootIdent === 'crate' || (pkgName && rootIdent === pkgName)) {
      addRustTarget(sub);
    }
  }
  if (pkgName) {
    if (new RegExp(`\\bextern\\s+crate\\s+${pkgName}\\b|\\b${pkgName}::[A-Za-z_]`).test(lexed.codeOnly)) {
      addRustTarget(null);
    }
  }
  for (const m of lexed.codeOnly.matchAll(/^\s*(?:pub\s+)?mod\s+([A-Za-z_][A-Za-z0-9_]*)\s*;/gm)) {
    addRustTarget(m[1]);
  }
  return [...prod].sort();
}

/**
 * Inspect a single formal test file statically for real production-code imports and proof markers.
 * Comments, docstrings, and string literals are isolated before analysis so spoofed imports
 * and string markers can never satisfy code binding; zero production imports classify as `proved_spec_model`.
 */
export function inspectFormalFileBinding({ root, filePath, targetModules = [], allRepoFiles = null } = {}) {
  const empty = reason => ({
    file: String(filePath ?? ''),
    language: detectLanguage(String(filePath ?? '')),
    importedProductionModules: [],
    coversTargets: false,
    codeBound: false,
    hasSolverImport: false,
    hasCodeBoundSolver: false,
    hasPropertyTesting: false,
    isStandaloneZ3: false,
    tier: 'proved_spec_model',
    satisfiesCodeVerification: false,
    reason,
  });

  if (!nonEmpty(root) || !canonicalRepoPath(filePath)) return empty('Invalid root or non-canonical formal test path.');
  let realRoot;
  try { realRoot = realpathSync(root); } catch { return empty('Repository root is unreadable.'); }
  const raw = readSafeUtf8(realRoot, filePath);
  if (typeof raw !== 'string') return empty(`Formal file "${filePath}" is missing, unreadable, or a symlink.`);

  const repoFiles = listRepoFilesSafe(realRoot, allRepoFiles);
  const repoSet = new Set(repoFiles);
  const language = detectLanguage(filePath);
  const lexed = language === 'python'
    ? lexPythonSource(raw)
    : lexCStyleSource(raw, { rust: language === 'rust', go: language === 'go' });

  let importedProductionModules = [];
  let importSpecs = [];
  if (language === 'javascript') {
    importSpecs = extractJsSpecifiers(lexed);
    importedProductionModules = resolveJsProductionImports(realRoot, filePath, lexed, repoSet);
  } else if (language === 'python') {
    importedProductionModules = resolvePythonProductionImports(realRoot, filePath, lexed, repoSet);
  } else if (language === 'go') {
    importSpecs = extractGoImportedPackages(lexed);
    importedProductionModules = resolveGoProductionImports(realRoot, filePath, lexed, repoFiles);
  } else if (language === 'rust') {
    importedProductionModules = resolveRustProductionImports(realRoot, lexed, repoSet);
  }

  const normalizedTargets = [...new Set((Array.isArray(targetModules) ? targetModules : []).filter(isProductionCodeFile))].sort();
  const importedSet = new Set(importedProductionModules);
  const coversTargets = normalizedTargets.length === 0
    ? importedProductionModules.length > 0
    : normalizedTargets.every(m => importedSet.has(m));

  const hasSolverImport = SOLVER_CODE_RE.test(lexed.codeOnly) || importSpecs.some(s => SOLVER_SPEC_RE.test(s));
  const hasCodeBoundSolver = CODE_BOUND_SOLVER_CODE_RE.test(lexed.codeOnly) || importSpecs.some(s => CODE_BOUND_SOLVER_SPEC_RE.test(s));
  const hasPropertyTesting = PROPERTY_TESTING_CODE_RE.test(lexed.codeOnly) || importSpecs.some(s => PROPERTY_TESTING_SPEC_RE.test(s));
  const isStandaloneZ3 = hasSolverImport && importedProductionModules.length === 0;
  const codeBound = importedProductionModules.length > 0;

  if (!codeBound) {
    return {
      file: filePath,
      language,
      importedProductionModules: [],
      coversTargets: false,
      codeBound: false,
      hasSolverImport,
      hasCodeBoundSolver,
      hasPropertyTesting,
      isStandaloneZ3,
      tier: 'proved_spec_model',
      satisfiesCodeVerification: false,
      reason: isStandaloneZ3
        ? `Standalone solver/Z3 spec model "${filePath}" does not import production code (proved_spec_model).`
        : `Formal test "${filePath}" does not import or reference any production module (proved_spec_model).`,
    };
  }

  return {
    file: filePath,
    language,
    importedProductionModules,
    coversTargets,
    codeBound: true,
    hasSolverImport,
    hasCodeBoundSolver,
    hasPropertyTesting,
    isStandaloneZ3: false,
    tier: 'bounded',
    satisfiesCodeVerification: true,
    reason: `Formal test "${filePath}" imports production module(s): ${importedProductionModules.join(', ')}.`,
  };
}

function extractMarkdownSectionItems(markdown, headingRe) {
  const items = [];
  let inSection = false;
  for (const rawLine of String(markdown ?? '').split(/\r?\n/)) {
    const trimmed = rawLine.trim();
    if (/^#{1,6}\s+/.test(trimmed)) {
      inSection = headingRe.test(trimmed);
      continue;
    }
    if (!inSection || !trimmed) continue;
    if (/^\|[\s:-]+\|/.test(trimmed)) continue;
    if (/^(?:[-*+]|\d+[.)])\s+\S/.test(trimmed)) {
      items.push(trimmed.replace(/^(?:[-*+]|\d+[.)])\s+/, '').trim());
    } else if (/^\|.+\|$/.test(trimmed) && !/^\|\s*(?:rule|id|check|part|decision)\s*\|/i.test(trimmed)) {
      items.push(trimmed);
    }
  }
  return items;
}

/**
 * Discover formal verification scope for a repository diff:
 * touched formal files, existing repo formal files importing touched production modules,
 * and touched explicit invariant rules (`## Rules to check` / invariant `## Domain decisions`).
 */
export function discoverFormalScope({ root, touchedFiles = [], allFiles = null, formalCommand = null } = {}) {
  const cleanTouched = [...new Set((Array.isArray(touchedFiles) ? touchedFiles : []).filter(canonicalRepoPath))].sort();
  if (!nonEmpty(root)) {
    return {
      applicable: Boolean(formalCommand),
      touchedFormalFiles: [],
      linkedFormalFiles: [],
      formalFiles: [],
      touchedProdFiles: cleanTouched.filter(isProductionCodeFile),
      invariantRules: [],
      invariantSources: [],
      allRepoFiles: [],
    };
  }
  let realRoot;
  try { realRoot = realpathSync(root); } catch {
    return {
      applicable: Boolean(formalCommand),
      touchedFormalFiles: [],
      linkedFormalFiles: [],
      formalFiles: [],
      touchedProdFiles: [],
      invariantRules: [],
      invariantSources: [],
      allRepoFiles: [],
    };
  }
  const allRepoFiles = listRepoFilesSafe(realRoot, allFiles);
  const allRepoSet = new Set(allRepoFiles);
  const touchedProdFiles = cleanTouched.filter(f => isProductionCodeFile(f) && allRepoSet.has(f));
  const touchedProdSet = new Set(touchedProdFiles);
  const touchedFormalFiles = cleanTouched.filter(f => FORMAL_TEST_FILE_RE.test(f) && allRepoSet.has(f));
  const touchedFormalSet = new Set(touchedFormalFiles);

  // Discover existing repo formal files that statically bind to any touched production module.
  const linkedFormalFiles = [];
  if (touchedProdSet.size > 0) {
    const candidateFormals = allRepoFiles.filter(f => FORMAL_TEST_FILE_RE.test(f) && !touchedFormalSet.has(f));
    for (const formalFile of candidateFormals) {
      const binding = inspectFormalFileBinding({ root: realRoot, filePath: formalFile, allRepoFiles });
      if (binding.importedProductionModules.some(m => touchedProdSet.has(m))) {
        linkedFormalFiles.push(formalFile);
      }
    }
  }
  const formalFiles = [...new Set([...touchedFormalFiles, ...linkedFormalFiles])].sort();

  const invariantRules = [];
  const invariantSources = [];
  for (const rel of cleanTouched) {
    if (!allRepoSet.has(rel)) continue;
    const isPrompt = rel.endsWith('.prompt.md');
    const isStory = !isPrompt && STORY_PATH_RE.test(rel);
    if (!isPrompt && !isStory) continue;
    const text = readSafeUtf8(realRoot, rel);
    if (typeof text !== 'string') continue;
    const rulesToCheck = extractMarkdownSectionItems(text, /^##\s+Rules\s+to\s+check\s*$/i);
    if (rulesToCheck.length > 0) {
      invariantSources.push(rel);
      for (const r of rulesToCheck) invariantRules.push({ source: rel, section: 'Rules to check', text: r.slice(0, 200) });
    }
    if (isPrompt) {
      const domainItems = extractMarkdownSectionItems(text, /^##\s+Domain\s+decisions\s*$/i)
        .filter(item => INVARIANT_DOMAIN_KEYWORD_RE.test(item));
      if (domainItems.length > 0) {
        if (!invariantSources.includes(rel)) invariantSources.push(rel);
        for (const r of domainItems) invariantRules.push({ source: rel, section: 'Domain decisions', text: r.slice(0, 200) });
      }
    }
  }

  const applicable = formalFiles.length > 0 || Boolean(nonEmpty(formalCommand)) || invariantRules.length > 0;
  return {
    applicable,
    touchedFormalFiles,
    linkedFormalFiles: linkedFormalFiles.sort(),
    formalFiles,
    touchedProdFiles,
    invariantRules,
    invariantSources: invariantSources.sort(),
    allRepoFiles,
  };
}

export function chooseRunnerForFormalFile(root, filePath) {
  if (PY_EXT_RE.test(filePath)) return 'pytest';
  if (GO_EXT_RE.test(filePath)) return 'go';
  if (RS_EXT_RE.test(filePath)) return 'cargo';
  if (JS_EXT_RE.test(filePath)) {
    const raw = readSafeUtf8(root, filePath) ?? '';
    if (raw.includes('node:test')) return 'node:test';
    const detected = detectTestRunner(root);
    if (detected?.kind === 'vitest') return 'vitest';
    if (detected?.kind === 'jest') return 'jest';
    if (/\.(?:mjs|cjs|js)$/i.test(filePath)) return 'node:test';
    return detected?.kind ?? 'vitest';
  }
  return detectTestRunner(root)?.kind ?? null;
}

function parseFormalRunOutput({ kind, stdout, stderr, junitPath }) {
  if (junitPath && existsSync(junitPath)) {
    try {
      const xml = readFileSync(junitPath, 'utf8');
      const parsed = parseJunitXml(xml);
      if (parsed.ok) return parsed;
    } catch {
      // fall through to stdout/stderr parsing
    }
  }
  const combined = `${stdout ?? ''}\n${stderr ?? ''}`;
  if (kind === 'node:test') {
    const r = parseTapReport(stdout || combined);
    if (r.ok) return r;
  } else if (kind === 'pytest') {
    const r = parsePytestVerboseReport(combined);
    if (r.ok) return r;
  } else if (kind === 'vitest') {
    const r = parseVitestVerboseReport(combined);
    if (r.ok) return r;
  } else if (kind === 'go') {
    const r = parseGoJsonReport(stdout || combined);
    if (r.ok) return r;
  } else if (kind === 'cargo') {
    const r = parseCargoReport(combined);
    if (r.ok) return r;
  }
  const counts = parseTestSummaryOutput(combined, kind);
  if (counts) {
    const cases = extractTestCases(combined, kind ?? 'auto');
    return { ok: true, complete: true, format: counts.format ?? kind ?? 'unknown', cases, counts, reason: null };
  }
  return { ok: false, complete: false, format: kind ?? 'unknown', cases: [], counts: null, reason: 'unparsed_output' };
}

const INTERRUPT_SIGNALS = new Set(['SIGINT', 'SIGTERM', 'SIGHUP']);

export function detectSignalInterruption(proc) {
  if (!proc) return null;
  if (proc.interruptedBy) return proc.interruptedBy;
  if (!proc.timedOut && proc.signal && INTERRUPT_SIGNALS.has(proc.signal)) return proc.signal;
  const code = typeof proc.exitCode === 'number' ? proc.exitCode : (typeof proc.status === 'number' ? proc.status : null);
  if (!proc.timedOut && code === 130) return 'SIGINT';
  if (!proc.timedOut && code === 143) return 'SIGTERM';
  if (!proc.timedOut && code === 129) return 'SIGHUP';
  return null;
}

export function killProcessTree(child, sig = 'SIGTERM') {
  if (!child || child.exitCode !== null || child.signalCode !== null) return;
  const pid = child.pid;
  if (pid && process.platform !== 'win32') {
    try { process.kill(-pid, sig); return; } catch {}
  }
  try { child.kill(sig); } catch {}
}

export function execChildAsync(command, args, opts = {}, signalCtrl = null) {
  if (signalCtrl?.signal) {
    return Promise.resolve({
      status: null,
      signal: signalCtrl.signal,
      interruptedBy: signalCtrl.signal,
      stdout: '',
      stderr: '',
      error: null,
    });
  }
  return new Promise(resolve => {
    const {
      cwd,
      env,
      shell = false,
      timeout = 0,
      maxBuffer = 16 * 1024 * 1024,
    } = opts ?? {};
    const spawnOpts = {
      cwd,
      env,
      shell,
      stdio: ['ignore', 'pipe', 'pipe'],
      detached: process.platform !== 'win32',
    };
    let child;
    try {
      child = Array.isArray(args) ? spawn(command, args, spawnOpts) : spawn(command, spawnOpts);
    } catch (err) {
      resolve({ status: null, signal: null, interruptedBy: null, stdout: '', stderr: '', error: err });
      return;
    }

    signalCtrl?.activeChildren?.add(child);
    let stdout = '';
    let stderr = '';
    let outBytes = 0;
    let errBytes = 0;
    let settled = false;
    let timedOut = false;
    let spawnError = null;
    let timeoutTimer = null;
    let killTimer = null;

    const finish = (code, sig) => {
      if (settled) return;
      settled = true;
      if (timeoutTimer) clearTimeout(timeoutTimer);
      if (killTimer) clearTimeout(killTimer);
      signalCtrl?.activeChildren?.delete(child);
      const error = timedOut
        ? Object.assign(new Error(`Command timed out after ${timeout}ms`), { code: 'ETIMEDOUT' })
        : spawnError;
      const interruptedBy = !timedOut ? (signalCtrl?.signal ?? (sig && INTERRUPT_SIGNALS.has(sig) ? sig : null)) : null;
      resolve({
        status: typeof code === 'number' ? code : null,
        signal: sig ?? null,
        interruptedBy,
        stdout,
        stderr,
        error,
      });
    };

    if (child.stdout) {
      child.stdout.on('data', chunk => {
        const buf = Buffer.isBuffer(chunk) ? chunk : Buffer.from(String(chunk));
        if (outBytes < maxBuffer) {
          const slice = buf.subarray(0, maxBuffer - outBytes);
          stdout += slice.toString('utf8');
          outBytes += slice.length;
        }
      });
    }
    if (child.stderr) {
      child.stderr.on('data', chunk => {
        const buf = Buffer.isBuffer(chunk) ? chunk : Buffer.from(String(chunk));
        if (errBytes < maxBuffer) {
          const slice = buf.subarray(0, maxBuffer - errBytes);
          stderr += slice.toString('utf8');
          errBytes += slice.length;
        }
      });
    }

    if (timeout > 0) {
      timeoutTimer = setTimeout(() => {
        timedOut = true;
        killProcessTree(child, 'SIGTERM');
        killTimer = setTimeout(() => killProcessTree(child, 'SIGKILL'), 200);
        killTimer.unref?.();
      }, timeout);
      timeoutTimer.unref?.();
    }

    child.on('error', err => {
      spawnError = err;
      finish(null, null);
    });
    child.on('close', (code, sig) => finish(code, sig));
  });
}

function prepareFormalInvocation({ root, runnerRoot = null, filePath, formalCommand, timeoutMs, env, tempDir }) {
  const scrubbedEnv = scrubChildEnv(env);
  if (nonEmpty(formalCommand)) {
    const commandDisplay = formalCommand.trim();
    const cmdEnv = { ...scrubbedEnv, CI: 'true', ...(filePath ? { PDD_FORMAL_FILE: filePath } : {}) };
    delete cmdEnv.NODE_TEST_CONTEXT;
    delete cmdEnv.NODE_OPTIONS;
    return {
      ok: true,
      runnerKind: 'formal-command',
      commandDisplay,
      junitPath: null,
      bin: commandDisplay,
      args: null,
      spawnOpts: { cwd: root, env: cmdEnv, shell: true, encoding: 'utf8', timeout: timeoutMs, maxBuffer: 16 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] },
    };
  }
  const runnerKind = chooseRunnerForFormalFile(root, filePath);
  if (!runnerKind) {
    return {
      ok: false,
      earlyResult: {
        file: filePath,
        runnerKind: null,
        command: null,
        ok: false,
        timedOut: false,
        missingRunner: true,
        exitCode: null,
        signal: null,
        interruptedBy: null,
        durationMs: 0,
        passed: 0,
        failed: 0,
        skipped: 0,
        total: 0,
        syntaxOnlyCrash: false,
        summary: `No supported test runner found for "${filePath}".`,
      },
    };
  }
  const junitPath = (runnerKind === 'pytest' || runnerKind === 'vitest') ? join(tempDir, 'junit.xml') : null;
  const pytestBin = runnerKind === 'pytest' ? resolvePytestBinary(runnerRoot ?? root) : null;
  const inv = buildRunnerInvocation(runnerKind, { root, files: [filePath], junitPath, pytestBin });
  const childEnv = buildRunnerEnv(runnerKind, root, { ...scrubbedEnv, CI: 'true' });
  delete childEnv.NODE_TEST_CONTEXT;
  delete childEnv.NODE_OPTIONS;
  return {
    ok: true,
    runnerKind,
    commandDisplay: `${inv.bin} ${inv.args.join(' ')}`,
    junitPath,
    bin: inv.bin,
    args: inv.args,
    spawnOpts: { cwd: root, env: childEnv, shell: false, encoding: 'utf8', timeout: timeoutMs, maxBuffer: 16 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] },
  };
}

function finalizeFormalRun({ proc, filePath, runnerKind, commandDisplay, junitPath, timeoutMs, started }) {
  const stdout = String(proc?.stdout ?? '');
  const stderr = String(proc?.stderr ?? '');
  const combined = `${stdout}\n${stderr}`;
  const timedOut = proc?.error?.code === 'ETIMEDOUT';
  const exitCode = typeof proc?.status === 'number' ? proc.status : null;
  const signal = proc?.signal ?? null;
  const interruptedBy = proc?.interruptedBy ?? detectSignalInterruption({ timedOut, signal, exitCode });
  const missingRunner = Boolean(
    !timedOut
    && !interruptedBy
    && (proc?.error?.code === 'ENOENT' || exitCode === 127 || (exitCode !== 0 && MISSING_RUNNER_RE.test(proc?.error?.message ?? ''))),
  );
  const parsed = parseFormalRunOutput({ kind: runnerKind === 'formal-command' ? null : runnerKind, stdout, stderr, junitPath });
  let total = parsed.ok && parsed.counts ? parsed.counts.total : 0;
  let passed = parsed.ok && parsed.counts ? parsed.counts.passed : 0;
  let failed = parsed.ok && parsed.counts ? parsed.counts.failed : 0;
  let skipped = parsed.ok && parsed.counts ? parsed.counts.skipped : 0;
  if (runnerKind === 'formal-command' && !parsed.ok) {
    if (exitCode === 0 && !proc?.error && !signal) { total = 1; passed = 1; }
    else if (!timedOut && !missingRunner && !interruptedBy) { total = 1; failed = 1; }
  }
  const hasAssertionFailure = /\b(?:AssertionError|ERR_ASSERTION|AssertionError:|assert\s+.*failed|FAILED\b.*assert)/i.test(combined);
  const syntaxOnlyCrash = exitCode !== 0 && !interruptedBy && passed === 0 && !hasAssertionFailure && SYNTAX_CRASH_RE.test(combined);
  const ok = exitCode === 0 && !proc?.error && !signal && !interruptedBy && !timedOut && !missingRunner && failed === 0 && skipped === 0 && total > 0;
  const summaryText = causeText(
    interruptedBy ? `interrupted by signal ${interruptedBy}`
      : timedOut ? `timed out after ${Math.round(timeoutMs / 1000)}s`
        : missingRunner ? (proc?.error?.message || `runner binary not found for ${runnerKind}`)
          : parsed.ok && parsed.counts ? `${passed}/${total} passed${failed ? `, ${failed} failed` : ''}${skipped ? `, ${skipped} skipped` : ''}`
            : (stderr.trim() || stdout.trim() || `exit ${exitCode ?? 'null'}`),
  );
  return {
    file: filePath ?? '<formal_command>',
    runnerKind,
    command: commandDisplay,
    ok,
    timedOut,
    missingRunner,
    exitCode,
    signal,
    interruptedBy,
    durationMs: Math.max(0, Date.now() - started),
    passed,
    failed,
    skipped,
    total,
    syntaxOnlyCrash,
    summary: summaryText,
  };
}

export function runIsolatedFormalFile({ root, runnerRoot = null, filePath, formalCommand, timeoutMs, env }, ports = {}) {
  const runner = ports.spawnSync ?? spawnSync;
  const started = Date.now();
  const tempDir = mkdtempSync(join(tmpdir(), 'pdd-formal-run-'));
  try {
    const plan = prepareFormalInvocation({ root, runnerRoot, filePath, formalCommand, timeoutMs, env, tempDir });
    if (!plan.ok) return plan.earlyResult;
    const proc = Array.isArray(plan.args)
      ? runner(plan.bin, plan.args, plan.spawnOpts)
      : runner(plan.bin, plan.spawnOpts);
    return finalizeFormalRun({ proc, filePath, runnerKind: plan.runnerKind, commandDisplay: plan.commandDisplay, junitPath: plan.junitPath, timeoutMs, started });
  } finally {
    try { rmSync(tempDir, { recursive: true, force: true }); } catch {}
  }
}

export async function runIsolatedFormalFileAsync({ root, runnerRoot = null, filePath, formalCommand, timeoutMs, env }, ports = {}, signalCtrl = null) {
  const started = Date.now();
  const tempDir = mkdtempSync(join(tmpdir(), 'pdd-formal-run-'));
  const cleanup = () => { try { rmSync(tempDir, { recursive: true, force: true }); } catch {} };
  signalCtrl?.cleanups?.add(cleanup);
  try {
    const plan = prepareFormalInvocation({ root, runnerRoot, filePath, formalCommand, timeoutMs, env, tempDir });
    if (!plan.ok) return plan.earlyResult;
    let proc;
    if (typeof ports.spawnSync === 'function') {
      proc = Array.isArray(plan.args)
        ? ports.spawnSync(plan.bin, plan.args, plan.spawnOpts)
        : ports.spawnSync(plan.bin, plan.spawnOpts);
    } else {
      proc = await execChildAsync(plan.bin, plan.args, plan.spawnOpts, signalCtrl);
    }
    return finalizeFormalRun({ proc, filePath, runnerKind: plan.runnerKind, commandDisplay: plan.commandDisplay, junitPath: plan.junitPath, timeoutMs, started });
  } finally {
    cleanup();
    signalCtrl?.cleanups?.delete(cleanup);
  }
}

function isFailingMutationControl(mc) {
  if (typeof mc === 'string') return mc.trim().toLowerCase() === 'failed-on-mutation';
  if (!isPlainObj(mc)) return false;
  return mc.executed === true && mc.failedOnMutation === true && mc.mutatedProductionCode !== false && mc.passedOnMutation !== true && mc.syntaxOnlyCrash !== true;
}

/**
 * Execute formal verification in a disposable copy of `root` with a production-code mutation
 * (never mutating the caller checkout). Verifies at least one real assertion fails (syntax-only crashes do not count).
 */
export function verifyFormalMutationControl(
  { root, targetFile, mutatedContent, formalFiles = [], baseVerify = null, timeoutMs = 60_000, env = process.env } = {},
  ports = {},
) {
  const failResult = (summary, extra = {}) => ({
    executed: false,
    failedOnMutation: false,
    syntaxOnlyCrash: false,
    mutatedProductionCode: false,
    exitCode: null,
    summary,
    ...extra,
  });

  if (!nonEmpty(root) || !canonicalRepoPath(targetFile) || !isProductionCodeFile(targetFile)) {
    return failResult(`Invalid or non-production mutation target: "${String(targetFile ?? '')}".`);
  }
  if (typeof mutatedContent !== 'string') return failResult('mutatedContent must be a string.');

  let realRoot;
  try { realRoot = realpathSync(root); } catch { return failResult('Repository root is unreadable.'); }

  // Refuse symlinked path segments and non-regular files (e.g., directories) for targetFile in root.
  const parts = targetFile.split('/');
  let cur = realRoot;
  for (let idx = 0; idx < parts.length; idx += 1) {
    cur = join(cur, parts[idx]);
    try {
      const st = lstatSync(cur);
      if (st.isSymbolicLink()) return failResult(`Refused symlinked mutation target: "${targetFile}".`);
      if (idx === parts.length - 1 && !st.isFile()) return failResult(`Mutation target "${targetFile}" is not a regular file.`);
    } catch {
      return failResult(`Mutation target "${targetFile}" does not exist in repository.`);
    }
  }

  const tempDir = mkdtempSync(join(tmpdir(), 'pdd-formal-mut-'));
  const workDir = join(tempDir, 'work');
  try {
    mkdirSync(workDir, { mode: 0o700 });
    cpSync(realRoot, workDir, {
      recursive: true,
      dereference: false,
      verbatimSymlinks: true,
      filter: src => {
        const rel = relative(realRoot, src).split(sep).join('/');
        if (rel === '.git' || rel.startsWith('.git/')) return false;
        if (rel === 'node_modules' || rel.startsWith('node_modules/')) return false;
        if (rel === '.venv' || rel.startsWith('.venv/') || rel === 'venv' || rel.startsWith('venv/')) return false;
        const segments = rel.split('/');
        if (segments.some(seg => seg === '__pycache__' || seg === '.pytest_cache' || seg === '.mypy_cache' || seg === '.ruff_cache')) return false;
        if (/\.py[co]$/i.test(rel)) return false;
        return true;
      },
    });
    const nodeModulesSrc = join(realRoot, 'node_modules');
    try {
      const st = lstatSync(nodeModulesSrc);
      if (st.isDirectory() && !st.isSymbolicLink() && !existsSync(join(workDir, 'node_modules'))) {
        symlinkSync(nodeModulesSrc, join(workDir, 'node_modules'), 'dir');
      }
    } catch {}
    const targetFull = join(workDir, targetFile);
    const targetRealDir = realpathSync(dirname(targetFull));
    const realWork = realpathSync(workDir);
    if (targetRealDir !== realWork && !targetRealDir.startsWith(`${realWork}${sep}`)) {
      return failResult(`Refused escaping mutation path: "${targetFile}".`);
    }
    writeFileSync(targetFull, mutatedContent, 'utf8');

    const filesToRun = Array.isArray(formalFiles) && formalFiles.length > 0
      ? formalFiles.filter(canonicalRepoPath)
      : discoverFormalScope({ root: workDir, touchedFiles: [targetFile], formalCommand: baseVerify?.formalCommand ?? null }).formalFiles;
    const formalCommand = nonEmpty(baseVerify?.formalCommand) ? baseVerify.formalCommand.trim() : null;
    if (filesToRun.length === 0 && !formalCommand) {
      return failResult('No formal test files or formal_command available to verify mutation control.');
    }

    const runs = filesToRun.length > 0
      ? filesToRun.map(f => runIsolatedFormalFile({ root: workDir, runnerRoot: realRoot, filePath: f, formalCommand, timeoutMs, env }, ports))
      : [runIsolatedFormalFile({ root: workDir, runnerRoot: realRoot, filePath: null, formalCommand, timeoutMs, env }, ports)];

    const timedOut = runs.some(r => r.timedOut);
    const missingRunner = runs.some(r => r.missingRunner);
    if (timedOut || missingRunner) {
      return failResult(timedOut ? 'Formal mutation control timed out.' : 'Formal runner unavailable during mutation control.', { executed: false });
    }
    const syntaxOnly = runs.some(r => r.syntaxOnlyCrash) && !runs.some(r => !r.syntaxOnlyCrash && r.failed > 0);
    const realFail = runs.find(r => !r.ok && !r.syntaxOnlyCrash && (r.failed > 0 || (r.exitCode !== 0 && r.total > 0) || (r.runnerKind === 'formal-command' && r.exitCode !== 0)));
    const firstNonZero = runs.find(r => r.exitCode !== 0);
    return {
      executed: true,
      failedOnMutation: Boolean(realFail && !syntaxOnly),
      syntaxOnlyCrash: syntaxOnly,
      mutatedProductionCode: true,
      exitCode: (realFail ?? firstNonZero ?? runs[0])?.exitCode ?? 0,
      summary: realFail
        ? `Mutation control killed: ${realFail.file} failed on mutated ${targetFile} (${realFail.summary}).`
        : (syntaxOnly ? `Mutation control invalid: syntax-only crash on mutated ${targetFile}.` : `Mutation control survived: formal suite still passed on mutated ${targetFile}.`),
    };
  } finally {
    try { rmSync(tempDir, { recursive: true, force: true }); } catch {}
  }
}

function prepareFormalVerificationContext({
  root,
  touchedFiles = [],
  allFiles = null,
  baseVerify = null,
  claimedTier = null,
  mutationControl = null,
  targetModules = null,
}) {
  const formalCommand = nonEmpty(baseVerify?.formalCommand) ? baseVerify.formalCommand.trim() : null;
  const scope = discoverFormalScope({ root, touchedFiles, allFiles, formalCommand });
  const effectiveTargets = Array.isArray(targetModules) && targetModules.length > 0
    ? [...new Set(targetModules.filter(isProductionCodeFile))].sort()
    : scope.touchedProdFiles;
  const normClaim = typeof claimedTier === 'string' ? claimedTier.trim().toLowerCase() : null;
  const claimedPositiveCode = normClaim === 'proved_solver_code' || normClaim === 'proved';

  if (!scope.applicable) {
    if (claimedPositiveCode) {
      const msg = formatTeachingDetail({
        invariant: `Claimed formal=${normClaim} with zero changed or verified formal test files`,
        fix: 'Add a code-bound formal test importing production code, or report formal=not-applicable',
        rerun: 'pdd prove',
      });
      return {
        earlyResult: {
          applicable: true,
          ok: false,
          state: 'failed',
          tier: 'failed',
          satisfiesCodeVerification: false,
          files: [],
          formalProofs: [],
          targetModules: effectiveTargets,
          invariantRules: [],
          mutationControl: null,
          errors: [`Error: formal verification: [formal-empty-claim] ${msg}`],
          notProvedReasons: [],
          advisory: null,
          summary: `Formal: failed (claimed ${normClaim} with 0 formal test files)`,
        },
      };
    }
    return {
      earlyResult: {
        applicable: false,
        ok: true,
        state: 'not-applicable',
        tier: 'not-applicable',
        satisfiesCodeVerification: true,
        files: [],
        formalProofs: [],
        targetModules: effectiveTargets,
        invariantRules: [],
        mutationControl: null,
        errors: [],
        notProvedReasons: [],
        advisory: null,
        summary: 'Formal: not-applicable',
      },
    };
  }

  if (scope.formalFiles.length === 0 && !formalCommand) {
    if (claimedPositiveCode) {
      const msg = formatTeachingDetail({
        invariant: `Claimed formal=${normClaim} with zero formal test files`,
        fix: 'Add a code-bound formal/property test (e.g., seeded PRNG or finite grid) importing the production module',
        rerun: 'pdd prove',
      });
      return {
        earlyResult: {
          applicable: true,
          ok: false,
          state: 'failed',
          tier: 'failed',
          satisfiesCodeVerification: false,
          files: [],
          formalProofs: [],
          targetModules: effectiveTargets,
          invariantRules: scope.invariantRules,
          mutationControl: null,
          errors: [`Error: formal verification: [formal-empty-claim] ${msg}`],
          notProvedReasons: [],
          advisory: null,
          summary: `Formal: failed (claimed ${normClaim} with 0 formal test files)`,
        },
      };
    }
    const sourcesLabel = scope.invariantSources.slice(0, 3).join(', ');
    const advisory = `Formal: missing (advisory: ${scope.invariantRules.length} invariant rule(s) in ${sourcesLabel}; add a zero-install code-bound formal/property test or confirm not-applicable)`;
    return {
      earlyResult: {
        applicable: true,
        ok: true,
        state: 'missing',
        tier: 'missing',
        satisfiesCodeVerification: false,
        files: [],
        formalProofs: [],
        targetModules: effectiveTargets,
        invariantRules: scope.invariantRules,
        mutationControl: null,
        errors: [],
        notProvedReasons: [],
        advisory,
        summary: advisory,
      },
    };
  }

  return {
    earlyResult: null,
    realRoot: realpathSync(root),
    formalCommand,
    scope,
    effectiveTargets,
    normClaim,
    claimedPositiveCode,
    effectiveMutationControl: mutationControl ?? null,
    mutationControlPassed: isFailingMutationControl(mutationControl ?? null),
    filesToRun: scope.formalFiles.length > 0 ? scope.formalFiles : [null],
  };
}

function finalizeFormalVerification(ctx, runsWithFiles) {
  const {
    realRoot,
    formalCommand,
    scope,
    effectiveTargets,
    normClaim,
    claimedPositiveCode,
    effectiveMutationControl,
    mutationControlPassed,
  } = ctx;
  const fileResults = [];
  const formalProofs = [];
  const errors = [];
  const notProvedReasons = [];

  for (const { filePath, run } of runsWithFiles) {
    const binding = filePath
      ? inspectFormalFileBinding({ root: realRoot, filePath, targetModules: effectiveTargets, allRepoFiles: scope.allRepoFiles })
      : {
          file: '<formal_command>',
          language: 'other',
          importedProductionModules: effectiveTargets,
          coversTargets: effectiveTargets.length > 0,
          codeBound: effectiveTargets.length > 0,
          hasSolverImport: SOLVER_COMMAND_RE.test(formalCommand ?? ''),
          hasCodeBoundSolver: SOLVER_COMMAND_RE.test(formalCommand ?? ''),
          hasPropertyTesting: false,
          isStandaloneZ3: false,
          tier: effectiveTargets.length > 0 ? 'bounded' : 'proved_spec_model',
          satisfiesCodeVerification: effectiveTargets.length > 0,
          reason: `Executed merge-base verify.formal_command (${formalCommand}).`,
        };

    const hasSolverEvidence = binding.hasCodeBoundSolver || (Boolean(formalCommand) && SOLVER_COMMAND_RE.test(formalCommand));
    let fileTier = 'failed';
    if (run.ok) {
      if (!binding.codeBound) fileTier = 'proved_spec_model';
      else if (hasSolverEvidence && mutationControlPassed && binding.coversTargets) fileTier = 'proved_solver_code';
      else fileTier = 'bounded';
    }

    fileResults.push({
      file: run.file,
      runnerKind: run.runnerKind,
      command: run.command,
      ok: run.ok,
      timedOut: run.timedOut,
      missingRunner: run.missingRunner,
      exitCode: run.exitCode,
      durationMs: run.durationMs,
      passed: run.passed,
      failed: run.failed,
      skipped: run.skipped,
      total: run.total,
      summary: run.summary,
      language: binding.language,
      codeBound: binding.codeBound,
      importedProductionModules: binding.importedProductionModules,
      hasCodeBoundSolver: hasSolverEvidence,
      hasPropertyTesting: binding.hasPropertyTesting,
      isStandaloneZ3: binding.isStandaloneZ3,
      tier: fileTier,
    });

    formalProofs.push({
      id: run.file,
      file: run.file,
      tier: fileTier === 'proved_solver_code'
        ? 'proved_solver_code'
        : (claimedPositiveCode && !binding.codeBound ? 'proved_solver_code' : fileTier),
      codeBound: binding.codeBound,
      importedProductionModules: binding.importedProductionModules,
      executedProductionModules: run.ok ? binding.importedProductionModules : [],
      targetModules: effectiveTargets,
      mutationControl: effectiveMutationControl,
      satisfiesCode: claimedPositiveCode || fileTier === 'proved_solver_code',
      forCodeVerification: claimedPositiveCode || fileTier === 'proved_solver_code',
      passed: run.passed,
      total: run.total,
      skipped: run.skipped,
    });

    if (run.interruptedBy) {
      notProvedReasons.push(`Formal verification of "${run.file}" was interrupted by signal ${run.interruptedBy}.`);
    } else if (run.timedOut) {
      notProvedReasons.push(`Formal verification of "${run.file}" timed out (${run.summary}); rerun with --timeout MIN.`);
    } else if (run.missingRunner) {
      notProvedReasons.push(`Formal verification of "${run.file}" could not run: ${run.summary}.`);
    } else if (!run.ok) {
      if (run.skipped > 0 && run.failed === 0 && run.exitCode === 0) {
        errors.push(`Error: formal verification: ${run.file}:1 [formal-skipped-tests] ${run.skipped} skipped test(s) in formal file "${run.file}" (skipped tests never satisfy formal verification).`);
      } else if (run.total === 0 && run.exitCode === 0) {
        errors.push(`Error: formal verification: ${run.file}:1 [formal-zero-tests] Formal file "${run.file}" exited 0 with 0 executed tests.`);
      } else {
        errors.push(`Error: formal verification: ${run.file}:1 [formal-test-failed] Formal verification failed (${run.summary}).`);
      }
    } else if (!binding.codeBound) {
      const detail = formatTeachingDetail({
        invariant: binding.reason,
        fix: `Import and execute the real production module (${effectiveTargets.slice(0, 3).join(', ') || 'src/...'}) inside "${run.file}" instead of verifying a standalone spec model`,
        rerun: 'pdd prove',
      });
      notProvedReasons.push(`${run.file}:1 [formal-spec-model-only] ${detail}`);
      if (claimedPositiveCode) {
        errors.push(`Error: formal verification: ${run.file}:1 [formal-spec-model-refused] Refused formal=${normClaim} claim: ${binding.reason}`);
      }
    }
  }

  const totalPassed = fileResults.reduce((sum, f) => sum + f.passed, 0);
  const allOk = fileResults.every(f => f.ok);
  const anyUnbound = fileResults.some(f => f.ok && !f.codeBound);
  const allSolverBound = allOk && fileResults.length > 0 && fileResults.every(f => f.tier === 'proved_solver_code');

  let state, tier, satisfiesCodeVerification, summary;
  if (errors.length > 0 || !allOk) {
    const onlyNotProved = errors.length === 0 && notProvedReasons.length > 0;
    state = onlyNotProved ? 'not-run' : 'failed';
    tier = onlyNotProved ? 'not-run' : 'failed';
    satisfiesCodeVerification = false;
    summary = onlyNotProved
      ? `Formal: not proved (${notProvedReasons[0]})`
      : `Formal: failed (${fileResults.filter(f => !f.ok).map(f => f.file).join(', ') || errors[0]})`;
  } else if (anyUnbound) {
    state = 'proved_spec_model';
    tier = 'proved_spec_model';
    satisfiesCodeVerification = false;
    summary = `Formal: proved_spec_model (${totalPassed} passed, not code-bound)`;
  } else if (allSolverBound) {
    state = 'proved_solver_code';
    tier = 'proved_solver_code';
    satisfiesCodeVerification = true;
    summary = `Formal: proved_solver_code (${totalPassed} passed, code-bound)`;
  } else {
    state = 'bounded';
    tier = 'bounded';
    satisfiesCodeVerification = true;
    if (normClaim === 'proved_solver_code') {
      notProvedReasons.push('Formal claimed proved_solver_code without verified code-bound solver + failing production-code mutation control; classified as bounded.');
    }
    summary = `Formal: bounded (${totalPassed} passed, code-bound)`;
  }

  return {
    applicable: true,
    ok: errors.length === 0 && notProvedReasons.length === 0,
    state,
    tier,
    satisfiesCodeVerification,
    files: fileResults,
    formalProofs,
    targetModules: effectiveTargets,
    invariantRules: scope.invariantRules,
    mutationControl: effectiveMutationControl,
    errors,
    notProvedReasons,
    advisory: null,
    summary,
  };
}

/**
 * Shared Layer-1 code-bound formal verification orchestrator consumed by BOTH `pdd prove`
 * and Autopilot `collectLiveEvidenceContract`.
 */
export function runFormalVerification(opts = {}, ports = {}) {
  const ctx = prepareFormalVerificationContext(opts);
  if (ctx.earlyResult) return ctx.earlyResult;
  const timeoutMs = opts.timeoutMs ?? 120_000;
  const env = opts.env ?? process.env;
  const runsWithFiles = [];
  for (const filePath of ctx.filesToRun) {
    const run = runIsolatedFormalFile({ root: ctx.realRoot, filePath, formalCommand: ctx.formalCommand, timeoutMs, env }, ports);
    runsWithFiles.push({ filePath, run });
    if (run.interruptedBy) break;
  }
  return finalizeFormalVerification(ctx, runsWithFiles);
}

export async function runFormalVerificationAsync(opts = {}, ports = {}, signalCtrl = null) {
  const ctx = prepareFormalVerificationContext(opts);
  if (ctx.earlyResult) return ctx.earlyResult;
  const timeoutMs = opts.timeoutMs ?? 120_000;
  const env = opts.env ?? process.env;
  const runsWithFiles = [];
  for (const filePath of ctx.filesToRun) {
    if (signalCtrl?.signal) break;
    const run = await runIsolatedFormalFileAsync({ root: ctx.realRoot, filePath, formalCommand: ctx.formalCommand, timeoutMs, env }, ports, signalCtrl);
    runsWithFiles.push({ filePath, run });
    if (signalCtrl?.signal || run.interruptedBy) break;
  }
  return finalizeFormalVerification(ctx, runsWithFiles);
}
