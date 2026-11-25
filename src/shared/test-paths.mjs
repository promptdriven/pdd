// Single source of truth for test-directory and test-file path classification across Core and Autopilot.
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { join, posix } from 'node:path';
import { parse as parseToml } from './toml/parse.js';

export const SCENARIO_DIR_PATTERN = 'tests?|__tests__';
export const TEST_DIR_PATTERN = 'tests?(?:[_-][a-z0-9]+)?|__tests__';
export const TEST_DIR_WITH_SPEC_PATTERN = `${TEST_DIR_PATTERN}|spec`;
export const TEST_DIR_NAMES = Object.freeze(['test', 'tests', '__tests__', 'tests_py']);
export const TEST_DIR_WITH_SPEC_NAMES = Object.freeze(['test', 'tests', '__tests__', 'tests_py', 'spec']);

export const TEST_DIR_PREFIX_RE = new RegExp(`^(?:${TEST_DIR_PATTERN})/`, 'i');
export const TEST_DIR_SEGMENT_RE = new RegExp(`(?:^|/)(?:${TEST_DIR_PATTERN})/`, 'i');
export const TEST_DIR_WITH_SPEC_PREFIX_RE = new RegExp(`^(?:${TEST_DIR_WITH_SPEC_PATTERN})/`, 'i');
export const TEST_DIR_WITH_SPEC_SEGMENT_RE = new RegExp(`(?:^|/)(?:${TEST_DIR_WITH_SPEC_PATTERN})/`, 'i');
export const TEST_FILENAME_RE = /(?:^|\/)(?:[^/]+\.(?:test|spec)\.[^/]+|test_[^/]+\.[^/]+|[^/]+_test\.[^/]+)$/i;
export const PYTEST_FILENAME_RE = /(?:^|\/)(?:test_[^/]+\.py|[^/]+_test\.py)$/i;
export const TEST_TARGET_FILE_RE = /(?:\.(?:test|spec)\.[a-z0-9]+$|_test\.(?:py|go|rs)$|(?:^|\/)test_[^/]+\.py$)/i;
export const TEST_FILE_PATH_RE = new RegExp(`(?:(?:^|/)(?:${TEST_DIR_WITH_SPEC_PATTERN})/|\\.(?:test|spec)\\.[a-z0-9]+$|_test\\.(?:go|rs|py)$|(?:^|/)test_[^/]+\\.py$)`, 'i');
export const TEST_SCENARIO_JSON_RE = new RegExp(`(?:^|/)(?:${SCENARIO_DIR_PATTERN})/.*\\.json$`, 'i');
export const ROOT_TEST_SCENARIO_JSON_RE = new RegExp(`^(?:${SCENARIO_DIR_PATTERN})/.*\\.json$`, 'i');
export const COLOCATED_TEST_PATH_RE = new RegExp(`(?:\\.(?:test|spec)\\.(?:[cm]?[jt]s|[jt]sx)|(?:^|/)test_[^/]+\\.py$|_test\\.(?:py|go|rs)$|^(?:${TEST_DIR_PATTERN}|fixtures)/)`, 'i');
export const NON_PRODUCTION_DIR_RE = new RegExp(`^(?:${TEST_DIR_WITH_SPEC_PATTERN}|fixtures|examples|prompts|user_stories|docs)/`, 'i');
export const TEST_PLACE_RE = new RegExp(`(?:^|/)(?:${TEST_DIR_WITH_SPEC_PATTERN}|fixtures)/|\\.(?:test|spec)\\.[^/]+$|_test\\.(?:py|go|rs)$|(?:^|/)test_[^/]+\\.py$`, 'i');
export const VALIDATOR_TEST_FILE_RE = new RegExp(`(?:(?:^|/)(?:${TEST_DIR_WITH_SPEC_PATTERN})/|\\.(?:test|spec)\\.[a-z0-9]+$)`, 'i');
export const TEST_HELPER_SUBDIR_RE = new RegExp(`^(?:${TEST_DIR_PATTERN})/(?:helpers|fixtures)(?:/|$)`, 'i');
export const TEST_SETUP_FILE_RE = new RegExp(`^(?:${TEST_DIR_PATTERN})/(?:setup|preload|register|global-setup)\\.[^/]+$`, 'i');

const TEST_DIR_NAME_RE = new RegExp(`^(?:${TEST_DIR_PATTERN})$`, 'i');
const TEST_SPEC_PATH_RE = new RegExp(`(?:^|/|\\\\)(?:${TEST_DIR_WITH_SPEC_PATTERN})/|\\.(?:test|spec)\\.[^/]+$`, 'i');
const TEST_ANNOTATION_PATH_RE = new RegExp(`(?:^|/)(?:${TEST_DIR_WITH_SPEC_PATTERN})/|\\.(?:test|spec)\\.[A-Za-z0-9]+$`);
const TEST_PROMPT_PREFIX_RE = new RegExp(`(?:^|/)prompts/(?:${TEST_DIR_PATTERN})/|/(?:[^/]+\\.(?:test|spec)\\.prompt\\.md)$|^(?:[^/]+\\.(?:test|spec)\\.prompt\\.md)$`, 'i');
const TEST_FIXTURES_SUBDIR_RE = new RegExp(`(?:^|/)(?:${TEST_DIR_PATTERN})/fixtures/`, 'i');
const TOP_HELPER_RE = /^(?:fixtures|helpers|harbor|conftest|[^/]*harness)(?:\/|$)/i;
const DEV_TOOL_KEYS = new Set(['ruff', 'mypy', 'coverage', 'flake8', 'black', 'isort', 'pylint', 'pyright', 'ty']);

export const isTestDirSegment = seg => typeof seg === 'string' && TEST_DIR_NAME_RE.test(seg);
export const hasTestDirSegment = path => typeof path === 'string' && path.split('/').some(isTestDirSegment);
export const isTestOwnedPathMatch = path => TEST_DIR_SEGMENT_RE.test(path) || TEST_FILENAME_RE.test(path);
export const isTestPromptPathMatch = path =>
  TEST_PROMPT_PREFIX_RE.test(path) || (TEST_DIR_SEGMENT_RE.test(path) && !TEST_FIXTURES_SUBDIR_RE.test(path));
export const isTestSpecPath = path => TEST_SPEC_PATH_RE.test(String(path ?? ''));
export const isTestAnnotationPath = path => typeof path === 'string' && TEST_ANNOTATION_PATH_RE.test(path);
export const isJsTestPath = path => {
  if (typeof path !== 'string' || !path) return false;
  const parts = path.split('/');
  const base = parts.at(-1) ?? '';
  return /\.(?:[cm]?[jt]s|[jt]sx)$/.test(base) && (/\.(?:test|spec)\./.test(base) || parts.some(isTestDirSegment));
};
export const stripLeadingTestDir = path => String(path ?? '').replace(TEST_DIR_WITH_SPEC_PREFIX_RE, '');

const normDir = raw => {
  const s = String(raw ?? '').trim().replace(/\\/g, '/').replace(/^\.\//, '').replace(/\/+$/, '');
  return s && !s.startsWith('/') && !s.split('/').includes('..') ? s : '';
};

function readConfigText(root, rel, gitRef = null) {
  if (gitRef) {
    const res = spawnSync('git', ['show', `${gitRef}:${rel}`], { cwd: root, encoding: 'utf8', maxBuffer: 2 * 1024 * 1024, stdio: ['ignore', 'pipe', 'ignore'] });
    return res.status === 0 && typeof res.stdout === 'string' ? res.stdout : null;
  }
  try { return readFileSync(join(root, rel), 'utf8'); } catch { return null; }
}

function parseIniSection(text, allowedSections) {
  const entries = {};
  let section = '', activeKey = null;
  for (const rawLine of String(text ?? '').split(/\r?\n/)) {
    const stripped = rawLine.replace(/^\s*(?:#|;).*$/, '');
    const secMatch = /^\s*\[([^\]]+)\]\s*$/.exec(stripped);
    if (secMatch) { section = secMatch[1].trim().toLowerCase(); activeKey = null; continue; }
    if (!allowedSections.has(section)) continue;
    if (activeKey && /^[ \t]+\S/.test(rawLine)) {
      const val = rawLine.replace(/\s+[#;].*$/, '').trim();
      if (val) entries[activeKey] = `${entries[activeKey]}\n${val}`;
      continue;
    }
    const kv = /^\s*([A-Za-z0-9_.-]+)\s*[=:]\s*(.*)$/.exec(stripped);
    if (kv) {
      activeKey = kv[1].trim().toLowerCase();
      entries[activeKey] = kv[2].replace(/\s+[#;].*$/, '').trim();
    } else if (stripped.trim()) {
      activeKey = null;
    }
  }
  return entries;
}

const parseTomlSafe = raw => parseToml(raw, { integersAsBigInt: true });

export function readPytestTestpaths(root, { gitRef = null } = {}) {
  if (typeof root !== 'string' || !root) return [];
  const dirs = new Set();
  const add = items => { for (const x of items) { const d = normDir(x); if (d) dirs.add(d); } };
  const pyRaw = readConfigText(root, 'pyproject.toml', gitRef);
  if (pyRaw) {
    try {
      const parsed = parseTomlSafe(pyRaw);
      const tp = parsed?.tool?.pytest?.ini_options?.testpaths ?? parsed?.tool?.pytest?.testpaths;
      add(Array.isArray(tp) ? tp : typeof tp === 'string' ? tp.split(/[\s,]+/) : []);
    } catch {}
  }
  const iniFiles = [
    ['pytest.ini', new Set(['pytest'])],
    ['setup.cfg', new Set(['tool:pytest', 'pytest'])],
  ];
  for (const [ini, sections] of iniFiles) {
    const raw = readConfigText(root, ini, gitRef);
    if (!raw) continue;
    const tp = parseIniSection(raw, sections).testpaths;
    if (tp) add(tp.split(/[\s,]+/));
  }
  return [...dirs];
}

export const isConfiguredTestPath = (filePath, testpaths = []) =>
  typeof filePath === 'string' && Array.isArray(testpaths) && testpaths.some(dir => filePath === dir || filePath.startsWith(`${dir}/`));

export function isTestHelperSpecifier(spec, fromRelPath = '', testpaths = [], repoFiles = null) {
  const raw = String(spec ?? '').trim();
  if (!raw) return false;
  if (raw.startsWith('./') || raw.startsWith('../')) {
    const resolved = posix.normalize(posix.join(posix.dirname(String(fromRelPath || '').replace(/\\/g, '/')), raw.replace(/\\/g, '/'))).replace(/^\.\//, '');
    return Boolean(resolved && !resolved.startsWith('..'))
      && (isTestDirSegment(resolved.split('/')[0]) || hasTestDirSegment(resolved) || TOP_HELPER_RE.test(resolved) || isConfiguredTestPath(resolved, testpaths));
  }
  const dots = /^\.+/.exec(raw)?.[0].length ?? 0;
  const clean = raw.slice(dots).replace(/\\/g, '/').replace(/\./g, '/');
  if (!clean) return false;
  if (dots > 0) {
    if (isTestDirSegment(clean.split('/')[0]) || TOP_HELPER_RE.test(clean)) return true;
    if (fromRelPath && repoFiles instanceof Set) {
      let base = posix.dirname(String(fromRelPath).replace(/\\/g, '/'));
      for (let i = 1; i < dots; i++) base = posix.dirname(base);
      const resolved = posix.normalize(posix.join(base === '.' ? '' : base, clean)).replace(/^\.\//, '');
      const inTest = Boolean(resolved && !resolved.startsWith('..'))
        && (isTestDirSegment(resolved.split('/')[0]) || hasTestDirSegment(resolved) || isConfiguredTestPath(resolved, testpaths));
      if (inTest && (repoFiles.has(`${resolved}.py`) || repoFiles.has(`${resolved}/__init__.py`))) return true;
    }
    return false;
  }
  return isTestDirSegment(clean.split('/')[0]) || TOP_HELPER_RE.test(clean) || isConfiguredTestPath(clean, testpaths);
}

const canonicalSort = v => {
  if (v instanceof Date) return { __tomlDate: v.toISOString() };
  if (typeof v === 'bigint') return { __tomlBigInt: v.toString() };
  if (Array.isArray(v)) return v.map(canonicalSort);
  if (v && typeof v === 'object') return Object.fromEntries(Object.keys(v).sort().map(k => [k, canonicalSort(v[k])]));
  return v;
};

function stripNonProductionPyproject(doc) {
  const out = {};
  for (const [k, v] of Object.entries(doc ?? {})) {
    if (k === 'dependency-groups') continue;
    if (k === 'tool' && v && typeof v === 'object' && !Array.isArray(v)) {
      const kept = Object.fromEntries(Object.entries(v).filter(([tk]) => !DEV_TOOL_KEYS.has(tk.toLowerCase())));
      if (Object.keys(kept).length) out.tool = kept;
    } else if (k === 'project' && v && typeof v === 'object' && !Array.isArray(v)) {
      const proj = { ...v };
      if (proj['optional-dependencies'] && typeof proj['optional-dependencies'] === 'object') {
        const opt = Object.fromEntries(Object.entries(proj['optional-dependencies']).filter(([ok]) => !/^(?:dev|test|tests|lint)$/i.test(ok)));
        if (Object.keys(opt).length) proj['optional-dependencies'] = opt; else delete proj['optional-dependencies'];
      }
      if (Object.keys(proj).length) out.project = proj;
    } else out[k] = v;
  }
  return canonicalSort(out);
}

export function isNonProductionPyprojectEdit(baseRaw, headRaw) {
  if (typeof headRaw !== 'string' || !headRaw.trim()) return false;
  try {
    const headProd = stripNonProductionPyproject(parseTomlSafe(headRaw));
    const baseProd = typeof baseRaw === 'string' && baseRaw.trim() ? stripNonProductionPyproject(parseTomlSafe(baseRaw)) : {};
    return JSON.stringify(baseProd) === JSON.stringify(headProd);
  } catch { return false; }
}

export function detectPytestConfigEdits(root, baseSha, touchedFiles = []) {
  if (!root || !baseSha || !Array.isArray(touchedFiles) || !touchedFiles.length) return [];
  const touched = new Set(touchedFiles);
  const changed = [];
  if (touched.has('pyproject.toml')) {
    const bRaw = readConfigText(root, 'pyproject.toml', baseSha);
    const wRaw = readConfigText(root, 'pyproject.toml', null);
    try {
      const bPt = bRaw ? canonicalSort(parseTomlSafe(bRaw)?.tool?.pytest ?? null) : null;
      const wPt = wRaw ? canonicalSort(parseTomlSafe(wRaw)?.tool?.pytest ?? null) : null;
      if (JSON.stringify(bPt) !== JSON.stringify(wPt)) changed.push('pyproject.toml:[tool.pytest]');
    } catch { changed.push('pyproject.toml'); }
  }
  if (touched.has('pytest.ini')) {
    if (readConfigText(root, 'pytest.ini', baseSha) !== readConfigText(root, 'pytest.ini', null)) changed.push('pytest.ini');
  }
  if (touched.has('setup.cfg')) {
    const sections = new Set(['tool:pytest', 'pytest']);
    const bSec = canonicalSort(parseIniSection(readConfigText(root, 'setup.cfg', baseSha) ?? '', sections));
    const wSec = canonicalSort(parseIniSection(readConfigText(root, 'setup.cfg', null) ?? '', sections));
    if (JSON.stringify(bSec) !== JSON.stringify(wSec)) changed.push('setup.cfg:[tool:pytest]');
  }
  return changed;
}
