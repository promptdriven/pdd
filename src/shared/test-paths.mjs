// Single source of truth for test-directory and test-file path classification across Core and Autopilot.
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
const HELPER_DIR_RE = /(?:^|\/)(?:fixtures|helpers|harbor|conftest|[^/]*harness)(?:\/|$)/i;
const DEV_TOOL_KEYS = new Set(['pytest', 'ruff', 'mypy', 'coverage', 'flake8', 'black', 'isort', 'pylint', 'pyright', 'ty']);

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

export function readPytestTestpaths(root) {
  if (typeof root !== 'string' || !root) return [];
  const dirs = new Set();
  const add = items => { for (const x of items) { const d = normDir(x); if (d) dirs.add(d); } };
  try {
    const tp = parseToml(readFileSync(join(root, 'pyproject.toml'), 'utf8'))?.tool?.pytest?.ini_options?.testpaths;
    add(Array.isArray(tp) ? tp : typeof tp === 'string' ? tp.split(/[\s,]+/) : []);
  } catch {}
  for (const ini of ['pytest.ini', 'setup.cfg']) {
    try { const m = /^\s*testpaths\s*=\s*([^\r\n#]+)/m.exec(readFileSync(join(root, ini), 'utf8')); if (m) add(m[1].split(/[\s,]+/)); } catch {}
  }
  return [...dirs];
}

export const isConfiguredTestPath = (filePath, testpaths = []) =>
  typeof filePath === 'string' && Array.isArray(testpaths) && testpaths.some(dir => filePath === dir || filePath.startsWith(`${dir}/`));

export function isTestHelperSpecifier(spec, fromRelPath = '', testpaths = []) {
  const raw = String(spec ?? '').trim();
  if (!raw) return false;
  if (raw.startsWith('./') || raw.startsWith('../')) {
    const resolved = posix.normalize(posix.join(posix.dirname(String(fromRelPath || '').replace(/\\/g, '/')), raw.replace(/\\/g, '/'))).replace(/^\.\//, '');
    return Boolean(resolved && !resolved.startsWith('..')) && (isTestDirSegment(resolved.split('/')[0]) || HELPER_DIR_RE.test(resolved) || isConfiguredTestPath(resolved, testpaths));
  }
  const clean = raw.replace(/^\.+/, '').replace(/\\/g, '/').replace(/\./g, '/');
  if (!clean) return false;
  if (raw.startsWith('.')) return isTestDirSegment(clean.split('/')[0]) || HELPER_DIR_RE.test(clean);
  return isTestDirSegment(clean.split('/')[0]) || HELPER_DIR_RE.test(clean) || isConfiguredTestPath(clean, testpaths);
}

const canonicalSort = v => Array.isArray(v)
  ? v.map(canonicalSort)
  : (v && typeof v === 'object' ? Object.fromEntries(Object.keys(v).sort().map(k => [k, canonicalSort(v[k])])) : v);

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
    const headProd = stripNonProductionPyproject(parseToml(headRaw));
    const baseProd = typeof baseRaw === 'string' && baseRaw.trim() ? stripNonProductionPyproject(parseToml(baseRaw)) : {};
    return JSON.stringify(baseProd) === JSON.stringify(headProd);
  } catch { return false; }
}
