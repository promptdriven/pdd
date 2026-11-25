// Single source of truth for test-directory and test-file path classification across Core and Autopilot.

export const TEST_DIR_PATTERN = 'tests?|__tests__';
export const TEST_DIR_WITH_SPEC_PATTERN = `${TEST_DIR_PATTERN}|spec`;
export const TEST_DIR_NAMES = Object.freeze(['test', 'tests', '__tests__']);
export const TEST_DIR_WITH_SPEC_NAMES = Object.freeze(['test', 'tests', '__tests__', 'spec']);

export const TEST_DIR_PREFIX_RE = new RegExp(`^(?:${TEST_DIR_PATTERN})/`, 'i');
export const TEST_DIR_SEGMENT_RE = new RegExp(`(?:^|/)(?:${TEST_DIR_PATTERN})/`, 'i');
export const TEST_DIR_WITH_SPEC_PREFIX_RE = new RegExp(`^(?:${TEST_DIR_WITH_SPEC_PATTERN})/`, 'i');
export const TEST_DIR_WITH_SPEC_SEGMENT_RE = new RegExp(`(?:^|/)(?:${TEST_DIR_WITH_SPEC_PATTERN})/`, 'i');
export const TEST_FILENAME_RE = /(?:^|\/)(?:[^/]+\.(?:test|spec)\.[^/]+|test_[^/]+\.[^/]+|[^/]+_test\.[^/]+)$/i;
export const PYTEST_FILENAME_RE = /(?:^|\/)(?:test_[^/]+\.py|[^/]+_test\.py)$/i;
export const TEST_TARGET_FILE_RE = /(?:\.(?:test|spec)\.[a-z0-9]+$|_test\.(?:py|go|rs)$|(?:^|\/)test_[^/]+\.py$)/i;
export const TEST_FILE_PATH_RE = new RegExp(`(?:(?:^|/)(?:${TEST_DIR_WITH_SPEC_PATTERN})/|\\.(?:test|spec)\\.[a-z0-9]+$|_test\\.(?:go|rs|py)$|(?:^|/)test_[^/]+\\.py$)`, 'i');
export const TEST_SCENARIO_JSON_RE = new RegExp(`(?:^|/)(?:${TEST_DIR_PATTERN})/.*\\.json$`, 'i');
export const ROOT_TEST_SCENARIO_JSON_RE = new RegExp(`^(?:${TEST_DIR_PATTERN})/.*\\.json$`, 'i');
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
