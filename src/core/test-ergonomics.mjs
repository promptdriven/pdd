// Prompt: prompts/cli/test-ergonomics.prompt.md

export const AUTO_RECONCILE_DEFAULT_TIMEOUT_MS = 10_000;
export const AUTO_RECONCILE_MIN_TIMEOUT_MS = 100;
export const AUTO_RECONCILE_MAX_TIMEOUT_MS = 60_000;

const BATCH_ID_RE = /^\d{8}-\d{6}-[a-z0-9]{4}$/;
const WINDOWS_DRIVE_RE = /^[A-Za-z]:/;
const CTRL_CHAR_RE = /[\x00-\x1f\x7f]/;

const AFFECTED_FILES_ALLOWED_OPTIONS = new Set([
  '--affected',
  '--files',
  '--json',
  '--app-map',
]);

const RETRY_UNRESOLVED_ALLOWED_OPTIONS = new Set([
  '--retry-unresolved',
  '--json',
  '--details',
  '--timeout',
  '--batch-timeout',
  '--max-calls',
  '--max-total-calls',
  '--no-restart-replacement',
  '--fresh',
  '--cache-clear',
]);

const NON_DISPATCH_OPTIONS = new Set([
  '--files',
  '--app-map',
  '--explain-bindings',
  '--read',
  '--retry',
  '--retry-unresolved',
  '--reconcile',
  '--reconcile-stale',
  '--request',
  '--screen',
  '--drawing',
  '--look',
  '--lint',
  '--local',
  '--emit-v1',
  '--write',
  '--bind-criteria',
  '--target',
]);

const TERMINAL_RECEIPT_STATES = new Set(['passed', 'failed', 'refused']);
const STALE_OPEN_STATES = new Set(['sending', 'queued', 'running', 'waiting', 'unknown', 'partial']);

function isPlainObject(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function activeOptionKeys(options) {
  if (!isPlainObject(options)) return [];
  return Object.keys(options).filter(key => options[key] !== undefined);
}

export function isValidBatchId(value) {
  return typeof value === 'string' && BATCH_ID_RE.test(value);
}

export function isSafeScenarioPath(value) {
  if (typeof value !== 'string' || !value.length || value.length > 1000) return false;
  if (value.startsWith('/') || WINDOWS_DRIVE_RE.test(value) || value.includes('\\') || CTRL_CHAR_RE.test(value)) {
    return false;
  }
  const segments = value.split('/');
  return segments.every(seg => seg.length > 0 && seg !== '.' && seg !== '..' && seg.toLowerCase() !== '.git');
}

export function planTestErgonomicsOptions(input = {}) {
  const safeInput = isPlainObject(input) ? input : {};
  const words = Array.isArray(safeInput.words) ? safeInput.words.filter(w => typeof w === 'string') : [];
  const options = isPlainObject(safeInput.options) ? safeInput.options : {};
  const keys = activeOptionKeys(options);

  const hasRetryUnresolved = options['--retry-unresolved'] !== undefined;
  const hasAffected = options['--affected'] !== undefined;
  const hasFiles = options['--files'] !== undefined;

  if (hasRetryUnresolved) {
    const rawBatch = options['--retry-unresolved'];
    const trimmed = typeof rawBatch === 'string' ? rawBatch.trim() : '';
    if (typeof rawBatch !== 'string' || rawBatch !== trimmed || !isValidBatchId(trimmed)) {
      return {
        handled: true,
        mode: 'invalid',
        exit_code: 2,
        ai_calls: 0,
        error: 'Invalid batch ID for --retry-unresolved. Pass a local batch ID like 20261125-100000-ab12.',
        batch_id: null,
        forwarded_options: {},
      };
    }
    const disallowed = keys.filter(key => !RETRY_UNRESOLVED_ALLOWED_OPTIONS.has(key));
    if (words.length > 0 || disallowed.length > 0) {
      return {
        handled: true,
        mode: 'invalid',
        exit_code: 2,
        ai_calls: 0,
        error: 'Use pdd test --retry-unresolved BATCH [--json] [--details] [--timeout MIN] [--batch-timeout MIN] [--max-calls N] [--max-total-calls N] [--no-restart-replacement] [--fresh] [--cache-clear] without Story operands or conflicting modes.',
        batch_id: null,
        forwarded_options: {},
      };
    }
    const forwarded = {};
    for (const key of keys) {
      if (key === '--retry-unresolved') continue;
      if (key === '--json') forwarded['--json'] = options['--json'] === true;
      else forwarded[key] = options[key];
    }
    return {
      handled: true,
      mode: 'retry-unresolved',
      exit_code: 0,
      ai_calls: null,
      error: null,
      batch_id: trimmed,
      forwarded_options: forwarded,
    };
  }

  if (hasAffected && hasFiles) {
    if (options['--affected'] !== true || options['--files'] !== true) {
      return {
        handled: true,
        mode: 'invalid',
        exit_code: 2,
        ai_calls: 0,
        error: '--affected and --files take no values.',
        batch_id: null,
        forwarded_options: {},
      };
    }
    const disallowed = keys.filter(key => !AFFECTED_FILES_ALLOWED_OPTIONS.has(key));
    if (words.length > 0 || disallowed.length > 0) {
      return {
        handled: true,
        mode: 'invalid',
        exit_code: 2,
        ai_calls: 0,
        error: 'Use pdd test --affected --files [--app-map PATH] [--json] without Story operands or other options.',
        batch_id: null,
        forwarded_options: {},
      };
    }
    const forwarded = { '--files': true };
    if (options['--json'] === true) forwarded['--json'] = true;
    if (options['--app-map'] !== undefined) forwarded['--app-map'] = options['--app-map'];
    return {
      handled: true,
      mode: 'affected-files',
      exit_code: 0,
      ai_calls: 0,
      error: null,
      batch_id: null,
      forwarded_options: forwarded,
    };
  }

  return {
    handled: false,
    mode: 'passthrough',
    exit_code: 0,
    ai_calls: null,
    error: null,
    batch_id: null,
    forwarded_options: {},
  };
}

export function selectUnresolvedBatchTests(input = {}) {
  const safeInput = isPlainObject(input) ? input : {};
  const batchId = typeof safeInput.batch_id === 'string' ? safeInput.batch_id : null;
  const rows = Array.isArray(safeInput.rows) ? safeInput.rows : [];
  const receiptsById = isPlainObject(safeInput.receipts_by_id) ? safeInput.receipts_by_id : {};

  const order = [];
  const statusByTest = new Map();
  const invalidPaths = [];
  const seenInvalid = new Set();

  for (const row of rows) {
    if (!isPlainObject(row)) continue;
    const testPath = row.test;
    if (!isSafeScenarioPath(testPath)) {
      const display = typeof testPath === 'string' ? testPath : String(testPath ?? '');
      if (!seenInvalid.has(display)) {
        seenInvalid.add(display);
        invalidPaths.push(display);
      }
      continue;
    }

    const requestIds = Array.isArray(row.request_ids)
      ? row.request_ids.filter(id => typeof id === 'string' && id.length > 0)
      : [];
    const lastId = requestIds.length > 0 ? requestIds[requestIds.length - 1] : null;
    const receiptState = lastId && typeof receiptsById[lastId] === 'string' ? receiptsById[lastId] : null;

    const noteCode = typeof row.note_code === 'string'
      ? row.note_code
      : (isPlainObject(row.note) && typeof row.note.code === 'string' ? row.note.code : null);
    const failedCheckCount = Number.isSafeInteger(row.failed_check_count) && row.failed_check_count > 0
      ? row.failed_check_count
      : (Array.isArray(row.failed_checks) ? row.failed_checks.length : 0);
    const refusalCount = Number.isSafeInteger(row.refusal_count) && row.refusal_count > 0
      ? row.refusal_count
      : (Array.isArray(row.refusals) ? row.refusals.length : 0);

    const rawState = typeof row.recovery_state === 'string' && row.recovery_state.length > 0
      ? row.recovery_state
      : (typeof row.state === 'string' ? row.state : '');

    let effectiveState = rawState;
    if (
      receiptState &&
      TERMINAL_RECEIPT_STATES.has(receiptState) &&
      (STALE_OPEN_STATES.has(rawState) || !rawState)
    ) {
      effectiveState = receiptState;
    }

    const isPassed =
      effectiveState === 'passed' &&
      noteCode !== 'criteria-not-checked' &&
      failedCheckCount === 0 &&
      refusalCount === 0;

    if (!statusByTest.has(testPath)) {
      order.push(testPath);
      statusByTest.set(testPath, isPassed ? 'passed' : 'retry');
    } else if (!isPassed) {
      // Non-passed occurrence wins over an earlier passed occurrence for the same scenario path.
      statusByTest.set(testPath, 'retry');
    }
  }

  const retryTests = [];
  const passedTests = [];
  for (const testPath of order) {
    if (statusByTest.get(testPath) === 'passed') passedTests.push(testPath);
    else retryTests.push(testPath);
  }

  return {
    batch_id: batchId,
    retry_tests: retryTests,
    passed_tests: passedTests,
    skipped_count: passedTests.length,
    all_passed: retryTests.length === 0 && invalidPaths.length === 0,
    invalid_paths: invalidPaths,
  };
}

function clampTimeoutMs(configured, fallback) {
  const candidate =
    typeof configured === 'number' && Number.isFinite(configured) && configured > 0
      ? configured
      : typeof fallback === 'number' && Number.isFinite(fallback) && fallback > 0
        ? fallback
        : AUTO_RECONCILE_DEFAULT_TIMEOUT_MS;
  return Math.max(AUTO_RECONCILE_MIN_TIMEOUT_MS, Math.min(AUTO_RECONCILE_MAX_TIMEOUT_MS, Math.trunc(candidate)));
}

export function planAutoReconcile(input = {}) {
  const safeInput = isPlainObject(input) ? input : {};
  const options = isPlainObject(safeInput.options) ? safeInput.options : {};

  for (const key of NON_DISPATCH_OPTIONS) {
    if (options[key] !== undefined && options[key] !== false) {
      return {
        should_reconcile: false,
        reason: 'non-dispatch-mode',
        stale_batches: [],
        expired_count: 0,
        within_ttl_count: 0,
        timeout_ms: 0,
      };
    }
  }

  const rawBatches = Array.isArray(safeInput.stale_batches) ? safeInput.stale_batches : [];
  const byId = new Map();
  for (const entry of rawBatches) {
    if (!isPlainObject(entry) || !isValidBatchId(entry.batch_id)) continue;
    const expired = Number.isSafeInteger(entry.expired_count) && entry.expired_count > 0 ? entry.expired_count : 0;
    const withinTtl = Number.isSafeInteger(entry.within_ttl_count) && entry.within_ttl_count > 0 ? entry.within_ttl_count : 0;
    if (expired + withinTtl <= 0) continue;
    const prev = byId.get(entry.batch_id) ?? { expired: 0, withinTtl: 0 };
    byId.set(entry.batch_id, {
      expired: Math.max(prev.expired, expired),
      withinTtl: Math.max(prev.withinTtl, withinTtl),
    });
  }

  const staleBatchIds = [...byId.keys()].sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
  if (staleBatchIds.length === 0) {
    return {
      should_reconcile: false,
      reason: 'no-stale-reservations',
      stale_batches: [],
      expired_count: 0,
      within_ttl_count: 0,
      timeout_ms: 0,
    };
  }

  let expiredCount = 0;
  let withinTtlCount = 0;
  for (const id of staleBatchIds) {
    const counts = byId.get(id);
    expiredCount += counts.expired;
    withinTtlCount += counts.withinTtl;
  }

  return {
    should_reconcile: true,
    reason: 'stale-reservations-present',
    stale_batches: staleBatchIds,
    expired_count: expiredCount,
    within_ttl_count: withinTtlCount,
    timeout_ms: clampTimeoutMs(safeInput.configured_timeout_ms, safeInput.default_timeout_ms),
  };
}

export function classifyTargetedScenarioCriteria(input = {}) {
  const safeInput = isPlainObject(input) ? input : {};
  const explicitPaths = new Set(
    (Array.isArray(safeInput.explicit_scenario_paths) ? safeInput.explicit_scenario_paths : [])
      .filter(p => typeof p === 'string' && p.length > 0),
  );
  const targetTestPath = typeof safeInput.target_test_path === 'string' ? safeInput.target_test_path : '';
  const isTargetedSlice = targetTestPath.length > 0 && explicitPaths.has(targetTestPath);

  const uniqueStoryIds = [];
  const storyIdSet = new Set();
  for (const id of Array.isArray(safeInput.story_criteria_ids) ? safeInput.story_criteria_ids : []) {
    if (typeof id !== 'string' || !id || storyIdSet.has(id)) continue;
    storyIdSet.add(id);
    uniqueStoryIds.push(id);
  }

  const ownSet = new Set();
  for (const id of Array.isArray(safeInput.own_checked_ids) ? safeInput.own_checked_ids : []) {
    if (typeof id === 'string' && storyIdSet.has(id)) ownSet.add(id);
  }

  const siblingSet = new Set();
  for (const id of Array.isArray(safeInput.sibling_checked_ids) ? safeInput.sibling_checked_ids : []) {
    if (typeof id === 'string' && storyIdSet.has(id)) siblingSet.add(id);
  }

  const siblingCoveredIds = [];
  const uncoveredIds = [];
  for (const id of uniqueStoryIds) {
    if (ownSet.has(id)) continue;
    if (siblingSet.has(id)) siblingCoveredIds.push(id);
    else uncoveredIds.push(id);
  }

  const canPassAsTargetedSlice =
    isTargetedSlice &&
    uniqueStoryIds.length > 0 &&
    ownSet.size > 0 &&
    uncoveredIds.length === 0;

  return {
    is_targeted_slice: isTargetedSlice,
    own_checked_count: ownSet.size,
    sibling_covered_ids: siblingCoveredIds,
    uncovered_ids: uncoveredIds,
    can_pass_as_targeted_slice: canPassAsTargetedSlice,
  };
}
