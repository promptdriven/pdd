import test from 'node:test';
import assert from 'node:assert/strict';
import {
  AUTO_RECONCILE_DEFAULT_TIMEOUT_MS,
  AUTO_RECONCILE_MAX_TIMEOUT_MS,
  AUTO_RECONCILE_MIN_TIMEOUT_MS,
  classifyTargetedScenarioCriteria,
  isSafeScenarioPath,
  isValidBatchId,
  planAutoReconcile,
  planTestErgonomicsOptions,
  selectUnresolvedBatchTests,
} from '../src/core/test-ergonomics.mjs';

// Oracles: Rules to check and Acceptance criteria in user_stories/test-ergonomics.md,
// qualified by prompts/cli/test-ergonomics.prompt.md.
// Exhaustive over the finite domains below plus deterministic seeded PRNG sweeps.
// Pure functional core properties only; no Git, filesystem, CLI subprocess, or HTTP effect is proved here.

function mulberry32(seed) {
  let state = seed >>> 0;
  return () => {
    state = (state + 0x6d2b79f5) >>> 0;
    let t = Math.imul(state ^ (state >>> 15), 1 | state);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function* words(alphabet, length) {
  if (length === 0) {
    yield [];
    return;
  }
  for (const prefix of words(alphabet, length - 1)) {
    for (const item of alphabet) yield [...prefix, item];
  }
}

function* subsets(items) {
  const total = 1 << items.length;
  for (let mask = 0; mask < total; mask++) {
    const out = [];
    for (let i = 0; i < items.length; i++) {
      if (mask & (1 << i)) out.push(items[i]);
    }
    yield out;
  }
}

const AFFECTED_FILES_ALLOW = new Set(['--affected', '--files', '--json', '--app-map']);
const RETRY_UNRESOLVED_ALLOW = new Set([
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
const NON_DISPATCH_FLAGS = [
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
];

test('formal: planTestErgonomicsOptions enforces exact routing and fails closed on every invalid option mix', t => {
  const batchValues = [undefined, '20261125-100000-ab12', 'not-a-batch', ' 20261125-100000-ab12', '../20261125-100000-ab12', '20261125-100000-AB12', true];
  const affectedValues = [undefined, true, false, 'yes'];
  const filesValues = [undefined, true, false, 'yes'];
  const extraOptions = [
    null,
    ['--json', true],
    ['--app-map', 'app-map.json'],
    ['--details', true],
    ['--timeout', 15],
    ['--batch-timeout', 30],
    ['--max-calls', 20],
    ['--max-total-calls', 100],
    ['--no-restart-replacement', true],
    ['--fresh', true],
    ['--cache-clear', true],
    ['--lf', true],
    ['--retry', '20261125-100000-ab12'],
    ['--reconcile', '20261125-100000-ab12'],
    ['--target', 'code'],
  ];
  const wordVariants = [[], ['split'], ['tests/split.a.json']];

  let count = 0;
  for (const batch of batchValues) {
    for (const affected of affectedValues) {
      for (const files of filesValues) {
        for (const extra of extraOptions) {
          for (const wordList of wordVariants) {
            const options = {};
            if (batch !== undefined) options['--retry-unresolved'] = batch;
            if (affected !== undefined) options['--affected'] = affected;
            if (files !== undefined) options['--files'] = files;
            if (extra !== null) options[extra[0]] = extra[1];

            const input = { words: [...wordList], options };
            const snapshot = structuredClone(input);
            const got = planTestErgonomicsOptions(input);
            assert.deepEqual(input, snapshot, 'planTestErgonomicsOptions must not mutate input');

            const activeKeys = Object.keys(options).filter(k => options[k] !== undefined);
            if (batch !== undefined) {
              assert.equal(got.handled, true);
              const validBatch = typeof batch === 'string' && batch === batch.trim() && isValidBatchId(batch);
              const validKeys = activeKeys.every(k => RETRY_UNRESOLVED_ALLOW.has(k));
              if (!validBatch || wordList.length > 0 || !validKeys) {
                assert.equal(got.mode, 'invalid');
                assert.equal(got.exit_code, 2);
                assert.equal(got.ai_calls, 0);
                assert.equal(got.batch_id, null);
                assert.ok(typeof got.error === 'string' && got.error.length > 0);
              } else {
                assert.equal(got.mode, 'retry-unresolved');
                assert.equal(got.exit_code, 0);
                assert.equal(got.batch_id, batch);
                assert.equal(got.error, null);
                assert.equal(Object.hasOwn(got.forwarded_options, '--retry-unresolved'), false);
              }
            } else if (affected !== undefined && files !== undefined) {
              assert.equal(got.handled, true);
              const validFlags = affected === true && files === true;
              const validKeys = activeKeys.every(k => AFFECTED_FILES_ALLOW.has(k));
              if (!validFlags || wordList.length > 0 || !validKeys) {
                assert.equal(got.mode, 'invalid');
                assert.equal(got.exit_code, 2);
                assert.equal(got.ai_calls, 0);
                assert.ok(typeof got.error === 'string' && got.error.length > 0);
              } else {
                assert.equal(got.mode, 'affected-files');
                assert.equal(got.exit_code, 0);
                assert.equal(got.ai_calls, 0);
                assert.equal(got.error, null);
                assert.equal(got.forwarded_options['--files'], true);
              }
            } else {
              assert.equal(got.handled, false);
              assert.equal(got.mode, 'passthrough');
              assert.equal(got.exit_code, 0);
              assert.equal(got.error, null);
            }
            count++;
          }
        }
      }
    }
  }
  assert.equal(count, 7 * 4 * 4 * 15 * 3);
  t.diagnostic(`planTestErgonomicsOptions: ${count} exhaustive option combinations verified`);
});

test('formal: selectUnresolvedBatchTests skips only confirmed passes, retains all non-passed outcomes, and rejects unsafe paths', t => {
  const states = ['passed', 'partial', 'unknown', 'not_run', 'failed', 'refused', 'running', 'queued', 'sending', 'waiting', ''];
  const receiptStates = [null, 'passed', 'failed', 'refused', 'running'];
  const noteCodes = [null, 'criteria-not-checked', 'no-server-verdict'];

  // Part A: Exhaustive single-row classification oracle over all state/receipt/note/failure/refusal combinations.
  let singleCount = 0;
  for (const state of states) {
    for (const receipt of receiptStates) {
      for (const noteCode of noteCodes) {
        for (const failedChecks of [0, 1]) {
          for (const refusals of [0, 1]) {
            const reqId = '11111111-1111-4111-8111-111111111111';
            const input = {
              batch_id: '20261125-100000-ab12',
              rows: [
                {
                  test: 'tests/a.json',
                  state,
                  note_code: noteCode,
                  request_ids: receipt ? [reqId] : [],
                  failed_check_count: failedChecks,
                  refusal_count: refusals,
                },
              ],
              receipts_by_id: receipt ? { [reqId]: receipt } : {},
            };
            const before = structuredClone(input);
            const got = selectUnresolvedBatchTests(input);
            assert.deepEqual(input, before, 'selectUnresolvedBatchTests must not mutate input');

            const receiptPromoted =
              receipt === 'passed' &&
              ['sending', 'queued', 'running', 'waiting', 'unknown', 'partial', ''].includes(state);
            const expectedPassed =
              (state === 'passed' || receiptPromoted) &&
              noteCode !== 'criteria-not-checked' &&
              failedChecks === 0 &&
              refusals === 0;

            assert.deepEqual(got.passed_tests, expectedPassed ? ['tests/a.json'] : []);
            assert.deepEqual(got.retry_tests, expectedPassed ? [] : ['tests/a.json']);
            assert.equal(got.skipped_count, got.passed_tests.length);
            assert.equal(got.all_passed, expectedPassed);
            assert.deepEqual(got.invalid_paths, []);
            singleCount++;
          }
        }
      }
    }
  }
  assert.equal(singleCount, 11 * 5 * 3 * 2 * 2);

  // Part B: Exhaustive duplicate-path dominance over 3-row sequences of passed/partial/unknown/not_run/failed.
  const fiveStates = ['passed', 'partial', 'unknown', 'not_run', 'failed'];
  let dupCount = 0;
  for (const seq of words(fiveStates, 3)) {
    const got = selectUnresolvedBatchTests({
      batch_id: '20261125-100000-ab12',
      rows: seq.map(state => ({ test: 'tests/dup.json', state })),
    });
    const allPassed = seq.every(s => s === 'passed');
    assert.deepEqual(got.passed_tests, allPassed ? ['tests/dup.json'] : []);
    assert.deepEqual(got.retry_tests, allPassed ? [] : ['tests/dup.json']);
    assert.equal(got.all_passed, allPassed);
    dupCount++;
  }
  assert.equal(dupCount, 125);

  // Part C: Seeded PRNG (mulberry32) sweep across 2,000 randomized multi-row batches including unsafe paths.
  const rand = mulberry32(0x3703cafe);
  const validPool = ['tests/a.json', 'tests/b.json', 'tests/c.json', 'tests/d.json', 'test/runtime/e.json'];
  const unsafePool = ['/etc/passwd', '../escape.json', 'tests\\win.json', 'C:drive.json', '.git/config', 'tests/./a.json', 'bad\x00.json', ''];
  let randCount = 0;
  for (let trial = 0; trial < 2000; trial++) {
    const rowCount = Math.floor(rand() * 10);
    const rows = [];
    const receipts = {};
    for (let i = 0; i < rowCount; i++) {
      const useUnsafe = rand() < 0.15;
      const testPath = useUnsafe
        ? unsafePool[Math.floor(rand() * unsafePool.length)]
        : validPool[Math.floor(rand() * validPool.length)];
      const state = states[Math.floor(rand() * states.length)];
      const receipt = receiptStates[Math.floor(rand() * receiptStates.length)];
      const reqId = `00000000-0000-4000-8000-${String(i + 1).padStart(12, '0')}`;
      if (receipt) receipts[reqId] = receipt;
      rows.push({
        test: testPath,
        state,
        note_code: noteCodes[Math.floor(rand() * noteCodes.length)],
        request_ids: receipt ? [reqId] : [],
        failed_check_count: rand() < 0.2 ? 1 : 0,
        refusal_count: rand() < 0.15 ? 1 : 0,
      });
    }
    const got = selectUnresolvedBatchTests({ batch_id: '20261125-100000-ab12', rows, receipts_by_id: receipts });
    const retrySet = new Set(got.retry_tests);
    const passSet = new Set(got.passed_tests);
    assert.equal(retrySet.size, got.retry_tests.length, 'retry_tests must be deduplicated');
    assert.equal(passSet.size, got.passed_tests.length, 'passed_tests must be deduplicated');
    for (const p of got.retry_tests) {
      assert.equal(passSet.has(p), false, 'retry_tests and passed_tests must be disjoint');
      assert.equal(isSafeScenarioPath(p), true, 'retry_tests must contain only safe paths');
    }
    for (const p of got.passed_tests) {
      assert.equal(isSafeScenarioPath(p), true, 'passed_tests must contain only safe paths');
    }
    for (const bad of got.invalid_paths) {
      assert.equal(isSafeScenarioPath(bad), false, 'invalid_paths must contain only unsafe paths');
    }
    assert.equal(got.skipped_count, got.passed_tests.length);
    assert.equal(got.all_passed, got.retry_tests.length === 0 && got.invalid_paths.length === 0);
    randCount++;
  }
  t.diagnostic(`selectUnresolvedBatchTests: ${singleCount} exhaustive + ${dupCount} dominance + ${randCount} PRNG cases verified`);
});

test('formal: planAutoReconcile never reconciles on non-dispatch or clean repos and always bounds timeout', t => {
  const timeouts = [undefined, null, -5, 0, 1, 99, 100, 1000, 10000, 60000, 60001, 999999, NaN, Infinity, 1234.9];
  const staleInputs = [
    [],
    [{ batch_id: 'bad-id', expired_count: 3, within_ttl_count: 1 }],
    [{ batch_id: '20261125-100000-ab12', expired_count: 0, within_ttl_count: 0 }],
    [{ batch_id: '20261125-100000-ab12', expired_count: 1, within_ttl_count: 0 }],
    [{ batch_id: '20261125-100000-ab12', expired_count: 0, within_ttl_count: 2 }],
    [
      { batch_id: '20261125-100002-zz99', expired_count: 1, within_ttl_count: 1 },
      { batch_id: '20261125-100001-aa01', expired_count: 2, within_ttl_count: 0 },
      { batch_id: '20261125-100002-zz99', expired_count: 3, within_ttl_count: 0 },
    ],
  ];

  let count = 0;
  // Every non-dispatch flag suppresses auto-reconciliation even when stale batches exist.
  for (const flag of NON_DISPATCH_FLAGS) {
    for (const stale of staleInputs) {
      const value = flag === '--target' ? 'code' : flag === '--retry' ? '20261125-100000-ab12' : true;
      const input = { options: { [flag]: value }, stale_batches: stale, configured_timeout_ms: 500 };
      const before = structuredClone(input);
      const got = planAutoReconcile(input);
      assert.deepEqual(input, before);
      assert.equal(got.should_reconcile, false);
      assert.equal(got.reason, 'non-dispatch-mode');
      assert.deepEqual(got.stale_batches, []);
      assert.equal(got.timeout_ms, 0);
      count++;
    }
  }

  // Dispatch modes: clean -> false; stale -> true with sorted deduped batches and bounded timeout.
  const dispatchOptionSets = [{}, { '--json': true }, { '--fresh': true }, { '--affected': true }, { '--max-total-calls': 20 }];
  for (const options of dispatchOptionSets) {
    for (const stale of staleInputs) {
      for (const configured of timeouts) {
        const input = { options, stale_batches: stale, configured_timeout_ms: configured };
        const before = structuredClone(input);
        const got = planAutoReconcile(input);
        assert.deepEqual(input, before);

        const hasValidStale = stale.some(
          entry => isValidBatchId(entry.batch_id) && entry.expired_count + entry.within_ttl_count > 0,
        );
        if (!hasValidStale) {
          assert.equal(got.should_reconcile, false);
          assert.equal(got.reason, 'no-stale-reservations');
          assert.deepEqual(got.stale_batches, []);
          assert.equal(got.timeout_ms, 0);
        } else {
          assert.equal(got.should_reconcile, true);
          assert.equal(got.reason, 'stale-reservations-present');
          assert.ok(got.stale_batches.length > 0);
          assert.deepEqual(got.stale_batches, [...new Set(got.stale_batches)].sort());
          assert.ok(got.expired_count + got.within_ttl_count > 0);
          assert.ok(got.timeout_ms >= AUTO_RECONCILE_MIN_TIMEOUT_MS);
          assert.ok(got.timeout_ms <= AUTO_RECONCILE_MAX_TIMEOUT_MS);
          assert.equal(Number.isSafeInteger(got.timeout_ms), true);
          if (typeof configured === 'number' && Number.isFinite(configured) && configured > 0) {
            const expectedTimeout = Math.max(
              AUTO_RECONCILE_MIN_TIMEOUT_MS,
              Math.min(AUTO_RECONCILE_MAX_TIMEOUT_MS, Math.trunc(configured)),
            );
            assert.equal(got.timeout_ms, expectedTimeout);
          } else {
            assert.equal(got.timeout_ms, AUTO_RECONCILE_DEFAULT_TIMEOUT_MS);
          }
        }
        count++;
      }
    }
  }
  t.diagnostic(`planAutoReconcile: ${count} exhaustive dispatch/non-dispatch/timeout cases verified`);
});

test('formal: classifyTargetedScenarioCriteria is fail-closed across all subsets of 4 Story criteria', t => {
  const storyCriteria = ['AC1', 'AC2', 'AC3', 'AC4'];
  let count = 0;
  for (const explicit of [false, true]) {
    for (const own of subsets(storyCriteria)) {
      for (const sibling of subsets(storyCriteria)) {
        const input = {
          explicit_scenario_paths: explicit ? ['tests/split.a.json'] : [],
          target_test_path: 'tests/split.a.json',
          story_criteria_ids: [...storyCriteria, 'AC1'], // include duplicate Story ID to verify deduplication
          own_checked_ids: [...own, 'UNKNOWN_CRIT'],
          sibling_checked_ids: [...sibling, 'OTHER_UNKNOWN'],
        };
        const before = structuredClone(input);
        const got = classifyTargetedScenarioCriteria(input);
        assert.deepEqual(input, before, 'classifyTargetedScenarioCriteria must not mutate input');

        const ownSet = new Set(own);
        const sibSet = new Set(sibling);
        const expectedSib = storyCriteria.filter(id => !ownSet.has(id) && sibSet.has(id));
        const expectedUncovered = storyCriteria.filter(id => !ownSet.has(id) && !sibSet.has(id));
        const expectedCanPass = explicit && ownSet.size > 0 && expectedUncovered.length === 0;

        assert.equal(got.is_targeted_slice, explicit);
        assert.equal(got.own_checked_count, ownSet.size);
        assert.deepEqual(got.sibling_covered_ids, expectedSib);
        assert.deepEqual(got.uncovered_ids, expectedUncovered);
        assert.equal(got.can_pass_as_targeted_slice, expectedCanPass);
        count++;
      }
    }
  }
  assert.equal(count, 2 * 16 * 16);
  t.diagnostic(`classifyTargetedScenarioCriteria: ${count} exhaustive power-set cases verified`);
});
