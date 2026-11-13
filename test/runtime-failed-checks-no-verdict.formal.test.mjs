import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {
  exitCodeFor,
  projectAnswer,
  PROVIDER_TEXT,
  renderJson,
  renderText,
  runtimeOutcomeSlice,
  summaryLine,
} from '../src/runtime-seam.mjs';
import { checkCause } from '../src/workflow-results.mjs';

const { resultOutcome } = runtimeOutcomeSlice();

const STATES = ['passed', 'failed', 'unknown', 'refused', 'not_run'];
const PROVIDERS = [false, true];
const FAILED_COUNTS = [0, 1, 2];
const PASSED_COUNTS = [0, 1];
const SAMPLE_COUNTS = [1, 2];

function buildAnswer({ state, provider, failedCount, passedCount, sampleCount }, storyIndex) {
  const checks = [];
  for (let i = 0; i < passedCount; i++) {
    checks.push({
      step_id: `pass-${storyIndex}-${i}`,
      criterion_id: 'AC1',
      target: 'result',
      path: '/ok',
      expected: true,
      actual: true,
      passed: true
    });
  }
  for (let i = 0; i < failedCount; i++) {
    checks.push({
      step_id: `fail-${storyIndex}-${i}`,
      criterion_id: i === 0 ? 'AC2' : 'AC3',
      target: 'result',
      path: `/v${i}`,
      expected: `want-${i}`,
      actual: `got-${i}`,
      passed: false
    });
  }
  const samples = Array.from({ length: sampleCount }, (_, sampleIndex) => ({
    sample: sampleIndex + 1,
    steps: []
  }));
  checks.forEach((check, idx) => {
    const bucket = samples[idx % sampleCount];
    bucket.steps.push({
      step_id: check.step_id,
      result: { ok: check.passed },
      checks: [check]
    });
  });
  const refusals = [];
  if (state === 'not_run') {
    refusals.push({ code: 'pool-copy-unavailable', message: 'Pool busy.', retryable: true });
  } else if (provider) {
    refusals.push({ code: 'graph-provider-failure', message: 'Provider failed.', cause: 'ai-service' });
    samples.at(-1).refusal = { code: 'graph-provider-failure', failure_cause: { kind: 'transport_unknown', detail: 'synthetic' } };
  } else if (state === 'refused') {
    refusals.push({ code: 'invalid-input', message: 'Invalid input.', cause: 'test' });
  }
  return {
    command: 'check',
    state: state === 'not_run' ? 'refused' : state,
    ...(state === 'not_run' ? { dispatch: 'not_started' } : {}),
    usage: {
      calls: passedCount + failedCount,
      known_calls: passedCount + failedCount,
      unknown_calls: state === 'unknown' ? 1 : 0,
      accounting_complete: state !== 'unknown'
    },
    result: {
      refusals,
      report: {
        ...(state === 'not_run' ? { dispatch: 'not_started' } : {}),
        criterion_results: [
          { criterion_id: 'AC1', status: passedCount > 0 ? 'passed' : 'not_checked' },
          { criterion_id: 'AC2', status: failedCount > 0 ? 'failed' : 'not_checked' },
          { criterion_id: 'AC3', status: failedCount > 1 ? 'failed' : 'not_checked' }
        ],
        samples
      }
    }
  };
}

function makeRow(spec, storyIndex) {
  const story = `story-${storyIndex}`;
  const answer = buildAnswer(spec, storyIndex);
  const view = projectAnswer(answer, { test: `tests/${story}.json` });
  return {
    spec,
    row: {
      story,
      title: `Story ${storyIndex}`,
      test: `tests/${story}.json`,
      phase: 'server',
      request_ids: [`req-${storyIndex}`],
      ...view
    }
  };
}

test('Proved (bounded): 120 single-row states and 14,400 two-row batches satisfy R1-R3 invariants across public projections', () => {
  const singleSpecs = [];
  for (const state of STATES) {
    for (const provider of PROVIDERS) {
      for (const failedCount of FAILED_COUNTS) {
        for (const passedCount of PASSED_COUNTS) {
          for (const sampleCount of SAMPLE_COUNTS) {
            singleSpecs.push({ state, provider, failedCount, passedCount, sampleCount });
          }
        }
      }
    }
  }
  assert.equal(singleSpecs.length, 120);

  const singleRows = singleSpecs.map(spec => {
    const built = makeRow(spec, 1);
    const { row } = built;
    const outcome = resultOutcome(row);
    const text = renderText({ batch: '20261112-000000-form', rows: [row], exitCode: exitCodeFor([row]) });
    const json = renderJson({ batch: '20261112-000000-form', repo: 'example/repo', rows: [row], exitCode: exitCodeFor([row]) });

    // R3: projectAnswer and renderJson preserve all failed checks across samples[0..sampleCount-1]
    assert.equal(row.failed_checks.length, spec.failedCount, JSON.stringify(spec));
    assert.equal(json.rows[0].failed_checks.length, spec.failedCount, JSON.stringify(spec));
    const expectedTotal = spec.passedCount + spec.failedCount;
    assert.deepEqual(row.checks, expectedTotal > 0 ? { passed: spec.passedCount, total: expectedTotal } : null);

    // R2: When failedCount > 0, neither reason.message nor terminal text says "not a failed check"
    if (spec.failedCount > 0) {
      assert.doesNotMatch(outcome.reason?.message ?? '', /not a failed check/i, JSON.stringify({ spec, outcome }));
      assert.doesNotMatch(text, /not a failed check/i, JSON.stringify({ spec, text }));
      assert.match(text, /FAILED {2}Story 1 \(tests\/story-1\.json\)/, JSON.stringify({ spec, text }));
      assert.equal(checkCause([row]), 'issue', JSON.stringify(spec));
    } else if (row.provider) {
      assert.equal(outcome.reason?.message, PROVIDER_TEXT, JSON.stringify({ spec, outcome }));
    }

    return built;
  });

  let pairsChecked = 0;
  for (const left of singleRows) {
    for (const rightSpec of singleSpecs) {
      const right = makeRow(rightSpec, 2);
      const rows = [left.row, right.row];
      const totalFailedChecks = left.spec.failedCount + right.spec.failedCount;
      const nonFailedRowChecks = (left.row.state !== 'failed' ? left.spec.failedCount : 0)
        + (right.row.state !== 'failed' ? right.spec.failedCount : 0);
      const anyFailedRow = rows.some(r => r.state === 'failed');
      const line = summaryLine(rows);

      // R1: Summary mark and non-failed-row failed check count
      if (totalFailedChecks > 0 || anyFailedRow) {
        assert.ok(line.includes(': ✗ '), `expected ✗ in "${line}"`);
        assert.ok(!line.includes(': no verdict · '), `unexpected no verdict in "${line}"`);
      } else {
        assert.ok(!line.includes(': ✗ '), `unexpected ✗ in "${line}"`);
      }
      if (nonFailedRowChecks > 0) {
        assert.ok(line.includes(` · ${nonFailedRowChecks} failed · `), `expected "${nonFailedRowChecks} failed" in "${line}"`);
      }

      // R3 + workflow classification on batches with failed checks
      if (totalFailedChecks > 0) {
        assert.equal(checkCause(rows), 'issue');
      }
      pairsChecked += 1;
    }
  }
  assert.equal(pairsChecked, 14_400);
});
