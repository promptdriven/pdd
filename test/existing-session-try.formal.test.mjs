import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { bindExistingTry, projectTryCall, projectTryObservation, selectTryToStop } from '../src/try-session.mjs';

const TRY_ID = '520c7aa5-72f6-4add-b60e-8ed87db656c2';
const OTHER_ID = '11111111-1111-4111-8111-111111111111';

const baseRecord = (overrides = {}) => ({
  id: TRY_ID,
  test_path: 'tests/quote-total.json',
  test_name: 'quote-total',
  story: 'quote-total',
  story_path: 'user_stories/quote-total.md',
  source_sha256: '2fb88fd07157409cc408d4278e875567c3362f0eb64b13870430db815239c571',
  engine_sha: 'ee85fa4be756bc138a1b302b92cf44a428bc0025',
  server_commit: '217f8d38036f5dfaa98f915bc1b9011805ac9ac6',
  max_calls: 40,
  ...overrides,
});

test('formal rule 1: explicit try_id binding exhaustively enforces guard precedence and never admits non-running or cap-mismatched sessions', () => {
  const recordVariants = [
    { kind: 'empty', records: [] },
    { kind: 'wrong-id', records: [baseRecord({ id: OTHER_ID })] },
    { kind: 'duplicate-id', records: [baseRecord(), baseRecord({ test_path: 'tests/dup.json' })] },
    { kind: 'matched-cap-40', records: [baseRecord({ max_calls: 40 })] },
    { kind: 'matched-cap-null', records: [baseRecord({ max_calls: null })] },
  ];
  const stories = [undefined, '', 'quote-total', 'user_stories/quote-total.md', 'tests/quote-total.json', 'other-story'];
  const drifts = [null, 'prompt changed'];
  const models = [
    { status: 200, error_code: null, cap: 40, remaining: 40 },
    { status: 200, error_code: null, cap: 400, remaining: 400 },
    { status: 200, error_code: null, cap: null, remaining: null },
    { status: 404, error_code: 'not-found', cap: null, remaining: null },
    { status: 409, error_code: 'session-stopped', cap: null, remaining: null },
    { status: 410, error_code: 'expired', cap: null, remaining: null },
    { status: 500, error_code: 'internal', cap: null, remaining: null },
  ];

  let checked = 0;
  for (const rec of recordVariants) {
    for (const story of stories) {
      for (const drift of drifts) {
        for (const model of models) {
          checked++;
          let result = null, code = null;
          try {
            result = bindExistingTry({ try_id: TRY_ID, ...(story !== undefined ? { story } : {}), records: rec.records, drift, model });
          } catch (error) {
            code = error.code;
          }
          if (!rec.kind.startsWith('matched')) {
            assert.equal(code, 'try-not-found');
          } else if (story === 'other-story') {
            assert.equal(code, 'story-mismatch');
          } else if (drift !== null) {
            assert.equal(code, 'source-drift');
          } else if (model.status !== 200) {
            assert.equal(code, 'session-not-running');
          } else if (rec.kind === 'matched-cap-40' && model.cap === 400) {
            assert.equal(code, 'cap-mismatch');
          } else {
            assert.equal(code, null);
            assert.equal(result.try_id, TRY_ID);
            assert.equal(result.cap, model.cap ?? rec.records[0].max_calls);
          }
        }
      }
    }
  }
  assert.equal(checked, recordVariants.length * stories.length * drifts.length * models.length);
});

test('formal rule 2: run_id and action_id stay distinct across call and observation projections, and undeclared or unknown outcomes never turn into normal results', () => {
  const states = ['passed', 'failed', 'refused', 'queued', 'running', 'unknown'];
  const hasResults = [true, false];
  const declaredSets = [[], ['invalid-quantity']];
  const reports = [
    null,
    { action_id: 'act-1', verdict: 'passed', error_code: null, replayed: false, remaining_calls: 39 },
    { action_id: 'act-2', verdict: 'failed', error_code: 'invalid-quantity', replayed: true, remaining_calls: 38 },
    { action_id: 'act-3', verdict: 'failed', error_code: 'undeclared-code', replayed: false, remaining_calls: 37 },
    { action_id: 'act-4', verdict: 'refused', error_code: 'invalid-quantity', replayed: false, remaining_calls: 37 },
  ];

  for (const state of states) {
    for (const has_program_result of hasResults) {
      for (const declared_errors of declaredSets) {
        for (const report of reports) {
          const request_id = 'req-external-uuid';
          let out = null, code = null;
          try {
            out = projectTryCall({ request_id, declared_errors, state, has_program_result, usage_calls: 1, report });
          } catch (error) {
            code = error.code;
          }
          if (['queued', 'running', 'unknown'].includes(state) || (state === 'passed' && !has_program_result)) {
            assert.equal(code, 'unknown-outcome');
          } else if (state === 'passed' && has_program_result) {
            assert.equal(out.outcome, 'result');
            assert.equal(out.run_id, request_id);
            assert.equal(out.action_id, report ? report.action_id : null);
            assert.notEqual(out.run_id, out.action_id);
          } else if (['failed', 'refused'].includes(state) && report?.verdict === 'failed' && report.error_code && declared_errors.includes(report.error_code)) {
            assert.equal(out.outcome, 'program_error');
            assert.equal(out.error_code, 'invalid-quantity');
            assert.equal(out.run_id, request_id);
            assert.equal(out.action_id, report.action_id);
          } else {
            assert.equal(code, 'call-refused');
          }
        }
      }
    }
  }

  for (const session_state of ['running', 'paused', 'stopping', 'stopped', 'unknown']) {
    for (const state of ['queued', 'running', 'passed', 'failed', 'refused', 'unknown']) {
      const obs = projectTryObservation({
        try_id: TRY_ID,
        run_id: 'req-external-uuid',
        status: 200,
        body: {
          request_id: 'req-external-uuid',
          action_id: 'act-internal-hex',
          session_id: TRY_ID,
          state,
          session_state,
          source_sha256: 'src-sha',
          server_commit: 'srv-sha',
          engine_sha: 'eng-sha',
        },
      });
      assert.equal(obs.run_id, 'req-external-uuid');
      assert.equal(obs.action_id, 'act-internal-hex');
      assert.equal(obs.unknown_outcome, state === 'unknown');
      assert.equal(obs.terminal, ['passed', 'failed', 'refused'].includes(state));
    }
  }
});

test('formal rule 3: stop selection resolves at most one saved simulation and never touches unrelated records', () => {
  const r1 = { id: TRY_ID, test_path: 'tests/a.json', test_name: 'a', story: 'story-a', story_path: 'user_stories/story-a.md' };
  const r2 = { id: OTHER_ID, test_path: 'tests/b.json', test_name: 'b', story: 'story-b', story_path: 'user_stories/story-b.md' };
  const rDup = { id: '22222222-2222-4222-8222-222222222222', test_path: 'tests/sub/a.json', test_name: 'a', story: 'story-a', story_path: 'user_stories/sub/story-a.md' };

  assert.deepEqual(selectTryToStop({ selector: TRY_ID, records: [r1, r2, rDup] }), { id: TRY_ID, test_path: 'tests/a.json', story_path: 'user_stories/story-a.md' });
  assert.deepEqual(selectTryToStop({ selector: OTHER_ID, records: [r1, r2, rDup] }), { id: OTHER_ID, test_path: 'tests/b.json', story_path: 'user_stories/story-b.md' });
  assert.deepEqual(selectTryToStop({ records: [r1] }), { id: TRY_ID, test_path: 'tests/a.json', story_path: 'user_stories/story-a.md' });
  assert.throws(() => selectTryToStop({ records: [] }), { code: 'stop-not-found' });
  assert.throws(() => selectTryToStop({ records: [r1, r2] }), { code: 'stop-ambiguous' });
  assert.throws(() => selectTryToStop({ selector: 'story-a', records: [r1, rDup] }), { code: 'stop-ambiguous' });
  assert.throws(() => selectTryToStop({ selector: 'missing-uuid', records: [r1, r2] }), { code: 'stop-not-found' });
});
