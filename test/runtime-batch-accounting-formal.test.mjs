import test from 'node:test';
import assert from 'node:assert/strict';
import { projectAnswer, renderJson, summaryLine } from '../src/runtime-output.mjs';

// Contract: runtime-output.prompt.md incomplete-accounting rule and the Story's
// criterion 4 / Rules to check: only positively unsent work defaults to zero.
// Exhaustive finite domain: 5 incomplete-evidence variants × 3 known lower
// bounds × 3 reported totals × 3 terminal states = 135 independent receipts.
// This is a bounded check of projection/rendering, not receipt recovery or an
// unbounded proof. No transport, filesystem cache or provider is involved.
test('2655 formal: incomplete call accounting never invents a total in 135 bounded receipts', () => {
  const evidence = [
    { name: 'usage flag', usage: { accounting_complete: false }, report: {}, unknown: 1 },
    { name: 'report flag', usage: {}, report: { accounting_complete: false }, unknown: 1 },
    { name: 'one unknown', usage: { unknown_calls: 1 }, report: {}, unknown: 1 },
    { name: 'three unknown', usage: { unknown_calls: 3 }, report: {}, unknown: 3 },
    { name: 'false with zero unknown', usage: { accounting_complete: false, unknown_calls: 0 }, report: {}, unknown: 1 },
  ];
  let cases = 0;
  for (const incomplete of evidence)
    for (const known of [0, 2, undefined])
      for (const calls of [0, 3, 'unknown'])
        for (const state of ['passed', 'failed', 'refused']) {
          const context = JSON.stringify({ evidence: incomplete.name, known, calls, state });
          const usage = { calls, ...incomplete.usage, ...(known === undefined ? {} : { known_calls: known }) };
          const view = projectAnswer({ state, usage, result: { report: incomplete.report } });
          // The client carries these projection fields as internal row metadata;
          // use that same shape, then check the real public JSON boundary.
          const row = { story: 'recover-retried-check-results', test: 'accounting', phase: 'server',
            state: view.state, calls: view.calls, known_calls: view.known_calls, unknown_calls: view.unknown_calls };
          const json = renderJson({ repo: 'fixture', rows: [row], exitCode: 0 });
          const lowerBound = known ?? (typeof calls === 'number' ? calls : 0);
          const expectedUsage = `${lowerBound} AI call${lowerBound === 1 ? '' : 's'} + ${incomplete.unknown} unknown`;
          assert.equal(view.calls, 'unknown', `projection must not invent total: ${context}`);
          assert.equal(json.rows[0].calls, 'unknown', `public row must not invent total: ${context}`);
          for (const line of [summaryLine([row]), json.summary_line, json.rows[0].summary_line])
            assert.equal(line.split(' · ').at(-1), expectedUsage, `retain lower bound and unknown component: ${context}`);
          cases++;
        }
  assert.equal(cases, 135);

  // Ordinary complete receipts retain their numeric total and existing format;
  // known_calls alone must not override a complete reported total.
  for (const state of ['passed', 'failed', 'refused']) {
    const view = projectAnswer({ state, usage: { calls: 3, known_calls: 2, accounting_complete: true, unknown_calls: 0 }, result: { report: { accounting_complete: true } } });
    const row = { story: 'ordinary', phase: 'server', ...view };
    const json = renderJson({ repo: 'fixture', rows: [row], exitCode: 0 });
    assert.equal(json.rows[0].calls, 3, state);
    assert.equal(json.summary_line.split(' · ').at(-1), '3 AI calls', state);
  }
});
