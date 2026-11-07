import test from 'node:test';
import assert from 'node:assert/strict';
import { outcomeFor, outcomeExitCode } from '../src/runtime-outcome.mjs';
import { pure, mutate } from './runtime-compatibility/replay.mjs';

// Approved Rules to check: old own/reached refusals win, matched concrete blockers
// refuse, ended unavailable readiness holds, only complete matched support admits.
// This checks supplied reports, not the engine's feature detector or OS schedules.
test('COMPAT bounded selected admission oracle (360 combinations)', t => {
  const fixture = pure(t);
  let count = 0;
  for (const variant of ['supported','unsupported','missing-binding','invalid-source','unknown'])
    for (const complete of [true,false]) for (const association of ['matched','mismatch','unavailable'])
      for (const own of ['pass','refusal','unlisted']) for (const lifecycle of ['passed','failed','refused','running']) {
        const answer = structuredClone(fixture.answer), options = structuredClone(fixture.options);
        const report = mutate(answer.result.capabilities[0].report, variant);
        if (!complete) {
          report.complete = false;
          if (variant === 'supported') { report.verdict = 'unknown'; Object.assign(report.operations[0], { verdict: 'unknown', reason_code: 'analysis-unavailable' }); }
        }
        answer.result.report.lint.tests[0].capabilities = report;
        answer.state = lifecycle;
        if (association === 'mismatch') options.sourceFiles.find(file => file.path === options.test).sha256 = 'd'.repeat(64);
        if (association === 'unavailable') delete options.sourceFiles;
        if (own === 'refusal') answer.result.refusals = [{ file: options.test, code: 'own-refusal' }];
        if (own === 'unlisted') answer.result.report.lint.tests = [];
        const concrete = ['unsupported','missing-binding','invalid-source'].includes(variant);
        const expected = lifecycle === 'running' ? 'running'
          : own === 'refusal' || own === 'unlisted' && lifecycle === 'refused' ? 'refused'
          : own === 'unlisted' ? 'not_run'
          : association !== 'matched' ? 'not_run'
          : concrete ? 'refused'
          : variant === 'supported' && complete ? 'passed' : 'not_run';
        const actual = outcomeFor(answer, options);
        const identity = `${variant}/${complete}/${association}/${own}/${lifecycle}`;
        assert.equal(actual.state, expected, `COMPAT admission rule ${identity}`);
        assert.equal(outcomeExitCode([actual]), { running:3, refused:4, not_run:5, passed:0 }[expected], `COMPAT exit rule ${identity}`);
        count++;
      }
  assert.equal(count, 360);
});
