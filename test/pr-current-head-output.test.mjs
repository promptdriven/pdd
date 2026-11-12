import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { renderJson, renderText } from '../src/runtime-seam.mjs';

test('authored criterion coverage remains structural for passed and failed text and JSON', () => {
  for (const state of ['passed', 'failed']) {
    const row = { story: 'release', title: 'Release', test: 'release.json', state,
      criterion_texts: { AC1: 'Prints release', AC2: 'Exits', AC3: 'Empty' },
      steps: [{ checks: [{ criterion_id:'AC1', target:'result', path:'/stdout' }, { criterion_id:'AC2', target:'result', path:'/exit_code' }] },
        { checks: [{ criterion_id:'AC2', target:'result', path:'/exitCode' }, { criterion_id:'AC4', target:'result', path:'/exit_code' }] }] };
    const rows = [row], exitCode = state === 'passed' ? 0 : 1;
    assert.deepEqual(renderJson({ rows, exitCode }).rows[0].criterion_coverage, [
      { criterion_id:'AC1', check_count:1, exit_code_only:false }, { criterion_id:'AC2', check_count:2, exit_code_only:true },
      { criterion_id:'AC3', check_count:0, exit_code_only:false }, { criterion_id:'AC4', check_count:1, exit_code_only:true }]);
    const text = renderText({ rows, exitCode });
    assert.match(text, /criterion AC2: Exits — checked by exit code only/);
    assert.match(text, /criterion AC4: — checked by exit code only/);
    assert.doesNotMatch(text, /criterion AC1: Prints release — checked/);
    assert.equal(renderJson({ rows: [{...row, steps: undefined}], exitCode }).rows[0].criterion_coverage, null);
  }
});

test('unavailable or malformed authored checks leave coverage unknown without changing the verdict', () => {
  const exitCheck = { criterion_id:'AC1', target:'result', path:'/exit_code' };
  for (const steps of [null, {}, [null], [{}], [{checks:null}], [{checks:{}}],
    [{checks:[null]}], [{checks:[{}]}], [{checks:[{criterion_id:''}]}],
    [{checks:[exitCheck]}, {checks:[null]}]]) {
    const row = { story:'legacy', title:'Legacy', test:'legacy.json', state:'passed',
      criterion_texts:{AC1:'Exits'}, steps };
    let result;
    assert.doesNotThrow(() => { result = renderJson({rows:[row], exitCode:0}); }, 'malformed saved coverage must not escape rendering');
    assert.equal(result.rows[0].criterion_coverage, null, 'partial or malformed authored facts cannot establish a count');
    assert.equal(result.rows[0].state, 'passed');
    assert.equal(result.exit_code, 0);
    assert.doesNotMatch(renderText({rows:[row], exitCode:0}), /checked by exit code only/);
  }
});
