import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { projectAnswer } from '../../src/runtime-seam.mjs';

// 4 depths × 2 reference states = 8 bounded preservation cases. Alternating
// object/array containers also check full pointer escaping and authored order.
test('PREDECESSOR formal: deep traversal in 8 bounded cases', () => {
  let cases = 0;
  for (const depth of [0, 1, 100, 3500]) for (const hasReference of [false, true]) {
    const reference = () => ({ $step_result: { step_id: 'load', path: '/loaded ' } });
    let nested = hasReference ? reference() : null;
    for (let i = depth - 1; i >= 0; i--) nested = i % 2 ? [nested] : { ' a/~ ': nested };
    const pointer = '/deep' + Array.from({ length: depth }, (_, i) => i % 2 ? '/0' : '/ a~1~0 ').join('');
    const steps = [{ step_id: 'load', input: {} }, { step_id: 'show', input: {
      first: reference(), deep: nested, last: [reference()]
    } }];
    const answer = { command: 'check', state: 'refused', usage: { calls: 2 }, result: {
      refusals: [{ code: 'key-error', section: 'samples[0].steps[1]' }],
      report: { samples: [{ steps: [{ step_id: 'load', result: null, error: { code: 'unavailable' } }] }] }
    } };
    const before = JSON.stringify({ answer, steps }); let view;
    assert.doesNotThrow(() => { view = projectAnswer(answer, { steps }); },
      `PREDECESSOR deep traversal preserves output at depth ${depth} reference ${hasReference}`);
    const fact = input_path => ({ step_id: 'show', input_path, predecessor_step_id: 'load', result_path: '/loaded ', error_code: 'unavailable' });
    assert.deepEqual(view.refusals[0].dependency_errors,
      [fact('/first'), ...(hasReference ? [fact(pointer)] : []), fact('/last/0')]);
    const unchanged = { ...view, refusals: view.refusals.map(({ dependency_errors, ...refusal }) => refusal) };
    assert.deepEqual(unchanged, projectAnswer(answer), 'deep traversal cannot change non-diagnostic evidence');
    assert.equal(JSON.stringify({ answer, steps }), before, 'deep traversal cannot mutate authored data');
    cases++;
  }
  assert.equal(cases, 8);
});

// Synthetic bounded inputs from show-predecessor-error.md Rules to check.
// 2 sample positions × 2 dependent positions × 3 reference variants ×
// 3 predecessor identities × 3 result variants × 3 code variants ×
// 2 reported-dependent-row states = 648 cases.
// This checks association only. It proves no live Runtime or application behavior.
// Control, to run separately after implementation:
// PDD_PREDECESSOR_CONTROL=drop node --test test/runtime-predecessor-errors.formal.test.mjs
// The control plants the old defect: it drops only the added projected field.
// A nonzero assertion exit is required; a crash is not a detecting control.
test('PREDECESSOR formal: exact same-sample association in 648 bounded cases', () => {
  let cases = 0, positives = 0;
  for (const sampleIndex of [0, 1])
    for (const dependentIndex of [1, 2])
      for (const reference of ['present', 'absent', 'malformed'])
        for (const identity of ['correct', 'wrong', 'duplicate'])
          for (const resultKind of ['error', 'normal', 'missing'])
            for (const codeKind of ['present', 'missing', 'redacted'])
              for (const dependentReported of [false, true]) {
              const label = JSON.stringify({ sampleIndex, dependentIndex, reference, identity, resultKind, codeKind, dependentReported });
              const steps = [{ step_id: 'load-record', input: {} }];
              if (dependentIndex === 2) steps.push({ step_id: 'unrelated', input: {} });
              const input = reference === 'present' ? { loaded: { $step_result: { step_id: 'load-record', path: '/loaded' } } }
                : reference === 'malformed' ? { loaded: { $step_result: { step_id: 'load-record', path: 7 } } } : {};
              steps.push({ step_id: 'show-record', input });
              const predecessor = { step_id: identity === 'wrong' ? 'other-record' : 'load-record', checks: [] };
              if (resultKind !== 'missing') {
                predecessor.result = resultKind === 'normal' ? { loaded: true } : null;
                predecessor.error = codeKind === 'missing' ? {} : { code: codeKind === 'redacted' ? '[secret]' : 'record-unavailable' };
              }
              const reported = [predecessor];
              if (dependentIndex === 2) reported.push({ step_id: 'unrelated', result: {}, checks: [] });
              if (dependentReported) reported.push({ step_id: 'show-record', checks: [] });
              if (identity === 'duplicate') reported.push({ ...predecessor });
              // The other sample deliberately has a tempting matching predecessor.
              const other = { steps: [{ step_id: 'load-record', result: null, error: { code: 'wrong-sample-code' }, checks: [] }] };
              const samples = sampleIndex ? [other, { steps: reported }] : [{ steps: reported }, other];
              const answer = { command: 'check', state: 'refused', usage: { calls: 2 }, result: {
                refusals: [{ code: 'key-error', section: `samples[${sampleIndex}].steps[${dependentIndex}]`, at: `steps[${dependentIndex}]` }], report: { samples } } };
              const view = projectAnswer(answer, { steps });
              const got = view.refusals[0];
              if (process.env.PDD_PREDECESSOR_CONTROL === 'drop') delete got.dependency_errors;
              // Oracle uses only the approved evidence conditions, never projected output.
              const supported = reference === 'present' && identity === 'correct' && resultKind === 'error' && codeKind === 'present';
              if (supported) {
                assert.deepEqual(got.dependency_errors, [{ step_id: 'show-record', input_path: '/loaded',
                  predecessor_step_id: 'load-record', result_path: '/loaded', error_code: 'record-unavailable' }],
                `PREDECESSOR supported fact must survive: ${label}`);
                positives++;
              } else assert.equal(Object.hasOwn(got, 'dependency_errors'), false, `PREDECESSOR unsupported association must be omitted: ${label}`);
              assert.equal(got.code, 'key-error', `PREDECESSOR refusal code must not change: ${label}`);
              cases++;
            }
  assert.equal(cases, 648);
  assert.equal(positives, 8);
});

// Exact section and agreement rules require typed location evidence. Optional
// absent/null companions remain valid legacy reports. 4 fields × 7 value kinds ×
// 2 sample positions × 2 reported-dependent-row states = 112 bounded cases.
test('PREDECESSOR formal: location types in 112 bounded cases', () => {
  let cases = 0, positives = 0;
  for (const field of ['section', 'at', 'field', 'where'])
    for (const kind of ['string', 'absent', 'null', 'array', 'object', 'number', 'boolean'])
      for (const sampleIndex of [0, 1]) for (const dependentReported of [false, true]) {
        const steps = [{ step_id: 'load', input: {} }, { step_id: 'show', input: {
          loaded: { $step_result: { step_id: 'load', path: '/loaded' } }
        } }];
        const anchor = `samples[${sampleIndex}].steps[1]`;
        const refusal = { code: 'key-error', section: anchor, at: 'steps[1]', field: anchor, where: `test/example.json ${anchor}` };
        const values = { string: anchor, null: null, array: [field === 'section' ? anchor : `samples[${1 - sampleIndex}].steps[0]`],
          object: {}, number: 1, boolean: false };
        if (kind === 'absent') delete refusal[field]; else refusal[field] = values[kind];
        const reported = [{ step_id: 'load', result: null, error: { code: 'unavailable' } }];
        if (dependentReported) reported.push({ step_id: 'show' });
        const other = { steps: [{ step_id: 'load', error: { code: 'wrong-sample' } }] };
        const samples = sampleIndex ? [other, { steps: reported }] : [{ steps: reported }, other];
        const answer = { command: 'check', state: 'refused', usage: { calls: 2 }, result: { refusals: [refusal], report: { samples } } };
        const view = projectAnswer(answer, { steps }), baseline = projectAnswer(answer);
        const supported = kind === 'string' || field !== 'section' && ['absent', 'null'].includes(kind);
        const label = JSON.stringify({ field, kind, sampleIndex, dependentReported });
        if (supported) {
          assert.deepEqual(view.refusals[0].dependency_errors, [{ step_id: 'show', input_path: '/loaded',
            predecessor_step_id: 'load', result_path: '/loaded', error_code: 'unavailable' }],
          `PREDECESSOR supported location types must retain association: ${label}`);
          positives++;
        } else assert.equal(Object.hasOwn(view.refusals[0], 'dependency_errors'), false,
          `PREDECESSOR malformed location types must omit association: ${label}`);
        const unchanged = structuredClone(view); delete unchanged.refusals[0].dependency_errors;
        assert.deepEqual(unchanged, baseline, `PREDECESSOR location types cannot alter other evidence: ${label}`);
        cases++;
      }
  assert.equal(cases, 112);
  assert.equal(positives, 40);
});

// The approved privacy/pointer rules also apply to the five new strings.
// 4 host-path delimiters × 4 pointer tokens = 16 bounded cases. Host-like
// pointer tokens remain pointers; ordinary spaces survive removed controls.
test('PREDECESSOR formal: diagnostic privacy and pointer structure in 16 bounded cases', () => {
  const delimiters = [':', '=', '(', ' '];
  const pointers = [
    { key: 'loaded ', path: '/loaded ', expected: '/loaded ' },
    { key: ' loaded', path: '/ loaded', expected: '/ loaded' },
    { key: ' loaded \u0007 ', path: '/ loaded \u0007 ', expected: '/ loaded  ' },
    { key: 'home', path: '/home/member ', expected: '/home/member ' }
  ];
  let cases = 0;
  for (const delimiter of delimiters) for (const pointer of pointers) {
    const predecessorId = `load${delimiter}/srv/private/predecessor`, dependentId = `show${delimiter}/srv/private/dependent`;
    const steps = [{ step_id: predecessorId, input: {} }, { step_id: dependentId,
      input: { [pointer.key]: { $step_result: { step_id: predecessorId, path: pointer.path } } } }];
    const answer = { command: 'check', state: 'refused', result: {
      refusals: [{ code: 'key-error', section: 'samples[0].steps[1]' }],
      report: { samples: [{ steps: [{ step_id: predecessorId, result: null,
        error: { code: `unavailable${delimiter}/srv/private/code` } }] }] }
    } };
    const facts = projectAnswer(answer, { steps }).refusals[0].dependency_errors;
    assert.equal(facts?.length, 1, 'PREDECESSOR safe partial identities retain the supported fact');
    assert.deepEqual(facts[0], { step_id: `show${delimiter}<server path>`,
      input_path: pointer.key === 'home' ? '/home' : pointer.expected,
      predecessor_step_id: `load${delimiter}<server path>`, result_path: pointer.expected,
      error_code: `unavailable${delimiter}<server path>` },
    `PREDECESSOR privacy/pointer oracle ${JSON.stringify({ delimiter, pointer })}`);
    cases++;
  }
  assert.equal(cases, 16);
});
