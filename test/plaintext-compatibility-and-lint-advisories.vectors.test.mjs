import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';

const scenarioText = readFileSync(new URL('./runtime/plaintext-compatibility-and-lint-advisories.json', import.meta.url), 'utf8');
const scenario = JSON.parse(scenarioText, (key, value, context) =>
  typeof value === 'number' && /^-?(?:0|[1-9][0-9]*)$/.test(context.source) && !Number.isSafeInteger(value)
    ? BigInt(context.source)
    : value
);

async function loadDisplayModule() {
  try {
    return await import('../src/lint-compatibility-display.mjs');
  } catch (error) {
    if (error?.code === 'ERR_MODULE_NOT_FOUND') {
      assert.fail(
        'lint-compatibility-display module is missing; plain-text compatibility summary and severity-split lint advisories are unimplemented',
      );
    }
    throw error;
  }
}

test('issue3237 vector replay: all 6 approved scenario steps in order', async () => {
  const mod = await loadDisplayModule();
  assert.equal(scenario.steps.length, 6);
  const world = structuredClone(scenario.initial_world);
  const failures = [];

  for (const step of scenario.steps) {
    const fn = mod[step.operation];
    assert.equal(typeof fn, 'function', `expected exported operation ${step.operation}`);
    const input = structuredClone(step.input);
    const before = structuredClone(input);
    const result = fn(input);
    for (let checkIndex = 0; checkIndex < step.checks.length; checkIndex++) {
      const check = step.checks[checkIndex];
      assert.equal(check.target, 'result');
      assert.equal(check.path, '/text');
      assert.equal(check.op, 'equals');
      try {
        assert.deepEqual(result.text, check.value, `${check.criterion_id}: ${step.step_id}`);
      } catch (error) {
        failures.push([step.step_id, checkIndex, error.message]);
      }
    }
    assert.deepEqual(input, before, `display formatter must never mutate supplied inputs (${step.step_id})`);
  }

  assert.deepEqual(world, scenario.initial_world);
  assert.equal(
    failures.length,
    0,
    `Failed scenario checks (${failures.map(([stepId, checkIndex]) => `${stepId}[${checkIndex}]`).join(', ')}):\n${failures
      .map(([stepId, checkIndex, message]) => `[${stepId}#${checkIndex}] ${message}`)
      .join('\n')}`,
  );
});

test('issue3237 edge cases: empty/multi-mode structured, absent report, null advice, and diagnostic ordering', async () => {
  const { describeCompatibility, describeLintDiagnostics } = await loadDisplayModule();

  const emptyStructured = {
    label: 'tests/empty.json',
    compatibility: {
      state: 'supported',
      association: 'matched',
      issue: '   ',
      reported: {
        complete: true,
        engine_build: 'unknown',
        operations: [],
        edges: [],
      },
    },
  };
  const emptyBefore = structuredClone(emptyStructured);
  assert.deepEqual(describeCompatibility(emptyStructured), {
    text: 'Compatibility (tests/empty.json): supported (association matched); 0 steps (0 operations, 0 edges); execution none; resources none; complete true; engine unknown.',
  });
  assert.deepEqual(emptyStructured, emptyBefore);

  const multiMode = {
    label: 'tests/multi.json',
    clientAdvice: null,
    details: false,
    compatibility: {
      state: 'unsupported-capability',
      association: 'matched',
      issue: null,
      reported: {
        complete: false,
        engine_build: 'abcdef0123456789abcdef0123456789abcdef01',
        operations: [
          {
            selection: { step_id: 's1', node_id: 'n1', prompt_path: 'prompts/a.prompt.md', operation: 'opA' },
            execution_mode: 'ordinary',
            resource_mode: 'simulated',
            verdict: 'unsupported-capability',
            reason_code: 'retained-mutation-unsupported',
          },
          {
            selection: { step_id: 's2', node_id: 'n2', prompt_path: 'prompts/b.prompt.md', operation: 'opB' },
            execution_mode: 'streaming',
            resource_mode: 'live',
            verdict: 'unsupported-capability',
            reason_code: 'retained-mutation-unsupported',
          },
        ],
        edges: [
          {
            selection: {
              step_id: 's1',
              node_id: 'n1',
              prompt_path: 'prompts/a.prompt.md',
              operation: 'opA',
              edge: { edge_id: 'e1', kind: 'resource', call_operation: 'save', target_node_id: '', target_path: '', target_operation: '', resource_operation: 'save' },
            },
            execution_mode: 'ordinary',
            resource_mode: 'live',
            verdict: 'missing-binding',
            reason_code: 'binding-missing',
          },
          {
            selection: {
              step_id: 's2',
              node_id: 'n2',
              prompt_path: 'prompts/b.prompt.md',
              operation: 'opB',
              edge: { edge_id: 'e2', kind: 'internal', call_operation: 'callB', target_node_id: 'n2', target_path: 'prompts/b.prompt.md', target_operation: 'opB', resource_operation: '' },
            },
            execution_mode: 'streaming',
            resource_mode: 'simulated',
            verdict: 'supported',
            reason_code: 'supported',
          },
        ],
      },
    },
  };
  assert.deepEqual(describeCompatibility(multiMode), {
    text: 'Compatibility (tests/multi.json): unsupported-capability (association matched); 2 steps (2 operations, 2 edges); execution ordinary, streaming; resources simulated, live; complete false; engine abcdef012345; non-supported: retained-mutation-unsupported, binding-missing.',
  });

  const absentReport = {
    label: 'place-order / tests/place-order.json',
    compatibility: {
      state: 'unknown',
      association: 'unknown',
      issue: 'capability-report-absent',
      reported: null,
    },
  };
  assert.deepEqual(describeCompatibility(absentReport), {
    text: 'Compatibility (place-order / tests/place-order.json): unknown (association unknown); issue capability-report-absent.',
  });
  assert.deepEqual(describeCompatibility({ ...absentReport, details: true }), {
    text: `Compatibility (place-order / tests/place-order.json): ${JSON.stringify(absentReport.compatibility, null, 2)}`,
  });

  assert.deepEqual(describeLintDiagnostics({ problems: [] }), { text: '' });
  const mixedProblems = [
    { code: 'advisory-first', path: 'prompts/a.prompt.md', section: null, message: 'First advisory.', hint: '   ', severity: 'warning' },
    { code: 'omitted-severity', path: 'prompts/b.prompt.md', section: 'Runtime interface', message: 'Blocking without severity.' },
    { code: 'advisory-second', path: null, section: null, message: 'Second advisory.', hint: 'Optional improvement.', severity: 'warning' },
    { code: 'explicit-error', path: 'prompts/c.prompt.md', section: '/limits', message: 'Blocking error.', hint: 'Fix /limits.', severity: 'error' },
  ];
  const problemsBefore = structuredClone(mixedProblems);
  assert.deepEqual(describeLintDiagnostics({ problems: mixedProblems }), {
    text: [
      'Lint problems (from the PDD interpreter):',
      '  omitted-severity  prompts/b.prompt.md  Runtime interface  Blocking without severity.',
      '  explicit-error  prompts/c.prompt.md  /limits  Blocking error.',
      '    Fix /limits.',
      'Lint advisories (from the PDD interpreter):',
      '  advisory-first  prompts/a.prompt.md  First advisory.',
      '  advisory-second  Second advisory.',
      '    Optional improvement.',
    ].join('\n'),
  });
  assert.deepEqual(mixedProblems, problemsBefore);
});
