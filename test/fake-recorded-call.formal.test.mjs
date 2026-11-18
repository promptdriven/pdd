import { test } from 'node:test';
import assert from 'node:assert/strict';
import { fixtureProject, pureProject, clean, report, seamModule } from './helpers/code-call-project.mjs';

// Oracles come from the Story's rules: preserve whole numbers, advance fixture
// counters in order, and restart per-step call counts. A fresh formal actor owns
// the verdict. Builder execution provides implementation feedback only.
const integerSchema = { type: 'object', properties: { id: { type: 'integer' } }, required: ['id'], additionalProperties: false };
const check = (criterion_id, target, path, value) => ({ criterion_id, target, path, op: 'equals', value });
const control = process.env.PDD_NATIVE_FORMAL_CONTROL;
const makeRepo = (options, pure = false) => (pure ? pureProject : fixtureProject)(options);

test('bounded Story rule: all 15 whole numbers at three signed integer boundaries survive native transport exactly', () => {
  let exercised = 0;
  for (const center of [-9007199254740992n, 9007199254740992n, 9223372036854775807n]) {
    for (let offset = -2n; offset <= 2n; offset++) {
      const value = center + offset;
      const root = makeRepo(
        {
          inputSchema: integerSchema,
          resultSchema: integerSchema,
          change: doc => {
            doc.initial_world = { sentinel: value };
            for (const step of doc.steps) {
              const id = step.checks[0].criterion_id;
              step.input = { id: value };
              step.checks = [check(id, 'result', '/id', value), check(id, 'world', '/sentinel', value)];
            }
          },
          ...(control === 'integer'
            ? {
                app: `import {parseScenarioJson,stringifyScenarioJson} from ${JSON.stringify(seamModule)};let raw='';for await(const c of process.stdin)raw+=c;const r=parseScenarioJson(raw);const id=typeof r.input.id==='bigint'?r.input.id+1n:r.input.id+1;process.stdout.write(stringifyScenarioJson({schema_version:r.schema_version,result:{id},world:r.initial_world,calls:{resources:{},internal:{}}}));`,
              }
            : {}),
        },
        true
      );
      try {
        const { out, data } = report(root);
        assert.equal(out.status, 0, `FORMAL_EXACT_INTEGER: ${value}: ${out.stdout}\n${out.stderr}`);
        for (const step of data.stories[0].steps) {
          assert.equal(BigInt(step.checks[0].actual), value);
          assert.equal(BigInt(step.checks[1].actual), value);
        }
        exercised++;
      } finally {
        clean(root);
      }
    }
  }
  assert.equal(exercised, 15);
});

test('bounded Story rule: all four initial counters 0..3 advance twice with one call per step and preserve other world values', () => {
  for (let start = 0; start <= 3; start++) {
    const root = makeRepo({
      change: doc => {
        doc.initial_world.fixture_counters.lookup = start;
        for (const [i, item] of doc.simulation['service.lookup'].cases.entries()) item.call_index = start + i + 1;
        for (const [i, step] of doc.steps.entries()) {
          step.checks.find(c => c.target === 'world' && c.path === '/fixture_counters/lookup').value = start + i + 1;
        }
      },
      ...(control === 'counter' ? { appChange: text => text.replace('return match.result;', 'return fixture.cases[0].result;') } : {}),
    });
    try {
      const { out, data } = report(root);
      assert.equal(out.status, 0, `FORMAL_ORDERED_COUNTER: start=${start}: ${out.stdout}\n${out.stderr}`);
      for (const [i, step] of data.stories[0].steps.entries()) {
        assert.equal(step.checks.find(c => c.target === 'world' && c.path === '/fixture_counters/lookup').actual, start + i + 1);
        assert.equal(step.checks.find(c => c.target === 'calls').actual, 1);
        assert.equal(step.checks.find(c => c.target === 'world' && c.path === '/note').actual, 'keep');
      }
    } finally {
      clean(root);
    }
  }
});
