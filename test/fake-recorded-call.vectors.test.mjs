import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { lookup } from '../examples/fakes/service.mjs';
import { parseScenarioJson } from '../src/runtime-seam.mjs';
import { fixtureProject, clean, read, report, scenarioPath, sourceRoot } from './helpers/code-call-project.mjs';

function makeRepo(t, options) {
  const root = fixtureProject(options);
  t.after(() => clean(root));
  return root;
}

test('native saved-reply Story replay: actual CLI executes all eight unchanged checks in order', t => {
  const root = makeRepo(t);
  assert.equal(readFileSync(join(root, scenarioPath), 'utf8'), read(scenarioPath));
  const original = parseScenarioJson(read(scenarioPath));
  const { out, data } = report(root);
  assert.equal(out.status, 0, `NATIVE_SAVED_REPLY_REQUIRED: ${out.stderr}\n${out.stdout}`);
  assert.equal(data.ai_calls, 0);
  assert.equal(data.target, 'code');
  assert.equal(data.dirty, false);
  assert.equal(data.stories[0].status, 'passed');
  assert.deepEqual(data.stories[0].steps.map(step => step.step_id), original.steps.map(step => step.step_id));
  for (const [i, step] of data.stories[0].steps.entries()) {
    assert.equal(step.checks.length, original.steps[i].checks.length);
    for (const [j, check] of step.checks.entries()) {
      assert.equal(check.status, 'passed');
      for (const key of ['criterion_id', 'target', 'path', 'op']) {
        assert.equal(check[key], original.steps[i].checks[j][key]);
      }
      assert.deepEqual(check.expected, original.steps[i].checks[j].value);
      assert.deepEqual(check.actual, check.expected);
    }
  }
  assert.deepEqual(parseScenarioJson(readFileSync(join(root, '.pdd/code-test/latest.json'), 'utf8')), data);
});

test('semantic control changes native answer and fails original saved-reply assertions', t => {
  const root = makeRepo(t, {
    appChange: text => text.replace('return service.lookup({ id });', "return {...service.lookup({ id }),label:'WRONG_NATIVE_ANSWER'};"),
  });
  assert.equal(readFileSync(join(root, scenarioPath), 'utf8'), read(scenarioPath));
  const { out, data } = report(root);
  assert.equal(out.status, 1);
  assert.equal(data.stories[0].status, 'failed');
  const checks = data.stories[0].steps.flatMap(step => step.checks ?? []);
  assert.equal(checks.length, 8);
  assert.equal(checks.filter(check => check.status === 'failed').length, 2);
  assert.equal(checks[0].actual, 'WRONG_NATIVE_ANSWER');
  assert.equal(checks[0].expected, 'Available');
  assert.equal(checks[6].actual, 2, 'valid failed response still advances the fixture world');
});

test('existing fixed-service Story replays unchanged through exported lookup with supplied port world', () => {
  const doc = parseScenarioJson(readFileSync(join(sourceRoot, 'test/runtime/fake-service.json'), 'utf8'));
  const world = structuredClone(doc.initial_world);
  for (const step of doc.steps) {
    const binding = doc.simulation['service.lookup'];
    let calls = 0;
    const result = lookup({
      lookup(args) {
        calls++;
        world.requests.push(args);
        return binding.result_template;
      },
    }, step.input.id);
    assert.equal(calls, 1);
    for (const check of step.checks) {
      assert.equal(check.op, 'equals');
      const target = { result, world }[check.target];
      assert.ok(target, check.target);
      const actual = check.path.slice(1).split('/').reduce((value, key) => value[key], target);
      assert.deepEqual(actual, check.value, `${step.step_id} ${check.criterion_id} ${check.target} ${check.path}`);
    }
  }
});
