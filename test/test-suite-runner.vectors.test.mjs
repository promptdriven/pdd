import test from 'node:test';
import assert from 'node:assert/strict';
import { EventEmitter } from 'node:events';
import { existsSync, readFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { PassThrough } from 'node:stream';

const repo = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const runnerPath = resolve(repo, 'src/test-suite-runner.mjs');
const vectorPath = resolve(repo, 'test/runtime/test-suite-isolation.json');
const scenario = JSON.parse(readFileSync(vectorPath, 'utf8'));

function pointer(value, path) {
  if (path === '') return value;
  assert.ok(path.startsWith('/'), `Unsupported JSON Pointer: ${path}`);
  return path.slice(1).split('/').reduce((current, token) => {
    const key = token.replaceAll('~1', '/').replaceAll('~0', '~');
    return current?.[key];
  }, value);
}

function fakeChild() {
  const child = new EventEmitter();
  child.stdout = new PassThrough();
  child.stderr = new PassThrough();
  return child;
}

test('the approved runtime JSON replays every public call and check in order', { skip: !existsSync(runnerPath) }, async () => {
  const { runTestSuite } = await import(pathToFileURL(runnerPath).href);
  const world = structuredClone(scenario.initial_world);
  const checks = [];
  const cases = scenario.simulation['nodeTest.run'].cases;

  for (const step of scenario.steps) {
    assert.equal(step.operation, 'runTestSuite');
    const callIndex = world.kv.node_test_calls + 1;
    const expected = cases.find(item => item.call_index === callIndex);
    assert.ok(expected, `No approved nodeTest.run case for call ${callIndex}`);
    const stepCalls = [];
    const result = await runTestSuite({
      cwd: step.input.cwd,
      testFiles: step.input.testFiles,
      environment: step.input.environment,
    }, {
      nodeTest: {
        run(options) {
          stepCalls.push(options);
          assert.deepEqual(options, expected.args, `${step.step_id}: nodeTest.run arguments`);
          const child = fakeChild();
          setImmediate(() => child.emit('close', expected.result.exit_code));
          return child;
        },
      },
    });
    world.kv.node_test_calls += stepCalls.length;

    for (const [check_index, check] of step.checks.entries()) {
      assert.equal(check.op, 'equals', `${step.step_id}/${check_index}: unsupported operation`);
      let target;
      if (check.target === 'result') target = result;
      else if (check.target === 'calls') {
        target = { resources: { 'test-suite-runner-nodeTest-run': stepCalls.length } };
      } else {
        assert.fail(`Not replayed: ${step.step_id}/${check_index} target ${check.target}`);
      }
      const actual = pointer(target, check.path);
      assert.deepEqual(actual, check.value, `${step.step_id}/${check_index} ${check.criterion_id} ${check.target}${check.path}`);
      checks.push({ step_id: step.step_id, check_index, outcome: 'pass' });
    }
  }

  const totalChecks = scenario.steps.reduce((sum, step) => sum + step.checks.length, 0);
  assert.equal(checks.length, totalChecks);
  assert.ok(checks.every(row => row.outcome === 'pass'));
  assert.equal(world.kv.node_test_calls, scenario.steps.length);
});
