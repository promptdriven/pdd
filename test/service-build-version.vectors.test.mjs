import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { runDetailedVersion } from '../src/interpreter-version.mjs';

const pointer = (value, path) => path.slice(1).split('/').reduce((row, key) => row?.[key.replaceAll('~1', '/').replaceAll('~0', '~')], value);

test('replay every approved service-build-version check through runDetailedVersion', async t => {
  const scenario = JSON.parse(readFileSync(new URL('./runtime/service-build-version.json', import.meta.url), 'utf8'));
  const world = structuredClone(scenario.initial_world);
  let fixtureErrors;
  const port = name => args => {
    const fixture = scenario.simulation[name], counter = fixture.world_pointer.split('/').at(-1);
    const index = ++world.counters[counter];
    const row = fixture.cases.find(row => row.call_index === index);
    try {
      assert.ok(row, `${name} fixture ${index}`);
      assert.deepEqual(JSON.parse(JSON.stringify(args)), row.args, `${name} arguments`);
    } catch (error) {
      fixtureErrors.push(error);
      throw error;
    }
    return structuredClone(row.result);
  };
  const ports = {
    resolveOrigin: port('origin.resolve'),
    readToken: port('credentials.readToken'),
    getMetadata: port('metadata.get'),
  };
  for (const step of scenario.steps) await t.test(step.step_id, async st => {
    assert.equal(step.operation, 'runDetailedVersion');
    assert.equal(step.entry_path, 'prompts/cli/interpreter-version.prompt.md');
    fixtureErrors = [];
    const result = await runDetailedVersion(step.input, ports);
    assert.deepEqual(fixtureErrors, [], 'all fixture arguments matched the scenario');
    for (const check of step.checks) await st.test(`${check.criterion_id} ${check.target} ${check.path}`, () => {
      assert.equal(check.op, 'equals');
      assert.equal(check.target, 'result');
      assert.deepEqual(pointer(result, check.path), check.value);
    });
  });
});
