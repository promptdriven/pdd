import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {changeRun} from '../src/workflow-runner.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/workflow-expected-gate.json', import.meta.url)));
test('replay the expected gate Story vectors through changeRun', async t => {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  const saved = f.record();
  const scenarioRun = JSON.parse(scenario.simulation['runs.resolveRun'].cases[0].result.json).run;
  const path = join(saved.runDir, 'status.json');
  Object.assign(saved, scenarioRun);
  writeFileSync(path, JSON.stringify(saved));
  let lookups = 0;
  const execFile = f.ports.execFile;
  f.ports.execFile = async (file, args, opts) => {
    if (file === 'git' && args[0] === 'rev-parse' && args.includes('--show-toplevel')) lookups++;
    return execFile(file, args, opts);
  };
  for (const step of scenario.steps) {
    const {ref, cwd, ...input} = step.input;
    assert.equal(ref, '17'); assert.equal(cwd, '/repo');
    const result = await changeRun({ref, cwd:f.source, packageRoot, ...input}, f.ports);
    for (const check of step.checks) {
      assert.equal(check.op, 'equals');
      const actual = check.target === 'result' ? result[check.path.slice(1)] :
        check.target === 'world' && check.path === '/lookups' ? lookups : assert.fail(`Unknown check ${check.target}${check.path}`);
      assert.deepEqual(actual, check.value, `${step.step_id} ${check.target}${check.path}`);
    }
  }
});
