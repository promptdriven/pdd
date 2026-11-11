import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync, readdirSync, statSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {approveRun, changeRun, cancelRun, openRun} from '../src/workflow-runner.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';

const snapshot = dir => Object.fromEntries(readdirSync(dir, {recursive:true}).filter(p => statSync(join(dir,p)).isFile()).sort().map(p => [p, readFileSync(join(dir,p)).toString('base64')]));

test('bounded stale expectations preserve saved files and produce no chat effects', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
  const original = f.record(), path = join(original.runDir, 'status.json');
  let cases = 0;
  for (const [name, action] of Object.entries({changes:changeRun, approve:approveRun, cancel:cancelRun, open:openRun})) {
    for (const gate of [null, 'g1']) for (const step of [null, 's1']) {
      const run = structuredClone(original);
      run.gate = gate ? {id:gate} : null;
      run.areas = [{name:'code',steps: step ? [step] : []}]; run.area = 0; run.done = {};
      for (const expected of [{expectGate:'other'}, {expectStep:'other'}, {expectGate:gate ?? 'other',expectStep:'other'}, {expectGate:'other',expectStep:step ?? 'other'}]) {
        writeFileSync(path, JSON.stringify(run));
        const before = snapshot(run.runDir); f.herdr.calls.length = 0;
        const result = await action({ref:'17',cwd:f.source,packageRoot,text:'Fix it',area:'story',newSession:true,...expected}, f.ports);
        assert.equal(result.exitCode,3,`${name} ${JSON.stringify({gate,step,expected})}: ${result.message}`);
        assert.ok(result.message.includes(gate ?? 'none'), result.message);
        assert.ok(result.message.includes(step ?? 'none'), result.message);
        assert.deepEqual(snapshot(run.runDir),before);
        assert.equal(f.herdr.calls.length,0);
        cases++;
      }
    }
  }
  assert.equal(cases,64);
});
