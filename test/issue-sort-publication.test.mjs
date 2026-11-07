import test from 'node:test';
import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { stepDone, approveRun } from '../src/workflow-runner.mjs';
import { writeRun } from '../src/workflow-runs.mjs';
import { readDependencySnapshot } from '../src/issue-dependencies-github.mjs';
import { fixture as workflow } from './helpers/workflow-runner-fixture.mjs';
import { fixture as sortWorld, repository, key } from './helpers/issue-sort-fixture.mjs';

test('an umbrella code PR closes all three current group members through ordinary publication', async t => {
  for (const unsafe of [false, true]) {
  const f = await workflow(t);
  assert.equal((await f.run()).exitCode, 0);
  let run = f.record(); f.tick();
  assert.equal((await stepDone({ step: 'scope', summary: 'Fix the shared cause.', cwd: run.root }, f.agentPorts())).exitCode, 0);
  f.tick(); assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  run = f.record();
  const w = sortWorld([17,18,19]);
  for (const n of [17,18,19]) { w.save(w.record(n)); w.review(n); }
  const snapshot = (await readDependencySnapshot({ repository }, w.ports)).snapshot;
  if (unsafe) snapshot.coverage.issues.find(x => x.key === key(18)).comments = false;
  run.automaticOrigin = { repository, coordinatorId: 'coordinator', machine: 'test-machine', claim: { commentId: '500', labelEventId: '600' } };
  writeRun(run, f.ports);
  const ports = f.agentPorts({
    owners: { read: async () => ({ json: JSON.stringify({ localOwner: 'coordinator', claims: [{ issue: key(17), active: true, owner: 'coordinator', coordinatorId: 'coordinator', machine: 'test-machine', commentId: '500', labelEventId: '600' }] }) }) },
    readDependencySnapshot: async () => ({ snapshot }),
  });
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n');
  f.git(run.root, 'add', '.'); f.git(run.root, 'commit', '-qm', 'One shared fix');
  for (const step of ['change','verify','formal']) {
    f.tick();
    if (step === 'verify') writeFileSync(join(run.runDir, 'verify.md'), 'Focused synthetic cases passed.\n');
    const result = await stepDone({ step, summary: 'The shared behavior works.', cwd: run.root }, ports);
    assert.equal(result.exitCode, 0, result.message);
  }
  assert.equal(f.prs.length, 1);
  assert.match(f.prs[0].body, /Closes #17/);
  for (const n of [18,19]) assert.equal(f.prs[0].body.includes(`Closes ${key(n)}`), !unsafe);
  }
});
