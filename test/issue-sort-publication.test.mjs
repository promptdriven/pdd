import test from 'node:test';
import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { stepDone, approveRun } from '../src/workflow-runner.mjs';
import { writeRun } from '../src/workflow-runs.mjs';
import { readDependencySnapshot } from '../src/issue-dependencies-github.mjs';
import { fixture as workflow } from './helpers/workflow-runner-fixture.mjs';
import { fixture as sortWorld, repository, key } from './helpers/issue-sort-fixture.mjs';

test('an umbrella code PR references its members and reserves closure for post-merge sorts', async t => {
  for (const unsafe of [false, true]) {
  const f = await workflow(t);
  assert.equal((await f.run()).exitCode, 0);
  let run = f.record(); f.tick();
  assert.equal((await stepDone({ step: 'scope', summary: 'Fix the shared cause.', cwd: run.root }, f.agentPorts())).exitCode, 0);
  f.tick(); assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  run = f.record();
  const w = sortWorld([17,18,19,20]);
  w.issues[0].body = '<!-- pdd-issue-group:v1 shared-context -->';
  await w.ports.sortGroups.save({ groups: [{ area: 'default', rootCause: 'shared-context', umbrella: key(17), members: [key(18),key(19),key(20)] }] });
  for (const n of [17,18,19,20]) { w.save(w.record(n)); w.review(n); }
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
  for (const n of [18,19,20]) {
    assert.equal(f.prs[0].body.includes(`Closes ${key(n)}`), false);
    assert.equal(f.prs[0].body.includes(`Refs ${key(n)}`), !unsafe);
  }
  }
});

test('a group code PR emits Closes #A, Closes #B for members with reproduce and test evidence and splits out failed members', async t => {
  const f = await workflow(t);
  assert.equal((await f.run()).exitCode, 0);
  let run = f.record(); f.tick();
  assert.equal((await stepDone({ step: 'scope', summary: 'Fix the shared cause.', cwd: run.root }, f.agentPorts())).exitCode, 0);
  f.tick(); assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  run = f.record();
  const w = sortWorld([17, 18, 19, 20]);
  await w.ports.sortGroups.save({ groups: [{ area: 'default', rootCause: 'shared-context', umbrella: key(17), members: [key(17), key(18), key(19), key(20)] }] });
  for (const n of [17, 18, 19, 20]) { w.save(w.record(n, { paths: ['src/cli.mjs'], symbol: 'parseArgs' })); w.review(n); }
  const members = [17, 18, 19, 20].map(key);
  const groupClaims = members.map((issue, index) => ({ issue, commentId: String(500 + index), labelEventId: String(600 + index), coordinatorId: 'coordinator', machine: 'test-machine' }));
  run.automaticOrigin = { repository, coordinatorId: 'coordinator', machine: 'test-machine', claim: { commentId: '500', labelEventId: '600' },
    group: { umbrella: key(17), members, owningModule: 'src/cli.mjs', signal: 'symbol:parseArgs' }, groupClaims };
  writeRun(run, f.ports);
  const memberEvidence = (number, passed = true) => ({
    reproduce: { confirmed: true, owningModule: 'src/cli.mjs', symbol: 'parseArgs', summary: `Reproduced #${number} on parseArgs` },
    test: { passed, name: 'test/cli.test.mjs', summary: passed ? `Case ${number} passed` : 'No passing test was recorded' },
  });
  writeFileSync(join(run.runDir, 'member-evidence.json'), JSON.stringify({
    [key(17)]: memberEvidence(17),
    [key(18)]: memberEvidence(18),
    [key(19)]: memberEvidence(19),
    [key(20)]: { ...memberEvidence(20, false), failed: true, splitOut: true, reason: 'different-module' },
  }, null, 2));
  const releasedClaims = [];
  const ports = f.agentPorts({
    sortGroups: w.ports.sortGroups,
    github: w.ports.github,
    owners: { read: async () => ({ json: JSON.stringify({ localOwner: 'coordinator', claims: groupClaims.map(claim => ({ ...claim, active: true, owner: 'coordinator' })) }) }) },
    releaseCoordinatorIssueClaim: async ({ claim }) => { releasedClaims.push(claim.issue); return { state: 'released' }; },
    readDependencySnapshot: async () => readDependencySnapshot({ repository }, w.ports),
  });
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n');
  f.git(run.root, 'add', '.'); f.git(run.root, 'commit', '-qm', 'One shared fix');
  for (const step of ['change', 'verify', 'formal']) {
    f.tick();
    if (step === 'verify') writeFileSync(join(run.runDir, 'verify.md'), 'Focused synthetic cases passed.\n');
    const result = await stepDone({ step, summary: 'The shared behavior works.', cwd: run.root }, ports);
    assert.equal(result.exitCode, 0, result.message);
  }
  assert.equal(f.prs.length, 1);
  assert.match(f.prs[0].body, /Closes #17, Closes #18, Closes #19/);
  assert.equal(f.prs[0].body.includes('Closes #20'), false);
  assert.deepEqual(releasedClaims, [key(20)]);
  const savedGroups = (await w.ports.sortGroups.read({ repository })).groups;
  assert.deepEqual(savedGroups[0].members, [key(17), key(18), key(19)]);
  assert.deepEqual(savedGroups[0].splitOut, [key(20)]);
});

test('a group with an unproved leader keeps that run and releases only peers', async t => {
  const f = await workflow(t);
  assert.equal((await f.run()).exitCode, 0);
  let run = f.record(); f.tick();
  assert.equal((await stepDone({ step: 'scope', summary: 'Fix the shared cause.', cwd: run.root }, f.agentPorts())).exitCode, 0);
  f.tick(); assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  run = f.record();
  const w = sortWorld([17, 18]);
  const members = [key(17), key(18)];
  await w.ports.sortGroups.save({ groups: [{ area: 'default', umbrella: key(17), members }] });
  for (const n of [17, 18]) { w.save(w.record(n, { paths: ['src/cli.mjs'], symbol: 'parseArgs' })); w.review(n); }
  const groupClaims = members.map((issue, index) => ({ issue, commentId: String(500 + index), labelEventId: String(600 + index), coordinatorId: 'coordinator', machine: 'test-machine' }));
  const leaderClaim = groupClaims[0];
  run.automaticOrigin = { repository, coordinatorId: 'coordinator', machine: 'test-machine',
    claim: { commentId: leaderClaim.commentId, labelEventId: leaderClaim.labelEventId },
    group: { umbrella: key(17), members, owningModule: 'src/cli.mjs', signal: 'symbol:parseArgs' }, groupClaims };
  writeRun(run, f.ports);
  writeFileSync(join(run.runDir, 'member-evidence.json'), JSON.stringify({
    [key(18)]: {
      reproduce: { confirmed: true, owningModule: 'src/cli.mjs', symbol: 'parseArgs', summary: 'Reproduced member #18.' },
      test: { passed: true, name: 'test/cli.test.mjs', summary: 'Member #18 passed.' },
    },
  }));
  const releasedClaims = [];
  const ports = f.agentPorts({
    sortGroups: w.ports.sortGroups,
    github: w.ports.github,
    owners: { read: async () => ({ json: JSON.stringify({ localOwner: 'coordinator',
      claims: groupClaims.map(claim => ({ ...claim, active: true, owner: 'coordinator' })) }) }) },
    releaseCoordinatorIssueClaim: async ({ claim }) => { releasedClaims.push(claim.issue); return { state: 'released' }; },
  });
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n');
  f.git(run.root, 'add', '.'); f.git(run.root, 'commit', '-qm', 'Shared fix without leader reproduction');
  for (const step of ['change', 'verify', 'formal']) {
    f.tick();
    if (step === 'verify') writeFileSync(join(run.runDir, 'verify.md'), 'Synthetic focused cases passed.\n');
    const result = await stepDone({ step, summary: 'The shared behavior works.', cwd: run.root }, ports);
    if (step === 'formal') {
      assert.notEqual(result.exitCode, 0, 'an unproved leader must hold group publication');
      assert.match(result.message, /leader lacks matching reproduction or passing test evidence/i);
    } else assert.equal(result.exitCode, 0, result.message);
  }
  assert.equal(f.prs.length, 0);
  run = f.record();
  assert.equal(run.issue.url, key(17), 'the original worktree stays attached to its leader');
  assert.equal(run.groupHold.reason, 'leader-reproduction-unconfirmed');
  assert.deepEqual(releasedClaims, [key(18)], 'only the peer claim is released');
  assert.equal(run.automaticOrigin.claim.commentId, leaderClaim.commentId);
  assert.deepEqual(run.automaticOrigin.groupClaims.map(claim => claim.issue), [key(17)]);
});
