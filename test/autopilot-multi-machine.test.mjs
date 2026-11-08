import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { join } from 'node:path';
import { autopilotGithubWorld, analysisFor } from './helpers/autopilot-github-world.mjs';
import { createGithubRepoFake } from './helpers/github-repo-fake.mjs';
import { createDependencyReadPorts } from '../src/issue-dependencies-github.mjs';
import { checkDependencyStart, completeDependencyIntake } from '../src/issue-dependencies-intake.mjs';

const repo = 'acme/widgets', minute = 60000;
const key = n => `https://github.com/${repo}/issues/${n}`;
async function fleet(t, count = 4) {
  const clock = { now: Date.parse('2026-11-07T12:00:00Z') };
  const github = createGithubRepoFake({ repository: repo, issues: 8, now: () => clock.now });
  const machines = [];
  for (let i = 0; i < count; i++) {
    const world = await autopilotGithubWorld({ issues: 8, sharedGithub: github, machine: `machine-${i}` });
    machines.push(world); t.after(() => world.cleanup());
  }
  const advance = ms => { clock.now += ms; for (const w of machines) w.time = clock.now; };
  return { machines, github, advance, clock };
}
const claimPorts = w => createDependencyReadPorts({ cwd: w.cwd }, w.commandPorts());
async function claim(w, n) {
  const state = w.state();
  w.github.claim(n, state);
  const observed = JSON.parse((await claimPorts(w).owners.read({ repository: repo, issues: [key(n)] })).json);
  return observed.claims[0];
}
async function allowed(w, n, winning) {
  const state = w.state();
  return checkDependencyStart({ cwd: w.cwd, repository: repo, issue: key(n), coordinator: {
    repository: repo, coordinatorId: state.coordinatorId, machine: state.machine, activation: state.activatedAt,
    claim: { commentId: winning.commentId, labelEventId: winning.labelEventId },
  } }, w.commandPorts());
}

test('four machines share one reviewer, one issue owner and one merge actor; dead owner and reviewer expire', async t => {
  const { machines, github, advance } = await fleet(t);
  const started = await Promise.all(machines.map(w => w.invoke('start')));
  assert.deepEqual(started.map(r => r.exitCode), [0, 0, 0, 0]);
  assert.equal(machines.reduce((n, w) => n + w.requests.length, 0), 1, 'one repository analysis request, not four');
  const reviewer = machines.find(w => w.requests.length);
  const first = reviewer.requests[0];
  assert.equal((await reviewer.complete(first)).exitCode, 0);
  await reviewer.idle();
  for (const w of machines) { w.agent = 'idle'; await w.tick(); }
  assert.equal(machines.reduce((n, w) => n + w.requests.length, 0), 1, 'saved reviews are reused');
  for (let n = 1; n <= 8; n++) assert.equal(github.reviewComments(n).length, 1, `issue ${n} reviewed once`);

  // Issue claims keep their existing event winner even when all four contenders race.
  for (const w of [reviewer, ...machines.filter(w => w !== reviewer)]) github.claim(1, w.state());
  let winning = JSON.parse((await claimPorts(machines[0]).owners.read({ repository: repo, issues: [key(1)] })).json).claims[0];
  const decisions = await Promise.all(machines.map(w => allowed(w, 1, winning)));
  assert.equal(decisions.filter(r => r.allowed).length, 1, 'one accepted workflow owner');
  // The merge skill requires this same current winning ownership. Count its permitted actors,
  // without pretending this native test executes an AI skill or GitHub's merge service.
  const mergeActors = machines.filter((_, i) => decisions[i].allowed);
  assert.equal(mergeActors.length, 1, 'one permitted merge actor for the issue PR');
  for (let i = 0; i < machines.length; i++) await claim(machines[i], i + 2);
  const status = await machines[3].invoke('status');
  assert.equal(status.exitCode, 0);
  for (const w of machines) { assert.ok(status.message.includes(w.state().machine)); assert.ok(status.message.includes(w.state().coordinatorId)); }
  assert.ok(status.message.includes(reviewer.state().coordinatorId));
  assert.match(status.message, /#2.*|#3.*|#4.*|#5.*/);
  await machines[3].tick();
  const warnings = machines[3].warnings.filter(text => /login acme/.test(text));
  assert.equal(warnings.length, 1);
  await machines[3].tick();
  assert.equal(machines[3].warnings.filter(text => /login acme/.test(text)).length, 1, 'shared login warned once');

  // Leave the reviewer dead and change a requirement. Only its successor reviews the change.
  github.edit(8, 'A new trusted requirement.');
  advance(91 * minute);
  const survivors = machines.filter(w => w !== reviewer);
  for (const w of survivors) { w.agent = 'idle'; await w.tick(); }
  const successor = survivors.find(w => w.requests.length);
  assert.ok(successor, 'expired reviewer is taken over');
  assert.notEqual(successor.state().coordinatorId, reviewer.state().coordinatorId);
  const before = github.reviewComments(8).length;
  const stale = await completeDependencyIntake({ cwd: reviewer.cwd, request: first, analysis: analysisFor(first) }, reviewer.commandPorts());
  assert.equal(stale.reason, 'reviewer-lease', 'dead reviewer cannot write a late completion');
  assert.equal(github.reviewComments(8).length, before);
  assert.equal((await successor.complete(successor.requests.at(-1))).exitCode, 0);
  assert.equal(github.reviewComments(8).length, before + 1);

  // The original claim holder is dead too. Existing four-hour claim expiry is unchanged.
  advance(150 * minute);
  winning = JSON.parse((await claimPorts(survivors[0]).owners.read({ repository: repo, issues: [key(1)] })).json).claims[0];
  assert.equal(winning.expired, true);
  assert.equal(winning.active, false);
  github.unlabel(1, 'pdd:working');
  const replacement = await claim(survivors.at(-1), 1);
  const takeover = await Promise.all(machines.map(w => allowed(w, 1, replacement)));
  assert.equal(takeover.filter(r => r.allowed).length, 1);
  assert.equal(takeover[machines.indexOf(survivors.at(-1))].allowed, true);
});

test('managed nonreviewer prepare cannot bypass the shared lease and status makes no GitHub write', async t => {
  const { machines, github } = await fleet(t, 2);
  for (const w of machines) assert.equal((await w.invoke('start')).exitCode, 0);
  const { prepareDependencyIntake } = await import('../src/issue-dependencies-intake.mjs');
  const follower = machines[1];
  const prepared = await prepareDependencyIntake({ cwd: follower.cwd, repository: repo }, follower.commandPorts());
  assert.deepEqual(prepared.queued, []);
  const before = github.mark();
  const result = await follower.invoke('status');
  assert.equal(result.exitCode, 0);
  assert.ok(result.message.includes(machines[0].state().coordinatorId));
  assert.equal(github.since(before).calls.filter(c => c.method !== 'GET').length, 0);
});

test('the reviewer refreshes an issue held by another worker and commands from worktrees keep managed custody', async t => {
  const { machines, github } = await fleet(t, 2);
  const [reviewer, worker] = machines;
  for (const w of machines) assert.equal((await w.invoke('start')).exitCode, 0);
  assert.equal((await reviewer.complete(reviewer.requests[0])).result.state, 'complete');
  await reviewer.idle();
  await claim(worker, 3);
  github.edit(3, 'Changed requirement while a different machine works on it.');
  reviewer.agent = 'idle';
  await reviewer.tick();
  const request = reviewer.requests.at(-1);
  assert.deepEqual(request.issues, [key(3)]);
  assert.equal((await reviewer.complete(request)).result.state, 'complete');
  assert.equal(github.reviewComments(3).length, 2, 'one review for each requirement revision');
  const { prepareDependencyIntake } = await import('../src/issue-dependencies-intake.mjs');
  const state = worker.state();
  const context = { version: 'pdd.autopilot-coordinator.v1', repository: repo, machine: state.machine, coordinatorId: state.coordinatorId, activation: state.activatedAt };
  const issueWorktree = join(worker.dir, 'issue-worktree');
  execFileSync('git', ['worktree', 'add', '--quiet', '--detach', issueWorktree, 'HEAD'], { cwd: worker.cwd });
  const prepared = await prepareDependencyIntake({ cwd: issueWorktree, repository: repo }, worker.commandPorts({ env: { ...worker.commandPorts().env, PDD_AUTOPILOT_CONTEXT: JSON.stringify(context) } }));
  assert.deepEqual(prepared.queued, [], 'carried nonreviewer context cannot become manual');
});
