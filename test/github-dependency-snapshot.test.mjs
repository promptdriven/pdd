import { machineJson } from '../src/autopilot-store.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { existsSync, readFileSync, statSync } from 'node:fs';
import { dirname, basename, join } from 'node:path';
import { autopilotGithubWorld } from './helpers/autopilot-github-world.mjs';
import { GITHUB_FLOOR, githubBudgetSettings, githubLedger } from '../src/github-calls.mjs';
import { createDependencyReadPorts, readDependencySnapshot } from '../src/issue-dependencies-github.mjs';
import { checkDependencyStart } from '../src/issue-dependencies-intake.mjs';

// Issue #3051: on a repository with about 200 open issues Autopilot used the whole GitHub limit and never finished the
// dependency review. The world is the real launcher tick, intake and `pdd dependencies complete` with a counting fake
// GitHub (ETags, 304 replies, `since`, the REST limit) of 200 open issues: 150 trusted comments, 5 issues claimed by
// another machine and 5 open issues blocked by closed ones.
const minute = 60 * 1000, hour = 60 * minute;
const key = (w, n) => `https://github.com/${w.repository}/issues/${n}`;
// The saved snapshot and the kept completion beside the ledger: ROOT/github/H.snapshot.json and H.completion.json.
const fileOf = (w, kind) => join(w.stateRoot, 'github', `${createHash('sha256').update(w.repository.toLowerCase()).digest('hex').slice(0, 20)}.${kind}.json`);
const readJson = file => {
  const [, id, kind] = /^([0-9a-f]{20})\.(snapshot|completion)\.json$/.exec(basename(file));
  return machineJson({ root: dirname(dirname(file)), bucket: kind === 'snapshot' ? 'cache' : 'queue', key: `${kind}:${id}`, file }).read();
};
const savedSnapshot = w => { const value = readJson(fileOf(w, 'snapshot')); assert.ok(value?.list?.rows && value.issues, 'a saved dependency snapshot exists'); return value; };
const kept = w => readJson(fileOf(w, 'completion'));
const counts = (w, mark) => { const { rest, counted, graphql } = w.github.since(mark); return { rest, counted, graphql }; };
const reviews = (w, n) => w.github.reviewComments(n).length;

async function busyWorld(t, options) {
  const w = await autopilotGithubWorld(options);
  t.after(w.cleanup);
  w.github.busy();
  const started = await w.invoke('start');
  assert.equal(started.exitCode, 0, started.message);
  assert.equal(w.requests.length, 1, 'the activation tick delivers the first review request');
  return w;
}
// One review batch: the coordinator completes the newest request, the CLI runs its completion tick, then the idle wake.
async function batch(w) {
  const request = w.requests.at(-1), mark = w.github.mark();
  w.time += 4 * minute;
  const done = await w.complete(request);
  w.time += minute;
  await w.idle();
  return { request, done, mark };
}
// A full read of the same repository without a saved snapshot: what GitHub shows now.
const fullRead = w => readDependencySnapshot({ cwd: w.cwd, repository: w.repository }, w.commandPorts({ snapshotStore: null })).then(r => r.snapshot);
const savedRead = w => readDependencySnapshot({ cwd: w.cwd, repository: w.repository }, w.commandPorts()).then(r => r.snapshot);
const view = snapshot => ({ issues: snapshot.issues.map(i => [i.key, i.revision, i.state, i.holds.join(','), i.execution]).sort(), edges: snapshot.edges.map(e => `${e.dependent} < ${e.blocker}`).sort(),
  reviews: snapshot.reviews.map(r => r.id).sort(), inputs: snapshot.inputs.map(r => `${r.key} ${r.revision}`).sort(), complete: snapshot.complete });

test('a quiet tick with a saved snapshot makes fewer than 10 REST calls', async t => {
  const w = await busyWorld(t);
  await batch(w);
  w.time += 30 * minute;
  const mark = w.github.mark(), result = await w.tick(), used = counts(w, mark);
  assert.equal(result.exitCode, 0);
  assert.ok(used.rest < 10, `REST requests of a quiet tick: ${used.rest}`);
  assert.ok(used.counted < 10, `counted REST calls of a quiet tick: ${used.counted}`);
  t.diagnostic(`quiet tick: ${JSON.stringify(used)}`);
  assert.deepEqual(view(await savedRead(w)), view(await fullRead(w)), 'the saved snapshot gives what a full read gives');
});

test('one review batch of 10 subjects makes fewer than 300 REST calls on a 200-issue repository, and the next request follows', async t => {
  const w = await busyWorld(t);
  const { request, done, mark } = await batch(w);
  assert.equal(done.exitCode, 0); assert.equal(done.result.state, 'complete', JSON.stringify(done.result));
  assert.equal(request.issues.length, 10);
  for (const issue of request.issues) assert.equal(reviews(w, Number(issue.split('/').pop())), 1, `one saved review on ${issue}`);
  const used = counts(w, mark);
  assert.ok(used.rest < 300, `REST requests of one batch: ${used.rest}`);
  assert.ok(used.counted < 300, `counted REST calls of one batch: ${used.counted}`);
  const individual = w.github.since(mark).calls.filter(call => call.method === 'GET' && /\/issues\/comments\/\d+$/.test(call.endpoint));
  const savedIds = request.issues.flatMap(issue => w.github.issues.get(Number(issue.split('/').pop())).comments.filter(comment => /pdd-(?:dependency-review|issue-sort):v1/.test(comment.body)).map(comment => comment.id));
  assert.ok(individual.every(call => savedIds.includes(call.endpoint.split('/').pop())), 'individual comment GETs only read back newly saved records');
  t.diagnostic(`one batch (complete, completion tick, idle wake): ${JSON.stringify(used)}`);
  assert.equal(w.requests.length, 2, 'the completion or idle wake delivers the next request');
  const next = w.requests.at(-1);
  assert.equal(next.issues.length, 10);
  assert.ok(next.issues.every(issue => !request.issues.includes(issue)), 'the next request names the next 10 subjects');
});

test('a changed issue, comment, link or label is seen on the next tick', async t => {
  const w = await busyWorld(t);
  await batch(w);
  // Move the watermark past issue 146 before a link change that does not move its update time.
  w.time += 10 * minute; w.github.edit(151, 'Keep the public name.'); await w.tick();
  w.time += 10 * minute;
  w.github.edit(150, 'Make part 150 work, and keep its old name.');
  const comment = w.github.comment(149, 'Also check the old file.');
  w.github.editComment(147, w.github.issues.get(147).comments[0].id, 'Also keep part 147 very small.');
  w.github.link(146, 145);                     // GitHub may not move updated_at for a link; the link counts change.
  w.github.label(144, 'pdd:stuck');
  w.github.close(143);
  w.time += 20 * minute;
  const mark = w.github.mark(); await w.tick();
  assert.ok(counts(w, mark).rest < 100, `changed tick REST requests: ${counts(w, mark).rest}`);
  const saved = savedSnapshot(w);
  assert.equal(saved.list.rows[150].body, 'Make part 150 work, and keep its old name.');
  assert.ok(saved.issues[149].kinds.comments.some(c => String(c.id) === comment.id), 'the new comment');
  assert.ok(saved.issues[147].kinds.comments.some(c => c.body === 'Also keep part 147 very small.'), 'the edited comment');
  assert.deepEqual(saved.issues[146].kinds.blockedBy.map(x => x.html_url), [key(w, 145)], 'the new link');
  assert.ok(saved.list.rows[144].labels.some(l => l.name === 'pdd:stuck'), 'the new label');
  assert.equal(saved.list.rows[143], undefined, 'the closed issue leaves the open list');
  const snapshot = await savedRead(w);
  assert.ok(snapshot.edges.some(e => e.dependent === key(w, 146) && e.blocker === key(w, 145)));
  assert.ok(snapshot.issues.find(i => i.key === key(w, 144)).holds.includes('Stuck'));
  assert.ok(snapshot.inputs.some(r => r.key === `${key(w, 149)}#issuecomment-${comment.id}`));
  assert.deepEqual(view(snapshot), view(await fullRead(w)), 'the saved snapshot gives what a full read gives');
});

test('a deleted or moved issue disappears at the full refresh', async t => {
  const w = await busyWorld(t);
  w.github.remove(120); w.github.move(121, 'acme/other');
  w.time += 30 * minute; await w.tick();
  const mark = w.github.mark(); await w.tick();
  assert.ok(counts(w, mark).rest < 10, `quiet REST requests before refresh: ${counts(w, mark).rest}`);
  w.time += 24 * hour;
  const beforeRefresh = readJson(fileOf(w, 'snapshot')).refreshedAt;
  w.github.failRead = call => call.endpoint.includes('/issues?state=open');
  assert.equal((await savedRead(w)).complete, false, 'a failed daily refresh is incomplete');
  assert.equal(readJson(fileOf(w, 'snapshot')).refreshedAt, beforeRefresh, 'a failed full refresh does not renew the old index');
  w.github.failRead = null;
  await w.tick();
  const saved = savedSnapshot(w);
  assert.equal(saved.list.rows[120], undefined, 'the deleted issue is gone after the daily full refresh');
  assert.equal(saved.list.rows[121], undefined, 'the moved issue is gone after the daily full refresh');
  assert.ok(saved.refreshedAt >= w.time - minute, 'the refresh read everything again');
  const snapshot = await savedRead(w);
  assert.ok(!snapshot.issues.some(i => [key(w, 120), key(w, 121)].includes(i.key)));
});

test('a new claim by another machine is always seen before a start, a push or a merge, also when the saved snapshot does not show it', async t => {
  const w = await busyWorld(t);
  await batch(w);
  const state = w.state();
  // Another machine claims issue 130. Here the change does not show in the update time, so `since` and the saved
  // snapshot do not show it: only a live read can.
  const before = w.github.issues.get(130).updated;
  w.github.claim(130, { coordinatorId: 'coordinator-c', machine: 'machine-c' });
  w.github.issues.get(130).updated = before - hour;
  w.time += minute;
  // The workflow start and every continuation step (push, approve, park, open, yield) read the claim with this port.
  const owners = JSON.parse((await createDependencyReadPorts({ cwd: w.cwd }, w.commandPorts()).owners.read({ repository: w.repository, issues: [key(w, 130)] })).json);
  const claim = owners.claims.find(c => c.issue === key(w, 130));
  assert.equal(claim?.coordinatorId, 'coordinator-c', 'the live claim check sees the other machine');
  assert.equal(claim.active, true);
  const floorPorts = w.commandPorts({ githubFloor: { blocked: () => true, observe: () => {} } });
  const guardedStart = await checkDependencyStart({ cwd: w.cwd, repository: w.repository, issue: key(w, 130) }, floorPorts);
  assert.equal(guardedStart.reason, 'owner', 'the live subject and claim are still read below the floor');
  const start = await checkDependencyStart({ cwd: w.cwd, repository: w.repository, issue: key(w, 130),
    coordinator: { repository: w.repository, coordinatorId: state.coordinatorId, machine: state.machine, activation: state.activatedAt, claim: { commentId: '1', labelEventId: '1' } } }, w.commandPorts());
  assert.deepEqual(start, { allowed: false, reason: 'owner' }, 'no start for an issue that another machine holds');
  const mark = w.github.mark(); await savedRead(w);
  assert.ok(counts(w, mark).rest < 30, `incremental read after claim: ${counts(w, mark).rest}`);
});

test('when the limit runs out mid-batch, the saved reviews stay, the rest is kept, and the next tick after the reset finishes it', async t => {
  const w = await busyWorld(t);
  const request = w.requests.at(-1);
  // The limit runs out after the 4th review save of this completion.
  let posts = 0;
  w.github.failRest = call => call.method === 'POST' && call.endpoint.endsWith('/comments') && ++posts > 4;
  w.time += 4 * minute;
  const first = await w.complete(request);
  assert.equal(first.result.state, 'pending', JSON.stringify(first.result));
  assert.equal(first.result.reason, 'write-unconfirmed');
  assert.equal(first.result.reviewIds.length, 4, 'four reviews were saved');
  const subjects = request.issues.map(issue => Number(issue.split('/').pop()));
  assert.deepEqual(subjects.map(n => reviews(w, n)), [1, 1, 1, 1, 0, 0, 0, 0, 0, 0]);
  const keptCompletion = kept(w);
  assert.equal(keptCompletion?.request.id, request.id, 'the request and analysis are kept');
  // Until the reset the tick waits; then it finishes the kept completion without a new analysis.
  w.github.failRest = null;
  w.time += 10 * minute; await w.idle(); await w.tick();
  assert.deepEqual(subjects.map(n => reviews(w, n)), [1, 1, 1, 1, 0, 0, 0, 0, 0, 0], 'below the floor nothing is saved');
  // Repeated command retries during an outage must not consume or discard the kept analysis.
  for (let retry = 0; retry < 7; retry++) { const waiting = await w.complete(request); assert.equal(waiting.result.state, 'pending'); }
  assert.equal(kept(w)?.request.id, request.id);
  w.time = w.github.resetAt * 1000 + minute;
  const delivered = w.requests.length;
  await w.tick();
  assert.deepEqual(subjects.map(n => reviews(w, n)), [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 'each subject has exactly one review');
  assert.equal(kept(w), null, 'the kept completion is done');
  assert.ok(w.requests.slice(delivered).every(next => next.issues.every(issue => !request.issues.includes(issue))), 'no subject of the finished request is sent for analysis again');
});

test('a snapshot that the limit stopped is not saved as complete, and the next read takes the changes', async t => {
  const w = await busyWorld(t);
  const before = readJson(fileOf(w, 'snapshot'));
  w.time += 10 * minute;
  w.github.comment(111, 'Also check the second case.');
  w.github.failRest = call => call.endpoint.includes('/issues?');
  const stopped = await savedRead(w);
  assert.equal(stopped.complete, false, 'the stopped read is not complete');
  assert.equal(readJson(fileOf(w, 'snapshot'))?.list.readAt, before?.list.readAt, 'the saved list is not advanced');
  w.github.failRest = null;
  w.time = w.github.resetAt * 1000 + minute;
  const mark = w.github.mark();
  const after = await savedRead(w);
  assert.ok(counts(w, mark).rest < 30, `resumed read REST requests: ${counts(w, mark).rest}`);
  assert.equal(after.complete, true, after.warnings.join('; '));
  assert.ok(after.inputs.some(r => r.key.startsWith(`${key(w, 111)}#issuecomment-`) && r.key !== `${key(w, 111)}#issuecomment-${w.github.issues.get(111).comments[0].id}`), 'the new comment is read');
});

test('the floor stops non-safety reads at 1,000 calls left, but not the claim checks', async t => {
  const w = await busyWorld(t);
  const request = w.requests.at(-1);
  // Other use on the login leaves 900 calls until the reset.
  githubLedger({ root: w.stateRoot, repository: w.repository }).record({ at: w.time, api: 'rest', purpose: 'other', status: 200, resource: 'core', remaining: 900, limit: 5000, resetAt: w.github.resetAt * 1000 });
  w.github.remaining = 900;
  w.time += 4 * minute;
  const mark = w.github.mark();
  const done = await w.complete(request);
  const made = w.github.since(mark).calls;
  assert.equal(done.result.state, 'pending'); assert.equal(done.result.reason, 'github-limit');
  assert.ok(!made.some(call => call.endpoint.includes('/issues?') || call.endpoint === 'graphql' || /\/(comments|timeline|dependencies)/.test(call.endpoint)), `no list, batch, page or comment read: ${made.map(c => c.endpoint).join(', ')}`);
  assert.equal(kept(w)?.request.id, request.id, 'the analysis is kept for after the reset');
  assert.equal(request.issues.map(issue => reviews(w, Number(issue.split('/').pop()))).reduce((a, b) => a + b), 0);
  // The claim checks are safety reads: below the floor they still ask GitHub.
  const guarded = w.commandPorts({ githubFloor: { blocked: () => true, observe: () => {}, stopped: true } }), claimMark = w.github.mark();
  const owners = JSON.parse((await createDependencyReadPorts({ cwd: w.cwd }, guarded).owners.read({ repository: w.repository, issues: [key(w, 10)] })).json);
  assert.equal(owners.claims.find(c => c.issue === key(w, 10))?.coordinatorId, 'coordinator-b');
  assert.ok(w.github.since(claimMark).calls.some(call => call.endpoint.endsWith('/issues/10/timeline?per_page=100')), 'the claim history is read live');
  // After the reset the tick finishes the kept completion.
  w.time = w.github.resetAt * 1000 + minute;
  await w.tick();
  assert.deepEqual(request.issues.map(issue => reviews(w, Number(issue.split('/').pop()))), Array(10).fill(1));
  assert.equal(kept(w), null);
  const saved = JSON.stringify(readJson(fileOf(w, 'snapshot')));
  assert.ok(saved.length < 64 * 1024 * 1024 && JSON.parse(saved).v === 1, 'the saved snapshot is versioned and bounded');
  assert.equal(statSync(join(w.stateRoot, 'machine.sqlite')).mode & 0o777, 0o600, 'the saved snapshot is private');
  assert.equal(GITHUB_FLOOR, 1000, 'the default floor');
  assert.deepEqual(githubBudgetSettings({}), { share: 30, floor: 1000 });
});


test('a failed detail read keeps other finished snapshot updates and retries the incomplete issue', async t => {
  const w = await busyWorld(t);
  w.time += 10 * minute;
  const first = w.github.comment(201, 'Keep the first closed prerequisite clear.');
  const second = w.github.comment(202, 'Keep the second closed prerequisite clear.');
  w.github.failRead = call => call.endpoint.includes('/issues/201/timeline');
  const partial = await savedRead(w);
  assert.equal(partial.complete, false);
  assert.ok(partial.inputs.some(row => row.key === `${key(w, 202)}#issuecomment-${second.id}`));
  w.github.failRead = null;
  w.time += minute;
  const mark = w.github.mark(), recovered = await savedRead(w);
  assert.equal(recovered.complete, true, recovered.warnings.join('; '));
  assert.ok(recovered.inputs.some(row => row.key === `${key(w, 201)}#issuecomment-${first.id}`));
  const made = w.github.since(mark);
  assert.ok(made.rest < 20, `recovery REST requests: ${made.rest}`);
  assert.ok(!made.calls.some(call => /issues\/202\/(?:comments|timeline|dependencies)/.test(call.endpoint)), 'the finished issue needs no detail reread');
  // A failed metadata pass keeps the successful since rows and full issue reads as pending staging.
  w.time += minute;
  const prior = readJson(fileOf(w, 'snapshot'));
  w.github.edit(150, 'Keep the current behavior after recovery.');
  w.github.failRead = call => call.endpoint.includes('/issues?state=open');
  const staged = await savedRead(w);
  assert.equal(staged.complete, false);
  const disk = readJson(fileOf(w, 'snapshot'));
  assert.equal(disk.list.readAt, prior.list.readAt, 'a failed metadata pass does not advance complete coverage');
  assert.ok(disk.pendingList?.rows[150], 'the changed row is kept as pending');
  w.github.failRead = null; w.time += minute;
  const retryMark = w.github.mark(), done = await savedRead(w);
  assert.equal(done.complete, true, done.warnings.join('; '));
  assert.ok(!w.github.since(retryMark).calls.some(call => call.api === 'graphql' && /\bcomments\s*\(/.test(call.query)), 'the finished changed issue is reused after staging; only link metadata is read');
  assert.equal(readJson(fileOf(w, 'snapshot')).pendingList, undefined, 'successful coverage clears the pending list');
  assert.deepEqual(view(done), view(await fullRead(w)));
});

test('crossing the floor in a tick stops further non-safety reads and new deliveries', async t => {
  const w = await busyWorld(t);
  w.time += 30 * minute;
  w.github.comment(190, 'Check the changed input.');
  w.github.remaining = 1001;
  githubLedger({ root: w.stateRoot, repository: w.repository }).record({ at: w.time, api: 'rest', purpose: 'other', status: 200, resource: 'core', remaining: 1001, limit: 5000, resetAt: w.github.resetAt * 1000 });
  const mark = w.github.mark(), delivered = w.requests.length;
  const result = await w.tick();
  assert.equal(result.exitCode, 0);
  const made = w.github.since(mark).calls;
  assert.equal(w.requests.length, delivered, 'the tick does not deliver work below the floor');
  assert.ok(made.filter(call => call.endpoint.includes('/issues?')).length <= 2, 'the index stops when it crosses the floor');
  assert.ok(!made.some(call => call.endpoint === 'graphql' || /\/issues\/\d+\/(?:comments|timeline|dependencies)/.test(call.endpoint)), 'detail reads wait after crossing the floor');
});
