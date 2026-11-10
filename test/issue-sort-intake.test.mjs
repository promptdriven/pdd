import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { fixture, complete, repository, key } from './helpers/issue-sort-fixture.mjs';
import { readDependencySnapshot } from '../src/issue-dependencies-github.mjs';
import { prepareDependencyIntake, completeDependencyIntake, reconcileDependencyIntake } from '../src/issue-dependencies-intake.mjs';
import { saveSortBatch, validateSortBatch } from '../src/issue-sort-github.mjs';
import { projectIssueGraph } from '../src/issue-dependencies.mjs';
import { sortPlan } from '../src/issue-sort.mjs';
import { analysisFor } from './helpers/autopilot-github-world.mjs';

const read = async w => (await readDependencySnapshot({ repository }, w.ports)).snapshot;
const sortComments = (w, n) => w.comments.get(n).filter(c => c.body.includes('<!-- pdd-issue-sort:v1 -->'));
const independent = (w, n) => w.record(n, { rootCause: `defect-${n}` });

test('assigned subjects are skipped while free subjects complete and become eligible', async () => {
  const w = fixture([1, 2, 3]);
  w.issues[2].assignees = [{ login: 'person' }];
  const prepared = await prepareDependencyIntake({ repository }, w.ports);
  assert.deepEqual(prepared.queued, [key(2), key(1)], 'INTAKE_ASSIGNED_QUEUED');
  assert.deepEqual(prepared.skipped, [key(3)]);
  assert.equal(prepared.skipReasons[0].issue, key(3));
  assert.ok(prepared.skipReasons[0].reason.length);
  assert.deepEqual((await prepareDependencyIntake({ repository, issue: '3' }, w.ports)).queued, []);
  const result = await complete(w, [independent(w, 2), independent(w, 1)]);
  assert.equal(result.state, 'complete');
  assert.equal(result.reviewIds.length, 2);
  const next = await reconcileDependencyIntake({ repository, mode: 'auto' }, w.ports);
  assert.deepEqual(new Set(next.eligible), new Set([key(1), key(2)]));
  assert.ok(next.skipped.includes(key(3)));
  assert.equal(sortComments(w, 3).length, 0);
  assert.equal(w.writes.filter(x => x.issue === 3).length, 0);
  assert.ok(next.groups.every(g => !g.members.includes(key(3))));
});

test('an assigned requested issue needs no sort and its supplied sort is ignored', async () => {
  const w = fixture([1, 2]); w.issues[1].assignees = [{ login: 'person' }];
  const snapshot = await read(w), sorts = [w.record(1, { paths: [] }), w.record(2, { paths: [] })];
  const args = { snapshot, prepared: snapshot, issues: [key(1), key(2)] };
  assert.deepEqual(validateSortBatch({ ...args, sorts: [sorts[0]] }), [sorts[0]], 'INTAKE_ASSIGNED_REQUIRED');
  assert.deepEqual(validateSortBatch({ ...args, sorts }), [sorts[0]]);
  await saveSortBatch({ repository, snapshot, sorts }, w.ports);
  assert.equal(sortComments(w, 1).length, 1);
  assert.equal(sortComments(w, 2).length, 0);
});

for (const failure of ['throw', 'unconfirmed']) test(`one ${failure} sort save leaves other issues saved, routed and eligible`, async () => {
  const w = fixture([1, 2, 3]);
  let note; w.ports.results = { save: async ({ json }) => { note = JSON.parse(json); return { ok: true }; } };
  const append = w.ports.github.appendComment;
  w.ports.github.appendComment = async args => {
    if (args.issue === 3 && args.body.includes('<!-- pdd-issue-sort:v1 -->')) {
      if (failure === 'throw') throw Error('synthetic-save-failure');
      return { json: '{}' };
    }
    return append(args);
  };
  const records = [3, 2, 1].map(n => independent(w, n));
  records[1].status = { ...records[1].status, state: 'fixed', fix: 'https://github.com/example/project/pull/90' };
  const result = await complete(w, records);
  assert.equal(sortComments(w, 1).length, 1, 'INTAKE_BATCH_ABORTED');
  assert.equal(sortComments(w, 2).length, 1);
  assert.equal(w.issues[1].state, 'closed');
  assert.equal(result.state, 'pending'); assert.equal(result.pendingIssue, key(3));
  assert.equal(result.sortFailures[0].issue, key(3)); assert.ok(result.sortFailures[0].reason.length);
  assert.equal(note.reviewIds.length, 3); assert.equal(note.sortFailures[0].issue, key(3));
  assert.deepEqual(note.rows.map(x => x.key), [key(3)]);
  const next = await reconcileDependencyIntake({ repository, mode: 'auto' }, w.ports);
  assert.ok(next.eligible.includes(key(1))); assert.deepEqual(next.queued, [key(3)]);
  assert.equal(sortComments(w, 3).length, 0);
});

test('one failed route does not stop a later route or a work issue', async () => {
  const w = fixture([1, 2, 3]);
  const records = [3, 2, 1].map(n => independent(w, n));
  for (const r of records.slice(0, 2)) r.status = { ...r.status, state: 'fixed', fix: 'https://github.com/example/project/pull/90' };
  const append = w.ports.github.appendComment;
  w.ports.github.appendComment = async args => {
    if (args.issue === 2 && args.body.includes('<!-- pdd-issue-route:v1 -->')) throw Error('synthetic-route-failure');
    return append(args);
  };
  const result = await complete(w, records);
  assert.equal(w.issues[2].state, 'closed', 'INTAKE_ROUTE_BATCH_ABORTED');
  assert.equal(w.issues[1].state, 'open');
  assert.equal(result.sortFailures[0].issue, key(2));
  const next = await reconcileDependencyIntake({ repository, mode: 'auto' }, w.ports);
  assert.ok(next.eligible.includes(key(1)));
});

test('kept completion retries sort after reviews were saved without duplicate comments', async () => {
  const w = fixture([1, 2]);
  const { request } = await prepareDependencyIntake({ repository }, w.ports);
  const analysis = { ...analysisFor(request), sorts: [independent(w, 2), independent(w, 1)] };
  const append = w.ports.github.appendComment;
  let fail = true, note;
  w.ports.results = { save: async ({ json }) => { note = JSON.parse(json); return { ok: true }; } };
  w.ports.github.appendComment = async args => {
    if (fail && args.issue === 2 && args.body.includes('<!-- pdd-issue-sort:v1 -->')) throw Error('synthetic-save-failure');
    return append(args);
  };
  const first = await completeDependencyIntake({ request, analysis }, w.ports);
  assert.equal(first.state, 'pending');
  fail = false;
  const result = await completeDependencyIntake({ request, analysis }, w.ports);
  assert.equal(result.state, 'complete', 'INTAKE_SORT_RETRY_HELD');
  assert.equal(sortComments(w, 2).length, 1, 'INTAKE_SORT_RETRY_OMITTED');
  assert.equal(sortComments(w, 1).length, 1);
  for (const n of [1, 2]) assert.equal(w.comments.get(n).filter(c => c.body.includes('<!-- pdd-dependency-review:v1 -->')).length, 1);
  assert.equal(note.state, 'complete');
});

test('assignment acquired after prepare stops that sort only', async () => {
  const w = fixture([1, 2]);
  const { request } = await prepareDependencyIntake({ repository }, w.ports);
  const analysis = { ...analysisFor(request), sorts: [independent(w, 2), independent(w, 1)] };
  const issue = w.ports.github.issue;
  w.ports.github.issue = async args => {
    // The authoritative sort write read observes a new assignee.
    const reply = await issue(args), raw = JSON.parse(reply.json);
    if (args.issue === 2) raw.assignees = [{ login: 'person' }];
    return { json: JSON.stringify(raw) };
  };
  await completeDependencyIntake({ request, analysis }, w.ports);
  assert.equal(sortComments(w, 2).length, 0);
  assert.equal(sortComments(w, 1).length, 1, 'INTAKE_ASSIGNMENT_ABORTED_BATCH');
});

for (const stale of [false, true]) test(`retained groups exclude assigned members and umbrellas (${stale ? 'stale' : 'current'} sort)`, async () => {
  const w = fixture([1, 2, 3]);
  for (const n of [1, 2, 3]) { w.save(w.record(n)); w.review(n); }
  const snapshot = await read(w);
  snapshot.sortContext.groups = [{ rootCause: 'shared-context', area: 'cli', umbrella: key(1), members: [key(1), key(2), key(3)] }];
  snapshot.issues.find(x => x.key === key(1)).assignees = ['person'];
  if (stale) snapshot.issues.find(x => x.key === key(1)).revision = 'changed';
  const plan = sortPlan({ snapshot });
  assert.ok(plan.groups.every(g => !g.members.includes(key(1)) && g.umbrella !== key(1)), 'INTAKE_ASSIGNED_RETAINED_IN_GROUP');
});

test('an assigned sibling with a stale sort cannot hold free work', async () => {
  const w = fixture([1, 2]);
  for (const n of [1, 2]) w.save(w.record(n));
  w.issues[0].assignees = [{ login: 'person' }]; w.issues[0].body = 'A changed human requirement.';
  w.review(2);
  const graph = projectIssueGraph({ snapshot: await read(w) });
  assert.equal(graph.nodes.find(n => n.key === key(2)).eligible, true, 'INTAKE_ASSIGNED_SIBLING_HOLDS_FREE_WORK');
});

test('assigned umbrella markers are not recovered from the snapshot or live index', async () => {
  const w = fixture([1, 2, 3, 100]);
  w.issues[3].body += '\n<!-- pdd-issue-group:v1 shared-context -->';
  w.issues[3].assignees = [{ login: 'person' }];
  const result = await complete(w, [3, 2, 1].map(n => w.record(n)));
  assert.equal(result.state, 'complete');
  const snapshot = await read(w);
  assert.ok(snapshot.sortContext.groups.length);
  assert.ok(snapshot.sortContext.groups.every(g => g.umbrella !== key(100) && !g.members.includes(key(100))), 'INTAKE_ASSIGNED_UMBRELLA_RECOVERED');
  assert.equal(w.writes.filter(x => x.issue === 100).length, 0);
});

test('an unconfirmed group write does not prevent an independent close route', async () => {
  const w = fixture([1, 2, 3, 4]);
  for (const n of [1, 2]) { w.save(w.record(n)); w.review(n); }
  await reconcileDependencyIntake({ repository, mode: 'auto' }, w.ports);
  w.issues[0].labels = ['pdd:working'];
  w.claims.push({ issue: key(1), active: true, owner: 'worker' });
  const append = w.ports.github.appendComment;
  w.ports.github.appendComment = async args => {
    if (args.issue === 1 && args.body.includes('Group members')) throw Error('synthetic-group-failure');
    return append(args);
  };
  const records = [w.record(3)];
  records.push(w.record(4, { rootCause: 'independent', status: { ...w.record(4).status, state: 'fixed', fix: 'https://github.com/example/project/pull/90' } }));
  const result = await complete(w, records);
  assert.equal(w.issues[3].state, 'closed', 'INTAKE_GROUP_ABORTED_ROUTE');
  assert.equal(result.state, 'pending');
  assert.ok(result.sortFailures.some(x => x.issue === key(1) && x.reason.length));
});
