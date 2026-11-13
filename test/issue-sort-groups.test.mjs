import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { readDependencySnapshot, createDependencyReadPorts } from '../src/issue-dependencies-github.mjs';
import { reconcileDependencyIntake, prepareDependencyIntake } from '../src/issue-dependencies-intake.mjs';
import { projectIssueGraph } from '../src/issue-dependencies.mjs';
import { renderIssueGraph } from '../src/issue-dependency-graph-view.mjs';
import { sortPlan, sortClosingReferences } from '../src/issue-sort.mjs';
import { fixture, complete, repository, key } from './helpers/issue-sort-fixture.mjs';
const read = async w => (await readDependencySnapshot({ repository }, w.ports)).snapshot;
const tick = w => reconcileDependencyIntake({ repository, mode: 'auto' }, w.ports);
const seed = (w, numbers) => { for (const n of numbers) { w.save(w.record(n)); w.review(n); } };
const groups = async w => { const saved = (await w.ports.sortGroups.read({ repository })).groups; assert.ok(saved.length > 0, 'expected durable root-cause groups'); return saved; };
const replace = (w, n, changes = {}) => w.save(w.record(n, { base: w.comments.get(n).filter(c => c.body.includes('pdd-issue-sort:v1')).map(c => String(c.id)), ...changes }));

test('saved sorts form a pair, then a third issue creates one durable global umbrella', async () => {
  const w = fixture([1,2,3]); seed(w, [1,2]);
  await tick(w);
  assert.equal((await groups(w))[0].members.length, 2);
  assert.equal(w.writes.filter(x => x.kind === 'umbrella').length, 0);
  seed(w, [3]); await tick(w);
  const [group] = await groups(w);
  assert.deepEqual(group.members, [key(1),key(2),key(3)]);
  assert.ok(!group.members.includes(group.umbrella));
  const umbrella = w.issues.find(x => x.html_url === group.umbrella);
  assert.ok(umbrella.title.startsWith('Global fix:'));
  assert.ok(group.members.every(x => umbrella.body.includes(x)));
  assert.ok(umbrella.body.includes(group.rootCause));
  assert.match(umbrella.body, /One fix:/);
  await tick(w); assert.equal(w.writes.filter(x => x.kind === 'umbrella').length, 1);
  const graph = projectIssueGraph({ snapshot: await read(w) });
  assert.ok(graph.nodes.filter(x => group.members.includes(x.key)).every(x => !x.eligible && x.blockers.includes(group.umbrella)));
  assert.equal(graph.groups[0].umbrella, group.umbrella);
});

test('two issues in different locally owned areas get one global umbrella', async () => {
  const w = fixture([1,2], { context: { areas: [
    { name: 'cli', owner: 'autopilot', match: { paths: ['src/**'] } },
    { name: 'docs', owner: 'autopilot', match: { paths: ['docs/**'] } },
  ] } });
  seed(w, [1]); w.save(w.record(2, { paths: ['docs/guide.md'], belongs: { kind: 'area', area: 'docs', repository: '' } })); w.review(2);
  await tick(w); const [group] = await groups(w);
  assert.deepEqual(group.members, [key(1),key(2)]);
  assert.equal(group.area, 'cli,docs');
  assert.ok(!group.members.includes(group.umbrella));
});

test('a changed cause leaves the old group and joins the matching saved group', async () => {
  const w = fixture([1,2,3,4,5]); seed(w, [1,2,3]);
  for (const n of [4,5]) { w.save(w.record(n, { rootCause: 'other-cause' })); w.review(n); }
  await tick(w);
  const original = (await groups(w)).find(g => g.rootCause === 'shared-context').umbrella;
  replace(w, 3, { rootCause: 'other-cause' }); await tick(w);
  const saved = await groups(w);
  assert.deepEqual(saved.find(g => g.rootCause === 'shared-context').members, [key(1),key(2)]);
  assert.equal(saved.find(g => g.rootCause === 'shared-context').umbrella, original);
  assert.deepEqual(saved.find(g => g.rootCause === 'other-cause').members, [key(3),key(4),key(5)]);
});

for (const hold of ['claim','open-pr','person']) test(`${hold} work is deferred and compared again after it finishes`, async () => {
  const w = fixture([1,2,3]); seed(w, [1,2,3]);
  const page = w.ports.github.page;
  let running = true;
  if (hold === 'claim') { w.issues[2].labels = ['pdd:working']; w.claims.push({ issue: key(3), active: true, owner: 'worker' }); }
  if (hold === 'person') w.issues[2].assignees = [{ login: 'person' }];
  if (hold === 'open-pr') w.ports.github.page = args => args.kind === 'timeline' && args.issue === 3
    ? { json: JSON.stringify({ items: running ? [{ event: 'cross-referenced', source: { issue: { pull_request: {}, state: 'open' } } }] : [], next: '' }) } : page(args);
  await tick(w);
  assert.deepEqual((await groups(w))[0].members, [key(1),key(2)]);
  assert.equal(w.writes.filter(x => x.kind === 'umbrella').length, 0);
  running = false; w.issues[2].labels = []; w.issues[2].assignees = []; w.claims.length = 0;
  await tick(w);
  assert.deepEqual((await groups(w))[0].members, [key(1),key(2),key(3)]);
  assert.equal(w.writes.filter(x => x.kind === 'umbrella').length, 1);
});

test('an idle new member joins a running dedicated umbrella with one note', async () => {
  const w = fixture([1,2,3,4]); seed(w, [1,2,3]); await tick(w);
  const [before] = await groups(w), umbrella = w.issues.find(x => x.html_url === before.umbrella);
  umbrella.labels = ['pdd:working'];
  w.claims.push({ issue: before.umbrella, active: true, owner: 'worker' });
  seed(w, [4]); await tick(w); await tick(w);
  const [after] = await groups(w);
  assert.equal(after.umbrella, before.umbrella); assert.equal(after.members.length, 4);
  const notes = w.comments.get(umbrella.number).filter(x => x.body.includes('pdd-issue-route:v1'));
  assert.equal(notes.length, 1); assert.ok(notes[0].body.includes(key(4)));
});

test('a claim arriving during the group wait prevents umbrella creation', async () => {
  const w = fixture([1,2,3]); seed(w, [1,2,3]);
  const wait = w.ports.wait.sleep;
  w.ports.wait.sleep = async args => { await wait(args); w.claims.push({ issue: key(3), active: true, owner: 'worker' }); };
  // Share a prior paced save so creation must pass through a wait.
  w.comments.set(3, []);
  await complete(w, [w.record(3)]);
  assert.equal(w.writes.filter(x => x.kind === 'umbrella').length, 0);
  w.claims.length = 0; w.ports.wait.sleep = wait; await tick(w);
  assert.equal(w.writes.filter(x => x.kind === 'umbrella').length, 1);
});

test('a lost local group save recovers the confirmed umbrella by cause marker', async () => {
  const w = fixture([1,2,3]); seed(w, [1,2,3]);
  const save = w.ports.sortGroups.save; let lost = true;
  w.ports.sortGroups.save = args => lost ? { ok: false } : save(args);
  await tick(w); lost = false; await tick(w);
  assert.equal(w.writes.filter(x => x.kind === 'umbrella').length, 1);
  assert.equal((await groups(w)).length, 1);
});

test('merge requires new sorts for every member and closes only a fresh fixed member', async () => {
  const options = {}, w = fixture([1,2,3], options); seed(w, [1,2,3]); await tick(w);
  const [group] = await groups(w), umbrella = w.issues.find(x => x.html_url === group.umbrella);
  umbrella.state = 'closed'; options.mergedFix = 'https://github.com/example/project/pull/90';
  await tick(w);
  const prepared = await prepareDependencyIntake({ repository }, w.ports);
  assert.deepEqual(prepared.queued.slice().sort(), [key(1),key(2),key(3)]);
  assert.equal(w.issues.slice(0,3).filter(x => x.state === 'closed').length, 0);
  const s = JSON.parse(prepared.request.snapshotJson);
  assert.equal(s.sortContext.groups[0].merged, options.mergedFix);
  const records = [1,2,3].map(n => w.record(n, { base: w.comments.get(n).filter(c => c.body.includes('pdd-issue-sort:v1')).map(c => String(c.id)),
    ...(n === 1 ? { status: { state: 'fixed', release: '1.0.0', fix: options.mergedFix, evidence: ['src/cli.mjs:12'] } } : {}) }));
  assert.equal((await complete(w, records)).state, 'complete');
  assert.equal(w.issues[0].state, 'closed');
  assert.deepEqual(w.issues.slice(1,3).map(x => x.state), ['open','open']);
  assert.ok(w.comments.get(1).some(x => x.body.includes(options.mergedFix) && x.body.includes('pdd-issue-route:v1')));
});

test('closing an umbrella without a merged fixing PR does not queue post-merge closure', async () => {
  const w = fixture([1,2,3]); seed(w, [1,2,3]); await tick(w);
  const [group] = await groups(w); w.issues.find(x => x.html_url === group.umbrella).state = 'closed';
  await tick(w);
  assert.equal((await groups(w))[0].merged, undefined);
  assert.equal(w.issues.slice(0,3).filter(x => x.state === 'closed').length, 0);
  assert.ok(projectIssueGraph({ snapshot: await read(w) }).nodes.every(x => !x.eligible));
});

for (const closer of [null, { __typename: 'PullRequest', merged: false, url: 'https://github.com/example/project/pull/90' }, { __typename: 'PullRequest', merged: true, url: 'https://github.com/example/project/pull/90' }]) test(`native merge evidence follows the closing event: ${closer?.merged ?? 'none'}`, async () => {
  const native = createDependencyReadPorts({}, { execFile: async (_file, args, options) => {
    assert.equal(args[args.indexOf('--method') + 2], 'graphql');
    const body = JSON.parse(options.input); assert.ok(body.query.includes('CLOSED_EVENT'));
    return { code: 0, stdout: JSON.stringify({ data: { repository: { issue: { state: 'CLOSED', timelineItems: { nodes: [{ closer }] } } } } }) };
  } });
  const result = await native.github.sortMergedFix?.({ repository, issue: 100 });
  assert.equal(result?.url, closer?.merged ? closer.url : '');
});

test('the factory graph shows group size, cause and a safe umbrella link', async () => {
  const w = fixture([1,2,3]); seed(w, [1,2,3]); await tick(w);
  const graph = projectIssueGraph({ snapshot: await read(w) });
  assert.ok(Array.isArray(graph.groups), 'expected projected group summaries');
  const [group] = graph.groups;
  const rendered = renderIssueGraph({ graph });
  assert.match(rendered.html, /aria-label="Issue groups"/);
  assert.ok(rendered.html.includes(`3 issues · ${group.rootCause}`));
  assert.ok(rendered.html.includes(`href="${group.umbrella}"`));
  graph.groups = [{ ...group, rootCause: '<script>bad()</script>', umbrella: 'javascript:bad()' }];
  const malicious = renderIssueGraph({ graph }).html;
  assert.ok(!malicious.includes('<script>bad()'));
  assert.ok(!malicious.includes('href="javascript:'));
});

test('both group PRs reference members and leave closure to the post-merge sort', async () => {
  const w = fixture([1,2,3]); seed(w, [1,2,3]); await tick(w);
  const [group] = await groups(w), n = Number(group.umbrella.split('/').pop()); seed(w, [n]);
  const s = await read(w), graph = projectIssueGraph({ snapshot: s });
  for (const code of [false,true]) assert.deepEqual(sortClosingReferences({ snapshot: s, issue: group.umbrella, code, graph }), group.members.map(x => `Refs ${x}`));
});

test('bounded group plans never offer member starts before a required umbrella', async () => {
  for (let size = 3; size <= 6; size++) {
    const w = fixture(Array.from({ length: size }, (_, i) => i+1)); seed(w, w.issues.map(x => x.number));
    const s = await read(w), plan = sortPlan({ snapshot: s });
    assert.equal(plan.groups.length, 1); assert.equal(plan.groups[0].members.length, size);
    assert.equal(projectIssueGraph({ snapshot: s }).nodes.filter(x => x.eligible).length, 0);
  }
});

test('an empty completed pair is removed and the next snapshot remains readable', async () => {
  const w = fixture([1,2]); seed(w, [1,2]); await tick(w);
  assert.equal((await groups(w))[0].members.length, 2);
  w.issues.forEach(x => { x.state = 'closed'; }); await tick(w);
  const saved = await w.ports.sortGroups.read({ repository });
  assert.deepEqual(saved.groups, []);
  assert.equal((await read(w)).complete, true);
});

test('a later pending group advances after ten confirmed groups', async () => {
  const w = fixture(Array.from({ length: 33 }, (_, i) => i + 1));
  for (let n = 1; n <= 33; n++) { w.save(w.record(n, { rootCause: `cause-${Math.floor((n-1)/3)}` })); w.review(n); }
  await tick(w); assert.equal((await groups(w)).length, 11);
  assert.equal(w.writes.filter(x => x.kind === 'umbrella').length, 10);
  await tick(w); assert.equal(w.writes.filter(x => x.kind === 'umbrella').length, 11);
  await tick(w); assert.equal(w.writes.filter(x => x.kind === 'umbrella').length, 11);
});

test('native group state survives a fresh read from a real Git checkout', async t => {
  const cwd = mkdtempSync(join(tmpdir(), 'pdd-sort-store-'));
  t.after(() => rmSync(cwd, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q', cwd]);
  execFileSync('git', ['remote', 'add', 'origin', 'https://github.com/example/project.git'], { cwd });
  const w = fixture([1,2,3]); seed(w, [1,2,3]); delete w.ports.sortGroups;
  // Git is real. GitHub remains the fixture. Repository resolution has a fake CLI reply.
  w.ports.execFile = async (file, args, options) => {
    if (file === 'git') return { code: 0, stdout: execFileSync(file, args, { cwd: options.cwd, encoding: 'utf8' }) };
    assert.equal(file, 'gh');
    return { code: 0, stdout: JSON.stringify({ nameWithOwner: repository, url: `https://github.com/${repository}` }) };
  };
  await reconcileDependencyIntake({ cwd, repository, mode: 'auto' }, w.ports);
  const after = (await readDependencySnapshot({ cwd, repository }, { ...w.ports })).snapshot;
  assert.equal(after.sortContext.groups?.length, 1);
  assert.equal(after.sortContext.groups[0].members.length, 3);
  assert.ok(after.issues.some(x => x.key === after.sortContext.groups[0].umbrella));
});

test('an empty dedicated umbrella stays held instead of becoming ordinary work', async () => {
  const w = fixture([1,2,3]); seed(w, [1,2,3]); await tick(w);
  const [group] = await groups(w), n = Number(group.umbrella.split('/').pop()); seed(w, [n]);
  w.issues.slice(0,3).forEach(x => { x.state = 'closed'; }); await tick(w);
  const s = await read(w), node = projectIssueGraph({ snapshot: s }).nodes.find(x => x.key === group.umbrella);
  assert.equal(node.eligible, false);
  assert.deepEqual(s.sortContext.groups[0].members, []);
});

test('a merged pair work issue forces a fresh sort of its remaining member', async () => {
  const options = {}, w = fixture([1,2], options); seed(w, [1,2]); await tick(w);
  const [group] = await groups(w); assert.equal(group.umbrella, key(1));
  w.issues[0].state = 'closed'; options.mergedFix = 'https://github.com/example/project/pull/90';
  await tick(w);
  const prepared = await prepareDependencyIntake({ repository }, w.ports);
  assert.deepEqual(prepared.queued, [key(2)]);
  assert.equal((await groups(w))[0].merged, options.mergedFix);
  assert.equal(projectIssueGraph({ snapshot: await read(w) }).nodes.find(x => x.key === key(2)).eligible, false);
});

test('ambiguous cause markers cannot select a recovery umbrella', async () => {
  const w = fixture([1,2,3,100,101]); seed(w, [1,2,3]);
  for (const n of [100,101]) {
    w.issues.find(x => x.number === n).body = '<!-- pdd-issue-group:v1 shared-context -->'; seed(w, [n]);
  }
  await tick(w);
  const [group] = await groups(w);
  assert.equal(group.umbrella, '');
  assert.equal(w.writes.filter(x => x.kind === 'umbrella').length, 0);
  assert.ok(projectIssueGraph({ snapshot: await read(w) }).nodes.every(x => !x.eligible));
});

test('a pair keeps its running work issue and no peer can start beside it', async () => {
  const w = fixture([1,2,3]); seed(w, [1,2]); await tick(w);
  assert.equal((await groups(w))[0].umbrella, key(1));
  w.issues[0].labels = ['pdd:working']; w.claims.push({ issue: key(1), active: true, owner: 'worker' });
  await tick(w);
  assert.equal((await groups(w))[0].umbrella, key(1));
  assert.deepEqual((await groups(w))[0].members, [key(1),key(2)]);
  assert.equal(projectIssueGraph({ snapshot: await read(w) }).nodes.find(x => x.key === key(2)).eligible, false);
  seed(w, [3]); await tick(w);
  assert.equal((await groups(w))[0].umbrella, key(1));
  assert.equal(w.writes.filter(x => x.kind === 'umbrella').length, 0);
  assert.ok(w.comments.get(1).some(x => x.body.includes(key(3)) && x.body.includes('pdd-issue-route:v1')));
});

test('a duplicate marker is held even when the dedicated umbrella is already saved', async () => {
  const w = fixture([1,2,3,100]); seed(w, [1,2,3]); await tick(w);
  const [group] = await groups(w); seed(w, [Number(group.umbrella.split('/').pop())]);
  w.issues.find(x => x.number === 100).body = '<!-- pdd-issue-group:v1 shared-context -->'; seed(w, [100]);
  await tick(w);
  const graph = projectIssueGraph({ snapshot: await read(w) });
  assert.equal(graph.nodes.find(x => x.key === key(100)).eligible, false);
  assert.equal(graph.nodes.filter(x => x.eligible).length, 0);
});
