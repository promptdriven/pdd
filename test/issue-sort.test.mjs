import test from 'node:test';
import assert from 'node:assert/strict';
import { readDependencySnapshot } from '../src/issue-dependencies-github.mjs';
import { prepareDependencyIntake, reconcileDependencyIntake } from '../src/issue-dependencies-intake.mjs';
import { projectIssueGraph } from '../src/issue-dependencies.mjs';
import { sortPlan, confirmGroupAfterReproduce, splitGroupMember, sortClosingReferences, chunkGroupMembers } from '../src/issue-sort.mjs';
import { fixture, complete, repository, key } from './helpers/issue-sort-fixture.mjs';
const read = async w => (await readDependencySnapshot({ repository }, w.ports)).snapshot;
const graph = async w => projectIssueGraph({ snapshot: await read(w) });
const node = async (w, n = 1) => (await graph(w)).nodes.find(x => x.key === key(n));
const fixed = w => ({ ...w.record(1).status, state: 'fixed', fix: 'https://github.com/example/project/pull/90' });

test('ordinary labels do not reserve an issue; assignment still does', async () => {
  for (const label of ['person-work', 'pdd:manual']) {
    const w = fixture();
    w.issues[0].labels = [label];
    w.save(w.record(1)); w.review(1);
    const snapshot = await read(w);
    assert.deepEqual(snapshot.issues[0].holds, []);
    assert.equal(projectIssueGraph({snapshot}).nodes.find(row => row.key === key(1)).eligible, true);

    w.issues[0].assignees = [{login:'person'}];
    assert.equal((await node(w)).eligible, false);
    await reconcileDependencyIntake({repository, mode:'auto'}, w.ports);
    assert.equal(w.writes.length, 0);
  }
});

test('a current dependency review cannot start an unsorted issue', async () => {
  const w = fixture(); w.review(1);
  assert.equal((await node(w)).eligible, false, 'new work must wait for sort');
  const { request } = await prepareDependencyIntake({ repository }, w.ports);
  assert.deepEqual(request.issues, [key(1)]);
  assert.ok(JSON.parse(request.contextJson).sort?.draft?.areas.length);
});

test('completion validates and saves a sort record, and refuses malformed records before writes', async () => {
  const w = fixture();
  const result = await complete(w, [w.record(1)]);
  assert.equal(result.state, 'complete');
  assert.equal((await node(w)).sort?.action, 'work');
  const bad = fixture();
  await assert.rejects(complete(bad, [{ ...bad.record(1), severity: 'critical' }]), /invalid-analysis/);
  assert.equal(bad.writes.length, 0);
  const missingFix = fixture();
  await assert.rejects(complete(missingFix, [missingFix.record(1, { status: { state: 'fixed', release: '1.0.0', fix: 'fixed', evidence: ['done'] } })]), /invalid-analysis/);
  assert.equal(missingFix.writes.length, 0);
});

test('only changed sort inputs require a new record', async () => {
  const w = fixture([1, 2]); w.save(w.record(1)); w.review(1);
  assert.equal((await node(w)).sort?.action, 'work');
  w.issues[1].body += ' unrelated edit';
  assert.equal((await node(w)).sort?.action, 'work');
  w.issues[0].body += ' changed requirement';
  assert.equal((await node(w)).sort?.action, 'hold');
  assert.ok((await prepareDependencyIntake({ repository }, w.ports)).queued.includes(key(1)));
});

for (const change of ['comment','source','release','areas','edited-record','untrusted-record']) test(`${change} invalidates the saved sort`, async () => {
  const w = fixture(); const r = w.record(1);
  if (change === 'source') { r.inputs.push({ key: 'https://github.com/example/project/blob/HEAD/src/other.mjs', revision: 'old' }); w.files.set(r.inputs.at(-1).key, 'old'); }
  const saved = w.save(r); w.review(1);
  assert.equal((await node(w)).sort?.action, 'work');
  if (change === 'comment') w.append(1, 'A trusted requirement changed.');
  if (change === 'source') w.files.set(r.inputs.at(-1).key, 'new');
  if (change === 'release') w.context.release = '1.0.1';
  if (change === 'areas') w.context.areas = [{ name: 'cli', owner: 'someone', match: { paths: ['src/**'] } }];
  if (change === 'edited-record') saved.updated_at = '2026-11-07T13:00:00Z';
  if (change === 'untrusted-record') saved.user.login = 'outsider';
  assert.equal((await node(w)).sort?.action, 'hold');
});

for (const count of [1,2,3]) test(`${count} explicit areas resolve ahead of CODEOWNERS`, async () => {
  const areas = [{ name: 'cli', owner: 'autopilot', match: { paths: ['src/cli.mjs'] } }, { name: 'runtime', owner: 'runtime-owner', match: { keywords: ['interpreter'] } }, { name: 'docs', owner: 'docs-owner', match: { labels: ['documentation'] } }].slice(0, count);
  const w = fixture([1], { context: { areas, codeowners: '* @wrong-owner' } });
  w.save(w.record(1)); w.review(1);
  assert.equal((await node(w)).sort?.owner, 'autopilot');
  assert.equal((await node(w)).eligible, true);
});

test('CODEOWNERS uses its last match and unknown team ownership waits', async () => {
  const w = fixture([1], { context: { codeowners: '* @general\n/src/** @specific' } }); w.save(w.record(1)); w.review(1);
  assert.equal((await node(w)).sort?.owner, 'specific');
  w.context.codeowners += '\n/src/** @team/cli'; w.comments.get(1).length = 0; w.save(w.record(1)); w.review(1);
  assert.equal((await node(w)).sort?.action, 'question');
});

for (const mode of ['auto','observe']) test(`${mode} routes fixed issues with evidence and a reopen hint`, async () => {
  const w = fixture([1], { mode });
  assert.equal((await complete(w, [w.record(1, { status: fixed(w) })])).state, 'complete');
  const notes = w.writes.filter(x => x.body?.includes('pdd-issue-route:'));
  assert.equal(notes.length, 1);
  assert.match(notes[0].body, /https:\/\/github.com\/example\/project\/pull\/90/);
  assert.match(notes[0].body, /reopen/i);
  assert.equal(w.issues[0].state, mode === 'auto' ? 'closed' : 'open');
  assert.equal(w.issues[0].labels.includes('pdd:close-proposed'), mode === 'observe');
  assert.ok(w.writes.findIndex(x => x.kind === 'close') < 0 || w.writes.indexOf(notes[0]) < w.writes.findIndex(x => x.kind === 'close'));
});

for (const kind of ['duplicate','old-code','not-genuine']) test(`${kind} routes to closure`, async () => {
  const w = fixture(); const r = w.record(1);
  if (kind === 'old-code') { r.belongs.kind = 'old-code'; r.genuine.reason = 'The removed Python command owns this report.'; }
  else r.genuine = { kind, duplicateOf: kind === 'duplicate' ? key(2) : '', reason: 'No product defect remains.' };
  assert.equal((await complete(w, [r])).state, 'complete');
  assert.equal(w.issues[0].state, 'closed');
});

test('another login gets one note and an assignment, with no eligible start', async () => {
  const w = fixture([1], { context: { areas: [{ name: 'cli', owner: 'runtime-owner', match: { paths: ['src/**'] } }] } });
  assert.equal((await complete(w, [w.record(1)])).state, 'complete');
  assert.deepEqual(w.issues[0].assignees, [{ login: 'runtime-owner' }]);
  assert.equal((await node(w)).eligible, false);
  assert.equal(w.writes.filter(x => x.body?.includes('pdd-issue-route:')).length, 1);
});

test('another repository gets a link note and no start', async () => {
  const w = fixture([1], { context: { areas: [{ name: 'runtime', owner: 'repo:example/runtime', match: { repositories: ['example/runtime'] } }] } });
  const r = w.record(1, { belongs: { kind: 'repository', area: '', repository: 'example/runtime' } });
  assert.equal((await complete(w, [r])).state, 'complete');
  assert.equal((await node(w)).sort?.action, 'link');
  assert.equal((await node(w)).eligible, false);
  assert.equal(w.writes.filter(x => x.kind === 'assign').length, 0);
  assert.ok(w.writes.some(x => x.body?.includes('https://github.com/example/runtime')));
});

test('unsure gets needs-owner and one question, with no start or repeated note', async () => {
  const w = fixture(); const r = w.record(1, { belongs: { kind: 'unknown', area: '', repository: '' }, question: 'Which repository owns this parser?' });
  assert.equal((await complete(w, [r])).state, 'complete');
  assert.ok(w.issues[0].labels.includes('pdd:needs-owner'));
  await reconcileDependencyIntake({ repository, mode: 'auto' }, w.ports);
  assert.equal(w.writes.filter(x => x.body?.includes('pdd-issue-route:')).length, 1);
  assert.equal((await node(w)).eligible, false);
});

for (const owned of ['person','claim','unknown-assignees']) for (const action of ['close','assign']) test(`${owned} prevents ${action}`, async () => {
  const w = fixture([1], { context: { areas: [{ name: 'cli', owner: 'another-owner', match: { paths: ['src/**'] } }] } });
  w.save(w.record(1, action === 'close' ? { status: fixed(w) } : {})); w.review(1);
  if (owned === 'person') w.issues[0].assignees = [{ login: 'person' }];
  if (owned === 'unknown-assignees') delete w.issues[0].assignees;
  if (owned === 'claim') { w.issues[0].labels.push('pdd:working'); w.claims.push({ issue: key(1), active: true, owner: 'another-coordinator' }); }
  assert.equal((await node(w)).sort?.action, 'hold');
  await reconcileDependencyIntake({ repository, mode: 'auto' }, w.ports);
  assert.equal(w.writes.length, 0);
});

test('three issues with one cause select the first member as leader without a synthetic umbrella', async () => {
  const w = fixture([3,2,1]); for (const n of [1,2,3]) { w.save(w.record(n)); w.review(n); }
  const result = await graph(w);
  assert.deepEqual(result.nodes.filter(x => x.eligible).map(x => x.key), [key(1)]);
  assert.equal(result.groups.length, 1);
  assert.equal(result.groups[0].umbrella, key(1));
  assert.deepEqual(result.nodes.find(x => x.key === key(1)).sort?.members, [key(1),key(2),key(3)]);
  assert.equal((await prepareDependencyIntake({ repository }, w.ports)).queued.length, 0);
});

test('routing writes are serial and paced across issues', async () => {
  const w = fixture([1,2]); const result = await complete(w, [w.record(1, { status: fixed(w) }), w.record(2, { status: fixed(w) })]);
  assert.equal(result.state, 'complete');
  const effects = w.writes.filter(x => !x.body?.includes('pdd-dependency-review:'));
  assert.ok(effects.length >= 6);
  for (let i = 1; i < effects.length; i++) assert.ok(effects[i].at - effects[i - 1].at >= 1000);
});

test('same owningModule and component across area hints selects the first member as leader', async () => {
  const w = fixture([1,2,3], { context: { areas: [
    { name: 'cli', owner: 'autopilot', match: { paths: ['src/cli.mjs'] } },
    { name: 'docs', owner: 'autopilot', match: { paths: ['docs/**'] } },
  ] } });
  for (const n of [1,2,3]) { w.save(w.record(n, n === 3 ? { owningModule: 'src/cli.mjs', belongs: { kind: 'area', area: 'docs', repository: '' }, paths: ['docs/guide.md'] } : {})); w.review(n); }
  const g = await graph(w);
  assert.deepEqual(g.nodes.filter(x => x.eligible).map(x => x.key), [key(1)]);
  assert.equal(g.groups[0].umbrella, key(1));
  assert.deepEqual(g.groups[0].members, [key(1),key(2),key(3)]);
});

test('claimed member work is not pulled into a new group', async () => {
  const w = fixture([1,2,3]);
  for (const n of [1,2,3]) { w.save(w.record(n)); w.review(n); }
  w.issues[1].labels.push('pdd:working');
  assert.equal((await node(w, 1)).sort?.umbrella, key(1));
  assert.deepEqual((await node(w, 1)).sort?.members, [key(1),key(3)]);
  assert.equal((await node(w, 3)).eligible, false);
  assert.equal((await graph(w)).nodes.filter(x => x.eligible).length, 1);
});

test('another-owner handoff is the same in observe mode', async () => {
  const w = fixture([1], { mode: 'observe', context: { areas: [{ name: 'cli', owner: 'other-owner', match: { paths: ['src/**'] } }] } });
  assert.equal((await complete(w, [w.record(1)])).state, 'complete');
  assert.equal(w.issues[0].assignees[0]?.login, 'other-owner');
  assert.equal((await node(w)).eligible, false);
});

test('a new assignment between route writes prevents closing', async () => {
  const w = fixture(); const original = w.ports.github.appendComment;
  w.ports.github.appendComment = async args => {
    const result = await original(args);
    if (args.body.includes('pdd-issue-route:')) w.issues[0].assignees = [{ login: 'person' }];
    return result;
  };
  const result = await complete(w, [w.record(1, { status: fixed(w) })]);
  assert.equal(result.state, 'pending');
  assert.equal(w.issues[0].state, 'open');
  assert.equal(w.writes.filter(x => x.kind === 'close').length, 0);
});

test('a trusted sort with conflicting heads waits for a new decision', async () => {
  const w = fixture(); w.save(w.record(1)); w.review(1);
  assert.equal((await node(w)).sort?.action, 'work');
  w.save(w.record(1, { rootCause: 'another-cause' }));
  assert.equal((await node(w)).sort?.action, 'hold');
  assert.deepEqual((await prepareDependencyIntake({ repository }, w.ports)).queued, [key(1)]);
});

test('ownership gained during a pacing wait prevents further route writes', async () => {
  const w = fixture(); const sleep = w.ports.wait.sleep;
  w.ports.wait.sleep = async args => { await sleep(args); w.issues[0].assignees = [{ login: 'person' }]; };
  assert.equal((await complete(w, [w.record(1, { status: fixed(w) })])).state, 'pending');
  assert.equal(w.writes.filter(x => x.kind === 'close').length, 0);
  assert.equal(w.writes.filter(x => x.body?.includes('pdd-issue-route:')).length, 0);
});

test('an unconfirmed route comment cannot close the issue', async () => {
  const w = fixture(); const append = w.ports.github.appendComment;
  w.ports.github.appendComment = args => args.body.includes('pdd-issue-route:') ? Promise.resolve({ json: '{}' }) : append(args);
  assert.equal((await complete(w, [w.record(1, { status: fixed(w) })])).state, 'pending');
  assert.equal(w.issues[0].state, 'open');
  assert.equal(w.writes.filter(x => x.kind === 'close').length, 0);
});

test('off refuses a sort completion without effects', async () => {
  const w = fixture([1], { mode: 'off' });
  assert.equal((await complete(w, [w.record(1, { status: fixed(w) })])).state, 'pending');
  assert.equal(w.writes.length, 0);
  const raced = fixture(); let mode = 'auto';
  raced.ports.settings.read = async () => ({ mode });
  const append = raced.ports.github.appendComment;
  raced.ports.github.appendComment = async args => { const result = await append(args); if (args.body.includes('pdd-dependency-review:')) mode = 'off'; return result; };
  assert.equal((await complete(raced, [raced.record(1)])).state, 'pending');
  assert.equal(raced.writes.filter(x => x.body?.includes('pdd-issue-sort:')).length, 0);
});

test('a changed area label needs a fresh sort while PDD work labels do not', async () => {
  const w = fixture(); w.save(w.record(1)); w.review(1);
  assert.equal((await node(w)).sort?.action, 'work');
  w.issues[0].labels.push('pdd:close-proposed');
  assert.equal((await node(w)).sort?.action, 'work');
  w.issues[0].labels.push('runtime');
  assert.equal((await node(w)).sort?.action, 'hold');
});

test('without an area map, different area hints still form one default area', async () => {
  const w = fixture([1,2]);
  w.save(w.record(1)); w.review(1);
  w.save(w.record(2, { belongs: { kind: 'area', area: 'docs', repository: '' } })); w.review(2);
  assert.equal((await node(w)).sort?.area, 'default');
  assert.deepEqual((await graph(w)).nodes.filter(x => x.eligible).map(x => x.key), [key(1)]);
  w.issues[1].body += ' A new requirement.';
  assert.equal((await node(w)).eligible, false, 'the known sibling needs a fresh sort before a group run');
});

test('the coordinator packet redacts an outsider sort record', async () => {
  const w = fixture(); const c = w.save(w.record(1)); c.user.login = 'outsider';
  const { request } = await prepareDependencyIntake({ repository }, w.ports);
  const sorts = JSON.parse(request.snapshotJson).issues[0].sorts;
  assert.equal(sorts?.length, 1);
  assert.equal(sorts[0].record, null);
});

test('incomplete trusted comments cannot authorize closure', async () => {
  const w = fixture(); w.save(w.record(1, { status: fixed(w) })); w.review(1);
  const page = w.ports.github.page;
  w.ports.github.page = async args => args.kind !== 'comments' ? page(args) : args.cursor ? { json: JSON.stringify({ error: 'Unavailable second page' }) } : { json: JSON.stringify({ items: w.comments.get(1), next: 'page2' }) };
  assert.equal((await node(w)).sort?.action, 'hold');
  await reconcileDependencyIntake({ repository, mode: 'auto' }, w.ports);
  assert.equal(w.writes.length, 0);
  assert.equal(w.issues[0].state, 'open');
});

test('an external repository cannot turn into local work through an Autopilot owner', async () => {
  const w = fixture([1], { context: { areas: [{ name: 'runtime', owner: 'autopilot', match: { repositories: ['example/runtime'] } }] } });
  w.save(w.record(1, { belongs: { kind: 'repository', area: 'runtime', repository: 'example/runtime' } })); w.review(1);
  assert.equal((await node(w)).sort?.action, 'link');
  assert.equal((await node(w)).eligible, false);
});

test('a missing examined path revision cannot authorize work', async () => {
  const w = fixture(); const r = w.record(1);
  r.inputs = r.inputs.filter(x => !x.key.includes('/blob/HEAD/'));
  w.save(r); w.review(1);
  assert.equal((await node(w)).sort?.action, 'hold');
  assert.equal((await node(w)).eligible, false);
});

for (const shape of ['not-planned','indirect-cycle']) test(`a group preserves ${shape} dependency holds`, async () => {
  const w = fixture([1,2]); for (const n of [1,2]) { w.save(w.record(n)); w.review(n); }
  const snapshot = await read(w), source = snapshot.issues[0];
  snapshot.issues.push({ ...source, key: key(4), title: 'External group prerequisite', sorts: [], state: shape === 'not-planned' ? 'not_planned' : 'open' });
  snapshot.coverage.issues.push({ ...snapshot.coverage.issues[0], key: key(4) });
  if (shape === 'not-planned') snapshot.edges.push({ dependent: key(2), blocker: key(4) });
  else snapshot.edges.push({ dependent: key(1), blocker: key(4) }, { dependent: key(4), blocker: key(2) });
  const result = projectIssueGraph({ snapshot });
  assert.deepEqual(result.nodes.find(x => x.key === key(1)).sort?.members, [key(1),key(2)]);
  assert.equal(result.nodes.find(x => x.key === key(1)).eligible, false);
  assert.equal(result.nodes.find(x => x.key === key(2)).eligible, false);
});

test('a trusted comment arriving during the pacing wait prevents closure', async () => {
  const w = fixture(); const sleep = w.ports.wait.sleep;
  w.ports.wait.sleep = async args => { await sleep(args); w.append(1, 'The issue still happens in the current release.'); };
  assert.equal((await complete(w, [w.record(1, { status: fixed(w) })])).state, 'pending');
  assert.equal(w.issues[0].state, 'open');
  assert.equal(w.writes.filter(x => x.kind === 'close').length, 0);
});

test('the area draft carries observed past assignees without assigning them', async () => {
  const w = fixture(); const page = w.ports.github.page;
  w.ports.github.page = args => args.kind === 'timeline' ? Promise.resolve({ json: JSON.stringify({ items: [{ event: 'assigned', assignee: { login: 'former-owner' } }], next: '' }) }) : page(args);
  const { request } = await prepareDependencyIntake({ repository }, w.ports);
  const draft = JSON.parse(request.contextJson).sort?.draft;
  assert.ok(draft?.signals.assignees.includes('former-owner'));
  assert.equal(w.issues[0].assignees.length, 0);
  assert.equal(w.writes.length, 0);
});

test('a changed area map replaces an undelivered sort request fingerprint', async () => {
  const w = fixture(); let saved = {}; const deliveries = [];
  w.ports.pending = { read: async () => ({ json: JSON.stringify(saved) }), save: async ({ json }) => { saved = JSON.parse(json); return { ok: true }; }, deliver: async ({ requestJson }) => { deliveries.push(JSON.parse(requestJson)); return { state: 'delivered' }; } };
  await reconcileDependencyIntake({ repository, mode: 'auto' }, w.ports);
  w.context.areas = [{ name: 'cli', owner: 'autopilot', match: { paths: ['src/**'] } }];
  await reconcileDependencyIntake({ repository, mode: 'auto' }, w.ports);
  assert.equal(deliveries.length, 2);
});

test('keyword rules can resolve an owner from the trusted issue body', async () => {
  const w = fixture([1], { context: { areas: [{ name: 'runtime', owner: 'runtime-owner', match: { keywords: ['hosted interpreter'] } }] } });
  w.issues[0].body = 'The hosted interpreter gives an invalid result.';
  w.save(w.record(1, { belongs: { kind: 'area', area: '', repository: '' } })); w.review(1);
  assert.equal((await node(w)).sort?.owner, 'runtime-owner');
  assert.equal((await node(w)).eligible, false);
});

test('a confirmed expired claim does not block a fixed-issue route', async () => {
  const w = fixture(); w.save(w.record(1, { status: fixed(w) })); w.review(1);
  w.issues[0].labels.push('pdd:working');
  w.claims.push({ issue: key(1), active: false, expired: true, lastSeen: '2026-11-06T01:00:00Z' });
  const context = w.ports.context.read;
  w.ports.context.read = async args => ({ json: JSON.stringify({ ...JSON.parse((await context(args)).json), nativeExecution: true }) });
  assert.equal((await node(w)).sort?.action, 'close');
  await reconcileDependencyIntake({ repository, mode: 'auto' }, w.ports);
  assert.equal(w.issues[0].state, 'closed');
});

test('groups form from shared owningModule + symbol even when free-text rootCause strings differ', async () => {
  const w = fixture([1, 2, 3]);
  w.save(w.record(1, {
    paths: ['prompts/cli/issue-sort.prompt.md'],
    symbol: 'sortPlan',
    rootCause: 'sortPlan requires exact string equality of free-form rootCause slugs',
  }));
  w.save(w.record(2, {
    paths: ['src/issue-sort.mjs'],
    symbol: 'sortPlan',
    rootCause: 'Completely different free-text rootCause phrasing for the same function',
  }));
  w.save(w.record(3, {
    paths: ['src/issue-sort.mjs'],
    symbol: 'validSort',
    rootCause: 'Unrelated symbol in the same module stays separate',
  }));
  for (const n of [1, 2, 3]) w.review(n);
  const g = await graph(w);
  assert.equal(g.groups.length, 1);
  assert.equal(g.groups[0].umbrella, key(1));
  assert.deepEqual(g.groups[0].members, [key(1), key(2)]);
  assert.deepEqual(g.nodes.filter(x => x.eligible).map(x => x.key), [key(1), key(3)]);
});

test('free-text rootCause equality alone or shared routing/doc files never form a group', async () => {
  const w = fixture([1, 2, 3, 4]);
  w.save(w.record(1, {
    paths: ['src/try-doors.mjs'],
    component: '',
    rootCause: 'Identical free-text description without structured signal',
  }));
  w.save(w.record(2, {
    paths: ['src/try-doors.mjs'],
    component: '',
    rootCause: 'Identical free-text description without structured signal',
  }));
  w.save(w.record(3, {
    paths: ['src/command-catalog.mjs', 'docs/cli.md'],
    symbol: 'PUBLIC_COMMAND_ROUTES',
    rootCause: 'Shared routing table and CLI docs touch',
  }));
  w.save(w.record(4, {
    paths: ['src/command-catalog.mjs', 'docs/cli.md'],
    symbol: 'PUBLIC_COMMAND_ROUTES',
    rootCause: 'Shared routing table and CLI docs touch',
  }));
  for (const n of [1, 2, 3, 4]) w.review(n);
  const plan = sortPlan({ snapshot: await read(w) });
  assert.deepEqual(plan.groups, []);
});

test('duplicates join the open target issue group before claiming', async () => {
  const w = fixture([1, 2, 3]);
  w.save(w.record(1, { paths: ['src/workflow-chat.mjs'], symbol: 'chatCommand', rootCause: 'chatCommand drops pane custody' }));
  w.save(w.record(2, { paths: ['src/workflow-chat.mjs'], component: '', duplicateOf: key(1), rootCause: 'Duplicate report of #1' }));
  w.save(w.record(3, { paths: ['src/workflow-chat.mjs'], symbol: 'chatCommand', rootCause: 'Another chatCommand pane custody failure' }));
  for (const n of [1, 2, 3]) w.review(n);
  const plan = sortPlan({ snapshot: await read(w) });
  assert.equal(plan.groups.length, 1);
  assert.equal(plan.groups[0].umbrella, key(1));
  assert.deepEqual(plan.groups[0].members, [key(1), key(2), key(3)]);
});

test('group size is capped at 2 to 5 issues and rebalances a trailing singleton', async () => {
  assert.deepEqual(chunkGroupMembers([1, 2, 3, 4, 5, 6]), [[1, 2, 3, 4], [5, 6]]);
  assert.deepEqual(chunkGroupMembers([1, 2, 3, 4, 5, 6, 7]), [[1, 2, 3, 4, 5], [6, 7]]);
  const w = fixture([1, 2, 3, 4, 5, 6, 7]);
  for (const n of [1, 2, 3, 4, 5, 6, 7]) {
    w.save(w.record(n, { paths: ['src/workflow-runner.mjs'], component: 'status-json', rootCause: `status json issue ${n}` }));
    w.review(n);
  }
  const plan = sortPlan({ snapshot: await read(w) });
  assert.equal(plan.groups.length, 2);
  assert.deepEqual(plan.groups[0].members, [key(1), key(2), key(3), key(4), key(5)]);
  assert.equal(plan.groups[0].umbrella, key(1));
  assert.deepEqual(plan.groups[1].members, [key(6), key(7)]);
  assert.equal(plan.groups[1].umbrella, key(6));
});

test('confirmGroupAfterReproduce and splitGroupMember split out a member that fails or turns out different', async () => {
  const group = {
    area: 'cli',
    rootCause: 'src/issue-sort.mjs:sortPlan',
    owningModule: 'src/issue-sort.mjs',
    signal: 'symbol:sortPlan',
    umbrella: key(1),
    members: [key(1), key(2), key(3)],
  };
  const afterRepro = confirmGroupAfterReproduce({
    group,
    reproduceResults: {
      [key(1)]: { confirmed: true, owningModule: 'src/issue-sort.mjs', symbol: 'sortPlan', summary: 'Reproduced in sortPlan' },
      [key(2)]: { confirmed: true, owningModule: 'prompts/cli/issue-sort.prompt.md', symbol: 'sortPlan', summary: 'Same symbol in sortPlan' },
      [key(3)]: { confirmed: true, owningModule: 'src/workflow-runner.mjs', symbol: 'stepDone', summary: 'Turned out to be in workflow-runner' },
    },
  });
  assert.equal(afterRepro.confirmed, true);
  assert.equal(afterRepro.umbrella, key(1));
  assert.deepEqual(afterRepro.members, [key(1), key(2)]);
  assert.deepEqual(afterRepro.splitOut, [key(3)]);
  assert.equal(afterRepro.standaloneRuns.length, 1);
  assert.equal(afterRepro.standaloneRuns[0].issue, key(3));

  const splitAgain = splitGroupMember({ group: afterRepro.group, member: key(2), reason: 'verify-failed' });
  assert.equal(splitAgain.umbrella, key(1));
  assert.deepEqual(splitAgain.members, [key(1)]);
  assert.deepEqual(splitAgain.splitOut, [key(3), key(2)]);
  assert.equal(splitAgain.group, null);
  assert.equal(splitAgain.standalone?.issue, key(2));
});

test('Assigned issues and Runtime-owned issues never join a group', async () => {
  const w = fixture([1, 2, 3, 4]);
  w.issues[2].assignees = [{ login: 'person' }];
  w.save(w.record(1, { paths: ['src/cli.mjs'], symbol: 'parseArgs', rootCause: 'cli bug 1' }));
  w.save(w.record(2, { paths: ['src/cli.mjs'], symbol: 'parseArgs', rootCause: 'cli bug 2' }));
  w.save(w.record(3, { paths: ['src/cli.mjs'], symbol: 'parseArgs', rootCause: 'assigned cli bug 3' }));
  w.save(w.record(4, { paths: ['src/runtime-client.mjs'], symbol: 'parseArgs', rootCause: 'runtime bug 4' }));
  for (const n of [1, 2, 3, 4]) w.review(n);
  const plan = sortPlan({ snapshot: await read(w) });
  assert.equal(plan.groups.length, 1);
  assert.deepEqual(plan.groups[0].members, [key(1), key(2)]);
  assert.ok(!plan.groups[0].members.includes(key(3)));
  assert.ok(!plan.groups[0].members.includes(key(4)));

  const wRuntime = fixture([5, 6]);
  for (const n of [5, 6]) {
    wRuntime.save(wRuntime.record(n, { paths: ['src/runtime-preflight.mjs'], symbol: 'captureSource', rootCause: `runtime preflight ${n}` }));
    wRuntime.review(n);
  }
  const runtimePlan = sortPlan({ snapshot: await read(wRuntime) });
  assert.deepEqual(runtimePlan.groups, []);
});

test('per-member reproduce and test evidence are required before Closes #N is emitted', async () => {
  const w = fixture([1, 2, 3]);
  for (const n of [1, 2, 3]) {
    w.save(w.record(n, { paths: ['src/issue-sort.mjs'], symbol: 'sortPlan', rootCause: `cause ${n}` }));
    w.review(n);
  }
  const snapshot = await read(w);
  const g = projectIssueGraph({ snapshot });
  assert.deepEqual(
    sortClosingReferences({ snapshot, issue: key(1), code: true, graph: g }),
    [`Refs ${key(2)}`, `Refs ${key(3)}`],
  );
  assert.deepEqual(
    sortClosingReferences({
      snapshot,
      issue: key(1),
      code: true,
      graph: g,
      memberEvidence: {
        [key(2)]: { reproduce: 'Failed before fix on sortPlan', test: 'test/issue-sort.test.mjs:groups form' },
        [key(3)]: { reproduce: 'Failed before fix on sortPlan', test: '' },
      },
    }),
    ['Closes #2'],
  );
  assert.deepEqual(
    sortClosingReferences({
      snapshot,
      issue: key(1),
      code: true,
      graph: g,
      memberEvidence: {
        '#2': { reproduce: 'Failed before fix on #2', test: 'test/issue-sort.test.mjs:case-2' },
        '#3': { reproduce: 'Failed before fix on #3', test: 'test/issue-sort.test.mjs:case-3' },
      },
    }),
    ['Closes #2', 'Closes #3'],
  );
});
