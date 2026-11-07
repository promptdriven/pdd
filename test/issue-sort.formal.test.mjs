import test from 'node:test';
import assert from 'node:assert/strict';
import { readDependencySnapshot } from '../src/issue-dependencies-github.mjs';
import { reconcileDependencyIntake } from '../src/issue-dependencies-intake.mjs';
import { projectIssueGraph } from '../src/issue-dependencies.mjs';
import { fixture, repository, key } from './helpers/issue-sort-fixture.mjs';

test('bounded ownership rule: 2 modes x 3 ownership states x 3 routes', async () => {
  for (const mode of ['auto','observe']) for (const ownership of ['free','person','claim']) for (const route of ['close','assign','question']) {
    const w = fixture([1], { mode, context: { areas: [{ name: 'cli', owner: route === 'assign' ? 'other-owner' : 'autopilot', match: { paths: ['src/**'] } }] } });
    const r = w.record(1);
    if (route === 'close') r.status = { ...r.status, state: 'fixed', fix: 'https://github.com/example/project/pull/90' };
    if (route === 'question') r.belongs.kind = 'unknown';
    w.save(r); w.review(1);
    if (ownership === 'person') w.issues[0].assignees = [{ login: 'person' }];
    if (ownership === 'claim') { w.issues[0].labels.push('pdd:working'); w.claims.push({ issue: key(1), active: true, owner: 'other' }); }
    const snapshot = (await readDependencySnapshot({ repository }, w.ports)).snapshot;
    const node = projectIssueGraph({ snapshot }).nodes[0];
    assert.equal(node.sort?.action, ownership === 'free' ? route : 'hold');
    assert.equal(node.eligible, false);
    await reconcileDependencyIntake({ repository, mode }, w.ports);
    if (ownership !== 'free') assert.equal(w.writes.length, 0);
    else {
      assert.equal(w.writes.filter(x => x.kind === 'close').length, route === 'close' && mode === 'auto' ? 1 : 0);
      assert.equal(w.writes.filter(x => x.kind === 'assign').length, route === 'assign' ? 1 : 0);
    }
  }
});

test('bounded group rule: sizes 1..3, cause counts 1..3, one eligible run per cause', async () => {
  for (const size of [1,2,3]) for (const causes of [1,2,3]) {
    const numbers = Array.from({ length: size }, (_, i) => i + 1), w = fixture(numbers);
    for (const n of numbers) { w.save(w.record(n, { rootCause: `cause-${n % causes}` })); w.review(n); }
    const snapshot = (await readDependencySnapshot({ repository }, w.ports)).snapshot;
    const graph = projectIssueGraph({ snapshot });
    assert.equal(graph.nodes.filter(x => x.eligible).length, Math.min(size, causes));
    assert.ok(graph.nodes.every(x => x.sort?.action === 'work'));
  }
});
