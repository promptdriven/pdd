import test from 'node:test';
import assert from 'node:assert/strict';
import { prepareDependencyIntake, completeDependencyIntake } from '../src/issue-dependencies-intake.mjs';
import { readDependencySnapshot } from '../src/issue-dependencies-github.mjs';
import { dependencyLinks } from '../src/issue-dependencies.mjs';
import { reviewWorld, reviewAll, analysisFor, repository, key } from './helpers/incremental-review-fixture.mjs';

const read = async w => (await readDependencySnapshot({ repository }, w.ports)).snapshot;
function appendReview(w, number, record) {
  const review = structuredClone(record);
  for (const field of ['id', 'authority', 'intact']) delete review[field];
  w.append(number, `<!-- pdd-dependency-review:v1 -->\n\`\`\`json\n${JSON.stringify({ schema_version: 'pdd.dependency-review.v1', review })}\n\`\`\``);
}

test('removed incoming PDD link outside top 20 retains provenance and permits completion', async () => {
  const w = reviewWorld(50); await reviewAll(w);
  const full = await read(w), old = full.reviews.findLast(r => r.issue === key(3));
  appendReview(w, 3, { ...old, base: [old.id], dependencies: [{ key: key(50), reason: 'Requires schema first.', evidence: [key(50)] }], effects: 'confirmed' });
  const current = await read(w);
  const { request } = await prepareDependencyIntake({ repository, issue: '50' }, w.ports);
  const packet = JSON.parse(request.snapshotJson);
  const result = await completeDependencyIntake({ request, analysis: analysisFor(w, request) }, w.ports);
  assert.equal(result.state, 'complete', 'unchanged incoming removal must not manufacture input-changed');
  assert.deepEqual(dependencyLinks({ snapshot: packet, issue: key(50) }), dependencyLinks({ snapshot: current, issue: key(50) }));
  assert.equal(packet.issues.some(i => i.key === key(3)), false, 'provenance does not load its unselected host');
  const provenance = packet.reviews.findLast(r => r.issue === key(3));
  assert.deepEqual(provenance.inputs, []);
  assert.deepEqual(provenance.candidates, []);
  assert.equal(provenance.analysis.length, 0);
  assert.deepEqual(provenance.dependencies.map(d => d.key), [key(50)]);
  assert.ok(Buffer.byteLength(JSON.stringify(request)) < 2 * 1024 * 1024);

  // The same removal must still prohibit re-adding the person's removed link.
  const next = (await prepareDependencyIntake({ repository, issue: '3' }, w.ports)).request;
  const analysis = analysisFor(w, next), review = analysis.reviews[0];
  review.dependencies = [{ key: key(50), reason: 'Requires schema first.', evidence: [key(50)] }];
  review.outcome = 'pending'; review.effects = 'pending';
  await assert.rejects(completeDependencyIntake({ request: next, analysis }, w.ports), /invalid-analysis/);
});

test('a subject can replace a review that examined an issue outside top 20 without a prerequisite', async () => {
  const w = reviewWorld(50); await reviewAll(w);
  const full = await read(w), old = full.reviews.findLast(r => r.issue === key(50)), examined = full.issues.find(i => i.key === key(3));
  appendReview(w, 50, { ...old, base: [old.id], inputs: [...old.inputs, { key: examined.key, revision: examined.revision }] });
  w.issues[49].body += ' Changed requirement.';
  const { request } = await prepareDependencyIntake({ repository, issue: '50' }, w.ports);
  const result = await completeDependencyIntake({ request, analysis: analysisFor(w, request) }, w.ports);
  assert.equal(result.state, 'complete', 'retained examined issue must not manufacture observations-incomplete');
  const packet = JSON.parse(request.snapshotJson), observation = packet.issues.find(i => i.key === examined.key);
  assert.equal(observation.revision, examined.revision);
  assert.equal(observation.state, examined.state);
  assert.equal(observation.authority, examined.authority);
  assert.equal(observation.sortText, undefined);
  assert.equal(observation.sorts, undefined);
  assert.ok(packet.coverage.issues.some(i => i.key === examined.key && i.issue));
  assert.ok(Buffer.byteLength(JSON.stringify(request)) < 2 * 1024 * 1024);
});

test('sort required work uses saved state and contains only queued subjects', async () => {
  const w = reviewWorld(25); await reviewAll(w);
  let request = (await prepareDependencyIntake({ repository, issue: '25' }, w.ports)).request;
  let sort = JSON.parse(request.contextJson).sort;
  assert.deepEqual(sort.required, [], 'trimmed sorted neighbours must not require sort outputs');
  assert.deepEqual(sort.records.map(r => r.issue), [key(25)]);
  assert.ok(JSON.parse(request.snapshotJson).issues.filter(i => i.key !== key(25)).every(i => i.sorts === undefined && i.reviewSummary));

  // An actually unsorted neighbour is still outside this explicit request.
  w.comments.set(3, w.comments.get(3).filter(c => !c.body.includes('pdd-issue-sort:v1')));
  request = (await prepareDependencyIntake({ repository, issue: '25' }, w.ports)).request;
  sort = JSON.parse(request.contextJson).sort;
  assert.deepEqual(sort.required, []);
  assert.deepEqual(sort.records.map(r => r.issue), [key(25)]);

  w.issues[24].body += ' Changed requirement.';
  request = (await prepareDependencyIntake({ repository, issue: '25' }, w.ports)).request;
  sort = JSON.parse(request.contextJson).sort;
  assert.deepEqual(sort.required, [key(25)], 'a queued subject with a stale sort still needs sorting');
  assert.deepEqual(sort.records, []);
  assert.equal((await completeDependencyIntake({ request, analysis: analysisFor(w, request) }, w.ports)).state, 'complete');
});
