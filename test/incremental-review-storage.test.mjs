import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { readSortGroups, syncSortGroups } from '../src/issue-sort-github.mjs';
import { readDependencySnapshot } from '../src/issue-dependencies-github.mjs';
import { prepareDependencyIntake, completeDependencyIntake } from '../src/issue-dependencies-intake.mjs';
import { reviewWorld, analysisFor, repository, key } from './helpers/incremental-review-fixture.mjs';
import { autopilotGithubWorld, analysisFor as nativeAnalysis } from './helpers/autopilot-github-world.mjs';

for (const fallback of [false, true]) test(`group memory imports once and saves through machine storage (${fallback ? 'snapshot' : 'sqlite'})`, async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-review-storage-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const commonDir = join(root, 'git'), state = join(root, 'state');
  mkdirSync(join(commonDir, 'pdd'), { recursive: true });
  const file = join(commonDir, 'pdd', `issue-groups-${createHash('sha256').update(repository).digest('hex').slice(0, 16)}.json`);
  const group = { area: 'cli', rootCause: 'shared-context', umbrella: key(1), members: [key(1)] };
  const legacy = JSON.stringify({ groups: [group] }); writeFileSync(file, legacy);
  const w = reviewWorld(1), ports = { ...w.ports, sortGroups: undefined, autopilotStateRoot: state,
    ...(fallback ? { sqlite: null } : {}), execFile: async (_file, args) => ({ stdout: args.includes('--show-toplevel') ? root : commonDir }) };
  assert.deepEqual(await readSortGroups({ cwd: root, repository }, ports), [group]);
  w.issues[0].state = 'closed';
  const snapshot = (await readDependencySnapshot({ repository }, w.ports)).snapshot;
  snapshot.sortContext.groups = [group];
  await syncSortGroups({ cwd: root, repository, snapshot, mode: 'observe' }, ports);
  assert.equal(readFileSync(file, 'utf8'), legacy);
  // An older process must not resurrect the imported group after a restart.
  assert.deepEqual(await readSortGroups({ cwd: root, repository }, { ...ports }), []);
});

test('a completion retry saves unfinished sorts without appending its saved review again', async () => {
  const w = reviewWorld(1), { request } = await prepareDependencyIntake({ repository }, w.ports);
  const analysis = analysisFor(w, request), append = w.ports.github.appendComment;
  let fail = true;
  w.ports.github.appendComment = async args => {
    if (fail && args.body.includes('pdd-issue-sort:v1')) { fail = false; throw Error('injected pre-transport failure'); }
    return append(args);
  };
  const first = await completeDependencyIntake({ request, analysis: structuredClone(analysis) }, w.ports);
  assert.equal(first.state, 'pending'); assert.equal(first.pendingStage, 'sort');
  const next = await completeDependencyIntake({ request, analysis: structuredClone(analysis) }, w.ports);
  assert.equal(next.state, 'complete');
  assert.equal((await completeDependencyIntake({ request, analysis: structuredClone(analysis) }, w.ports)).state, 'complete');
  assert.equal(w.comments.get(1).filter(c => c.body.includes('pdd-dependency-review:v1')).length, 1);
  assert.equal(w.comments.get(1).filter(c => c.body.includes('pdd-issue-sort:v1')).length, 1);
});

test('native stored review and sort survive a new command and an unrelated source change', async t => {
  const w = await autopilotGithubWorld({ issues: 1 }); t.after(() => w.cleanup());
  assert.equal((await w.invoke('start')).exitCode, 0);
  const request = w.requests[0], context = JSON.parse(request.contextJson), snapshot = JSON.parse(request.snapshotJson);
  const analysis = nativeAnalysis(request);
  const background = `https://github.com/${w.repository}/blob/HEAD/src/widget.mjs`;
  analysis.reviews[0].inputs.push({ key: background, revision: createHash('sha256').update(readFileSync(join(w.cwd, 'src/widget.mjs'))).digest('hex') });
  assert.ok(context.sort);
  analysis.sorts = request.issues.map(issue => ({ schema_version: 'pdd.issue-sort.v1', issue, base: [],
    inputs: snapshot.inputs.filter(x => x.key === context.sort.key || x.key === `${issue}#sort-labels`)
      .concat(snapshot.issues.filter(x => x.key === issue).map(({ key, revision }) => ({ key, revision }))),
    belongs: { kind: 'area', area: 'cli', repository: '' },
    status: { state: 'still-happens', release: context.sort.release, fix: '', evidence: [issue] },
    genuine: { kind: 'bug', duplicateOf: '', reason: '' }, paths: [], rootCause: 'single-context', severity: 'medium', question: '' }));
  const result = await w.complete(request, analysis, w.commandPorts({ wait: { sleep: async ({ ms }) => { w.time += ms; } } }));
  assert.equal(result.result.state, 'complete', JSON.stringify(result));
  writeFileSync(join(w.cwd, 'src/widget.mjs'), 'export const widget = 2;\n');
  const next = await prepareDependencyIntake({ cwd: w.cwd, repository: w.repository }, w.commandPorts());
  assert.deepEqual(next.queued, []);
  const current = (await readDependencySnapshot({ cwd: w.cwd, repository: w.repository }, w.commandPorts())).snapshot;
  assert.equal(current.reviews.length, 1);
  assert.equal(current.issues[0].sorts.length, 1);
  assert.ok(current.issues[0].sorts[0].record.summary);
});
