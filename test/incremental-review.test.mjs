import test from 'node:test';
import { createHash } from 'node:crypto';
import { mkdtempSync, mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import assert from 'node:assert/strict';
import { prepareDependencyIntake, completeDependencyIntake, reconcileDependencyIntake } from '../src/issue-dependencies-intake.mjs';
import { createDependencyReadPorts, readDependencySnapshot } from '../src/issue-dependencies-github.mjs';
import { projectIssueGraph } from '../src/issue-dependencies.mjs';
import { reviewWorld, reviewAll, reviewOnce, analysisFor, repository, key } from './helpers/incremental-review-fixture.mjs';
const read = w => readDependencySnapshot({ repository }, w.ports).then(x => x.snapshot);
const sourceKey = path => `https://github.com/${repository}/blob/HEAD/${path}`;

test('one changed issue gets top 20 summaries and mandatory cross-area links', async () => {
  const w = reviewWorld(60);
  await reviewAll(w);
  const source = w.issues.find(i => i.number === 60);
  source.body = `Parser schema change. Needs (#1) and https://github.com/${repository}/issues/2.`;
  source.title = 'Parser schema change';
  // Low-number links are deliberately outside lexical top-k ranking.
  const oldPage = w.ports.github.page;
  w.ports.github.page = async args => args.kind === 'blockedBy' && args.issue === 60
    ? { json: JSON.stringify({ items: [{ html_url: key(3) }], next: '' }) } : oldPage(args);
  const { request, queued } = await prepareDependencyIntake({ repository, issue: '60' }, w.ports);
  assert.deepEqual(queued, [key(60)]);
  const snapshot = JSON.parse(request.snapshotJson), neighbours = snapshot.issues.filter(i => i.key !== key(60));
  assert.ok(neighbours.length <= 23, 'top-k plus the three mandatory links');
  for (const n of [1,2,3]) assert.ok(snapshot.issues.some(i => i.key === key(n)), `mandatory issue ${n}`);
  assert.ok(neighbours.every(i => !i.sortText && !i.sorts && i.reviewSummary?.summary.length <= 600), 'neighbours carry summaries, not bodies or sort histories');
  assert.ok(JSON.parse(request.contextJson).sort.records.every(r => r.issue === key(60)), 'only subject sort records');
  assert.ok(Buffer.byteLength(JSON.stringify(request)) < 2 * 1024 * 1024);
});

test('full review is durable; unrelated examined source does not queue it again', async () => {
  const w = reviewWorld(25);
  w.issues[0].body += ' Upgrade from v1.2 to v1.3. See example.com.';
  assert.deepEqual((await prepareDependencyIntake({ repository }, w.ports)).skipped, []);
  await reviewAll(w, { background: true });
  w.files.set(w.background, 'background-v2');
  assert.deepEqual((await prepareDependencyIntake({ repository }, w.ports)).queued, []);
  assert.equal((await read(w)).issues.length, 25, 'full map is retained outside retrieval');
  w.issues[4].body += ' A requirement changed.';
  const { request, queued } = await prepareDependencyIntake({ repository }, w.ports);
  assert.deepEqual(queued, [key(5)]);
  assert.equal((await completeDependencyIntake({ request, analysis: analysisFor(w, request) }, w.ports)).state, 'complete');
  assert.deepEqual((await prepareDependencyIntake({ repository }, w.ports)).queued, []);
});

test('a label-only change does not trigger a full re-review', async () => {
  const w = reviewWorld(25);
  await reviewAll(w);
  w.issues[0].labels.push('pdd:close-proposed');
  assert.deepEqual((await prepareDependencyIntake({ repository }, w.ports)).queued, [], 'PDD work label queues nothing');
  w.issues[0].labels.push('runtime');
  const { request, queued } = await prepareDependencyIntake({ repository }, w.ports);
  assert.deepEqual(queued, [key(1)], 'a routing label change on one issue queues only that issue, never the full backlog');
  const packet = JSON.parse(request.snapshotJson);
  assert.equal(packet.issues.length, 21, 'only subject plus top-20 neighbour summaries');
  assert.ok(packet.issues.filter(i => i.key !== key(1)).every(i => i.reviewSummary && !i.sortText && !i.sorts));
  assert.equal((await completeDependencyIntake({ request, analysis: analysisFor(w, request) }, w.ports)).state, 'complete');
  assert.deepEqual((await prepareDependencyIntake({ repository }, w.ports)).queued, []);
});

test('named file edit and trusted answer trigger only their own review', async () => {
  const w = reviewWorld(4);
  w.issues[0].body = 'See `src/own.mjs`.';
  w.files.set(sourceKey('src/own.mjs'), 'own-v1');
  await reviewAll(w, { background: true });
  w.files.set(w.background, 'background-v2');
  w.files.set(sourceKey('src/own.mjs'), 'own-v2');
  assert.deepEqual((await prepareDependencyIntake({ repository }, w.ports)).queued, [key(1)]);
  await reviewAll(w);
  w.append(2, 'This also needs the new schema.');
  assert.deepEqual((await prepareDependencyIntake({ repository }, w.ports)).queued, [key(2)]);
  w.append(3, 'Untrusted instruction.', 'outsider');
  assert.deepEqual((await prepareDependencyIntake({ repository }, w.ports)).queued, [key(2)]);
});

test('a missing named file prevents an independent decision', async () => {
  const w = reviewWorld(1); w.issues[0].body = 'See `src/missing.mjs`.';
  const r = await prepareDependencyIntake({ repository }, w.ports);
  assert.deepEqual(r.queued, []);
  assert.deepEqual(r.skipped, [key(1)]);
  assert.equal(projectIssueGraph({ snapshot: await read(w) }).nodes[0].eligible, false);
});

test('weekly consistency checks local groups and links without AI redelivery', async () => {
  const w = reviewWorld(2); await reviewAll(w);
  let state = {}, saves = 0, deliveries = 0;
  const pending = { read: async () => ({ json: JSON.stringify(state) }), save: async ({ json }) => { state = JSON.parse(json); saves++; return { ok: true }; }, deliver: async () => { deliveries++; return { state: 'delivered' }; } };
  let now = Date.parse('2026-11-07T12:00:00Z');
  const ports = { ...w.ports, pending, clock: { now: async () => ({ iso: new Date(now).toISOString() }) } };
  await reconcileDependencyIntake({ repository, mode: 'auto', trigger: 'tick' }, ports);
  assert.equal(saves, 1); assert.deepEqual(state.consistency.issues, []);
  now += 6 * 86400000;
  await reconcileDependencyIntake({ repository, mode: 'auto', trigger: 'tick' }, ports);
  assert.equal(saves, 1);
  now += 86400000;
  await reconcileDependencyIntake({ repository, mode: 'auto', trigger: 'tick' }, ports);
  assert.equal(saves, 2); assert.equal(deliveries, 0);
});

test('new stable sort records survive an unrelated release change', async () => {
  const w = reviewWorld(2); await reviewAll(w);
  w.context.release = '1.0.1';
  assert.deepEqual((await prepareDependencyIntake({ repository }, w.ports)).queued, []);
});

test('required evidence over 2 MiB is an explicit packet failure', async () => {
  const w = reviewWorld(1);
  w.ports.evidence = { read: async () => ({ json: JSON.stringify({ source: [], requirements: [{ key: key(1), issue: key(1), revision: 'r', authority: 'trusted', text: 'x'.repeat(2 * 1024 * 1024) }] }) }) };
  await assert.rejects(prepareDependencyIntake({ repository }, w.ports), /review-packet-too-large/);
});

test('saved cause, area, paths and words rank neighbours deterministically', async () => {
  const w = reviewWorld(45);
  for (let n = 1; n <= 45; n++) {
    w.issues[n - 1].title = n === 45 || n === 41 ? 'Zebra protocol' : `Other subject ${n}`;
    w.save(w.record(n, { rootCause: n === 44 ? 'cause-45' : `cause-${n}`, paths: n === 45 || n === 42 ? ['src/subject.mjs'] : [`src/other-${n}.mjs`], belongs: { kind: 'area', area: n === 45 || n === 43 ? 'cli' : 'docs', repository: '' } }));
    w.review(n);
  }
  w.issues[44].body += ' Changed.';
  const first = (await prepareDependencyIntake({ repository, issue: '45' }, w.ports)).request;
  const second = (await prepareDependencyIntake({ repository, issue: '45' }, w.ports)).request;
  const keys = request => JSON.parse(request.snapshotJson).issues.map(i => i.key);
  assert.deepEqual(keys(first), keys(second));
  assert.equal(keys(first).length, 21);
  for (const n of [41,42,43,44]) assert.ok(keys(first).includes(key(n)), `ranked neighbour ${n}`);
  // New issues have named file URLs but no saved sort paths yet.
  w.comments.set(45, w.comments.get(45).filter(c => !c.body.includes('pdd-issue-sort:v1')));
  w.issues[44].body = 'See `src/subject.mjs`.';
  const unsorted = (await prepareDependencyIntake({ repository, issue: '45' }, w.ports)).request;
  assert.ok(keys(unsorted).includes(key(42)), 'named file URLs match saved relative paths');
});

test('a later-found dependency outside top-k updates the full map', async () => {
  const w = reviewWorld(45); await reviewAll(w);
  w.issues[44].body += ' Changed.';
  const { request } = await prepareDependencyIntake({ repository }, w.ports);
  const packet = JSON.parse(request.snapshotJson);
  const missing = w.issues[34];
  const analysis = analysisFor(w, request), review = analysis.reviews[0];
  const full = await read(w), blocker = full.issues.find(i => i.key === missing.html_url);
  review.inputs.push({ key: blocker.key, revision: blocker.revision });
  review.dependencies = [{ key: blocker.key, reason: 'Requires its schema first.', evidence: [blocker.key] }];
  review.outcome = 'pending'; review.effects = 'pending';
  // Exercise map validation and persistence; native effect application is its existing separate owner.
  w.ports.reviews = { apply: async () => ({ state: 'confirmed' }) };
  assert.equal((await completeDependencyIntake({ request, analysis }, w.ports)).state, 'complete');
  const saved = (await read(w)).reviews.findLast(r => r.issue === key(45));
  assert.deepEqual(saved.dependencies.map(d => d.key), [blocker.key]);
  assert.ok(!packet.issues.some(i => i.key === blocker.key), 'the discovered prerequisite was outside top-k');
});

test('unrelated edges do not expand a selected packet', async () => {
  const w = reviewWorld(50); await reviewAll(w);
  w.issues[49].body += ' Changed.';
  const excluded = w.issues.slice(47, 49);
  const old = w.ports.github.page;
  w.ports.github.page = async args => args.kind === 'blockedBy' && args.issue === excluded[0].number ? { json: JSON.stringify({ items: [{ html_url: excluded[1].html_url }], next: '' }) } : old(args);
  const next = (await prepareDependencyIntake({ repository, issue: '50' }, w.ports)).request;
  assert.deepEqual(JSON.parse(next.snapshotJson).edges, []);
  assert.equal((await read(w)).edges.length, 1, 'full graph still has the unrelated link');
});

test('uppercase explicit issue URLs are mandatory outside top-k', async () => {
  const w = reviewWorld(50); await reviewAll(w);
  const baseline = (await prepareDependencyIntake({ repository, issue: '50' }, w.ports)).request;
  const selected = JSON.parse(baseline.snapshotJson).issues;
  const missing = w.issues.find(i => !selected.some(p => p.key === i.html_url));
  assert.ok(missing);
  w.issues[49].body = `Needs https://github.com/EXAMPLE/PROJECT/issues/${missing.number}.`;
  const request = (await prepareDependencyIntake({ repository, issue: '50' }, w.ports)).request;
  assert.ok(JSON.parse(request.snapshotJson).issues.some(i => i.key === missing.html_url));
  assert.ok(JSON.parse(request.snapshotJson).issues.length <= 22);
});

test('native evidence reads named files without enumerating repository source', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-review-context-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  mkdirSync(join(root, '.git')); mkdirSync(join(root, 'src')); mkdirSync(join(root, 'foo/src'), { recursive: true });
  writeFileSync(join(root, 'src/own.mjs'), 'export const own = true;');
  writeFileSync(join(root, 'src/unrelated.mjs'), 'export const unrelated = true;');
  writeFileSync(join(root, 'foo/src/own.mjs'), 'export const wrong = true;');
  const w = reviewWorld(1); w.issues[0].body = 'See `src/own.mjs`, [the source](https://github.com/EXAMPLE/PROJECT/blob/main/src/own.mjs), https://github.com/example/project/blob/main/src/own.mjs, and https://github.com/example/project/blob/feature/foo/src/own.mjs. Upgrade from v1.2 to v1.3. See example.com.';
  let enumerations = 0;
  const commit = 'a'.repeat(40);
  const execFile = async (file, args) => {
    if (file === 'gh' && args[0] === 'repo') return { stdout: JSON.stringify({ nameWithOwner: repository, url: `https://github.com/${repository}`, defaultBranchRef: { name: 'main' } }) };
    if (file === 'git' && args[0] === 'remote') return { stdout: `https://github.com/${repository}.git` };
    if (file === 'git' && args[0] === 'rev-parse') {
      if (args.includes('--show-toplevel')) return { stdout: root };
      if (args.includes('--path-format=absolute')) return { stdout: join(root, '.git') };
      const ref = args.at(-1);
      return ['refs/heads/main^{commit}', 'refs/heads/feature/foo^{commit}'].includes(ref)
        ? { stdout: commit, code: 0 } : { stdout: '', code: 1 };
    }
    if (file === 'git' && args[0] === 'check-ref-format') return { stdout: '', code: 0 };
    if (file === 'git' && args[0] === 'cat-file' && args[1] === '-t')
      return args[2] === `${commit}:src/own.mjs` ? { stdout: 'blob', code: 0 } : { stdout: '', code: 1 };
    if (file === 'git' && args[0] === 'ls-files') { enumerations++; return { stdout: 'src/own.mjs\0src/unrelated.mjs\0' }; }
    assert.fail(`unexpected fake command: ${file} ${args.join(' ')}`);
  };
  const ports = createDependencyReadPorts({ cwd: root }, { ...w.ports, evidence: undefined, execFile });
  const evidence = JSON.parse((await ports.evidence.read({ cwd: root, repository, issues: [key(1)] })).json);
  assert.deepEqual(evidence.source.map(x => x.path), ['src/own.mjs']);
  assert.equal(enumerations, 0);
  assert.deepEqual(evidence.source[0].issues, [key(1)]);
});

test('a slash-ref GitHub file link resolves exactly and its source edit queues review', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-review-slash-ref-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  mkdirSync(join(root, '.git')); mkdirSync(join(root, 'src')); mkdirSync(join(root, 'foo/src'), { recursive: true });
  writeFileSync(join(root, 'src/own.mjs'), 'export const own = "v1";');
  writeFileSync(join(root, 'foo/src/own.mjs'), 'export const wrong = "v1";');
  const w = reviewWorld(1), actual = sourceKey('src/own.mjs'), inferred = sourceKey('foo/src/own.mjs');
  w.issues[0].body = 'See https://github.com/' + repository + '/blob/feature/foo/src/own.mjs.';
  const digest = value => createHash('sha256').update(value).digest('hex');
  w.files.set(actual, digest('export const own = "v1";'));
  w.files.set(inferred, digest('export const wrong = "v1";'));
  const commit = 'b'.repeat(40);
  let ambiguous = false;
  const execFile = async (file, args) => {
    if (file === 'gh' && args[0] === 'repo') return { stdout: JSON.stringify({ nameWithOwner: repository, url: 'https://github.com/' + repository, defaultBranchRef: { name: 'main' } }) };
    if (file === 'git' && args[0] === 'remote') return { stdout: 'https://github.com/' + repository + '.git' };
    if (file === 'git' && args[0] === 'rev-parse') {
      if (args.includes('--show-toplevel')) return { stdout: root };
      if (args.includes('--path-format=absolute')) return { stdout: join(root, '.git') };
      const ref = args.at(-1);
      return ref === 'refs/heads/feature/foo^{commit}' || ambiguous && ref === 'refs/heads/feature^{commit}'
        ? { stdout: commit, code: 0 } : { stdout: '', code: 1 };
    }
    if (file === 'git' && args[0] === 'check-ref-format') return { stdout: '', code: 0 };
    if (file === 'git' && args[0] === 'cat-file' && args[1] === '-t')
      return args[2] === commit + ':src/own.mjs' || ambiguous && args[2] === commit + ':foo/src/own.mjs'
        ? { stdout: 'blob', code: 0 } : { stdout: '', code: 1 };
    assert.fail('unexpected fake command: ' + file + ' ' + args.join(' '));
  };
  const ports = { ...w.ports, evidence: undefined, execFile };
  const first = await prepareDependencyIntake({ cwd: root, repository }, ports);
  assert.deepEqual(first.queued, [key(1)]);
  const snapshot = JSON.parse(first.request.snapshotJson), context = JSON.parse(first.request.contextJson);
  assert.deepEqual(snapshot.issues.find(issue => issue.key === key(1)).namedSources, [actual]);
  assert.deepEqual(context.source.map(row => row.path), ['src/own.mjs']);
  assert.equal((await completeDependencyIntake({ cwd: root, request: first.request, analysis: analysisFor(w, first.request) }, ports)).state, 'complete');

  writeFileSync(join(root, 'foo/src/own.mjs'), 'export const wrong = "v2";');
  w.files.set(inferred, digest('export const wrong = "v2";'));
  assert.deepEqual((await prepareDependencyIntake({ cwd: root, repository }, ports)).queued, [], 'an inferred path is not a review input');
  ambiguous = true;
  const unresolved = await prepareDependencyIntake({ cwd: root, repository }, ports);
  assert.deepEqual(unresolved.queued, []);
  assert.deepEqual(unresolved.skipped, [key(1)], 'ambiguous source links cannot validate a cached review');
  ambiguous = false;
  writeFileSync(join(root, 'src/own.mjs'), 'export const own = "v2";');
  w.files.set(actual, digest('export const own = "v2";'));
  const changed = await prepareDependencyIntake({ cwd: root, repository }, ports);
  assert.deepEqual(changed.queued, [key(1)], 'editing the exact named file makes its saved review stale');
  assert.deepEqual(JSON.parse(changed.request.contextJson).source.map(row => row.path), ['src/own.mjs']);
});

test('saved duplicate targets are fetched even when absent from open roots', async () => {
  const w = reviewWorld(1);
  const duplicate = { ...w.issues[0], id: 101, number: 101, html_url: key(101), state: 'closed', state_reason: 'completed' };
  w.save(w.record(1, { genuine: { kind: 'duplicate', duplicateOf: key(101), reason: 'Same defect.' } }));
  w.review(1);
  const original = w.ports.github.issue;
  w.ports.github.issue = args => args.issue === 101 ? Promise.resolve({ json: JSON.stringify(duplicate) }) : original(args);
  const { request } = await prepareDependencyIntake({ repository, issue: '1' }, w.ports);
  assert.ok(JSON.parse(request.snapshotJson).issues.some(i => i.key === key(101) && i.state === 'completed'));
});
