import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import * as fs from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { autopilotGithubWorld, analysisFor } from './helpers/autopilot-github-world.mjs';
import { createDependencyReadPorts, readDependencySnapshot, dependencySnapshotStore } from '../src/issue-dependencies-github.mjs';
import { runDependencyIntake } from '../src/issue-dependencies-intake.mjs';

const minute = 60000;
const key = (w, n) => `https://github.com/${w.repository}/issues/${n}`;
const read = (w, ports = w.commandPorts(), inputs = []) => readDependencySnapshot({ cwd: w.cwd, repository: w.repository, inputs }, ports).then(r => r.snapshot);
const edges = snapshot => snapshot.edges.map(e => [e.dependent, e.blocker]).sort();

test('equal-count link swaps replace the saved identities without rereading unchanged comments', async t => {
  const w = await autopilotGithubWorld({ issues: 200 }); t.after(w.cleanup);
  w.github.link(2, 1); w.github.link(4, 3);
  assert.equal((await w.invoke('start')).exitCode, 0);
  w.time += 10 * minute; w.github.edit(200, 'Move the watermark forward.'); await read(w);
  const times = [1, 2, 3, 4].map(n => w.github.issues.get(n).updated);
  w.github.issues.get(2).blockedBy = [3]; w.github.issues.get(4).blockedBy = [1];
  w.time += minute;
  const mark = w.github.mark(), saved = await read(w), calls = w.github.since(mark);
  assert.deepEqual([1, 2, 3, 4].map(n => w.github.issues.get(n).updated), times);
  assert.equal(saved.complete, true);
  assert.deepEqual(edges(saved), [[key(w, 2), key(w, 3)], [key(w, 4), key(w, 1)]], 'equal counts must expose new link identities');
  assert.deepEqual(edges(saved), edges(await read(w, w.commandPorts({ snapshotStore: null }))));
  assert.ok(calls.rest < 10, `link-swap REST requests: ${calls.rest}`);
  assert.ok(!calls.calls.some(c => /issues\/100\/(comments|timeline)/.test(c.endpoint)));
  t.diagnostic(`link swap: ${JSON.stringify({ rest: calls.rest, graphql: calls.graphql })}`);
  // Incomplete identity connections must use complete REST pages, never an old identity version.
  const native = w.commandPorts(), partial = { ...native, execFile: async (file, args, options) => {
    const result = await native.execFile(file, args, options);
    if (args.includes('graphql') && !/\bcomments\s*\(/.test(JSON.parse(options.input).query)) {
      const boundary = result.stdout.indexOf('\r\n\r\n'), body = JSON.parse(result.stdout.slice(boundary + 4));
      body.data.repository.i0.blockedBy.pageInfo.hasNextPage = true;
      return { ...result, stdout: result.stdout.slice(0, boundary + 4) + JSON.stringify(body) };
    }
    return result;
  } };
  w.github.issues.get(2).blockedBy = [1]; w.github.issues.get(4).blockedBy = [3];
  w.time += minute;
  const fallbackMark = w.github.mark(), fallback = await read(w, partial);
  assert.equal(fallback.complete, true);
  assert.deepEqual(edges(fallback), [[key(w, 2), key(w, 1)], [key(w, 4), key(w, 3)]]);
  assert.ok(w.github.since(fallbackMark).calls.some(c => c.method === 'GET' && c.endpoint.includes('/dependencies/')));
  w.github.failRead = call => call.endpoint.includes('/dependencies/'); w.time += minute;
  assert.equal((await read(w, partial)).complete, false, 'unavailable identity fallback cannot establish complete freshness');

});

test('a reused read session removes a deleted requirement comment on complete reread and invalidation', async t => {
  const w = await autopilotGithubWorld({ issues: 8 }); t.after(w.cleanup);
  const comment = w.github.comment(2, 'Keep the old public name.');
  assert.equal((await w.invoke('start')).exitCode, 0);
  const ports = createDependencyReadPorts({ cwd: w.cwd }, w.commandPorts());
  const row = (await read(w, ports)).inputs.find(r => r.key === `${key(w, 2)}#issuecomment-${comment.id}`);
  assert.ok(row);
  w.time += 10 * minute; w.github.issues.get(2).comments = []; w.github.edit(2, 'The requirement comment was removed.');
  const reused = await read(w, ports, [row]);
  assert.equal(reused.complete, true);
  assert.ok(!reused.inputs.some(r => r.key === row.key), 'complete current pages must remove deleted comments');
  assert.deepEqual(reused.inputs, (await read(w, w.commandPorts(), [row])).inputs);
  const replacement = w.github.comment(2, 'Keep the new public name.');
  w.time += minute;
  await read(w, ports);
  assert.ok(ports.dependencyReads.comments.has(`${key(w, 2)}#issuecomment-${replacement.id}`));
  ports.dependencyReads.invalidate(w.repository, 2);
  assert.ok(!ports.dependencyReads.comments.has(`${key(w, 2)}#issuecomment-${replacement.id}`));
});

const storeModule = new URL('../src/issue-dependencies-github.mjs', import.meta.url).href;
function worker(t, script, args) {
  const child = spawn(process.execPath, ['--input-type=module', '-e', script, ...args], { stdio: ['ignore', 'pipe', 'pipe', 'ipc'] });
  t.after(() => { if (child.exitCode === null) child.kill(); });
  return child;
}
const exited = child => new Promise((resolve, reject) => {
  child.once('error', reject);
  child.once('exit', code => code === 0 ? resolve() : reject(Error(`store worker exit ${code}`)));
});

test('real-file store saves keep invalidation times across stale and overlapping processes', { timeout: 15000 }, async t => {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-snapshot-repair-')); t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const store = dependencySnapshotStore({ root, repository: 'acme/widgets' });
  const initial = { v: 1, repository: 'acme/widgets', refreshedAt: 0,
    list: { readAt: 10, since: '2026-11-07T00:00:00Z', rows: { 1: { number: 1 } } },
    issues: { 1: { version: 'same', observedAt: 20, kinds: { comments: [], blockedBy: [], blocking: [], timeline: [] } } }, invalid: { 1: 5 } };
  store.save(initial);
  const stale = worker(t, `import {dependencySnapshotStore} from ${JSON.stringify(storeModule)};
    const store=dependencySnapshotStore({root:process.argv[1],repository:'acme/widgets'}), old=store.load();
    process.send('loaded'); process.once('message',()=>{store.save(old);process.disconnect();});`, [root]);
  const staleExit = exited(stale);
  await new Promise(resolve => stale.once('message', resolve));
  store.save({ ...initial, issues: {}, invalid: { 1: 30 } });
  stale.send('save'); await staleExit;
  assert.equal(store.load().invalid[1], 30, 'stale process must keep the greatest invalidation time');
  assert.equal(store.load().issues[1], undefined, 'stale process must not restore an invalidated issue');

  // Pause process A after its merge read. Process B tries to invalidate at that exact boundary.
  // The fs port still uses native files; only the scheduling is controlled.
  const release = join(root, 'release');
  const a = worker(t, `import * as fs from 'node:fs'; import {dependencySnapshotStore} from ${JSON.stringify(storeModule)};
    const root=process.argv[1], file=process.argv[2], release=process.argv[3];
    const port={...fs,readFileSync(path,...args){const bytes=fs.readFileSync(path,...args);if(path===file){process.send('read');while(!fs.existsSync(release))Atomics.wait(new Int32Array(new SharedArrayBuffer(4)),0,0,10);}return bytes;}};
    const store=dependencySnapshotStore({root,repository:'acme/widgets',fs:port});store.save(JSON.parse(process.argv[4]));process.disconnect();`, [root, store.file, release, JSON.stringify(initial)]);
  const aExit = exited(a);
  await new Promise(resolve => a.once('message', resolve));
  const b = worker(t, `import * as fs from 'node:fs'; import {dependencySnapshotStore} from ${JSON.stringify(storeModule)};
    const port={...fs,mkdirSync(path,...args){try{return fs.mkdirSync(path,...args);}catch(error){if(error.code==='EEXIST')process.send('waiting');throw error;}}};
    const store=dependencySnapshotStore({root:process.argv[1],repository:'acme/widgets',fs:port});
    store.save(JSON.parse(process.argv[2]));process.send('saved');process.disconnect();`, [root, JSON.stringify({ ...initial, issues: {}, invalid: { 1: 40 } })]);
  const bExit = exited(b);
  await new Promise(resolve => b.once('message', resolve));
  fs.writeFileSync(release, 'continue');
  await Promise.all([aExit, bExit]);
  assert.equal(store.load().invalid[1], 40, 'overlapping saves must serialize read, merge and write');
  assert.equal(store.load().issues[1], undefined);
  // A stale invalidation must survive even a later full-refresh period.
  store.save({ ...initial, refreshedAt: 25 });
  assert.equal(store.load().invalid[1], 40);
  assert.equal(store.load().issues[1], undefined);
});

test('a retry completes saved pending link effects before clearing the kept completion', async t => {
  const w = await autopilotGithubWorld({ issues: 2 }); t.after(w.cleanup);
  assert.equal((await w.invoke('start')).exitCode, 0);
  const prepared = await runDependencyIntake({ command: 'prepare', cwd: w.cwd, issue: 2 }, w.commandPorts({ repository: { read: async () => w.repository } }));
  assert.equal(prepared.exitCode, 0, prepared.message);
  const request = JSON.parse(prepared.message).request, analysis = analysisFor(request), review = analysis.reviews[0];
  review.outcome = 'pending'; review.effects = 'pending';
  review.dependencies = [{ key: key(w, 1), reason: 'Part 2 needs part 1.', evidence: [key(w, 1)] }];
  const complete = async () => {
    const result = await runDependencyIntake({ command: 'complete', cwd: w.cwd, stdin: JSON.stringify({ request, analysis }) }, w.commandPorts());
    assert.equal(result.exitCode, 0, result.message); return JSON.parse(result.message);
  };
  w.github.failRest = call => call.method === 'POST' && call.endpoint.endsWith('/dependencies/blocked_by');
  w.time += minute;
  const first = await complete();
  assert.equal(first.state, 'pending'); assert.equal(first.pendingStage, 'edge-confirmation');
  const store = dependencySnapshotStore({ root: w.stateRoot, repository: w.repository });
  assert.equal(store.completion.read().request.id, request.id);
  // Repeating before reset keeps the intent and its analysis.
  assert.equal((await complete()).state, 'pending');
  assert.equal(store.completion.read().request.id, request.id);
  w.github.failRest = null; w.time = w.github.resetAt * 1000 + minute;
  const retry = await complete();
  assert.equal(retry.state, 'complete');
  assert.deepEqual(w.github.issues.get(2).blockedBy, [1], 'completion requires the saved native edge');
  assert.equal(store.completion.read(), null);
  const records = w.github.reviewComments(2);
  assert.equal(records.length, 2, 'one intent and one confirmation');
  const snapshot = await read(w);
  assert.equal(snapshot.reviews.filter(r => r.continuation === first.reviewIds[0] && r.effects === 'confirmed').length, 1);
  const mark = w.github.mark();
  assert.equal((await complete()).state, 'complete');
  assert.equal(w.github.reviewComments(2).length, 2);
  assert.ok(!w.github.since(mark).calls.some(c => c.method === 'POST' && c.endpoint.endsWith('/dependencies/blocked_by')));
});
