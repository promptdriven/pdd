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

