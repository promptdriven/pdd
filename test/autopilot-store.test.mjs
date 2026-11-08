import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawn } from 'node:child_process';
import { once } from 'node:events';
import { openAutopilotStore, machineJson, readAutopilotState, saveAutopilotState, autopilotStateFiles } from '../src/autopilot-store.mjs';
import { githubLedger, githubEtagCache } from '../src/github-calls.mjs';

function fixture(t) { const root = fs.mkdtempSync(join(tmpdir(), 'pdd-store-')); t.after(() => fs.rmSync(root, { recursive: true, force: true })); return root; }
const moduleUrl = new URL('../src/autopilot-store.mjs', import.meta.url).href;
async function child(t, code, args) {
  const proc = spawn(process.execPath, ['--input-type=module', '-e', code, ...args], { stdio: ['ignore', 'pipe', 'pipe', 'ipc'] });
  let stderr = ''; proc.stderr.on('data', value => { stderr += value; });
  const done = once(proc, 'exit');
  t.after(() => { if (proc.exitCode === null && proc.signalCode === null) proc.kill('SIGKILL'); });
  return { proc, done, error: () => stderr };
}

test('transaction: all machine buckets and journal rows survive reopen, rollback leaves no partial writes', t => {
  const root = fixture(t), store = openAutopilotStore({ root });
  store.transaction(tx => {
    for (const bucket of ['control','queue','runs','leases','budgets','costs','events','cache','alerts']) tx.put(bucket, 'x', { count: 1, none: null });
    tx.append('costs', 'repo', { usd: 0.25 }); tx.append('events', 'repo', { type: 'launch' });
  });
  assert.throws(() => store.transaction(tx => { tx.put('queue', 'x', 2); tx.put('leases', 'y', true); tx.append('costs', 'repo', { usd: 9 }); throw Error('fault'); }));
  store.close();
  const reopened = openAutopilotStore({ root }); t.after(() => reopened.close());
  reopened.transaction(tx => {
    assert.deepEqual(tx.get('queue', 'x'), { count: 1, none: null }); assert.equal(tx.get('leases', 'y'), undefined);
    assert.deepEqual(tx.entries('costs', 'repo').map(row => row.value.usd), [0.25]);
    assert.equal(tx.entries('events').length, 1);
  });
  assert.equal(fs.statSync(join(root, 'machine.sqlite')).mode & 0o777, 0o600);
});

test('migration: failed import rolls back rows and marker, retry imports exactly once', t => {
  const store = openAutopilotStore({ root: fixture(t) }); t.after(() => store.close()); let reads = 0;
  const read = () => { reads++; return [1,2]; };
  assert.throws(() => store.transaction(tx => tx.migrate('legacy', read, rows => { tx.put('queue', 'one', rows[0]); throw Error('fault'); })));
  store.transaction(tx => { assert.equal(tx.get('queue','one'), undefined); tx.migrate('legacy', read, rows => tx.put('queue','one',rows)); });
  store.transaction(tx => tx.migrate('legacy', () => assert.fail('import repeated'), () => {}));
  assert.equal(reads, 2);
});

test('control: migration retains launcher identity, pending work and local lease observations across restart', t => {
  const root = fixture(t), name = 'a'.repeat(20) + '.json', file = join(root, name);
  const original = { enabled: true, coordinatorId: 'owner', dependencyPending: { issues: [7] }, claims: [{ issue: 7, lastSeen: 'now' }], runs: 2 };
  const bytes = JSON.stringify(original); fs.writeFileSync(file, bytes);
  assert.deepEqual(readAutopilotState(file), original);
  saveAutopilotState(file, { ...original, runs: 3 });
  assert.deepEqual(readAutopilotState(file).dependencyPending.issues, [7]);
  assert.equal(readAutopilotState(file).runs, 3);
  assert.equal(fs.readFileSync(file, 'utf8'), bytes);
  fs.rmSync(file);
  assert.deepEqual(autopilotStateFiles(root), [name]);
  assert.equal(readAutopilotState(file).coordinatorId, 'owner');
});

test('migration: malformed input stays untouched and clear of an absent record blocks later import', t => {
  const root = fixture(t), file = join(root, 'old.json'), record = machineJson({ root, bucket: 'queue', key: 'pending', file });
  fs.writeFileSync(file, '{broken'); assert.throws(() => record.read(), SyntaxError); assert.equal(fs.readFileSync(file, 'utf8'), '{broken');
  fs.writeFileSync(file, '{"issue":7}'); assert.deepEqual(record.read(), { issue: 7 });
  record.clear(); assert.equal(record.read(), null);
  const other = machineJson({ root, bucket: 'queue', key: 'other', file: join(root,'absent.json') }); other.clear();
  fs.writeFileSync(join(root,'absent.json'), '{"issue":8}'); assert.equal(other.read(), null);
});

test('transaction: process death before commit rolls back a queue, lease and event together', async t => {
  const root = fixture(t), store = openAutopilotStore({ root }); store.transaction(tx => tx.put('queue','task',{ state: 'ready' })); store.close();
  const c = await child(t, `import {openAutopilotStore} from ${JSON.stringify(moduleUrl)};
    const store=openAutopilotStore({root:process.argv[1]});
    store.transaction(tx=>{tx.put('queue','task',{state:'running'});tx.put('leases','task',{holder:'worker'});tx.append('events','task',{type:'claimed'});process.send('written');Atomics.wait(new Int32Array(new SharedArrayBuffer(4)),0,0,30000);});`, [root]);
  await once(c.proc, 'message'); c.proc.kill('SIGKILL'); await c.done;
  const reopened = openAutopilotStore({ root }); t.after(() => reopened.close());
  reopened.transaction(tx => { assert.equal(tx.get('queue','task').state, 'ready'); assert.equal(tx.get('leases','task'), undefined); assert.equal(tx.entries('events').length, 0); });
});

test('concurrency: independent processes retain every cost and event row while updating budgets', async t => {
  const root = fixture(t), initialized = openAutopilotStore({ root }); initialized.close();
  const children = await Promise.all(Array.from({ length: 4 }, (_, n) => child(t, `import {openAutopilotStore} from ${JSON.stringify(moduleUrl)};
    const s=openAutopilotStore({root:process.argv[1]});
    for(let i=0;i<20;i++)s.transaction(tx=>{const count=tx.get('budgets','count')??0;tx.put('budgets','count',count+1);tx.append('costs',process.argv[2],{usd:0.25});tx.append('events',process.argv[2],{i});});s.close();process.disconnect();`, [root, String(n)])));
  for (const c of children) { const [code] = await c.done; assert.equal(code, 0, c.error()); }
  const s = openAutopilotStore({ root }); t.after(() => s.close());
  s.transaction(tx => { assert.equal(tx.get('budgets','count'), 80); assert.equal(tx.entries('costs').length,80); assert.equal(tx.entries('events').length,80); });
});

test('ledger: compaction retains recent rows with out-of-order timestamps and duplicate calls', t => {
  const root = fixture(t), ledger = githubLedger({ root, repository: 'owner/repo' });
  for (const at of [10_000_000, 1, 10_000_000]) ledger.record({ at, purpose: 'issues', api: 'rest' });
  ledger.compact(10_000_001); assert.deepEqual(ledger.read().map(row => row.at), [10_000_000, 10_000_000]);
});

test('ETag cache: concurrent independent caches retain each other entries', t => {
  const root = fixture(t), a = githubEtagCache({ root, repository: 'owner/repo', now: () => 100 }), b = githubEtagCache({ root, repository: 'owner/repo', now: () => 100 });
  a.get('empty'); b.get('empty'); a.set('a',{etag:'a',body:'[]'}); b.set('b',{etag:'b',body:'[]'}); a.save(); b.save();
  const current = githubEtagCache({ root, repository: 'owner/repo' }); assert.equal(current.get('a').etag,'a'); assert.equal(current.get('b').etag,'b');
});

test('transaction scope: reject async, nested and escaped use without publishing', t => {
  const s = openAutopilotStore({ root: fixture(t) }); t.after(() => s.close()); let escaped;
  assert.throws(() => s.transaction(tx => { tx.put('queue','bad',1); return Promise.resolve(); }), TypeError);
  assert.throws(() => s.transaction(() => s.transaction(() => {})));
  s.transaction(tx => { escaped = tx; assert.equal(tx.get('queue','bad'), undefined); });
  assert.throws(() => escaped.put('queue','bad',1));
});

test('worker completion: native coordinator read observes database control after JSON removal', async t => {
  const { createHash } = await import('node:crypto');
  const { waitForWorkerCompletion } = await import('../src/workflow-worker-completion.mjs');
  const root = fixture(t), sourceRoot = fs.realpathSync(root), home = join(root,'home');
  const folder = join(home,'.local','state','pdd','autopilot'); fs.mkdirSync(folder,{recursive:true});
  const file = join(folder,createHash('sha256').update(sourceRoot).digest('hex').slice(0,20)+'.json');
  fs.writeFileSync(file, JSON.stringify({enabled:false,paneId:'old'}));
  readAutopilotState(file); saveAutopilotState(file,{enabled:true,paneId:'coordinator'}); fs.rmSync(file);
  const identity = {runId:'run',number:7,sourceRoot,runDir:join(root,'run'),area:'code',paneId:'worker',startAnchor:1,coordinatorPaneId:'coordinator'};
  const run = {runId:'run',area:0,areas:[{name:'code'}],chats:[{area:'code',paneId:'worker',startedAt:1}]};
  const waits=[]; let yields=0;
  await waitForWorkerCompletion(identity,{env:{HOME:home},readRun:()=>run,wait:async(session,pane)=>waits.push([session,pane]),acquireRunLock:()=>()=>{},yieldCapacity:async()=>{yields++;}});
  assert.deepEqual(waits,[['pdd','worker'],['pdd-autopilot','coordinator']]); assert.equal(yields,1);
});

test('run index: malformed legacy input recovers and separate runs remain discoverable after migration', async t => {
  const {writeRun,allRuns} = await import('../src/workflow-runs.mjs');
  const root=fixture(t), stateDir=join(root,'state'), commonDir=join(root,'repo','.git');
  fs.mkdirSync(stateDir); fs.writeFileSync(join(stateDir,'runs.json'),'{broken');
  for(const number of [7,8]){
    const runDir=join(commonDir,'pdd','runs',String(number));
    writeRun({v:1,number,runId:`r${number}`,runDir,commonDir,repo:'owner/repo',root:join(root,'repo'),areas:[],chats:[],state:'running'},{stateDir});
  }
  assert.deepEqual(allRuns({}, {stateDir}).map(run=>run.number),[7,8]);
  assert.equal(fs.readFileSync(join(stateDir,'runs.json'),'utf8'),'{broken');
});

test('schema: a newer database is refused and its records stay intact', async t => {
  const { DatabaseSync } = await import('node:sqlite');
  const root=fixture(t), s=openAutopilotStore({root});s.transaction(tx=>tx.put('queue','x',7));s.close();
  const db=new DatabaseSync(join(root,'machine.sqlite'));db.exec('PRAGMA user_version=2');db.close();
  assert.throws(()=>openAutopilotStore({root}));
  const check=new DatabaseSync(join(root,'machine.sqlite'));t.after(()=>check.close());
  assert.equal(check.prepare('PRAGMA user_version').get().user_version,2);
  assert.equal(check.prepare('SELECT value FROM records WHERE bucket=? AND key=?').get('queue','x').value,'7');
});
