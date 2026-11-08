import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { dependencySnapshotStore } from '../src/issue-dependencies-github.mjs';
import { githubLedger, githubEtagCache, githubMachineEntries } from '../src/github-calls.mjs';

function fixture(t) {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-store-regression-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  fs.mkdirSync(join(root, 'github'));
  return root;
}
const repository = 'owner/repo';
const snapshot = time => ({ v: 1, repository, refreshedAt: time, list: { readAt: time, since: '', rows: {} }, issues: {}, invalid: {} });

test('storage migration: a retained completion cannot resurrect after clear and restart', t => {
  const root = fixture(t), first = dependencySnapshotStore({ root, repository });
  fs.writeFileSync(first.completion.file, JSON.stringify({ v: 1, request: 'old', completed: [7] }));
  assert.deepEqual(first.completion.read().completed, [7]);
  first.completion.clear();
  // A retained recovery copy (or an older binary) must not restore cleared work.
  fs.writeFileSync(first.completion.file, JSON.stringify({ v: 1, request: 'old', completed: [7] }));
  assert.equal(dependencySnapshotStore({ root, repository }).completion.read(), null);
});

test('storage migration: imported snapshots do not replace newer observations on restart', t => {
  const root = fixture(t), first = dependencySnapshotStore({ root, repository });
  const legacy = JSON.stringify(snapshot(10)); fs.writeFileSync(first.file, legacy);
  assert.equal(first.load().refreshedAt, 10);
  assert.equal(first.save(snapshot(20)).refreshedAt, 20);
  fs.writeFileSync(first.file, legacy);
  assert.equal(dependencySnapshotStore({ root, repository }).load().refreshedAt, 20);
});

test('storage migration: call rows survive removal of the imported legacy ledger', t => {
  const root = fixture(t), ledger = githubLedger({ root, repository });
  const old = { repo: repository, at: 10, purpose: 'issues', api: 'rest', status: 200 };
  fs.writeFileSync(ledger.file, JSON.stringify(old) + '\n{torn');
  assert.equal(ledger.read().length, 1);
  ledger.record({ at: 20, purpose: 'claims', api: 'rest', status: 200 });
  fs.rmSync(ledger.file);
  assert.deepEqual(githubLedger({ root, repository }).read().map(row => row.at), [10, 20]);
  assert.equal(githubMachineEntries({ root }).length, 2);
});

test('storage migration: ETag writes do not change the retained recovery file', t => {
  const root = fixture(t), cache = githubEtagCache({ root, repository, now: () => 20 });
  const legacy = JSON.stringify({ a: { etag: 'a', body: '[]', next: '', at: 10 } });
  fs.writeFileSync(cache.file, legacy);
  assert.equal(cache.get('a').etag, 'a');
  cache.set('b', { etag: 'b', body: '[7]' }); cache.save();
  assert.equal(fs.readFileSync(cache.file, 'utf8'), legacy);
  assert.equal(githubEtagCache({ root, repository }).get('b').body, '[7]');
});
