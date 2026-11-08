import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawn } from 'node:child_process';
import { once } from 'node:events';
import { githubLedger, githubMachineEntries, githubUsage, githubBudget } from '../src/github-calls.mjs';
import { openAutopilotStore } from '../src/autopilot-store.mjs';

function fixture(t) {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-store-repair-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  return root;
}
const ledgerModule = new URL('../src/github-calls.mjs', import.meta.url).href;
const storeModule = new URL('../src/autopilot-store.mjs', import.meta.url).href;

test('initialization: a real WAL lock conflict retries after the reader releases it', { timeout: 10000 }, async t => {
  const { DatabaseSync } = await import('node:sqlite');
  const root = fixture(t), reader = new DatabaseSync(join(root, 'machine.sqlite'));
  t.after(() => reader.close());
  // A live reader in DELETE mode prevents the first WAL transition.
  reader.exec('CREATE TABLE legacy_reader (id INTEGER); BEGIN; SELECT * FROM legacy_reader');
  const script = `import {DatabaseSync} from 'node:sqlite';import {openAutopilotStore} from ${JSON.stringify(storeModule)};
    class ObservedDatabase extends DatabaseSync {
      // Force SQLite's immediate-contention path while keeping the real lock/error.
      exec(sql){if(sql.includes('journal_mode'))super.exec('PRAGMA busy_timeout=0');
        try{return super.exec(sql);}catch(error){
        if((error.errcode & 255)===5 && sql.includes('journal_mode'))process.send('blocked');
        throw error;
      }}
    }
    const store=openAutopilotStore({root:process.argv[1]},{sqlite:{DatabaseSync:ObservedDatabase}});
    store.transaction(tx=>tx.append('events','cold',{at:100}));store.close();process.disconnect();`;
  const proc = spawn(process.execPath, ['--input-type=module', '-e', script, root], { stdio: ['ignore', 'ignore', 'pipe', 'ipc'] });
  let stderr = ''; proc.stderr.on('data', value => { stderr += value; });
  t.after(() => { if (proc.exitCode === null && proc.signalCode === null) proc.kill('SIGKILL'); });
  const done = once(proc, 'exit');
  const [message] = await Promise.race([once(proc, 'message'), done.then(() => assert.fail(stderr))]);
  assert.equal(message, 'blocked');
  reader.exec('ROLLBACK');
  const [code] = await done;
  assert.equal(code, 0, stderr);
  const store = openAutopilotStore({ root });
  try { assert.deepEqual(store.transaction(tx => tx.entries('events', 'cold').map(row => row.value)), [{ at: 100 }]); }
  finally { store.close(); }
});

test('cold startup: concurrent public ledger writers retain every observation', { timeout: 30000 }, async t => {
  const counts = [];
  for (let round = 0; round < 12; round++) {
    const root = fixture(t);
    const children = Array.from({ length: 6 }, (_, worker) => {
      const script = `import {githubLedger} from ${JSON.stringify(ledgerModule)};
        process.send('ready');process.once('message',()=>{
          githubLedger({root:process.argv[1],repository:'owner/repo'}).record({at:100,purpose:'issues',api:'rest',worker:${worker}});
          process.disconnect();
        });`;
      const proc = spawn(process.execPath, ['--input-type=module', '-e', script, root], { stdio: ['ignore', 'ignore', 'pipe', 'ipc'] });
      let stderr = ''; proc.stderr.on('data', value => { stderr += value; });
      t.after(() => { if (proc.exitCode === null && proc.signalCode === null) proc.kill('SIGKILL'); });
      return { proc, ready: once(proc, 'message'), done: once(proc, 'exit'), error: () => stderr };
    });
    await Promise.all(children.map(child => child.ready));
    // No child has opened storage. Release all SQLite-capable first openers together.
    assert.equal(fs.existsSync(join(root, 'machine.sqlite')), false);
    for (const child of children) child.proc.send('record');
    for (const child of children) {
      const [code] = await child.done;
      assert.equal(code, 0, child.error());
    }
    const rows = githubLedger({ root, repository: 'owner/repo' }).read();
    counts.push(rows.length);
    // Preserve identities as well as the count; duplicate rows cannot mask a loss.
    assert.deepEqual(rows.map(row => row.worker).sort(), [0, 1, 2, 3, 4, 5]);
  }
  t.diagnostic(`Retained rows per fresh root: ${JSON.stringify(counts)}`);
});

for (const imported of [false, true]) test(`machine budget: an unreadable peer keeps healthy ${imported ? 'committed' : 'legacy'} evidence and retries later`, t => {
  const root = fixture(t), repository = 'owner/repo';
  const ledger = githubLedger({ root, repository }), peer = githubLedger({ root, repository: 'other/repo' });
  fs.mkdirSync(join(root, 'github'));
  const row = { repo: repository, at: 100, purpose: 'issues', api: 'rest', status: 200, resource: 'core', remaining: 5, limit: 5000, resetAt: 10000 };
  fs.writeFileSync(ledger.file, JSON.stringify(row) + '\n');
  if (imported) assert.deepEqual(ledger.read(), [row]);
  // A real EISDIR read error is portable even when tests run as root.
  fs.mkdirSync(peer.file);
  const entries = githubMachineEntries({ root });
  assert.equal(githubBudget({ usage: githubUsage(entries, 200) }).state, 'reserve');
  assert.deepEqual(entries, [row]);
  // The failed source must stay eligible for import and must be imported only once.
  fs.rmSync(peer.file, { recursive: true });
  const other = { repo: 'other/repo', at: 150, purpose: 'claims', api: 'rest', status: 200 };
  fs.writeFileSync(peer.file, JSON.stringify(other) + '\n');
  const expected = [row, other].sort((a, b) => a.at - b.at);
  for (let repeat = 0; repeat < 2; repeat++) {
    assert.deepEqual(githubMachineEntries({ root }).sort((a, b) => a.at - b.at), expected);
  }
});
