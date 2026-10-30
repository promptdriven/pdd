import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';

// E5: at the deadline/interruption an UNVERIFIABLE open receipt (wrong id / wrong command) must stay unknown.
for (const damage of ['wrong-id', 'wrong-command', 'unknown', 'verified']) test(`E5 interrupted read with ${damage} running cache`, async t => {
  const h = harbor(t);
  const f = await fakeRuntime(t, (e, f) => {
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    if (e.method === 'POST' && e.command === 'lint') return { status: 200, json: f.lint(id) };
    return { status: 200, json: f.check(id, 'running') };
  });
  const env = { HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin };
  await runCheck({ cwd: h.repo, words: ['place-order'], options: { '--json': true } }, portsFor(env).ports);
  const batch = readdirSync(join(h.state, 'batches'), { withFileTypes: true }).find(e => e.isDirectory()).name;
  const folder = join(h.state, 'batches', batch), doc = JSON.parse(readFileSync(join(folder, 'batch.json'))), id = doc.rows[0].request_ids[0];
  const raw = join(folder, `${id}.json`), receipt = JSON.parse(readFileSync(raw));
  if (damage === 'wrong-id') receipt.id = 'another'; if (damage === 'wrong-command') receipt.command = 'call';
  if (damage === 'unknown') { receipt.state = 'unknown'; receipt.result = { why: 'STALE UNKNOWN CACHE', outcome: 'Inconclusive' }; }
  writeFileSync(raw, JSON.stringify(receipt));
  const p = portsFor(env, { onInterrupt: handler => { handler(); return () => {}; } });
  await runCheck({ cwd: h.repo, words: [batch], options: { '--read': true, '--json': true } }, p.ports);
  const row = JSON.parse(p.ports.stdout.text).rows[0];
  assert.equal(row.state, damage === 'verified' ? 'running' : 'unknown');
  if (damage === 'unknown') assert.notEqual(row.why, 'STALE UNKNOWN CACHE', 'non-open cached receipt is not projected at interruption');
});
