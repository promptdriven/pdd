import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, PLACE, portsFor, fakeRuntime } from './runtime-fake.mjs';

// Relay I joins #2676 limits admission with #2590's saved lint/wait contract.
// Expectations come from LEAD04:12 and the two owning prompt rules.
test('RELAY-I a: invalid lint limits create no held row; valid lint keeps its explicit wait and pending batch', { timeout: 15000 }, async t => {
  const h = harbor(t), file = join(h.repo, PLACE), original = readFileSync(file, 'utf8');
  const fake = await fakeRuntime(t, (entry, f) => {
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    return { status: 202, json: f.job(id, 'lint', 'running') };
  });
  const env = { HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: fake.origin };
  writeFileSync(file, original.replace(/"limits": \{[^}]+\}/, '"limits": {"max_steps":4,"max_model_calls":0}'));
  assert.notEqual(readFileSync(file, 'utf8'), original);
  const refused = portsFor(env);
  const bad = await runCheck({ cwd: h.repo, words: ['place-order'], options: { '--lint': true, '--json': true, '--timeout': '0.01' } }, refused.ports);
  assert.equal(bad, 4, refused.ports.stderr.text);
  const result = JSON.parse(refused.ports.stdout.text);
  assert.equal(result.batch, null); assert.equal(result.rows[0].state, 'refused');
  assert.ok(result.problems.some(p => p.code === 'invalid-limits' && p.section === '/limits/max_model_calls'));
  assert.equal(fake.posts.length, 0); assert.equal(fake.gets.length, 0); assert.equal(refused.clock.gh.length, 0); assert.equal(refused.clock.uuids, 0);
  assert.equal(existsSync(join(h.state, 'batches')), false, 'no batch or held-for-lint row may precede limits admission');

  writeFileSync(file, original);
  const valid = portsFor(env), start = valid.clock.now;
  const pending = await runCheck({ cwd: h.repo, words: ['place-order'], options: { '--lint': true, '--json': true, '--timeout': '0.01' } }, valid.ports);
  assert.equal(pending, 3, valid.ports.stderr.text);
  assert.equal(valid.clock.now - start, 600, 'lint must use the explicit shared caller budget');
  assert.equal(fake.posts.length, 1); assert.equal(fake.posts[0].command, 'lint'); assert.equal(fake.posts[0].request.complete, true);
  const batches = readdirSync(join(h.state, 'batches'), { withFileTypes: true }).filter(e => e.isDirectory());
  assert.equal(batches.length, 1);
  const saved = JSON.parse(readFileSync(join(h.state, 'batches', batches[0].name, 'batch.json')));
  assert.equal(saved.timeout_min, 0.01); assert.equal(saved.intent, 'lint-only'); assert.equal(saved.lint.pending, true);
  assert.equal(saved.rows[0].phase, 'lint'); assert.deepEqual(saved.rows[0].request_ids, []); assert.equal(saved.rows[0].calls, 0);
});
