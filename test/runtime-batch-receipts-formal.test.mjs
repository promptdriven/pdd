import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

// Story: recover-retried-check-results, Rules to check. The oracle depends only
// on verified receipt evidence, never on the locally saved phase or verdict.
test('2655 formal: accepted-ID recovery obeys receipt evidence across all 144 bounded states', async t => {
  const setup = harbor(t);
  let response = 'passed';
  const checks = Array.from({ length: 17 }, (_, i) => ({ criterion_id: `AC${i % 4 + 1}`, target: 'result', path: '/totalCents', op: 'equals', expected: 900, actual: 900, passed: true }));
  const fake = await fakeRuntime(t, (entry, server) => {
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    if (entry.command === 'lint') return { status: 200, json: server.lint(id) };
    if (response === 'unavailable') return { status: 503, json: { error: { code: 'temporary' } } };
    const receipt = server.check(id, response, checks);
    receipt.usage.calls = response === 'passed' ? 4 : 'unknown';
    return { status: 200, json: receipt };
  });
  async function run(words, options) {
    const { ports, clock } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
    const code = await runCheck({ cwd: setup.repo, words, options: { '--json': true, ...options } }, ports);
    return { code, clock, json: JSON.parse(ports.stdout.text) };
  }
  const initial = await run(['place-order'], {});
  assert.equal(initial.code, 0);
  const batch = initial.json.batch, id = initial.json.rows[0].request_id;
  const folder = join(setup.state, 'batches', batch), batchFile = join(folder, 'batch.json'), rawFile = join(folder, `${id}.json`);
  const saved = JSON.parse(readFileSync(batchFile, 'utf8'));
  const terminal = JSON.parse(readFileSync(rawFile, 'utf8'));
  let count = 0;
  for (const phase of ['local', 'server'])
    for (const label of ['passed', 'running', 'unknown'])
      for (const cache of ['valid', 'missing', 'mismatched', 'pending'])
        for (const reply of ['passed', 'running', 'unavailable'])
          for (const operation of ['read', 'retry']) {
            const context = JSON.stringify({ phase, label, cache, reply, operation });
            const record = structuredClone(saved);
            Object.assign(record.rows[0], { phase, state: label, eligible: false, can_retry: false });
            writeFileSync(batchFile, JSON.stringify(record));
            const receipt = structuredClone(terminal);
            if (cache === 'missing') rmSync(rawFile, { force: true });
            else {
              if (cache === 'mismatched') receipt.id = 'a-different-request';
              if (cache === 'pending') { receipt.state = 'running'; receipt.result = null; receipt.usage.calls = 'unknown'; }
              writeFileSync(rawFile, JSON.stringify(receipt));
            }
            response = reply;
            const posts = fake.posts.length, gets = fake.gets.length;
            const actual = await run(operation === 'read' ? [batch] : [], operation === 'read' ? { '--read': true } : { '--retry': batch, '--timeout': '0.01' });
            const row = actual.json.rows[0];
            assert.equal(fake.posts.length, posts, `accepted ID must never be POSTed: ${context}`);
            assert.equal(actual.clock.uuids, 0, `recovery allocates no new ID: ${context}`);
            assert.equal(row.request_id, id, `retain accepted ID: ${context}`);
            const knownTerminal = cache === 'valid' || reply === 'passed';
            assert.equal(actual.code, knownTerminal ? 0 : 3, context);
            assert.equal(row.calls, knownTerminal ? 4 : 'unknown', `accounting follows evidence: ${context}`);
            if (knownTerminal) {
              assert.deepEqual(row.checks, { passed: 17, total: 17 }, context);
              assert.deepEqual(row.criteria, { passed: 4, total: 4 }, context);
              assert.equal(row.state, 'passed', context);
            } else assert.notEqual(row.state, 'passed', `saved success cannot replace evidence: ${context}`);
            if (cache === 'valid') assert.equal(fake.gets.length, gets, `verified receipt is reused: ${context}`);
            else assert.ok(fake.gets.length > gets, `unverified evidence requires same-ID read: ${context}`);
            count++;
          }
  assert.equal(count, 144);
});
