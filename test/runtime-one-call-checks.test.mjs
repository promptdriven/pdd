import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { PLACE, fakeRuntime, filesUnder, harbor, portsFor } from './runtime-fake.mjs';

const START = Date.parse('2026-10-27T16:27:47Z');
async function invoke(setup, fake, options = {}, words = ['place-order'], extra = {}) {
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }, extra);
  const code = await runCheck({ cwd: setup.repo, words, options: { '--json': true, ...options } }, ports);
  return { code, json: JSON.parse(ports.stdout.text), err: ports.stderr.text };
}
const commands = fake => fake.posts.map(post => post.command);
const savedBatch = (setup, batch) => JSON.parse(readFileSync(join(setup.state, 'batches', batch, 'batch.json'), 'utf8'));
const receiptPath = setup => filesUnder(join(setup.state, 'lint-receipts')).find(path => path.endsWith('.json'));

test('lint JSON and saved read retain the validated Runtime report link', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const lint = await invoke(setup, fake, { '--lint': true });
  assert.equal(lint.code, 0, lint.err);
  const link = fake.lint(fake.posts[0].request.requestId).report_url;
  assert.equal(lint.json.report_url, link);
  assert.equal(JSON.parse(readFileSync(join(setup.state, 'batches', lint.json.batch, 'summary.json'))).report_url, link);
  const read = await invoke(setup, fake, { '--read': true }, [lint.json.batch]);
  assert.equal(read.json.report_url, link);
  assert.deepEqual(commands(fake), ['lint']);
});

test('a recent standalone lint admits test without a second lint and keeps its receipt for recovery', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const lint = await invoke(setup, fake, { '--lint': true });
  const checked = await invoke(setup, fake);
  assert.equal(checked.code, 0, checked.err);
  assert.deepEqual(commands(fake), ['lint', 'check']);
  assert.match(checked.err, /Reusing recent passing lint for unchanged source/);
  assert.equal(fake.posts[0].request.source_sha256, fake.posts[1].request.source_sha256);
  const original = savedBatch(setup, lint.json.batch), reused = savedBatch(setup, checked.json.batch);
  assert.deepEqual(reused.lint.request_ids, original.lint.request_ids);
  assert.equal(JSON.parse(readFileSync(join(setup.state, 'batches', checked.json.batch, `${fake.posts[0].request.requestId}.json`))).command, 'lint');
  assert.equal((await invoke(setup, fake, { '--read': true }, [checked.json.batch])).code, 0);
  assert.deepEqual(commands(fake), ['lint', 'check']);
});

test('receipt age is inclusive at ten minutes and reuse never renews its time', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  await invoke(setup, fake, { '--lint': true }, undefined, { now: () => START });
  const first = readFileSync(receiptPath(setup), 'utf8');
  const boundary = await invoke(setup, fake, {}, undefined, { now: () => START + 600_000 });
  assert.equal(boundary.code, 0, boundary.err);
  assert.deepEqual(commands(fake), ['lint', 'check']);
  assert.equal(readFileSync(receiptPath(setup), 'utf8'), first);
  assert.equal((await invoke(setup, fake, {}, undefined, { now: () => START + 600_001 })).code, 0);
  assert.deepEqual(commands(fake), ['lint', 'check', 'lint', 'check']);
});

test('source and selected test changes require fresh lint', async t => {
  for (const change of ['source', 'selection']) {
    const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
    await invoke(setup, fake, { '--lint': true });
    if (change === 'source') {
      const story = join(setup.repo, 'user_stories/place-order.md');
      writeFileSync(story, `${readFileSync(story, 'utf8')}\nA note about this Story.\n`);
    }
    const result = await invoke(setup, fake, {}, change === 'selection' ? [] : undefined);
    assert.equal(result.code, 0, result.err);
    assert.equal(commands(fake).filter(command => command === 'lint').length, 2, change);
  }
});

test('explicit lint is always fresh, while a check can reuse another check preliminary lint', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  assert.equal((await invoke(setup, fake)).code, 0);
  assert.equal((await invoke(setup, fake)).code, 0);
  assert.deepEqual(commands(fake), ['lint', 'check', 'check']);
  await invoke(setup, fake, { '--lint': true });
  await invoke(setup, fake, { '--lint': true });
  assert.deepEqual(commands(fake), ['lint', 'check', 'check', 'lint', 'lint']);
});

test('damaged, future-dated, foreign-owner and incomplete receipts fall back to fresh lint', async t => {
  const changes = [
    () => '{',
    record => ({ ...record, received_at: START + 1 }),
    record => ({ ...record, scope: { ...record.scope, login: 'someone-else' } }),
    record => ({ ...record, scope: { ...record.scope, user_id: '9876' } }),
    record => ({ ...record, engine_sha: 'unknown' }),
    record => ({ ...record, answer: { ...record.answer, state: 'refused' } }),
    record => ({ ...record, answer: { ...record.answer, id: 'wrong-id' } }),
    record => ({ ...record, answer: { ...record.answer, result: { ...record.answer.result,
      report: { ...record.answer.result.report, lint: { complete: false, tests: [] } } } } }),
    record => ({ ...record, answer: { ...record.answer, result: { ...record.answer.result,
      report: { ...record.answer.result.report, lint: { complete: true, tests: [{ path: 'tests/place-order.json', verdict: 'refused' }] } } } } }),
  ];
  for (const change of changes) {
    const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
    await invoke(setup, fake, { '--lint': true }, undefined, { now: () => START });
    const path = receiptPath(setup), changed = change(JSON.parse(readFileSync(path, 'utf8')));
    writeFileSync(path, typeof changed === 'string' ? changed : JSON.stringify(changed));
    const result = await invoke(setup, fake, {}, undefined, { now: () => START });
    assert.equal(result.code, 0, result.err);
    assert.deepEqual(commands(fake), ['lint', 'lint', 'check']);
  }
});

test('a refused or unknown lint never supplies a reusable pass', async t => {
  for (const state of ['refused', 'unknown']) {
    const setup = harbor(t);
    const fake = await fakeRuntime(t, (entry, f) => {
      if (entry.command !== 'lint' || f.posts.length > 1) return f.normal(entry);
      const answer = f.lint(entry.request.requestId, [{ path: PLACE, admission_state: state, interface: { calls: [] } }]);
      answer.state = state;
      answer.result.report.lint.tests = [{ path: 'tests/place-order.json', verdict: state }];
      return { status: 200, json: answer };
    });
    assert.notEqual((await invoke(setup, fake, { '--lint': true })).code, 0);
    assert.equal((await invoke(setup, fake)).code, 0);
    assert.deepEqual(commands(fake), ['lint', 'lint', 'check']);
  }
});

test('capacity engine changes prevent reuse of an older lint build', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  await invoke(setup, fake, { '--lint': true });
  fake.capacity = () => ({ status: 200, json: { maintenance: null, engine_sha: 'b'.repeat(40) } });
  const result = await invoke(setup, fake, {}, undefined, { now: () => START + 10_000 });
  assert.equal(result.code, 0, result.err);
  assert.deepEqual(commands(fake), ['lint', 'lint', 'check']);
});

test('unsafe lint report links are null and valid links are printed in text', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => {
    const reply = f.normal(entry); reply.json.report_url = 'https://elsewhere.example/r/link'; return reply;
  });
  assert.equal((await invoke(setup, fake, { '--lint': true })).json.report_url, null);
  const normal = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: normal.origin });
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--lint': true } }, ports), 0);
  assert.match(ports.stdout.text, /^Report: http:\/\/127\.0\.0\.1:\d+\/r\/[a-f0-9]+$/m);
});
