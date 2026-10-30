import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, readdirSync, rmSync, existsSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

const read = path => JSON.parse(readFileSync(path, 'utf8'));
function runner(setup, fake) {
  return async (options = {}, words = []) => {
    const { ports, clock } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
    const code = await runCheck({ cwd: setup.repo, words, options: { '--json': true, ...options } }, ports);
    return { code, json: JSON.parse(ports.stdout.text), clock };
  };
}

// A definitive POST answer has no receipt. Its persisted provenance distinguishes
// it from an allocated ID whose server result is still unknown after a crash.
for (const [status, error, state, verdict, exit] of [
  [422, 'invalid-input', 'refused', 'refused', 4],
  [503, 'pool-low-room', 'not_run', 'not_run', 5],
  [429, 'rate-limited', 'not_run', 'not_run', 5],
]) test(`2655 new batch: ${status} ${error} retains final POST provenance on read and retry`, async t => {
  const setup = harbor(t);
  let beforePost;
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === 'lint') return { status: 200, json: f.lint(e.request.requestId) };
    if (e.method === 'POST') {
      const batches = join(setup.state, 'batches');
      const folder = readdirSync(batches).find(name => read(join(batches, name, 'batch.json')).rows.some(row => row.request_ids.includes(e.request.requestId)));
      beforePost = read(join(batches, folder, 'batch.json')).rows[0];
      return { status, json: { error: { code: error, message: `Advice for ${error}.` } } };
    }
    return { status: 404, json: { error: { code: 'not-found' } } };
  });
  const run = runner(setup, fake), first = await run({}, ['place-order']);
  const file = join(setup.state, 'batches', first.json.batch, 'batch.json');
  const id = first.json.rows[0].request_id;
  assert.equal(beforePost.post_verdict, 'uncertain', 'provenance must be durable before POST');
  assert.equal(beforePost.state, 'sending');
  assert.deepEqual(beforePost.request_ids, [id]);
  assert.equal(first.code, exit);
  assert.equal(first.json.rows[0].state, state);
  assert.equal(read(file).rows[0].post_verdict, verdict, 'actual final lifecycle classification must replace uncertain');
  assert.equal(existsSync(join(setup.state, 'batches', first.json.batch, `${id}.json`)), false);
  const advice = row => ({ why: row.why, reason: row.reason, note: row.note, refusals: row.refusals, next_step: row.next_step });
  const posts = fake.posts.length, gets = fake.gets.length;
  for (const retry of [false, false, true, true]) {
    const result = await run(retry ? { '--retry': first.json.batch, '--timeout': '0.01' } : { '--read': true }, retry ? [] : [first.json.batch]);
    assert.equal(result.code, exit);
    assert.equal(result.json.rows[0].state, state);
    assert.equal(result.json.rows[0].request_id, id);
    assert.deepEqual(advice(result.json.rows[0]), advice(first.json.rows[0]));
    assert.equal(read(file).rows[0].post_verdict, verdict);
    assert.deepEqual(read(file).rows[0].request_ids, [id]);
    assert.equal(result.clock.uuids, 0);
  }
  assert.equal(fake.gets.length, gets, 'definitive POST outcomes must never poll');
  assert.equal(fake.posts.length, posts, 'read and retry must never resubmit');
});

test('2655 legacy stale busy ID without POST provenance remains unknown and cannot retry', async t => {
  const setup = harbor(t);
  let down = false;
  const fake = await fakeRuntime(t, (e, f) => {
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    if (e.command === 'lint') return { status: 200, json: f.lint(id) };
    return down ? { status: 503, json: { error: { code: 'temporary' } } } : { status: 200, json: f.check(id) };
  });
  const run = runner(setup, fake), first = await run({}, ['place-order']);
  assert.equal(first.code, 0);
  const folder = join(setup.state, 'batches', first.json.batch), file = join(folder, 'batch.json'), id = first.json.rows[0].request_id;
  const saved = read(file), row = saved.rows[0];
  delete row.post_verdict;
  Object.assign(row, { state: 'not_run', busy: true, can_retry: true, eligible: true, phase: 'server', retry_at: null });
  writeFileSync(file, JSON.stringify(saved));
  rmSync(join(folder, `${id}.json`));
  rmSync(join(folder, `${id}.admission.json`), { force: true });
  down = true;
  const posts = fake.posts.length, gets = fake.gets.length;
  const result = await run({ '--retry': first.json.batch, '--timeout': '0.01' });
  assert.equal(result.code, 3);
  assert.equal(result.json.rows[0].state, 'unknown');
  assert.equal(result.json.rows[0].calls, 'unknown');
  assert.equal(result.json.rows[0].request_id, id);
  assert.equal(read(file).rows[0].can_retry, false);
  assert.equal(read(file).rows[0].busy, false);
  assert.deepEqual(read(file).rows[0].request_ids, [id]);
  assert.equal(fake.posts.length, posts);
  assert.ok(fake.gets.length > gets, 'known ID must be read despite stale busy labels');
  assert.equal(result.clock.uuids, 0);
});

for (const scenario of ['terminal cache', 'unrelated batch']) test(`2655 UUID refresh preserves ${scenario}`, async t => {
  const setup = harbor(t);
  let running = false;
  const fake = await fakeRuntime(t, (e, f) => {
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    if (e.command === 'lint') return { status: 200, json: f.lint(id) };
    return { status: 200, json: f.check(id, running ? 'running' : 'passed') };
  });
  const run = runner(setup, fake), first = await run({}, ['place-order']);
  assert.equal(first.code, 0);
  const folder = join(setup.state, 'batches', first.json.batch), id = first.json.rows[0].request_id;
  const raw = join(folder, `${id}.json`), terminal = readFileSync(raw);
  let unrelated;
  if (scenario === 'unrelated batch') {
    const second = await run({}, ['place-order']);
    assert.equal(second.code, 0);
    assert.notEqual(second.json.rows[0].request_id, id);
    unrelated = join(setup.state, 'batches', second.json.batch, `${id}.json`);
    assert.equal(existsSync(unrelated), false);
  }
  running = true;
  const posts = fake.posts.length, result = await run({ '--read': true }, [id]);
  assert.equal(result.code, 3);
  assert.equal(result.json.rows[0].state, 'running');
  assert.equal(result.json.rows[0].request_id, id);
  if (scenario === 'terminal cache') assert.deepEqual(readFileSync(raw), terminal, 'verified terminal receipt must survive a later running response');
  else assert.equal(existsSync(unrelated), false, 'same owner/root/origin without row membership must not receive a stray receipt');
  assert.equal(fake.posts.length, posts);
  assert.equal(result.clock.uuids, 0);
});
