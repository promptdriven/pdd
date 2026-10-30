import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { fakeRuntime, harbor, portsFor, PLACE } from './runtime-fake.mjs';

// Independent n7 timeline: 20 s capacity refusal, 5 s backoff, then >65 s lint work.
async function pending(t, mode = 'check') {
  const setup = harbor(t);
  let clock, attempts = 0, reply = 'running';
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST') {
      if (entry.command === 'check' && reply === 'passed') return { status: 200, json: f.check(entry.request.requestId) };
      assert.equal(entry.command, 'lint', 'a check or Try cannot pass a pending lint');
      if (++attempts === 1) {
        clock.now += 20_000;
        const refusal = { code: 'lint-queue-timeout', details: { retryable: true, retry_after: 5 } };
        return { status: 200, json: f.job(entry.request.requestId, 'lint', 'refused', { report: { refusal } }) };
      }
      return { status: 202, json: f.job(entry.request.requestId, 'lint', 'queued') };
    }
    const id = entry.url.split('/').at(-1);
    if (reply === 'passed') return { status: 200, json: f.lint(id) };
    if (reply === 'refused') return { status: 200, json: { ...f.lint(id, [{ path: PLACE, admission_state: 'missing' }]), state: 'refused' } };
    if (reply === 'wrong-id') return { status: 200, json: f.lint('00000000-0000-4000-8000-000000000000') };
    return { status: 200, json: f.job(id, 'lint', 'running') };
  });
  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };
  const first = portsFor(env); clock = first.clock;
  const options = mode === 'try' ? { '--no-open': true } : { '--json': true, ...(mode === 'lint' ? { '--lint': true } : {}) };
  const code = await (mode === 'try' ? runTry : runCheck)({ cwd: setup.repo, words: ['place-order'], options }, first.ports);
  return { setup, fake, env, code, ...first, setReply(value) { reply = value; } };
}

async function read(r, batch) {
  const next = portsFor(r.env);
  const code = await runCheck({ cwd: r.setup.repo, options: { '--read': batch, '--json': true } }, next.ports);
  return { code, json: JSON.parse(next.ports.stdout.text), ...next };
}

for (const mode of ['check', 'lint', 'try']) test(`LINT-PENDING: ${mode} reports known running lint at the shared 90 s deadline`, async t => {
  const r = await pending(t, mode);
  assert.equal(r.code, 3);
  assert.equal(r.clock.now - Date.parse('2026-10-27T16:27:47Z'), 90_000);
  assert.equal(r.fake.posts.length, 2);
  const output = r.ports.stdout.text + r.ports.stderr.text;
  assert.match(output, /Lint is still running/);
  assert.doesNotMatch(output, /lint result is unknown/);
  if (mode === 'check') {
    const json = JSON.parse(r.ports.stdout.text);
    assert.equal(json.rows[0].state, 'not_run');
    assert.equal(json.rows[0].calls, 0);
    assert.equal(json.rows[0].request_id, null);
    const saved = JSON.parse(readFileSync(join(r.setup.state, 'batches', json.batch, 'batch.json')));
    assert.equal(saved.lint.pending, true);
    const next = await read(r, json.batch);
    assert.equal(next.code, 3);
    assert.match(next.json.rows[0].reason.message, /Lint is still running/);
    assert.equal(next.clock.uuids, 0);
    assert.equal(r.fake.posts.length, 2);
  }
});

test('LINT-PENDING: read changes a pending lint into a reached refusal without sending a check', async t => {
  const r = await pending(t);
  const batch = JSON.parse(r.ports.stdout.text).batch;
  r.setReply('refused');
  const next = await read(r, batch);
  assert.equal(next.code, 4);
  assert.equal(next.json.rows[0].state, 'refused');
  assert.equal(next.json.rows[0].calls, 0);
  assert.equal(next.json.rows[0].refusals[0].code, 'interface-missing');
  assert.doesNotMatch(JSON.stringify(next.json), /lint result is unknown|Lint is still/);
  assert.equal(next.clock.uuids, 0);
  assert.equal(r.fake.posts.length, 2);
});

test('LINT-PENDING: late passing lint continues the original held check', async t => {
  const r = await pending(t);
  const batch = JSON.parse(r.ports.stdout.text).batch;
  r.setReply('passed');
  const next = await read(r, batch);
  assert.equal(next.code, 0);
  assert.equal(next.json.rows[0].state, 'passed');
  assert.equal(next.json.rows[0].calls, 1);
  assert.equal(new Set(r.fake.posts.filter(post => post.command === 'check').map(post => post.request.requestId)).size, 1);
  assert.equal(r.fake.posts.length, 3);
  assert.equal(r.fake.posts.at(-1).command, 'check');
});

test('LINT-PENDING: an older already-read terminal lint repairs stale unknown wording from saved bytes', async t => {
  const r = await pending(t);
  const batch = JSON.parse(r.ports.stdout.text).batch;
  const folder = join(r.setup.state, 'batches', batch), file = join(folder, 'batch.json');
  const saved = JSON.parse(readFileSync(file));
  const id = saved.lint.request_ids.at(-1);
  saved.lint = { ...saved.lint, pending: false, unknown: false, state: 'refused' };
  saved.rows[0].phase = 'server'; delete saved.rows[0].calls;
  saved.rows[0].note = { code: null, message: 'The lint result is unknown, so pdd sent no checks.' };
  writeFileSync(file, JSON.stringify(saved));
  const answer = r.fake.lint(id, [{ path: PLACE, admission_state: 'draft', interface: { calls: [] } }]);
  answer.state = 'refused';
  answer.result.refusals = [{ code: 'interface-missing', message: 'auxiliary.prompt.md has no Runtime interface.', path: 'auxiliary.prompt.md' }];
  writeFileSync(join(folder, id + '.json'), JSON.stringify(answer));
  const reads = r.fake.gets.length;
  const next = await read(r, batch);
  assert.equal(next.code, 5);
  assert.equal(next.json.rows[0].calls, 0);
  assert.match(next.json.rows[0].reason.message, /auxiliary.prompt.md/);
  assert.doesNotMatch(JSON.stringify(next.json), /lint result is unknown/);
  assert.equal(r.fake.gets.length, reads, 'matching saved terminal lint needs no GET');
  assert.equal(r.fake.posts.length, 2);
});

test('LINT-PENDING: a wrong-ID refresh remains unknown, with zero unsent check calls', async t => {
  const r = await pending(t);
  r.setReply('wrong-id');
  const next = await read(r, JSON.parse(r.ports.stdout.text).batch);
  assert.equal(next.code, 3);
  assert.equal(next.json.rows[0].calls, 0);
  assert.match(next.json.rows[0].reason.message, /unknown/);
  assert.equal(next.clock.uuids, 0);
  assert.equal(r.fake.posts.length, 2);
});
