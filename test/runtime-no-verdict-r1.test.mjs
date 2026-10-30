import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { runCheck } from '../src/runtime-client.mjs';
import { renderText } from '../src/runtime-output.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';

// Oracle: lead 01:20 decision, exact generic only; state owns the verdict.
const advice = 'The engine restarted. Read this request later; do not resubmit.';
async function run(setup, fake, options = { '--json': true }) {
  const { ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  const code = await runCheck({ words: options['--read'] ? [] : ['place-order'], options, cwd: setup.repo }, ports);
  return { code, text: ports.stdout.text, json: options['--json'] ? JSON.parse(ports.stdout.text) : null };
}

for (const outcome of [undefined, 'Fail']) test(`R1 engine restart advice survives unknown outcome ${outcome}`, async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command !== 'check' && e.method !== 'GET') return f.normal(e);
    const answer = f.check(e.request?.requestId ?? e.url.split('/').at(-1), 'unknown', [], []);
    delete answer.result.outcome;
    if (outcome) answer.result.outcome = outcome;
    answer.result.why = advice;
    return { status: 200, json: answer };
  });
  const result = await run(setup, fake);
  assert.equal(result.code, 3);
  assert.equal(result.json.rows[0].why, advice);
  assert.equal(result.json.rows[0].reason.message, advice);
  const text = await run(setup, fake, { '--read': result.json.batch });
  assert.ok(text.text.includes(advice));
  assert.equal(fake.posts.filter(e => e.command === 'check').length, 1);
});

// Compatibility controls exercise refused checks and unsent rows blocked by lint.
for (const mode of ['refused', 'not_run', 'unknown']) for (const why of [advice, 'Checks failed.', 'Checks failed. More detail.']) {
  test(`R1 ${mode} keeps only specific cleaned advice: ${why}`, async t => {
    const setup = harbor(t);
    const fake = await fakeRuntime(t, (e, f) => {
      if (mode === 'not_run' && e.command === 'lint') {
        const answer = f.job(e.request.requestId, 'lint', 'unknown', { why: `\u0001${why}\u0002`, outcome: 'Fail' });
        return { status: 200, json: answer };
      }
      if (e.command !== 'check') return f.normal(e);
      const answer = f.check(e.request.requestId, mode === 'unknown' ? 'unknown' : 'refused', [], [{ code: 'service', reason: 'Unavailable' }]);
      Object.assign(answer.result, { why: `\u0001${why}\u0002`, outcome: 'Fail' });
      return { status: 200, json: answer };
    });
    const result = await run(setup, fake);
    assert.equal(result.json.rows[0].state, mode);
    assert.equal(result.json.rows[0].why, why === 'Checks failed.' ? null : why);
  });
}

test('R1 saved lint read drops exact generic advice without submitting checks (A17)', async t => {
  const setup = harbor(t); let reading = false;
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.method === 'GET' && reading) return { status: 200, json: f.job(e.url.split('/').at(-1), 'lint', 'unknown', { why: 'Checks failed.', outcome: 'Fail' }) };
    if (e.command === 'lint') return { status: 200, json: f.job(e.request.requestId, 'lint', 'unknown') };
    return f.normal(e);
  });
  const first = await run(setup, fake); reading = true;
  const read = await run(setup, fake, { '--read': first.json.batch, '--json': true });
  assert.equal(read.json.rows[0].state, 'not_run');
  assert.equal(read.json.rows[0].why, null);
  assert.notEqual(read.json.rows[0].reason?.message, 'Checks failed.');
  const text = await run(setup, fake, { '--read': first.json.batch });
  assert.doesNotMatch(text.text, /Checks failed\./);
  assert.equal(fake.posts.filter(e => e.command === 'check').length, 0);
});

test('R1 cached unknown receipt refreshes to the newer terminal GET without stale advice', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (e, f) => e.command === 'check'
    ? { status: 200, json: f.check(e.request.requestId, 'refused', [], [{ code: 'service', reason: 'Unavailable' }]) } : f.normal(e));
  const first = await run(setup, fake);
  const folder = `${setup.state}/batches/${first.json.batch}`, file = `${folder}/batch.json`;
  const saved = JSON.parse(readFileSync(file)), id = saved.rows[0].request_ids.at(-1);
  // A saved refusal may coexist with a newer unknown receipt; it is not transport-loss evidence.
  Object.assign(saved.rows[0], { why: 'No verdict. OLD REFUSAL', lost: false });
  writeFileSync(file, JSON.stringify(saved));
  const answer = fake.check(id, 'unknown', [], []);
  delete answer.result.why;
  writeFileSync(`${folder}/${id}.json`, JSON.stringify(answer));
  const result = await run(setup, fake, { '--json': true, '--read': first.json.batch });
  // #2655 requires open caches to refresh the same ID; the newer GET owns the verdict.
  assert.equal(result.json.rows[0].state, 'passed');
  assert.equal(result.json.rows[0].why, null);
  assert.doesNotMatch(JSON.stringify(result.json), /OLD REFUSAL/);
  assert.equal(fake.gets.length, 1);
  assert.equal(fake.gets[0].url.split('/').at(-1), id);
  assert.equal(fake.posts.filter(e => e.command === 'check').length, 1);
});

// Integration oracle: polling eligibility is not proof that an old explanation came from transport loss.
test('R1 unknown GET cannot inherit a non-lost saved refusal explanation (A10 integration)', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === 'check') return { status: 200, json: f.check(e.request.requestId, 'refused', [], [{ code: 'service', reason: 'Unavailable' }]) };
    if (e.method === 'GET') {
      const answer = f.check(e.url.split('/').at(-1), 'unknown', [], []);
      delete answer.result.why;
      return { status: 200, json: answer };
    }
    return f.normal(e);
  });
  const first = await run(setup, fake);
  const folder = `${setup.state}/batches/${first.json.batch}`, file = `${folder}/batch.json`;
  const saved = JSON.parse(readFileSync(file)), id = saved.rows[0].request_ids.at(-1);
  Object.assign(saved.rows[0], { why: 'No verdict. OLD REFUSAL', lost: false });
  writeFileSync(file, JSON.stringify(saved));
  const cached = fake.check(id, 'unknown', [], []);
  delete cached.result.why;
  writeFileSync(`${folder}/${id}.json`, JSON.stringify(cached));
  const result = await run(setup, fake, { '--json': true, '--read': first.json.batch });
  assert.equal(result.code, 3);
  assert.equal(result.json.rows[0].state, 'unknown');
  assert.equal(result.json.rows[0].why, null);
  assert.doesNotMatch(JSON.stringify(result.json), /OLD REFUSAL/);
  assert.equal(fake.gets.length, 1);
  assert.equal(fake.gets[0].url.split('/').at(-1), id);
  const text = await run(setup, fake, { '--read': first.json.batch });
  assert.doesNotMatch(text.text, /OLD REFUSAL/);
  assert.equal(fake.posts.filter(e => e.command === 'check').length, 1);
});

test('R1 legacy unknown transport explanation survives an omitted lost flag', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === 'check' || e.method === 'GET') {
      const answer = f.check(e.request?.requestId ?? e.url.split('/').at(-1), 'unknown', [], []);
      delete answer.result.why;
      return { status: 200, json: answer };
    }
    return f.normal(e);
  });
  const first = await run(setup, fake);
  const file = `${setup.state}/batches/${first.json.batch}/batch.json`;
  const saved = JSON.parse(readFileSync(file));
  saved.rows[0].why = 'The answer to the request was lost.';
  delete saved.rows[0].lost;
  writeFileSync(file, JSON.stringify(saved));
  const result = await run(setup, fake, { '--json': true, '--read': first.json.batch });
  assert.equal(result.code, 3);
  assert.equal(result.json.rows[0].state, 'unknown');
  assert.equal(result.json.rows[0].why, 'The answer to the request was lost.');
  assert.equal(result.json.rows[0].reason.message, 'The answer to the request was lost.');
  assert.equal(fake.gets.length, 1);
  assert.equal(fake.posts.filter(e => e.command === 'check').length, 1);
});

test('R1 sent NOT RUN without a note explains no execution, with or without next advice (A12)', () => {
  for (const next_step of [null, 'Tell the person.']) {
    const row = { state: 'not_run', story: 'one', title: 'One', test: 'one.json', request_ids: ['sent-id'], refusals: [], next_step };
    const text = renderText({ rows: [row], exitCode: 5 });
    assert.match(text, /NOT RUN  One \(one.json\): No checks ran for this attempt\./);
    assert.doesNotMatch(text, /pdd did not send it/);
    if (next_step) assert.match(text, /Next: Tell the person\./);
  }
});
