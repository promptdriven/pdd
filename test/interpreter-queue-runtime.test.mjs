import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, readdirSync, existsSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { readInterpreterProgress } from '../src/interpreter-queue.mjs';
import { fakeRuntime, harbor, portsFor, temp } from './runtime-fake.mjs';

const check = (setup, ports, options = { '--json': true }) => runCheck({ cwd: setup.repo, words: ['place-order'], options }, ports);
const requestRows = root => readdirSync(root).filter(name => /^ticket-\d+\.json$/.test(name)).map(name => JSON.parse(readFileSync(join(root, name))));
async function until(predicate) {
  for (let n = 0; n < 300; n++) { if (predicate()) return; await new Promise(done => setTimeout(done, 10)); }
  assert.fail('controlled runtime did not reach the requested state');
}

test('public checks share two machine slots across three profiles and ledger each lint/check', async t => {
  const queue = temp(t), setups = [harbor(t), harbor(t), harbor(t)];
  let release = false;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'lint') return f.normal(entry);
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    return { status: 200, json: f.check(id, release ? 'passed' : 'running') };
  });
  const clients = setups.map(setup => portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state,
    PDD_RUNTIME_URL: fake.origin, PDD_INTERPRETER_QUEUE: queue },
    { now: Date.now, pollMs: 5, sleep: () => new Promise(done => setTimeout(done, 5)) }).ports);
  const work = setups.map((setup, i) => check(setup, clients[i]));
  try {
    await until(() => fake.posts.filter(row => row.command === 'check').length >= 2);
    await new Promise(done => setTimeout(done, 100));
    assert.equal(fake.posts.filter(row => row.command === 'check').length, 2, 'machine capacity must hold the third profile');
    const waiting = setups.map(setup => readInterpreterProgress({ cwd: setup.repo, env: clients[0].env })).find(row => row?.state === 'waiting');
    assert.equal(waiting?.position, 1, 'a third profile must have a waiting ticket');
    assert.ok(clients.some(port => /interpreter slot.*position 1/.test(port.stderr.text)));
  } finally { release = true; await Promise.all(work); }
  assert.deepEqual(await Promise.all(work), [0, 0, 0]);
  const rows = requestRows(queue);
  assert.equal(rows.length, 6);
  assert.equal(rows.filter(row => row.kind === 'lint').length, 3);
  assert.equal(rows.filter(row => row.kind === 'check').length, 3);
  assert.ok(rows.every(row => row.state === 'finished' && row.outcome === 'verdict' && row.dispatched));
  assert.ok(rows.every(row => row.activeAtStart <= 2 && row.activeAtEnd <= 2));
});

test('a paid unknown receipt is recorded once and is never resent', async t => {
  const setup = harbor(t), queue = temp(t);
  const fake = await fakeRuntime(t, (entry, f) => entry.command === 'check'
    ? { status: 200, json: f.check(entry.request.requestId, 'unknown') } : f.normal(entry));
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin, PDD_INTERPRETER_QUEUE: queue });
  assert.equal(await check(setup, ports), 3);
  assert.equal(fake.posts.filter(row => row.command === 'check').length, 1);
  const row = requestRows(queue).find(row => row.kind === 'check');
  assert.equal(row?.outcome, 'unknown', 'terminal unknown must have a request ledger row');
  assert.equal(row.state, 'finished');
});

test('lost paid dispatch retains capacity and same-ID saved-batch read completes its ledger', async t => {
  const setup = harbor(t), queue = temp(t); let recover = false;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === 'lint') return f.normal(entry);
    if (entry.method === 'POST') return { destroy: true };
    return recover ? f.normal(entry) : { status: 404, json: { error: { code: 'not-found' } } };
  });
  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin, PDD_INTERPRETER_QUEUE: queue };
  const first = portsFor(env, { pollMs: 60_000 });
  assert.equal(await check(setup, first.ports, { '--json': true, '--timeout': '1' }), 3);
  const held = requestRows(queue).find(row => row.kind === 'check');
  assert.equal(held?.outcome, 'unknown', 'lost dispatch must retain unknown ledger evidence');
  assert.equal(held.state, 'running');
  recover = true;
  const batch = JSON.parse(first.ports.stdout.text).batch, next = portsFor(env);
  assert.equal(await runCheck({ cwd: setup.repo, words: [batch], options: { '--read': true, '--json': true } }, next.ports), 0);
  assert.equal(fake.posts.filter(row => row.command === 'check').length, 1);
  const done = requestRows(queue).find(row => row.kind === 'check');
  assert.equal(done.state, 'finished'); assert.equal(done.outcome, 'verdict');
});

test('corrupt machine queue prevents every interpreter POST', async t => {
  const setup = harbor(t), queue = temp(t);
  writeFileSync(join(queue, 'ticket-broken.json'), '{');
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin, PDD_INTERPRETER_QUEUE: queue });
  assert.equal(await check(setup, ports), 5, 'unreadable machine admission must fail closed');
  assert.equal(fake.posts.length, 0);
});

test('uncertain busy reply backs off globally without allowing a new paid request', async t => {
  const setup = harbor(t), queue = temp(t);
  const fake = await fakeRuntime(t, (entry, f) => entry.command === 'check' ? { status: 503, json: {
    requestId: entry.request.requestId, dispatch: 'not_started', usage: { calls: 1 },
    error: { code: 'server-full', details: { retryable: true, retry_after: 1 } }
  } } : entry.method === 'GET' ? { status: 404, json: { error: { code: 'not-found' } } } : f.normal(entry));
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin, PDD_INTERPRETER_QUEUE: queue });
  assert.equal(await check(setup, ports, { '--json': true, '--timeout': '1' }), 3);
  assert.equal(fake.posts.filter(row => row.command === 'check').length, 1);
  assert.ok(existsSync(join(queue, 'capacity.json')), 'uncertain busy must write shared back-off evidence');
  const cap = JSON.parse(readFileSync(join(queue, 'capacity.json')));
  assert.equal(cap.limit, 1, 'uncertain busy must reduce machine capacity');
  const row = requestRows(queue).find(row => row.kind === 'check');
  assert.equal(row.outcome, 'unknown'); assert.equal(row.state, 'running');
});

test('a batch polls its dispatched requests while another Story waits for a machine slot', async t => {
  const { storyTest } = await import('./runtime-fake.mjs');
  const setup = harbor(t, repo => storyTest(repo, 'third-order')), queue = temp(t), sent = new Set();
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'check') sent.add(entry.request.requestId);
    if (entry.method === 'GET') assert.ok(sent.has(entry.url.split('/').at(-1)), 'an unsent machine waiter must not be polled');
    return f.normal(entry);
  });
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin, PDD_INTERPRETER_QUEUE: queue });
  assert.equal(await runCheck({ cwd: setup.repo, words: [], options: { '--json': true } }, ports), 0);
  assert.equal(fake.posts.filter(row => row.command === 'check').length, 3);
  const rows = requestRows(queue);
  assert.equal(rows.length, 4, 'each lint and check must have machine ledger evidence');
  assert.ok(rows.every(row => row.activeAtStart <= 2 && row.state === 'finished'));
});
