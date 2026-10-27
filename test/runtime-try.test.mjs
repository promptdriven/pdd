import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runTry } from '../src/runtime-client.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

async function tryStory(setup, fake, words, options = {}, extra = {}) {
  const opened = [];
  const { ports, clock } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state },
    { openUrl: async url => { opened.push(url); return true; }, ...extra });
  const code = await runTry({ words, options, cwd: setup.repo }, ports);
  return { code, opened, clock, out: ports.stdout.text, err: ports.stderr.text };
}

// The fake Try server: lint passes, a Try is queued, then running with `link(id)`; DELETE stops it.
function trying(link) {
  return (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.method === 'POST') return { status: 202, json: f.job(entry.request.requestId, 'try', 'queued') };
    if (entry.method === 'DELETE') return { status: 202, json: { ...f.job(entry.headers['x-request-id'], 'stop', 'running'), session_id: entry.url.split('/').at(-1) } };
    const id = entry.url.split('/').at(-1), stop = f.deletes.find(item => item.headers['x-request-id'] === id);
    if (stop) return { status: 200, json: f.stopJob(id, stop.url.split('/').at(-1)) };
    const stopped = f.deletes.some(item => item.url.endsWith(`/${id}`));
    return { status: 200, json: f.tryJob(id, link?.(f, id) ?? undefined, stopped ? 'stopped' : 'running') };
  };
}

// Wrong: the Try seed, tab or call cap differs from the spec, or a running Try is made again (spec 11, A7).
test('RUNTIME-TRY1: pdd try lints, posts one Try with the test as seed, opens the link, then reuses it', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, trying());
  const first = await tryStory(setup, fake, ['place-order']);
  assert.equal(first.code, 0, first.err + first.out);
  assert.deepEqual(fake.posts.map(post => post.command), ['lint', 'try']);
  const request = fake.posts[1].request;
  assert.deepEqual(Object.keys(request).sort(), ['requestId', 'seed', 'source_sha256', 'tab']);
  assert.equal(request.seed, 'tests/place-order.json'); assert.equal(request.tab, 'call');
  assert.deepEqual(first.opened, [`${fake.origin}/s/${'t'.repeat(43)}/`]);
  assert.equal(first.out, 'Try link for "Place a coffee order" is open in your browser. It ends in 24 hours, or with: pdd try --stop place-order\n');
  const again = await tryStory(setup, fake, ['place-order'], { '--no-open': true });
  assert.equal(again.code, 0, again.err);
  assert.equal(fake.posts.length, 2); assert.deepEqual(again.opened, []);
  assert.match(again.out, new RegExp(`Try link for "Place a coffee order": ${fake.origin}/s/t{43}/`));
  const screen = await tryStory(setup, fake, ['place-order'], { '--new': true, '--tab': 'screen' });
  assert.equal(screen.code, 0, screen.err);
  assert.equal(fake.deletes.length, 1); assert.match(fake.deletes[0].headers['x-request-id'], /^[0-9a-f-]{36}$/);
  assert.equal(fake.deletes[0].url, `/v1/try/${request.requestId}`);
  assert.deepEqual(fake.posts.map(post => post.command), ['lint', 'try', 'lint', 'try']);
  assert.equal(fake.posts[3].request.tab, 'screen');
});

// Wrong: --stop sends no request ID, or forgets the Try before the stop is confirmed.
test('RUNTIME-TRY2: --stop sends DELETE with X-Request-Id, reads the stop job and forgets the Try', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, trying());
  assert.equal((await tryStory(setup, fake, ['place-order'])).code, 0);
  const stopped = await tryStory(setup, fake, ['place-order'], { '--stop': true });
  assert.equal(stopped.code, 0, stopped.err);
  assert.equal(fake.deletes.length, 1);
  const id = fake.deletes[0].headers['x-request-id'];
  assert.match(id, /^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/);
  assert.ok(fake.gets.some(get => get.url === `/v1/runs/${id}`));
  assert.equal(stopped.out, 'The Try link for "Place a coffee order" is stopped.\n');
  const none = await tryStory(setup, fake, ['place-order'], { '--stop': true });
  assert.equal(none.code, 2); assert.equal(fake.deletes.length, 1);
});

// Wrong: pdd opens a link that points to another host, plain HTTP or a wrong path (spec 11 link checks).
test('RUNTIME-TRY3: a Try link with another host, scheme, path or a user is not opened', async t => {
  for (const bad of [
    f => `https://${new URL(f.origin).host}/s/abc/`, f => `${f.origin.replace('127.0.0.1', 'localhost')}/s/abc/`,
    f => `${f.origin}/r/abc`, f => `${f.origin}/s/abc`, f => f.origin.replace('http://', 'http://user:pw@') + '/s/abc/']) {
    const setup = harbor(t), fake = await fakeRuntime(t, trying(f => bad(f)));
    const result = await tryStory(setup, fake, ['place-order']);
    assert.equal(result.code, 3, `${bad(fake)}: ${result.out}${result.err}`); assert.deepEqual(result.opened, []);
    assert.equal((result.out + result.err).includes(bad(fake)), false);
    assert.match(result.out, /Stop this Try with: pdd try --stop place-order/);
    assert.equal((await tryStory(setup, fake, ['place-order'], { '--stop': true })).code, 0);
  }
});

// Wrong: too many Try links are retried, or pdd picks a test when several exist.
test('RUNTIME-TRY4: 429 is exit 5 with the stop hint; no STORY with many tests lists them (exit 2)', async t => {
  const setup = harbor(t);
  const busy = await fakeRuntime(t, (entry, f) => entry.method === 'POST' && entry.command === 'try'
    ? { status: 429, headers: { 'retry-after': '5' }, json: { error: { code: 'server-full', message: 'The runtime is busy. Try again later.' }, dispatch: 'not_started' } } : trying()(entry, f));
  const full = await tryStory(setup, busy, ['place-order']);
  assert.equal(full.code, 5); assert.match(full.err, /Too many Try links are open\. Stop one with pdd try --stop/);
  assert.equal(busy.posts.filter(post => post.command === 'try').length, 1);
  const many = await tryStory(setup, busy, []);
  assert.equal(many.code, 2); assert.match(many.err, /place-order/); assert.match(many.err, /unknown-item/);
  const one = harbor(t, repo => rmSync(join(repo, 'tests/unknown-item.json')));
  const lone = await fakeRuntime(t, trying());
  const used = await tryStory(one, lone, []);
  assert.equal(used.code, 0, used.err); assert.equal(lone.posts[1].request.seed, 'tests/place-order.json');
  const bad = harbor(t, repo => {
    const file = join(repo, 'tests/place-order.json'), doc = JSON.parse(readFileSync(file, 'utf8'));
    doc.steps[0].input.items[0].quantity = 0; writeFileSync(file, JSON.stringify(doc));
  });
  const quiet = await fakeRuntime(t, trying());
  const refused = await tryStory(bad, quiet, ['place-order']);
  assert.equal(refused.code, 4); assert.equal(quiet.posts.length, 0);
  assert.match(refused.out, /steps\[0\] input \/items\/0\/quantity is 0\. The prompt allows 1 to 20\./);
});

// Wrong: a Try that is still starting is made a second time, so the first one runs with no way to stop it.
test('RUNTIME-TRY5: a recorded Try that is not ready gives exit 3 and no new Try; --new stops it first', async t => {
  const setup = harbor(t);
  let ready = false;
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'GET' && !ready && !f.deletes.length
    ? { status: 200, json: f.job(entry.url.split('/').at(-1), 'try', 'running') } : trying()(entry, f));
  const slow = await tryStory(setup, fake, ['place-order'], {}, {});
  assert.equal(slow.code, 3); assert.equal(fake.posts.filter(post => post.command === 'try').length, 1);
  const again = await tryStory(setup, fake, ['place-order']);
  assert.equal(again.code, 3); assert.match(again.err, /pdd try place-order --new/);
  assert.equal(fake.posts.filter(post => post.command === 'try').length, 1);
  const fresh = await tryStory(setup, fake, ['place-order'], { '--new': true });
  assert.equal(fresh.code, 0, fresh.err);
  assert.equal(fake.deletes.length, 1); assert.equal(fake.posts.filter(post => post.command === 'try').length, 2);
  ready = true;
});
