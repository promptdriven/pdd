import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runTry } from '../src/runtime-client.mjs';
import { openServe } from '../src/try-http.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';

// Independent replays of whole-project safety and authored HTTP request examples.
test('2760 replay: an invalid non-seed Story refuses the whole project before authentication', async t => {
  const setup = harbor(t, root => {
    const file = join(root, 'tests/unknown-item.json'), doc = JSON.parse(readFileSync(file));
    doc.steps[0].input.items[0].quantity = 0;
    writeFileSync(file, JSON.stringify(doc));
  });
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state }, { gh: () => assert.fail('invalid selected source must not authenticate') });
  assert.equal(await runTry({ cwd: setup.repo }, ports), 4);
  assert.match(ports.stdout.text, /unknown-item/);
});

test('2760 replay: opening the whole project cannot reuse a narrower named session', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.command === 'try') return { status: 200, json: f.tryJob(entry.request.requestId) };
    if (entry.url.endsWith('/tests')) return { status: 404, json: { error: { code: 'not-found' } } };
    return { status: 200, json: f.tryJob(entry.url.split('/').at(-1)) };
  });
  const io = () => portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }, { openUrl: async () => true }).ports;
  const named = io();
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'] }, named), 0, named.stderr.text);
  const whole = io(), posts = fake.posts.length;
  assert.equal(await runTry({ cwd: setup.repo }, whole), 2);
  assert.match(whole.stderr.text, /whole project.*pdd simulate --new/);
  assert.equal(fake.posts.length, posts);
});

test('2760 replay: HTTP example uses authored path, query and body with safe shell quoting', async () => {
  const entry = { entry_path: 'prompts/books.prompt.md', operation: 'add', http: { method: 'POST', path: '/books/:id' }, input_schema: { type: 'object', required: ['body'], properties: { params: { type: 'object', properties: { id: { type: 'string' } } }, query: { type: 'object', properties: { shelf: { type: 'string' } }, required: ['shelf'] }, body: { type: 'object' } } } };
  const { ports } = portsFor({}, { serve: async () => {} });
  const scenario = { doc: { steps: [{ entry_path: entry.entry_path, operation: 'add', input: { params: { id: 'book 7' }, query: { shelf: 'read next' }, body: { title: "Sam's book" } } }] } };
  await openServe({ ports, runtime: { send: async () => ({ status: 200, json: { entries: [entry] } }) } }, scenario, 'synthetic', { '--serve': '0' });
  assert.match(ports.stdout.text, /curl -X POST .*\/books\/book%207\?shelf=read\+next/);
  assert.match(ports.stdout.text, /--data/);
  assert.ok(ports.stdout.text.includes("Sam'\\''s book"), 'single quotes in authored JSON are shell escaped');
  const missing = portsFor({}, { serve: async () => {} }).ports;
  await openServe({ ports: missing, runtime: { send: async () => ({ status: 200, json: { entries: [entry] } }) } }, {}, 'synthetic', { '--serve': '0' });
  assert.match(missing.stdout.text, /<required:id>/);
  assert.match(missing.stdout.text, /required%3Ashelf/);
  assert.match(missing.stdout.text, /<required:body>/);
});
