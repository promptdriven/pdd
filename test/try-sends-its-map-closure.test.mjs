import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { PLACE, fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

// Story: user_stories/try-sends-its-map-closure.md. A repo with two areas: "orders" (2 small Stories)
// and "shelf" (12 Stories whose tests are large, about 10.8 MB together, so all tests do not fit in one upload).
const SEED = 'tests/place-order.json', STORY = 'user_stories/place-order.md', TWIN = 'tests/place-order-twin.json';
const ORDERS_MAP = 'app/maps/orders.json', SHELF_MAP = 'app/maps/shelf.json', STOCK = 'prompts/shelf/stock.prompt.md';
const write = (repo, path, text) => { mkdirSync(join(repo, path, '..'), { recursive: true }); writeFileSync(join(repo, path), typeof text === 'string' ? text : JSON.stringify(text)); };
const tarNames = tar => {
  const listed = spawnSync('tar', ['-tf', '-'], { input: tar, encoding: 'utf8' });
  assert.equal(listed.status, 0, listed.stderr);
  return listed.stdout.trim().split('\n').sort();
};
const listed = ports => ports.stdout.text.split('\n').filter(line => /\d+ bytes$/.test(line)).map(line => line.trim().split(/\s{2,}/)[0]).sort();
// [path, size] of each regular file in a POSIX tar (a PAX header can give the next entry's path or size).
function tarEntries(tar) {
  const entries = [];
  let pax = {};
  for (let at = 0; at + 512 <= tar.length;) {
    const header = tar.subarray(at, at + 512);
    if (!header[0]) break;
    const field = (start, length) => header.subarray(start, start + length).toString('utf8').replace(/\0.*$/s, '');
    const size = parseInt(field(124, 12).trim() || '0', 8), type = String.fromCharCode(header[156] || 48), body = tar.subarray(at + 512, at + 512 + size);
    if (type === 'x') pax = Object.fromEntries(body.toString('utf8').split('\n').filter(Boolean).map(record => record.slice(record.indexOf(' ') + 1).split(/=(.*)/s).slice(0, 2)));
    else if (type === '0') { entries.push([pax.path ?? (field(345, 155) ? `${field(345, 155)}/${field(0, 100)}` : field(0, 100)), Number(pax.size ?? size)]); pax = {}; }
    at += 512 + Math.ceil(size / 512) * 512;
  }
  return entries.sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0);
}
const listedEntries = ports => ports.stdout.text.split('\n').map(line => /^\s+(\S+)\s+(\d+) bytes$/.exec(line)).filter(Boolean).map(match => [match[1], Number(match[2])])
  .sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0);

function twoAreas(t, { missing = null, twin = false } = {}) {
  return harbor(t, repo => {
    if (twin) write(repo, TWIN, readFileSync(join(repo, SEED), 'utf8'));
    const map = (name, prompt, stylesheet) => ({ schema_version: 'prompt-runtime.app-map.v1', name, stylesheets: [stylesheet],
      screens: [{ id: 'main', prompt_path: prompt }], handlers: [{ screen: 'main', kind: 'button', match: { name: 'go' }, handler: { prompt_path: prompt } }] });
    write(repo, ORDERS_MAP, map('Orders', missing === 'prompt' ? 'prompts/orders/gone.prompt.md' : PLACE, missing === 'stylesheet' ? 'app/styles/gone.css' : 'app/styles/orders.css'));
    write(repo, 'app/styles/orders.css', 'body { color: navy; }');
    write(repo, SHELF_MAP, map('Shelf', STOCK, 'app/styles/shelf.css'));
    write(repo, 'app/styles/shelf.css', 'body { color: teal; }');
    write(repo, STOCK, readFileSync(join(repo, PLACE), 'utf8'));
    const seed = JSON.parse(readFileSync(join(repo, SEED), 'utf8'));
    for (let i = 1; i <= 12; i++) {
      write(repo, `user_stories/shelf/s${i}.md`, `# Shelf ${i}\n\n## Acceptance criteria\n\n1. An order of 2 Espresso S and 1 Blueberry Muffin L has a total of 900 cents ($9.00).\n`);
      const doc = structuredClone(seed);
      doc.story_path = `user_stories/shelf/s${i}.md`;
      doc.steps.forEach(step => { step.entry_path = STOCK; step.input.note = 'x'.repeat(900_000); });
      write(repo, `tests/shelf/s${i}.json`, doc);
    }
  });
}
const CLOSURE = [ORDERS_MAP, 'app/styles/orders.css', PLACE, SEED, STORY].sort();
const offline = setup => portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: 'http://127.0.0.1:9' }, {
  gh: () => assert.fail('a listing never signs in'), fetch: () => assert.fail('a listing never contacts a server') }).ports;

test('CTRY1: an area Try uploads only its map closure and its one seed test, in a repo whose tests do not fit in one upload', async t => {
  const setup = twoAreas(t);
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.command === 'try') return { status: 200, json: f.tryJob(entry.request.requestId) };
    return { status: 404, json: {} };
  });
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--app-map': ORDERS_MAP, '--no-open': true, '--no-wait': true } }, ports), 0, ports.stderr.text);
  const tries = fake.posts.filter(post => post.command === 'try');
  assert.equal(tries.length, 1);
  for (const post of fake.posts) assert.deepEqual(tarNames(post.tar), CLOSURE, `${post.command} upload`);
  assert.ok(tries[0].tar.length < 1_048_576, `the Try upload is ${tries[0].tar.length} bytes`);
});

// The real Try path with a fake runtime: its exit code, stderr and the Try POST (null when nothing was posted).
async function realTry(t, setup, words, options) {
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.command === 'try') return { status: 200, json: f.tryJob(entry.request.requestId) };
    return { status: 404, json: {} };
  });
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  const code = await runTry({ cwd: setup.repo, words, options: { ...options, '--no-open': true, '--no-wait': true } }, ports);
  return { code, stderr: ports.stderr.text, posted: fake.posts.find(post => post.command === 'try') ?? null };
}
async function listing(setup, words, options) {
  const ports = offline(setup), code = await runCheck({ cwd: setup.repo, words, options: { ...options, '--files': true } }, ports);
  return { code, stderr: ports.stderr.text, stdout: ports.stdout.text, entries: listedEntries(ports) };
}
async function sameAsTry(t, setup, words, closure) {
  const options = { '--app-map': ORDERS_MAP }, real = await realTry(t, setup, words, options), preview = await listing(setup, words, options);
  assert.equal(real.code, 0, real.stderr);
  assert.ok(real.posted, 'the Try was posted');
  assert.equal(preview.code, 0, preview.stderr);
  const sent = tarEntries(real.posted.tar);
  assert.deepEqual(sent.map(([path]) => path), closure);
  assert.deepEqual(preview.entries, sent, 'same paths and byte sizes');
  const total = sent.reduce((sum, [, size]) => sum + size, 0);
  assert.match(preview.stdout, new RegExp(`^${sent.length} files, .*\\(${total} bytes\\)`, 'm'));
}

test('CTRY2: the --files listing of an area Try is exactly what the real Try path posts for the same arguments', async t => {
  await sameAsTry(t, twoAreas(t), ['place-order'], CLOSURE);
});

test('CTRY3: a Try listing needs exactly one Story, because a Try has one seed; it never lists an upload that no command sends', async t => {
  const setup = twoAreas(t);
  for (const words of [[], ['place-order', 'unknown-item'], ['place-order', 's1']]) {
    const ports = offline(setup);
    const code = await runCheck({ cwd: setup.repo, words, options: { '--files': true, '--app-map': ORDERS_MAP } }, ports);
    assert.equal(code, 2, `${JSON.stringify(words)}: ${ports.stderr.text}`);
    assert.match(ports.stderr.text, /one (?:Story|story)/, 'the refusal says why: a Try has one Story');
    for (const name of words.length ? words : ['place-order', 'unknown-item', 's12']) {
      assert.match(ports.stderr.text, new RegExp(`\\b${name}\\b`), 'the refusal lists the selected Stories to choose from');
    }
    assert.doesNotMatch(ports.stderr.text, /too big/, 'the refusal is about the choice, not a size');
    assert.deepEqual(listed(ports), [], 'no file listing');
  }
  // A check of every Story is still listed honestly: it is too big, and pdd names the largest files with their sizes.
  const all = offline(setup);
  assert.equal(await runCheck({ cwd: setup.repo, words: [], options: { '--files': true } }, all), 4, all.stderr.text);
  assert.match(all.stderr.text, /too big to send/);
  assert.match(all.stderr.text, /tests\/shelf\/s\d+\.json\s+\d+(?:\.\d+)? KB/);
});

for (const missing of ['prompt', 'stylesheet']) test(`CTRY4: a missing declared ${missing} refuses the Try by path before sign-in or upload`, async t => {
  const setup = twoAreas(t, { missing }), path = missing === 'prompt' ? 'prompts/orders/gone.prompt.md' : 'app/styles/gone.css';
  const blocked = offline(setup);
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--app-map': ORDERS_MAP, '--no-open': true, '--no-wait': true } }, blocked), 4, blocked.stderr.text);
  assert.match(blocked.stdout.text + blocked.stderr.text, new RegExp(`${ORDERS_MAP}: ${path.replace(/\./g, '\\.')}`));
  const preview = offline(setup);
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--files': true, '--app-map': ORDERS_MAP } }, preview), 4, preview.stderr.text);
  assert.match(preview.stderr.text, new RegExp(path.replace(/\./g, '\\.')));
  assert.deepEqual(listed(preview), []);
});

test('CTRY5: a Story with two test files is refused by name, and each test path given directly lists exactly what its Try posts', async t => {
  const setup = twoAreas(t, { twin: true });
  const named = await listing(setup, ['place-order'], { '--app-map': ORDERS_MAP });
  assert.equal(named.code, 2, named.stderr);
  for (const path of [SEED, TWIN]) assert.match(named.stderr, new RegExp(path.replace(/[./]/g, '\\$&')), 'both test files are listed to choose from');
  assert.deepEqual(named.entries, []);
  await sameAsTry(t, setup, [SEED], CLOSURE);
  await sameAsTry(t, setup, [TWIN], [ORDERS_MAP, 'app/styles/orders.css', PLACE, TWIN, STORY].sort());
});

test('CTRY6: the listing refuses in the same order and with the same choices as the Try', async t => {
  const broken = twoAreas(t);
  writeFileSync(join(broken.repo, ORDERS_MAP), 'not json');
  for (const words of [[], ['place-order']]) {
    const real = await realTry(t, broken, words, { '--app-map': ORDERS_MAP }), preview = await listing(broken, words, { '--app-map': ORDERS_MAP });
    assert.equal(real.posted, null);
    assert.deepEqual([preview.code, preview.stderr], [real.code, real.stderr], `${JSON.stringify(words)}: a bad map is reported first by both`);
  }
  const setup = twoAreas(t);
  const real = await realTry(t, setup, [], { '--app-map': ORDERS_MAP }), preview = await listing(setup, [], { '--app-map': ORDERS_MAP });
  assert.equal(real.posted, null);
  assert.deepEqual([preview.code, preview.stderr.split('\n').slice(1)], [real.code, real.stderr.split('\n').slice(1)], 'the same Stories to choose from');
});
