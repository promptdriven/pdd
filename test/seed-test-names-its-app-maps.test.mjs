import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { PLACE, fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

// Story: user_stories/seed-test-names-its-app-maps.md. The Harbor seed test names one app map whose tap calls
// prompts/receipts.prompt.md, a prompt that the Story's own step never reaches.
const SEED = 'tests/place-order.json', STORY = 'user_stories/place-order.md', MAP = 'app/app-map.json';
const RECEIPTS = 'prompts/receipts.prompt.md', STYLE = 'app/styles/app.css';
const write = (repo, path, text) => { mkdirSync(join(repo, path, '..'), { recursive: true }); writeFileSync(join(repo, path), typeof text === 'string' ? text : JSON.stringify(text)); };
const tarNames = tar => {
  const listed = spawnSync('tar', ['-tf', '-'], { input: tar, encoding: 'utf8' });
  assert.equal(listed.status, 0, listed.stderr);
  return listed.stdout.trim().split('\n').sort();
};
const listed = ports => ports.stdout.text.split('\n').filter(line => /\d+ bytes$/.test(line)).map(line => line.trim().split(/\s{2,}/)[0]).sort();

function seeded(t, { appMaps = [MAP], map = MAP } = {}) {
  return harbor(t, repo => {
    write(repo, map, { schema_version: 'prompt-runtime.app-map.v1', name: 'Harbor', stylesheets: [STYLE],
      screens: [{ id: 'menu', prompt_path: PLACE, operation: 'place_order', source: 'operation' }],
      handlers: [{ screen: 'menu', kind: 'button', match: { value: 'send-receipt' }, handler: { prompt_path: RECEIPTS, operation: 'send' } }] });
    write(repo, STYLE, 'body { color: navy; }');
    write(repo, RECEIPTS, readFileSync(join(repo, PLACE), 'utf8'));
    const seed = JSON.parse(readFileSync(join(repo, SEED), 'utf8'));
    if (appMaps !== null) seed.app_maps = appMaps;
    write(repo, SEED, JSON.stringify(seed, null, 2));
  });
}
const STORY_FILES = [PLACE, SEED, STORY];
const WITH_MAP = [...STORY_FILES, MAP, STYLE, RECEIPTS].sort();
const offline = setup => portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: 'http://127.0.0.1:9' }, {
  gh: () => assert.fail('this never signs in'), fetch: () => assert.fail('this never contacts a server') }).ports;

test('CSEED1: the file listing of a test that names its app map includes the map closure, with no --app-map', async t => {
  const setup = seeded(t), ports = offline(setup);
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--files': true } }, ports), 0, ports.stderr.text);
  assert.deepEqual(listed(ports), WITH_MAP);
});

for (const mode of ['check', 'lint']) test(`CSEED2: a ${mode} of that test sends the declared map closure in every upload`, async t => {
  const setup = seeded(t);
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  const options = mode === 'lint' ? { '--lint': true } : {};
  const code = await runCheck({ cwd: setup.repo, words: ['place-order'], options }, ports);
  assert.ok(fake.posts.length > 0, `the ${mode} was sent (exit ${code}): ${ports.stdout.text}${ports.stderr.text}`);
  for (const post of fake.posts) assert.deepEqual(tarNames(post.tar), WITH_MAP, `${post.command} upload`);
  assert.equal(code, 0, ports.stdout.text + ports.stderr.text);
});

test('CSEED3: a missing declared app map is refused by path before sign-in or upload', async t => {
  const setup = seeded(t, { appMaps: ['app/maps/gone.json'] });
  const preview = offline(setup);
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--files': true } }, preview), 4, preview.stderr.text);
  assert.match(preview.stderr.text, /tests\/place-order\.json: app\/maps\/gone\.json/);
  assert.deepEqual(listed(preview), []);
  const check = offline(setup);
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: {} }, check), 4, check.stderr.text);
  assert.match(check.stdout.text + check.stderr.text, /app\/maps\/gone\.json/);
});

for (const options of [{ '--lint': true, '--app-map': MAP }, { '--app-map': MAP }]) {
  test(`CSEED4: pdd test ${Object.keys(options).join(' ')} is refused and points to app_maps`, async t => {
    const setup = seeded(t), ports = offline(setup);
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options }, ports), 2, ports.stderr.text);
    assert.match(ports.stderr.text, /--app-map works only with pdd simulate and pdd test --files/);
    assert.match(ports.stderr.text, /"app_maps"/);
  });
}

test('CSEED5: a test without app_maps sends the same files as before', async t => {
  const setup = seeded(t, { appMaps: null }), ports = offline(setup);
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--files': true } }, ports), 0, ports.stderr.text);
  assert.deepEqual(listed(ports), [...STORY_FILES].sort());
});
