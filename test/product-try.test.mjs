import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { cpSync, existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runTry } from '../src/runtime-client.mjs';
import { fakeRuntime, portsFor, sha, temp } from './runtime-fake.mjs';

function coffee(t) {
  const folder = temp(t), repo = join(folder, 'repo'), home = join(folder, 'home'), state = join(folder, 'state');
  cpSync(new URL('../examples/coffee-pickup/', import.meta.url), repo, { recursive: true }); mkdirSync(home);
  for (const part of ['phone', 'server', 'barista']) {
    const path = join(repo, `app/maps/${part}.json`);
    writeFileSync(path, readFileSync(path, 'utf8').replaceAll('examples/coffee-pickup/', ''));
  }
  const plan = join(repo, 'product/plan.md'); writeFileSync(plan, readFileSync(plan, 'utf8').replaceAll('examples/coffee-pickup/', ''));
  mkdirSync(join(repo, 'tests')); mkdirSync(join(repo, 'user_stories/journeys'), { recursive: true });
  const scenario = JSON.parse(readFileSync(new URL('./runtime/J1-coffee-pickup.json', import.meta.url), 'utf8').replaceAll('examples/coffee-pickup/', ''));
  scenario.initial_world.journeyOnly = true;
  scenario.initial_world.menu[0].priceCents = 999;
  writeFileSync(join(repo, 'tests/J1.json'), JSON.stringify(scenario));
  cpSync(new URL('../user_stories/journeys/J1-coffee-pickup.md', import.meta.url), join(repo, scenario.story_path));
  writeFileSync(join(repo, 'prompts/phone/seed.json'), '{"enabled":false}');
  for (const args of [['init', '-q'], ['add', '-A']]) assert.equal(spawnSync('git', args, { cwd: repo }).status, 0);
  return { repo, home, state, scenario, authored: readFileSync(join(repo, 'tests/J1.json'), 'utf8') };
}
const extract = (tar, path) => {
  const result = spawnSync('tar', ['-xOf', '-', path], { input: tar });
  assert.equal(result.status, 0, result.stderr.toString()); return result.stdout.toString('utf8');
};
function trying(entry, fake) {
  if (entry.method === 'POST' && entry.command === 'lint') return { status: 200, json: fake.lint(entry.request.requestId,
    ['phone/phone', 'server/server', 'barista/board'].map(name => ({ path: `prompts/${name}.prompt.md`, state: 'draft', admission_state: 'draft', interface: { calls: [] } }))) };
  if (entry.method === 'POST') return { status: 200, json: fake.tryJob(entry.request.requestId) };
  if (entry.method === 'DELETE') return { status: 200, json: fake.stopJob(entry.headers['x-request-id'], entry.url.split('/').at(-1)) };
  if (entry.url.endsWith('/tests') || entry.url.endsWith('/approvals')) return { status: 200, json: { tests: [], approvals: [] } };
  return { status: 200, json: fake.tryJob(entry.url.split('/').at(-1)) };
}
async function open(setup, fake, options, words = []) {
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }, { openUrl: async () => true });
  const code = await runTry({ cwd: setup.repo, words, options: { '--no-open': true, '--no-wait': true, ...options } }, ports);
  return { code, out: ports.stdout.text, err: ports.stderr.text };
}

test('product Try uploads one map and merged world through the ordinary scenario without source writes', async t => {
  const setup = coffee(t), fake = await fakeRuntime(t, trying);
  const result = await open(setup, fake, { '--product': true });
  assert.equal(result.code, 0, result.err + result.out);
  assert.deepEqual(fake.posts.map(post => post.command), ['lint', 'try']);
  const post = fake.posts[1], request = post.request;
  assert.equal(request.seed, 'tests/J1.json');
  assert.equal(request.app_map, 'app/maps/product.json');
  assert.equal(request.tab, 'screen');
  assert.equal(request.source_sha256, sha(post.tar));
  const world = JSON.parse(extract(post.tar, 'contracts/product-seed.json'));
  assert.equal(world.enabled, false);
  assert.equal(Object.hasOwn(world, 'journeyOnly'), false);
  assert.equal(world.menu[0].priceCents, 450);
  const scenario = JSON.parse(extract(post.tar, request.seed));
  assert.deepEqual(scenario.initial_world, world);
  assert.deepEqual(scenario.steps, setup.scenario.steps);
  assert.deepEqual(scenario.criteria, setup.scenario.criteria);
  const map = JSON.parse(extract(post.tar, request.app_map));
  assert.deepEqual(map.screens.map(screen => screen.id), ['phone/menu', 'server/status', 'barista/board']);
  assert.equal(map.handlers[0].after.length, 2);
  assert.equal(map.handlers.find(rule => rule.screen === 'phone/menu').next.screen, 'barista/board');
  assert.equal(map.handlers.find(rule => rule.screen === 'barista/board').next.screen, 'phone/menu');
  assert.match(result.err, /up to 3 operations \(limit 40 calls per tap\)/);
  assert.equal(readFileSync(join(setup.repo, 'tests/J1.json'), 'utf8'), setup.authored);
  assert.equal(existsSync(join(setup.repo, request.app_map)), false);
  assert.equal(existsSync(join(setup.repo, 'contracts/product-seed.json')), false);
  assert.equal((await open(setup, fake, { '--product': true })).code, 0);
  assert.equal(fake.posts.length, 2);
  const changed = await open(setup, fake, { '--product': true, '--parts': 'phone' });
  assert.equal(changed.code, 4, changed.err);
  assert.equal(fake.posts.length, 2);
  assert.equal(fake.deletes.length, 0);
  const closedSubset = await open(setup, fake, { '--product': true, '--parts': 'phone,barista' });
  assert.equal(closedSubset.code, 4, closedSubset.err);
  assert.match(closedSubset.err, /setup changed/);
  assert.equal(fake.posts.length, 2);
});

test('explicit journey provides its world last and changed mode preserves an open session', async t => {
  const setup = coffee(t), fake = await fakeRuntime(t, trying);
  const result = await open(setup, fake, { '--product': true, '--journey': 'J1' });
  assert.equal(result.code, 0, result.err + result.out);
  const world = JSON.parse(extract(fake.posts[1].tar, 'contracts/product-seed.json'));
  assert.equal(world.enabled, false);
  assert.equal(world.journeyOnly, true);
  assert.equal(world.menu[0].priceCents, 999);
  const standalone = await open(setup, fake, {}, ['tests/J1.json']);
  assert.equal(standalone.code, 4, standalone.err);
  assert.equal(fake.posts.length, 2);
});

test('product option errors and ambiguous skeletons refuse before sign-in or upload', async t => {
  const setup = coffee(t), fake = await fakeRuntime(t, trying);
  assert.equal((await open(setup, fake, { '--parts': 'phone' })).code, 2);
  const second = { ...setup.scenario, story_path: 'user_stories/journeys/J2-other.md' };
  writeFileSync(join(setup.repo, 'tests/J2.json'), JSON.stringify(second));
  writeFileSync(join(setup.repo, second.story_path), readFileSync(join(setup.repo, setup.scenario.story_path)));
  assert.equal((await open(setup, fake, { '--product': true })).code, 2);
  assert.equal(fake.posts.length, 0);
  assert.equal(fake.gets.length, 0);
});
