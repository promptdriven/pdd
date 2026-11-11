import test from 'node:test';
import assert from 'node:assert/strict';
import { composeProductTry } from '../src/product-composition.mjs';

const schema = { type: 'object', properties: {}, required: [], additionalProperties: false };
function fixture() {
  const files = new Map();
  const put = (path, value) => files.set(`/project/${path}`, typeof value === 'string' ? value : JSON.stringify(value));
  put('product/map.md', '# Shop: map\nSize: medium\n## Parts\n| Part | Folder | What it is |\n|---|---|---|\n| server | prompts/server | Processing |\n| phone | prompts/phone | Ordering |\n| barista | prompts/barista | Preparation |\n## Stories\n| Id | Part | Story | Tag |\n|---|---|---|---|\n| P01 | phone | Order | CORE |\n');
  put('product/plan.md', '# Plan\n## Runs\n| Run | Part | Slice | Stories | Needs |\n|---|---|---|---|---|\n| phone-1 | phone | core | P01 | |\n## After every tap\n1. prompts/server/server.prompt.md#forward\n');
  put('contracts/world.md', '# World\n| Key | Writer | Readers |\n|---|---|---|\n| orders | phone | server |\n| tickets | server | barista |\n');
  put('contracts/seed-world.json', { base: true });
  put('prompts/server/seed.json', { tickets: ['retained'] });
  put('prompts/phone/seed.json', { orders: [] });
  put('prompts/server/server.prompt.md', '<details><summary>Runtime interface</summary>\n```json\n' + JSON.stringify({ entries: [{ operation: 'forward', result_schema: schema }] }) + '\n```\n</details>');
  for (const part of ['phone', 'barista']) put(`app/maps/${part}.json`, {
    schema_version: 'prompt-runtime.app-map.v1', name: part, initial_screen: 'home', initial_route: null,
    initial_state: { selected: part }, state_schema: { type: 'object', properties: { selected: { type: 'string' } }, required: ['selected'], additionalProperties: false }, synthetic: false,
    screens: [{ id: 'home', prompt_path: `prompts/${part}/view.prompt.md`, operation: 'render', source: 'operation', format: 'html', input: {}, result_pointer: '/html' }],
    router: null, routes: [], stylesheets: [], handlers: [{ screen: 'home', kind: 'click', match: {}, handler: { prompt_path: `prompts/${part}/view.prompt.md`, operation: 'tap' }, input: {}, next: { kind: 'screen', screen: 'home', route_pointer: null }, state: { selected: part } }],
  });
  const compose = (input = {}, overrides = {}) => composeProductTry({ root: '/project', ...input }, {
    statFile: path => ({ exists: files.has(path), is_symlink: false }), readFile: path => { if (!files.has(path)) throw Error(`Unexpected read ${path}`); return files.get(path); }, ...overrides,
  });
  return { files, put, compose, edit(part, change) { const path = `/project/app/maps/${part}.json`, map = JSON.parse(files.get(path)); change(map); files.set(path, JSON.stringify(map)); } };
}
const mapOf = result => JSON.parse(result.files[0].content);

test('three selected parts with two maps retain server seed and chain; initial screen follows first mapped part', () => {
  const f = fixture(); let result;
  assert.doesNotThrow(() => { result = f.compose(); }, 'A selected server without screens remains a valid product part');
  const map = mapOf(result);
  assert.deepEqual(result.parts, ['server', 'phone', 'barista']);
  assert.equal(map.initial_screen, 'phone/home');
  assert.deepEqual(map.screens.map(row => row.id), ['phone/home', 'barista/home']);
  assert.deepEqual(Object.keys(map.initial_state).sort(), ['barista', 'phone', 'product_after']);
  assert.deepEqual(map.initial_state.phone, { selected: 'phone' });
  assert.deepEqual(map.initial_state.barista, { selected: 'barista' });
  for (const handler of map.handlers) {
    assert.deepEqual(handler.after[0].handler, { prompt_path: 'prompts/server/server.prompt.md', operation: 'forward' });
    assert.ok(Object.hasOwn(handler.state, 'phone') && Object.hasOwn(handler.state, 'barista') && Object.hasOwn(handler.state, 'product_after'));
  }
  assert.deepEqual(JSON.parse(result.files[1].content), { base: true, tickets: ['retained'], orders: [] });
  f.put('tests/J1.json', { story_path: 'user_stories/journeys/J1-order.md', initial_world: { $seed: 'contracts/seed-world.json', set: { '/tickets': ['journey'] } } });
  assert.deepEqual(JSON.parse(f.compose({ journey: 'J1', testPath: 'tests/J1.json' }).files[1].content).tickets, ['journey']);
});

for (const field of ['prompt_path', 'operation', 'source', 'format', 'input', 'result_pointer']) {
  test(`missing screen ${field} names the actual field`, () => {
    const f = fixture(); f.edit('phone', map => { delete map.screens[0][field]; });
    let error; try { f.compose({ parts: ['phone'] }); } catch (caught) { error = caught; }
    assert.equal(error?.code, 'invalid-product-map');
    assert.match(error.message, new RegExp(field), `Missing screen ${field} must be identified`);
  });
}

test('explicit navigation to a screenless part and an entirely screenless selection refuse finitely', () => {
  const f = fixture(); f.edit('phone', map => { map.handlers[0].next.screen = 'server/status'; });
  assert.throws(() => f.compose(), error => error.code === 'invalid-product-map' && /server\/status/.test(error.message));
  assert.throws(() => f.compose({ parts: ['server'] }), error => error.code === 'invalid-product-map' && /screen/i.test(error.message));
});

test('optional maps preserve stat and read refusals', () => {
  for (const mode of ['symlink', 'stat-denied', 'unreadable', 'unknown-stat']) {
    const f = fixture();
    const statFile = path => {
      if (path === '/project/app/maps/server.json') {
        if (mode === 'stat-denied') throw Object.assign(Error('privacy refusal'), { exitCode: 4 });
        if (mode === 'unknown-stat') return undefined;
        return { exists: true, is_symlink: mode === 'symlink' };
      }
      return { exists: f.files.has(path), is_symlink: false };
    };
    assert.throws(() => f.compose({}, { statFile, readFile: path => { if (path.endsWith('/server.json')) throw Error('permission denied'); return f.files.get(path); } }), mode);
  }
});

test('scratch namespace reserves screenless selected part names too', () => {
  const f = fixture();
  for (const path of ['/project/product/map.md', '/project/product/plan.md', '/project/contracts/world.md']) f.files.set(path, f.files.get(path).replace(/server/g, 'product_after'));
  f.files.set('/project/prompts/product_after/seed.json', f.files.get('/project/prompts/server/seed.json'));
  f.files.set('/project/prompts/product_after/product_after.prompt.md', f.files.get('/project/prompts/server/server.prompt.md'));
  const map = mapOf(f.compose());
  assert.deepEqual(Object.keys(map.initial_state).sort(), ['barista', 'phone', 'product_after_']);
  assert.equal(map.handlers[0].after[0].bind, '/product_after_/0');
});
