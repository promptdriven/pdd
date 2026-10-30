import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { composeProductTry } from '../src/product-composition.mjs';
import { checkInput } from '../src/runtime-preflight.mjs';
import { isJsonNumber, jsonNumberIdentity, parseJsonValue, stringifyJsonValue } from '../src/contract-refs.mjs';

function fixture() {
  const files = structuredClone(JSON.parse(readFileSync(new URL('./runtime/product-compose-try.json', import.meta.url))).initial_world.files);
  const reads = [], stats = [];
  return { files, reads, stats, compose(input = {}) { return composeProductTry({ root: '/project', ...input }, { readFile(path) {
    reads.push(path);
    if (!Object.hasOwn(files, path)) throw Object.assign(Error('missing'), { code: 'ENOENT' });
    return files[path].content;
  }, statFile(path) { stats.push(path); const file = files[path]; return { exists: !!file, is_symlink: file?.is_symlink ?? false, size: file ? Buffer.byteLength(file.content) : 0 }; } }); },
  editMap(part, edit) { const file = files[`/project/app/maps/${part}.json`], map = JSON.parse(file.content); edit(map); file.content = JSON.stringify(map); },
  put(path, value) { files[`/project/${path}`] = { content: typeof value === 'string' ? value : JSON.stringify(value), is_symlink: false }; } };
}
const readMap = result => JSON.parse(result.files[0].content);
const pointer = (value, path) => path.slice(1).split('/').reduce((item, token) => item[token.replace(/~1/g, '/').replace(/~0/g, '~')], value);
const resolveTemplate = (value, context) => value && typeof value === 'object' ? Object.hasOwn(value, '$ref') ? pointer(context, value.$ref)
  : Object.fromEntries(Object.entries(value).map(([key, child]) => [key, resolveTemplate(child, context)])) : value;

test('lossless shared JSON facilities preserve numeric atoms and own keys', () => {
  const text = '{"__proto__":{"constructor":9007199254740993},"decimals":[1.2300,1e400,-0]}';
  const value = parseJsonValue(text);
  assert.ok(Object.hasOwn(value, '__proto__'));
  assert.equal(Object.getPrototypeOf(value), Object.prototype);
  assert.equal(isJsonNumber(value.__proto__.constructor), true);
  assert.equal(Object.isFrozen(value.__proto__.constructor), true);
  assert.equal(isJsonNumber({ text: '4' }), false);
  assert.equal(stringifyJsonValue(value), text);
  assert.throws(() => parseJsonValue('{'), SyntaxError);
  assert.equal(jsonNumberIdentity(parseJsonValue('1.00e3')), jsonNumberIdentity(1000));
  assert.equal(jsonNumberIdentity(parseJsonValue('-0.000')), jsonNumberIdentity(-0));
  assert.notEqual(jsonNumberIdentity(parseJsonValue('9007199254740993')), jsonNumberIdentity(parseJsonValue('9007199254740992')));
  for (const value of [null, true, '1', {}, NaN, Infinity]) assert.throws(() => jsonNumberIdentity(value), TypeError);
});

test('joined map preserves separate state and typed scratch through replacement', () => {
  const f = fixture(), result = f.compose(), map = readMap(result);
  const phone = map.handlers.find(rule => rule.screen === 'phone/menu');
  assert.equal(map.handlers.some(rule => rule.screen === '*'), false);
  assert.deepEqual(Object.keys(map.screens[0]).sort(), ['format', 'id', 'input', 'operation', 'prompt_path', 'result_pointer', 'source']);
  const state = { phone: { selected: 'latte' }, barista: { selected: 'espresso' }, product_after: { 0: { forwarded: 2 } } };
  assert.deepEqual(resolveTemplate(phone.state, { state }), state);
  assert.equal(phone.after[0].bind, '/product_after/0');
  assert.equal(phone.next.screen, 'phone/menu');
  assert.deepEqual(checkInput(map.initial_state, map.state_schema, 0).refusals, []);
});

test('scratch namespace avoids actual part names and retains __proto__ state as data', () => {
  const f = fixture();
  const names = ['product_after', 'product_after_', '__proto__'];
  f.put('product/map.md', '# Demo: map\nSize: medium\n## Parts\n| Part | Folder | What it is |\n|---|---|---|\n' + names.map(name => `| ${name} | prompts/${name} | Part |`).join('\n') + '\n## Stories\n| Id | Part | Story | Tag |\n|---|---|---|---|\n| P01 | product_after | Menu | CORE |\n');
  f.files['/project/product/plan.md'].content = f.files['/project/product/plan.md'].content.replace('| phone-1 | phone |', '| phone-1 | product_after |');
  for (const name of names) f.put(`app/maps/${name}.json`, f.files['/project/app/maps/phone.json'].content);
  const map = readMap(f.compose());
  assert.equal(Object.hasOwn(map.initial_state, '__proto__'), true);
  assert.deepEqual(map.initial_state.__proto__, { selected: 'latte' });
  assert.deepEqual(map.initial_state.product_after, { selected: 'latte' });
  assert.equal(map.handlers[0].after[0].bind, '/product_after__/0');
});

test('part contributions conflict even without a world writer and preserve overrides otherwise', () => {
  const f = fixture();
  f.put('prompts/phone/seed.json', { enabled: false });
  assert.equal(JSON.parse(f.compose().files[1].content).enabled, false);
  f.put('prompts/barista/seed.json', { enabled: false });
  assert.throws(() => f.compose(), error => error.code === 'world-writer-conflict' && /enabled/.test(error.message) && /phone/.test(error.message) && /barista/.test(error.message));
  f.put('prompts/barista/seed.json', { orders: [] });
  assert.throws(() => f.compose(), error => error.code === 'world-writer-conflict' && /orders/.test(error.message));
});

test('optional seed absence is observed by stat without a missing read; symlinks still refuse', () => {
  const f = fixture(); f.compose();
  assert.ok(f.stats.includes('/project/prompts/phone/seed.json'));
  assert.equal(f.reads.includes('/project/prompts/phone/seed.json'), false);
  f.put('prompts/phone/seed.json', '{}');
  f.files['/project/prompts/phone/seed.json'].is_symlink = true;
  assert.throws(() => f.compose(), error => error.exitCode === 4 && /symbolic links/.test(error.message));
  assert.equal(f.reads.includes('/project/prompts/phone/seed.json'), false);
});

test('journey set applies after parts while its alternate standalone seed is validated', () => {
  const f = fixture();
  f.put('prompts/phone/seed.json', { enabled: false });
  f.put('contracts/alternate.json', { enabled: true, orders: [] });
  f.put('test/J1.json', { story_path: 'user_stories/journeys/J1-order.md', initial_world: { $seed: 'contracts/alternate.json', set: { '/orders': [{ id: 'chosen' }] } } });
  const world = JSON.parse(f.compose({ journey: 'J1', testPath: 'test/J1.json' }).files[1].content);
  assert.equal(world.enabled, false);
  assert.deepEqual(world.orders, [{ id: 'chosen' }]);
  delete f.files['/project/contracts/alternate.json'];
  assert.throws(() => f.compose({ journey: 'J1', testPath: 'test/J1.json' }), error => error.code === 'contract-missing');
  f.put('test/J1.json', { story_path: 'user_stories/journeys/J10-order.md', initial_world: {} });
  assert.throws(() => f.compose({ journey: 'J1', testPath: 'test/J1.json' }), error => error.code === 'invalid-journey');
});

test('existing after bindings and nullable complete results retain their types and the eight-step limit', () => {
  const f = fixture();
  f.editMap('phone', map => {
    map.initial_state.buffer = null;
    map.state_schema.properties.buffer = { oneOf: [{ type: 'null' }, { type: 'object', properties: { forwarded: { type: 'integer' } }, required: ['forwarded'], additionalProperties: false }] };
    map.state_schema.required.push('buffer');
    map.handlers[0].after = [{ handler: { prompt_path: 'prompts/server.prompt.md', operation: 'forward' }, input: {}, bind: '/buffer' }];
  });
  const result = f.compose(), map = readMap(result);
  assert.equal(result.tapOperations, 3);
  assert.equal(map.handlers[0].after[0].bind, '/phone/buffer');
  assert.equal(map.handlers[0].after[1].bind, '/product_after/0');
  f.editMap('phone', map => { map.handlers[0].after = Array.from({ length: 8 }, () => map.handlers[0].after[0]); });
  assert.throws(() => f.compose(), error => error.code === 'invalid-product-map' && /limit is 8/.test(error.message));
});

test('wildcard priority preserves covered and identical rules and refuses unrepresentable overlap', () => {
  const f = fixture();
  f.editMap('phone', map => {
    const exact = structuredClone(map.handlers[0]); exact.screen = 'menu'; exact.handler.operation = 'render'; exact.input = {};
    map.handlers.push(exact);
  });
  assert.equal(readMap(f.compose()).handlers.find(rule => rule.screen === 'phone/menu').handler.operation, 'render');
  const same = fixture();
  same.editMap('phone', map => { const exact = structuredClone(map.handlers[0]); exact.screen = 'menu'; exact.match.name = 'primary'; map.handlers.push(exact); });
  assert.equal(readMap(same.compose()).handlers.filter(rule => rule.screen === 'phone/menu').length, 1);
  f.editMap('phone', map => { map.handlers[1].match = { name: 'primary' }; });
  assert.throws(() => f.compose(), error => error.code === 'invalid-product-map' && /wildcard priority/.test(error.message));
});

test('matcher priority uses exact numeric identity and Python Boolean/number equality recursively', () => {
  for (const [wildcard, exact] of [['1', '1.0'], ['true', '1'], ['false', '-0'], ['[true,{"x":1,"y":2}]', '[1,{"y":2.0,"x":1.00}]']]) {
    const f = fixture();
    f.editMap('phone', map => {
      map.handlers[0].match = { value: 'WILDCARD_VALUE' };
      const direct = structuredClone(map.handlers[0]); direct.screen = 'menu'; direct.match.value = 'EXACT_VALUE';
      direct.handler.operation = 'render'; direct.input = {}; map.handlers.push(direct);
    });
    const file = f.files['/project/app/maps/phone.json'];
    file.content = file.content.replace('"WILDCARD_VALUE"', wildcard).replace('"EXACT_VALUE"', exact);
    const handlers = readMap(f.compose()).handlers.filter(rule => rule.screen === 'phone/menu');
    assert.equal(handlers.length, 1, `${wildcard}/${exact}`);
    assert.equal(handlers[0].handler.operation, 'render');
  }
});

test('next-screen resolution prefers a literal local slash ID, then selected qualified targets', () => {
  const f = fixture();
  f.editMap('phone', map => { map.handlers[0].next.screen = 'barista/menu'; });
  f.editMap('barista', map => { map.handlers[0].next.screen = 'phone/menu'; });
  const map = readMap(f.compose());
  assert.equal(map.handlers.find(rule => rule.screen === 'phone/menu').next.screen, 'barista/menu');
  assert.equal(map.handlers.find(rule => rule.screen === 'barista/menu').next.screen, 'phone/menu');
  assert.throws(() => f.compose({ parts: ['phone'] }), error => error.code === 'invalid-product-map' && /barista\/menu/.test(error.message));
  f.editMap('phone', map => { map.screens.push({ ...map.screens[0], id: 'barista/menu' }); });
  assert.equal(readMap(f.compose()).handlers.find(rule => rule.screen === 'phone/menu').next.screen, 'phone/barista/menu');
  assert.equal(readMap(f.compose({ parts: ['phone'] })).handlers[0].next.screen, 'phone/barista/menu');
  f.editMap('phone', map => { map.handlers[0].next.screen = 'missing/counter'; });
  assert.throws(() => f.compose(), error => error.code === 'invalid-product-map' && /missing\/counter/.test(error.message));
});


test('missing or malformed required map fields fail finitely before JSON serialization', () => {
  const fields = ['schema_version', 'name', 'initial_screen', 'initial_route', 'initial_state', 'state_schema', 'synthetic', 'screens', 'router', 'routes', 'handlers', 'stylesheets'];
  for (const field of fields) {
    const f = fixture(); f.editMap('phone', map => { delete map[field]; });
    assert.throws(() => f.compose({ parts: ['phone'] }), error => error.code === 'invalid-product-map', field);
  }
  for (const [field, value] of [['router', 7], ['initial_route', {}], ['synthetic', null], ['name', ''], ['screens', null], ['initial_state', []]]) {
    const f = fixture(); f.editMap('phone', map => { map[field] = value; });
    assert.throws(() => f.compose({ parts: ['phone'] }), error => error.code === 'invalid-product-map', field);
  }
});

test('generated artifact names use the first absent pair and preserve stat refusals', () => {
  const f = fixture();
  f.put('app/maps/product.json', '{"authored":true}');
  f.put('contracts/product-seed_1.json', '{"authored":true}');
  const result = f.compose();
  assert.equal(result.appMapPath, 'app/maps/product_2.json');
  assert.equal(result.seedPath, 'contracts/product-seed_2.json');
  assert.equal(f.files['/project/app/maps/product.json'].content, '{"authored":true}');
  assert.equal(f.files['/project/contracts/product-seed_1.json'].content, '{"authored":true}');
  const unsafe = fixture();
  unsafe.files['/project/contracts/product-seed.json'] = { content: '{}', is_symlink: true };
  assert.throws(() => unsafe.compose(), error => error.exitCode === 4 && /symbolic links/.test(error.message));
});

test('nested required fields cannot introduce undefined into composed JSON', () => {
  for (const field of ['screen', 'kind', 'match', 'handler', 'input', 'next', 'state']) {
    const f = fixture(); f.editMap('phone', map => { delete map.handlers[0][field]; });
    assert.throws(() => f.compose(), error => error.code === 'invalid-product-map' && error.message.includes(field));
  }
  for (const field of ['handler', 'input', 'result_pointer']) {
    const f = fixture(); f.editMap('phone', map => { map.router = { handler: {}, input: {}, result_pointer: null }; delete map.router[field]; });
    assert.throws(() => f.compose(), error => error.code === 'invalid-product-map' && error.message.includes(field));
  }
});
