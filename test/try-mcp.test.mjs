import test from 'node:test';
import assert from 'node:assert/strict';
import { PassThrough } from 'node:stream';
import { createTryTools, runMcp } from '../src/try-mcp.mjs';

function fixture(overrides = {}) {
  const scenario = { criteria: [{ id: 'AC1', text: 'Adds bookmark' }], initial_world: { kv: {} }, steps: [{ step_id: 'add', entry_path: 'prompts/bm.prompt.md', operation: 'main', input: { argv: ['add', 'news'] }, checks: [{ criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', value: 'Added\n' }] }] };
  const owner = { root: '/project', test: { path: 'tests/add.json', storyPath: 'user_stories/add.md', title: 'Add', doc: scenario }, record: { id: 'try-1', origin: 'https://example.com', login: 'owner' }, model: { entries: [{ entry_path: 'prompts/bm.prompt.md', operation: 'main', cli: true, input_schema: { type: 'object' } }], calls: { cap: 400, remaining: 399 } }, data: { kv: { bookmarks: ['real current data'] } } };
  let calls = 0, saves = 0;
  return { owner, get calls() { return calls; }, get saves() { return saves; }, ports: {
    readTryOwner: async () => owner,
    runDoorCall: async (descriptor, input) => { calls++; assert.deepEqual(input, { argv: ['add', 'news'] }); return { id: `run-${calls}`, result: { stdout: 'Added\n' }, inputWorld: { kv: {} }, world: { kv: { bookmarks: ['news'] } } }; },
    saveDoorCase: (root, saved) => { saves++; assert.equal(saved.original_path, 'tests/add.json'); assert.equal(saved.test.steps[0].checks[0].value.stdout, 'Added\n'); return 'added to tests/add.json as step try-run-1'; }, ...overrides,
  } };
}

test('state uses current owner world, run preserves snapshots, check and save use confirmed evidence', async () => {
  const f = fixture(), tools = createTryTools({}, f.ports);
  const state = await tools.call('try_state');
  assert.deepEqual(state.data_now, f.owner.data);
  assert.equal(state.entries[0].entry, 'prompts/bm.prompt.md#main');
  const run = await tools.call('try_run', { argv: ['add', 'news'] });
  assert.deepEqual(run.data_before, { kv: {} });
  assert.deepEqual(run.data_after, { kv: { bookmarks: ['news'] } });
  assert.equal((await tools.call('try_check')).verdict.state, 'pass');
  assert.match((await tools.call('try_save_case')).result, /^added /);
  assert.equal((await tools.call('try_save_case')).already_saved, true);
  assert.equal(f.saves, 1); assert.equal(f.calls, 1);
});

test('validation and ambiguous save criterion send no accidental door call', async () => {
  const f = fixture(), tools = createTryTools({}, f.ports);
  for (const args of [{}, { argv: [2] }, { argv: [], input: {} }, { entry: 'unknown#entry', input: {} }, { argv: [], extra: true }]) await assert.rejects(tools.call('try_run', args));
  assert.equal(f.calls, 0);
  await assert.rejects(tools.call('try_save_case'), /confirmed run/);
});

test('unavailable world stays unavailable and uncertain run blocks a later mutation', async () => {
  const f = fixture({ runDoorCall: async () => { throw Object.assign(new Error('The command result is unknown. Do not repeat it automatically.'), { unknownOutcome: true }); } });
  delete f.owner.data; f.owner.data_error = 'Current saved data unavailable (HTTP 404)';
  const tools = createTryTools({}, f.ports);
  const state = await tools.call('try_state'); assert.equal(state.data_now, null); assert.match(state.data_error, /unavailable/);
  await assert.rejects(tools.call('try_run', { argv: [] }), /unknown/);
  await assert.rejects(tools.call('try_run', { argv: [] }), /prior run/);
});

test('concurrent tool calls are serialized', async () => {
  let active = 0, max = 0;
  const f = fixture({ readTryOwner: async () => { active++; max = Math.max(max, active); await new Promise(resolve => setTimeout(resolve, 5)); active--; return f.owner; } });
  const tools = createTryTools({}, f.ports);
  await Promise.all([tools.call('try_state'), tools.call('try_open')]);
  assert.equal(max, 1);
});

async function exchange(messages, ports = {}) {
  const stdin = new PassThrough(), stdout = new PassThrough(), stderr = new PassThrough();
  let output = ''; stdout.on('data', data => output += data);
  const promise = runMcp({}, { stdin, stdout, stderr, ...ports });
  stdin.end(messages.map(message => typeof message === 'string' ? message : JSON.stringify(message)).join('\n') + '\n');
  assert.equal(await promise, 0);
  return output.trim().split('\n').map(line => JSON.parse(line));
}
const request = (id, method, params) => ({ jsonrpc: '2.0', id, method, ...(params === undefined ? {} : { params }) });

test('stdio serves MCP negotiation and errors with stdout exclusively JSON', async () => {
  const rows = await exchange(['{', [], { jsonrpc: '2.0', id: {}, method: 'ping' }, request(1, 'initialize', { protocolVersion: 'future', capabilities: {}, clientInfo: { name: 'test', version: '1' } }), request(2, 'tools/list'), request(3, 'nope'), request(4, 'tools/call', {}), { jsonrpc: '2.0', method: 'notifications/initialized' }]);
  assert.equal(rows.filter(row => row.error?.code === -32700).length, 1);
  assert.equal(rows.filter(row => row.error?.code === -32600).length, 2);
  assert.equal(rows.find(row => row.id === 1).result.protocolVersion, '2025-06-18');
  assert.deepEqual(rows.find(row => row.id === 2).result.tools.map(tool => tool.name), ['try_open', 'try_state', 'try_run', 'try_check', 'try_save_case']);
  assert.equal(rows.find(row => row.id === 3).error.code, -32601);
  assert.equal(rows.find(row => row.id === 4).error.code, -32602);
});

test('duplicate request reuses pending answer and conflicting ID cannot dispatch', async () => {
  const f = fixture();
  const call = request(7, 'tools/call', { name: 'try_run', arguments: { argv: ['add', 'news'] } });
  const rows = await exchange([call, call, request(7, 'ping')], f.ports);
  assert.equal(f.calls, 1);
  assert.equal(rows.filter(row => row.result?.structuredContent?.run_id === 'run-1').length, 2);
  assert.equal(rows.filter(row => row.error?.code === -32600).length, 1);
});

test('tool errors are MCP tool results and valid notifications cannot run actions', async () => {
  const f = fixture();
  const rows = await exchange([{ jsonrpc: '2.0', method: 'tools/call', params: { name: 'try_run', arguments: { argv: ['add', 'news'] } } }, request(1, 'tools/call', { name: 'try_run', arguments: {} }), request(2, 'ping')], f.ports);
  assert.equal(f.calls, 0);
  assert.equal(rows.find(row => row.id === 1).result.isError, true);
  assert.deepEqual(rows.find(row => row.id === 2).result, {});
});

test('owner access opens exactly once and reads real current state with authenticated requests', async t => {
  const { harbor, fakeRuntime, portsFor } = await import('./runtime-fake.mjs');
  const { readTryOwner } = await import('../src/runtime-client.mjs');
  const { rmSync } = await import('node:fs');
  const { join } = await import('node:path');
  const setup = harbor(t, root => rmSync(join(root, 'tests/unknown-item.json')));
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.url.endsWith('/model')) return { status: 200, json: { entries: [], calls: { cap: 400, remaining: 397 } } };
    if (entry.url.endsWith('/state')) return { status: 200, json: { world: { kv: { live: 'actual' } }, actions: [{ id: 'page-run' }] } };
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.command === 'try') return { status: 200, json: f.tryJob(entry.request.requestId) };
    return { status: 200, json: f.tryJob(entry.url.split('/').at(-1)) };
  });
  const { ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  const first = await readTryOwner({ cwd: setup.repo }, ports);
  assert.deepEqual(first.data, { kv: { live: 'actual' } });
  assert.deepEqual(first.actions, [{ id: 'page-run' }]);
  const { readFileSync, writeFileSync } = await import('node:fs');
  writeFileSync(join(setup.repo, 'tests/recorded.json'), readFileSync(join(setup.repo, 'tests/place-order.json')));
  const again = await readTryOwner({ cwd: setup.repo, story: 'place-order' }, ports);
  assert.equal(again.test.path, 'tests/place-order.json');
  assert.equal(fake.posts.filter(p => p.command === 'try').length, 1);
});

test('isolated save retains actual starting world and leaves original scenario bytes intact', async t => {
  const { harbor } = await import('./runtime-fake.mjs');
  const { saveDoorCase } = await import('../src/runtime-client.mjs');
  const { readFileSync, readdirSync } = await import('node:fs');
  const { join } = await import('node:path');
  const setup = harbor(t), path = 'tests/place-order.json', original = readFileSync(join(setup.repo, path), 'utf8'), doc = JSON.parse(original);
  const saved = { id: 'confirmed-run', original_path: path, story_path: doc.story_path, test: { ...doc, initial_world: { kv: { exact: ['snapshot'] } }, steps: [{ ...doc.steps[0], step_id: 'recorded' }] } };
  const answer = saveDoorCase(setup.repo, saved, { isolated: true });
  assert.match(answer, /^added to tests\/place-order-try-confirmed-run.json/);
  assert.equal(readFileSync(join(setup.repo, path), 'utf8'), original);
  const record = JSON.parse(readFileSync(join(setup.repo, 'tests/place-order-try-confirmed-run.json'), 'utf8'));
  assert.deepEqual(record.initial_world, { kv: { exact: ['snapshot'] } });
  assert.deepEqual(record.simulation, doc.simulation);
  assert.equal(record.steps.length, 1);
  assert.match(saveDoorCase(setup.repo, saved, { isolated: true }), /^already saved /);
  assert.equal(readdirSync(join(setup.repo, 'tests')).filter(name => name.includes('try-confirmed-run')).length, 1);
  assert.match(saveDoorCase(setup.repo, { ...saved, test: { ...saved.test, initial_world: {} } }, { isolated: true }), /^not added: a different case/);
});

test('saving without a runtime before-world fails instead of inventing test data', async () => {
  const f = fixture({ runDoorCall: async () => ({ id: 'run', result: { stdout: 'Added\n' }, world: {} }) });
  const tools = createTryTools({}, f.ports);
  await tools.call('try_run', { argv: [] });
  await assert.rejects(tools.call('try_save_case'), /confirmed starting world/);
  assert.equal(f.saves, 0);
});

// A read can fail after dispatch with arbitrary server text: wording cannot prove no effect.
test('failed owner result reads block another run regardless of error wording', async t => {
  const { harbor, fakeRuntime, portsFor } = await import('./runtime-fake.mjs');
  const { runDoorCall } = await import('../src/runtime-client.mjs');
  for (const status of [401, 403, 410]) {
    const setup = harbor(t); let dispatched = 0;
    const fake = await fakeRuntime(t, (entry, server) => {
      if (entry.method === 'POST' && entry.url.endsWith('/call')) {
        dispatched++;
        return { status: 202, json: server.job(entry.json.requestId, 'call', 'running') };
      }
      return { status, json: { error: { message: 'Permission denied' } } };
    });
    const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
    const f = fixture();
    f.owner.root = setup.repo; f.owner.record.origin = fake.origin; f.owner.record.login = 'octo';
    const tools = createTryTools({}, { ...ports, readTryOwner: f.ports.readTryOwner, runDoorCall });
    await assert.rejects(tools.call('try_run', { argv: [] }), error => error.unknownOutcome === true);
    await assert.rejects(tools.call('try_run', { argv: [] }), /prior run/);
    assert.equal(dispatched, 1, `HTTP ${status} must not dispatch twice`);
  }
});

test('door snapshots use the matching immutable B1 action, never the latest world or another run', async t => {
  const { harbor, fakeRuntime, portsFor } = await import('./runtime-fake.mjs');
  const { runDoorCall } = await import('../src/runtime-client.mjs');
  for (const available of [true, false]) {
    const setup = harbor(t); let id, dispatched = 0;
    const before = { kv: { text: 'exact\n  before' } }, after = { kv: { text: 'exact\n  after' } };
    const fake = await fakeRuntime(t, (entry, server) => {
      if (entry.method === 'POST') {
        id = entry.json.requestId; dispatched++;
        return { status: 202, json: server.job(id, 'call', 'running') };
      }
      if (entry.url.endsWith('/state')) return available
        ? { status: 200, json: { world: { latest: 'another action already ran' }, actions: [
          { action_id: 'other-run', input_world: { wrong: true }, world: { wrong: true } },
          { action_id: 'internal-run', input_world: before, world: after },
        ] } }
        : { status: 503, json: { error: { message: 'State temporarily unavailable' } } };
      return { status: 200, json: server.job(id, 'call', 'passed', {
        report: { action_id: 'internal-run' }, program_result: { stdout: 'exact\n', stderr: '', exit_code: 0 },
      }) };
    });
    const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
    const answer = await runDoorCall({ root: setup.repo, origin: fake.origin, sessionId: 'try-id', login: 'octo', prompt: 'prompts/bm.prompt.md', operation: 'main' }, { argv: [] }, ports);
    assert.equal(answer.result.stdout, 'exact\n');
    assert.deepEqual(answer.inputWorld, available ? before : undefined);
    assert.deepEqual(answer.world, available ? after : undefined);
    assert.equal(dispatched, 1);
  }
});
