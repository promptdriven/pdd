import test from 'node:test';
import assert from 'node:assert/strict';
import { request } from 'node:http';
import { openServe } from '../src/try-http.mjs';
import { fakeRuntime, harbor, portsFor, PLACE } from './runtime-fake.mjs';

const object = properties => ({ type: 'object', properties, required: [], additionalProperties: false });
const route = (method, path, properties = {}) => ({ entry_path: PLACE, operation: 'main', http: { method, path }, input_schema: object(properties) });
const raw = (port, path, headers = {}, method = 'GET', body = '') => new Promise((done, reject) => {
  const req = request({ hostname: '127.0.0.1', port, path, headers, method }, res => {
    const parts = []; res.on('data', part => parts.push(part)); res.on('end', () => done({ status: res.statusCode, headers: res.headers, body: Buffer.concat(parts).toString() }));
  }); req.on('error', reject); req.end(body);
});
async function serving(t, entries, result, work, extra = {}) {
  const setup = harbor(t), seen = [];
  const fake = await fakeRuntime(t, (entry, f) => {
    if (!entry.json) return { status: 200, json: f.jobs.get(entry.url.split('/').at(-1)) };
    seen.push(entry.json);
    const program = typeof result === 'function' ? result(entry.json.input) : result;
    const view = { ...f.job(entry.json.requestId, 'call', 'passed', { program_result: program, report: { result: program, remaining_calls: extra.callUsage?.remaining } }), session_id: 'session' };
    if (extra.callUsage) view.usage.calls = extra.callUsage.calls;
    f.jobs.set(entry.json.requestId, view);
    return { status: 200, json: view };
  });
  const ports = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state }, extra).ports;
  ports.serve = async server => { const address = server.address(); if (extra.advertisedPort) server.address = () => ({ ...address, port: extra.advertisedPort }); return work(address.port, seen, ports); };
  const context = { root: setup.repo, ports, store: { dir: setup.state }, identity: { login: 'octo' }, origin: fake.origin,
    runtime: { send: async () => ({ status: 200, json: { entries, app_map: extra.appMap ?? false, calls: extra.modelCalls } }) } };
  assert.equal(await openServe(context, {}, 'session', { '--serve': '0' }), 0);
  return { seen, ports };
}

test('HTTP door: named GET and 404, query input and status-plus-data JSON output', async t => {
  await serving(t, [route('GET', '/api/books', { read: { type: 'string' } })], { status: 200, books: [{ title: 'Dune' }] }, async (port, seen) => {
    const ok = await raw(port, '/api/books?read=false');
    assert.equal(ok.status, 200); assert.deepEqual(JSON.parse(ok.body), { books: [{ title: 'Dune' }] });
    assert.deepEqual(seen[0].input, { read: 'false' });
    assert.equal((await raw(port, '/missing')).status, 404);
    assert.equal((await raw(port, '/api/books', {}, 'POST')).status, 404);
    assert.equal(seen.length, 1);
  });
});

test('HTTP door: route parameters, JSON body, raw body, custom status/headers and HEAD', async t => {
  const entries = [route('POST', '/books/:id', { id: { type: 'string' }, body: object({ title: { type: 'string' } }) }), route('GET', '/health')];
  await serving(t, entries, { status: 201, headers: { 'x-program': 'kept', 'content-length': '999', connection: 'keep-alive' }, body: 'created\n' }, async (port, seen) => {
    const created = await raw(port, '/books/a%20b', { 'content-type': 'application/json' }, 'POST', '{"title":"Dune"}');
    assert.equal(created.status, 201); assert.equal(created.body, 'created\n'); assert.equal(created.headers['x-program'], 'kept');
    assert.equal(created.headers['content-length'], '8');
    assert.deepEqual(seen[0].input, { id: 'a b', body: { title: 'Dune' } });
    assert.equal((await raw(port, '/health', {}, 'HEAD')).body, '');
  });
});

test('HTTP door: remote origins, rebinding Hosts and bad/duplicate query values spend no calls', async t => {
  await serving(t, [route('GET', '/books', { read: { type: 'boolean' } })], { status: 200, body: [] }, async (port, seen) => {
    for (const headers of [{ origin: 'https://evil.example' }, { host: 'evil.example' }, { 'sec-fetch-site': 'cross-site' }]) assert.equal((await raw(port, '/books', headers)).status, 403);
    for (const path of ['/books?read=perhaps', '/books?read=true&read=false', '/books?other=x']) assert.equal((await raw(port, path)).status, 400);
    assert.equal(seen.length, 0);
    assert.equal((await raw(port, '/books?read=false')).status, 200);
    assert.deepEqual(seen[0].input, { read: false });
  });
});

test('HTTP door: malformed program response becomes 502 with plain reason', async t => {
  await serving(t, [route('GET', '/books')], { status: 999, body: 'bad' }, async port => {
    const bad = await raw(port, '/books'); assert.equal(bad.status, 502); assert.match(bad.body, /^pdd try:/);
  });
});

test('HTTP door: HEAD fallback supplies GET to a constrained request-shaped entry', async t => {
  await serving(t, [route('GET', '/health', { method: { type: 'string', const: 'GET' } })], { status: 200, body: 'healthy' }, async (port, seen) => {
    const response = await raw(port, '/health', {}, 'HEAD');
    assert.equal(response.status, 200); assert.equal(response.body, '');
    assert.equal(seen[0].input.method, 'GET');
  });
});


test('HTTP door with Screen: named API works through fetch/curl, never through model resource loads', async t => {
  await serving(t, [route('GET', '/api/books')], { status: 200, books: [] }, async (port, seen) => {
    for (const dest of ['image', 'style', 'script', 'iframe', 'document']) assert.equal((await raw(port, '/api/books', { 'sec-fetch-dest': dest })).status, 403);
    assert.equal(seen.length, 0);
    assert.equal((await raw(port, '/api/books', { 'sec-fetch-dest': 'empty' })).status, 200);
    assert.equal(seen.length, 1);
  }, { appMap: true });
});


test('RELEASE7: port80 accepts default-port Host/Origin and still rejects cross-origin requests', async t => {
  await serving(t, [route('GET','/health')], {status:200,body:'healthy'}, async (port,seen) => {
    for (const host of ['127.0.0.1','localhost','127.0.0.1:80','localhost:80']) {
      assert.equal((await raw(port,'/health',{host,origin:'http://'+host})).status,200,host);
    }
    for (const headers of [{host:'evil.example'},{host:'127.0.0.1',origin:'http://evil.example'},{host:'127.0.0.1:81'}]) assert.equal((await raw(port,'/health',headers)).status,403);
    assert.equal(seen.length,4);
  }, {advertisedPort:80});
});


test('hcli-4: HTTP usage headers preserve program status/body and expose local zero-call errors', async t => {
  await serving(t, [route('GET', '/books')], { status: 201, headers: { 'x-program': 'kept', 'x-pdd-ai-calls': '999' }, body: 'program bytes\n' }, async (port, seen, ports) => {
    assert.match(ports.stderr.text, /Try AI usage:.*0 used.*40 remaining.*cap 40/);
    const result = await raw(port, '/books');
    assert.equal(result.status, 201); assert.equal(result.body, 'program bytes\n'); assert.equal(result.headers['x-program'], 'kept');
    assert.equal(result.headers['x-pdd-ai-calls'], '2'); assert.equal(result.headers['x-pdd-try-used'], '2');
    assert.equal(result.headers['x-pdd-try-remaining'], '38'); assert.equal(result.headers['x-pdd-try-cap'], '40');
    const miss = await raw(port, '/absent'); assert.equal(miss.status, 404); assert.equal(miss.headers['x-pdd-ai-calls'], '0');
    assert.equal(miss.headers['x-pdd-try-remaining'], '38'); assert.equal(miss.headers['x-pdd-usage-source'], 'last-known');
    assert.equal(seen.length, 1);
  }, { modelCalls: { cap: 40, remaining: 40 }, callUsage: { calls: 2, remaining: 38 } });
});

test('hcli-4: missing or malformed usage remains unknown, including a real zero remaining allowance', async () => {
  const { tryUsage, tryUsageHeaders } = await import('../src/runtime-output.mjs');
  assert.equal(typeof tryUsage, 'function');
  assert.deepEqual(tryUsage({}), { calls: 'unknown', remaining: 'unknown', cap: 'unknown', used: 'unknown' });
  assert.equal(tryUsageHeaders(tryUsage({ usage: { calls: '2' }, result: { report: { remaining_calls: -1 } } }))['x-pdd-ai-calls'], 'unknown');
  assert.deepEqual(tryUsage({ usage: { calls: 2 }, result: { report: { remaining_calls: 0 } } }, { cap: 40 }), { calls: 2, remaining: 0, cap: 40, used: 40 });
});
