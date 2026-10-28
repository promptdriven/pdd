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
    const view = { ...f.job(entry.json.requestId, 'call', 'passed', { program_result: program, report: { result: program } }), session_id: 'session' };
    f.jobs.set(entry.json.requestId, view);
    return { status: 200, json: view };
  });
  const ports = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state }, extra).ports;
  ports.serve = async server => work(server.address().port, seen, ports);
  const context = { root: setup.repo, ports, store: { dir: setup.state }, identity: { login: 'octo' }, origin: fake.origin,
    runtime: { send: async () => ({ status: 200, json: { entries, app_map: extra.appMap ?? false } }) } };
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
