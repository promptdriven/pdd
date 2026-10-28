import test from 'node:test';
import assert from 'node:assert/strict';
import { request } from 'node:http';
import { openServe } from '../src/try-http.mjs';
const raw = (port, path, method = 'GET', body = '', headers = {}) => new Promise((resolve, reject) => {
  const req = request({ hostname: '127.0.0.1', port, path, method, headers }, res => {
    const chunks = []; res.on('data', b => chunks.push(b)); res.on('end', () => resolve({ status: res.statusCode, headers: res.headers, body: Buffer.concat(chunks).toString() }));
  }); req.on('error', reject); req.end(body);
});
async function screen(work, model = { app_map: true, entries: [] }) {
  const calls = [], ports = { stdout: { write() {} }, serve: async server => work(server.address().port, calls) };
  const context = { ports, origin: 'http://runtime.test', root: '/tmp', identity: { login: 'owner' }, runtime: { send: async (path, init) => {
    calls.push({ path, ...init });
    if (path.endsWith('/model')) return { status: 200, json: model };
    const text = path.endsWith('/index.html') ? '<!doctype html><title>Actual Screen</title>' : '{"accepted":true}';
    return { status: init.method === 'POST' ? 202 : 200, text, headers: new Headers({ 'content-type': path.endsWith('.html') ? 'text/html' : 'application/json', 'set-cookie': 'private=no', 'access-control-allow-origin': '*' }) };
  } } };
  return openServe(context, {}, 'pinned-session', { '--serve': '0' });
}

test('Screen: app-map-only Story serves root and trusted assets; browser receives no upstream cookie/CORS', async () => {
  await screen(async (port, calls) => {
    const root = await raw(port, '/'); assert.equal(root.status, 200); assert.match(root.body, /Actual Screen/);
    assert.match(root.headers['content-security-policy'], /script-src 'self'/);
    assert.equal(root.headers['cache-control'], 'no-store'); assert.equal(root.headers['set-cookie'], undefined);
    assert.equal(root.headers['access-control-allow-origin'], undefined);
    assert.equal((await raw(port, '/', 'HEAD')).body, '');
    assert.equal((await raw(port, '/__pdd/screen/try-frame.js')).status, 200);
    assert.equal(calls.filter(c => c.method === 'POST').length, 0);
    assert.equal((await raw(port, '/missing')).status, 404);
  });
});

test('Screen: only pinned allowlisted resources and action bodies forward, origin checks run first', async () => {
  await screen(async (port, calls) => {
    for (const path of ['/__pdd/screen/dev/', '/__pdd/screen/api/save', '/__pdd/screen/app-asset/../../secret', '/__pdd/screen/api/state?url=http://evil']) assert.equal((await raw(port, path)).status, 404);
    for (const headers of [{ origin: 'https://evil.example' }, { host: 'evil.example' }, { 'sec-fetch-site': 'cross-site' }]) assert.equal((await raw(port, '/__pdd/screen/api/act', 'POST', '{}', headers)).status, 403);
    assert.equal(calls.length, 1);
    const body = '{"action_id":"saved-id","event":{"kind":"button","target":"unread"}}';
    const posted = await raw(port, '/__pdd/screen/api/act', 'POST', body, { authorization: 'Bearer browser-ignored', cookie: 'browser-ignored', 'content-type': 'application/json' });
    assert.equal(posted.status, 202);
    const call = calls.at(-1); assert.equal(call.path, '/v1/try/pinned-session/screen/api/act'); assert.equal(call.body, body);
    assert.equal(call.headers.Authorization, undefined); assert.equal(call.headers.Cookie, undefined);
    assert.equal((await raw(port, '/__pdd/screen/api/action?id=saved-id')).status, 200);
  });
});

test('Screen: reserved routes refuse ambiguity before opening a listener', async () => {
  for (const path of ['/', '/__pdd/screen/api/act']) {
    await assert.rejects(screen(() => assert.fail('must not listen'), { app_map: true, entries: [{ http: { method: 'GET', path } }] }), /reserved|conflict/i);
  }
});
