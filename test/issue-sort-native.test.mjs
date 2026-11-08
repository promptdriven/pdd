import test from 'node:test';
import assert from 'node:assert/strict';
import { createDependencyReadPorts } from '../src/issue-dependencies-github.mjs';
import { fixture, complete } from './helpers/issue-sort-fixture.mjs';

test('native GitHub boundary creates the proposal label, confirms each write and paces it', async () => {
  const w = fixture([1], { mode: 'observe' }), raw = w.issues[0], nativeWrites = [];
  let labelKnown = false;
  const http = (value, status = 200) => ({ code: 0, stdout: `HTTP/2.0 ${status} OK\r\ncontent-type: application/json\r\n\r\n${JSON.stringify(value)}` });
  const execFile = async (file, args, options) => {
    assert.equal(file, 'gh'); assert.equal(args[0], 'api');
    const method = args[args.indexOf('--method') + 1], endpoint = args[args.indexOf('--method') + 2];
    const body = options.input ? JSON.parse(options.input) : {};
    if (endpoint === 'graphql') return http({ errors: [{ message: 'Use the bounded REST fake.' }] });
    if (method !== 'GET') nativeWrites.push({ endpoint, method, body, at: Date.parse((await w.ports.clock.now({})).iso) });
    if (endpoint.endsWith('/labels/pdd%3Aclose-proposed')) return http(labelKnown ? { name: 'pdd:close-proposed' } : { message: 'Not Found' }, labelKnown ? 200 : 404);
    if (endpoint === 'repos/example/project/labels') { assert.equal(method, 'POST'); labelKnown = true; return http({ name: body.name }); }
    if (endpoint.endsWith('/issues?state=open&per_page=100')) return http([raw]);
    if (endpoint.endsWith('/issues/1/comments?per_page=100')) return http(w.comments.get(1));
    if (endpoint.endsWith('/issues/1/comments')) {
      assert.equal(method, 'POST'); return http(w.append(1, body.body));
    }
    if (/\/issues\/comments\/\d+$/.test(endpoint)) return http(w.comments.get(1).find(x => x.id === endpoint.split('/').pop()));
    if (endpoint.endsWith('/issues/1/labels')) { assert.equal(method, 'POST'); raw.labels.push(...body.labels.map(name => ({ name }))); return http(raw.labels); }
    if (endpoint.endsWith('/issues/1')) return http(raw);
    if (/\/(?:blocked_by|blocking|timeline)\?per_page=100$/.test(endpoint)) return http([]);
    assert.fail(`unexpected fake endpoint ${method} ${endpoint}`);
  };
  w.ports = createDependencyReadPorts({}, { ...w.ports, github: undefined, execFile });
  const r = w.record(1, { status: { ...w.record(1).status, state: 'fixed', fix: 'https://github.com/example/project/pull/90' } });
  assert.equal((await complete(w, [r])).state, 'complete');
  assert.equal(raw.state, 'open');
  assert.ok(raw.labels.some(x => x.name === 'pdd:close-proposed'));
  const sorted = nativeWrites.filter(x => !x.body.body?.includes('pdd-dependency-review:'));
  assert.equal(sorted.length, 4, 'sort record, label create, label attach, one route comment');
  for (let i = 1; i < sorted.length; i++) assert.ok(sorted[i].at - sorted[i - 1].at >= 1000);
});
