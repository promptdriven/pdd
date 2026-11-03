import test from 'node:test';
import assert from 'node:assert/strict';
import { request } from 'node:http';
import { writeFileSync, mkdirSync, renameSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join } from 'node:path';
import { runTry } from '../src/runtime-client.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';
import { openServe } from '../src/try-http.mjs';
const raw = (port, path, method = 'GET', body = '', headers = {}) => new Promise((resolve, reject) => {
  const req = request({ hostname: '127.0.0.1', port, path, method, headers }, res => {
    const chunks = []; res.on('data', b => chunks.push(b)); res.on('end', () => resolve({ status: res.statusCode, headers: res.headers, body: Buffer.concat(chunks).toString() }));
  }); req.on('error', reject); req.end(body);
});
async function screen(work, model = { app_map: true, entries: [] }) {
  const calls = [], output = [], ports = { stdout: { write(text) { output.push(text); } }, serve: async server => work(server.address().port, calls, output) };
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


test('Screen-only startup explicitly names its capability; neither capability has a plain diagnostic', async () => {
  await screen(async (port, calls, output) => {
    assert.match(output.join(''), /Screen only \(no named HTTP routes\)/);
    assert.equal((await raw(port, '/')).status, 200);
  });
  for (const app_map of [false, undefined]) await assert.rejects(screen(() => assert.fail('must not listen'), { app_map, entries: [] }), /neither a Screen app map nor named HTTP routes/);
});

test('Screen-only Story runs through map capture, Try creation and reuse without HTTP route labels', async t => {
  const setup = harbor(t, repo => writeFileSync(join(repo, 'app-map.json'), JSON.stringify({schema_version:'prompt-runtime.app-map.v1',name:'Harbor',initial_screen:'menu'})));
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.url.endsWith('/model')) return {status:200,json:{app_map:Boolean(f.posts.find(p=>p.command==='try')?.request.app_map),entries:[]}};
    if (entry.url.endsWith('/screen/index.html')) return {status:200,text:'<!doctype html><title>Harbor Screen</title>',headers:{'content-type':'text/html'}};
    if (entry.command==='lint') return {status:200,json:f.lint(entry.request.requestId)};
    if (entry.command==='try') return {status:200,json:f.tryJob(entry.request.requestId)};
    return {status:200,json:f.tryJob(entry.url.split('/').at(-1))};
  });
  for (let n=0;n<2;n++) {
    const {ports}=portsFor({HOME:setup.home,PDD_RUNTIME_URL:fake.origin,PDD_STATE_DIR:setup.state},{openUrl:()=>assert.fail('serve must not open hosted page'),serve:async server=>assert.equal((await raw(server.address().port,'/')).status,200)});
    assert.equal(await runTry({cwd:setup.repo,words:['place-order'],options:{'--serve':'0'}},ports),0,ports.stderr.text);
    assert.match(ports.stdout.text,/Screen only \(no named HTTP routes\)/);
  }
  const created=fake.posts.filter(p=>p.command==='try');
  assert.equal(created.length,1);assert.equal(created[0].request.app_map,'app-map.json');
  assert.ok(created[0].tar.includes(Buffer.from('app-map.json')));
  assert.equal(fake.jsonPosts.length,0);assert.equal(fake.deletes.length,0);
});

test('saved Try missing the current local app map gives deliberate recovery without replacing world', async t => {
  const setup=harbor(t),fake=await fakeRuntime(t,(entry,f)=> {
    if(entry.url.endsWith('/model'))return{status:200,json:{app_map:false,entries:[]}};
    if(entry.command==='lint')return{status:200,json:f.lint(entry.request.requestId)};
    if(entry.command==='try')return{status:200,json:f.tryJob(entry.request.requestId)};
    return{status:200,json:f.tryJob(entry.url.split('/').at(-1))};
  });
  const make=()=>portsFor({HOME:setup.home,PDD_RUNTIME_URL:fake.origin,PDD_STATE_DIR:setup.state},{openUrl:async()=>true,serve:()=>assert.fail('no Screen admitted')}).ports;
  assert.equal(await runTry({cwd:setup.repo,words:['place-order'],options:{'--no-open':true}},make()),0);
  writeFileSync(join(setup.repo,'app-map.json'),JSON.stringify({schema_version:'prompt-runtime.app-map.v1',name:'Harbor'}));
  const ports=make();
  assert.equal(await runTry({cwd:setup.repo,words:['place-order'],options:{'--serve':'8080'}},ports),125);
  assert.match(ports.stderr.text,/saved Try has no Screen app map/);
  assert.match(ports.stderr.text,/pdd simulate place-order --serve 8080 --new --app-map app-map.json/);
  assert.equal(fake.posts.filter(p=>p.command==='try').length,1);assert.equal(fake.deletes.length,0);assert.equal(fake.jsonPosts.length,0);
});


test('missing-map recovery works from a subdirectory and shell-quotes the selected map', async t => {
  const setup=harbor(t); const moved=setup.repo+' with $literal'; renameSync(setup.repo,moved);setup.repo=moved;
  const fake=await fakeRuntime(t,(entry,f)=> {
    if(entry.url.endsWith('/model'))return{status:200,json:{app_map:false,entries:[]}};
    if(entry.command==='lint')return{status:200,json:f.lint(entry.request.requestId)};
    if(entry.command==='try')return{status:200,json:f.tryJob(entry.request.requestId)};
    return{status:200,json:f.tryJob(entry.url.split('/').at(-1))};
  });
  const make=()=>portsFor({HOME:setup.home,PDD_RUNTIME_URL:fake.origin,PDD_STATE_DIR:setup.state},{openUrl:async()=>true,serve:()=>assert.fail('no Screen admitted')}).ports;
  const mapFolder=join(setup.repo,'map files');mkdirSync(mapFolder);
  writeFileSync(join(mapFolder,'my $literal.json'),JSON.stringify({schema_version:'prompt-runtime.app-map.v1',name:'Harbor'}));
  const cwd=join(setup.repo,'nested folder');mkdirSync(cwd);
  const ports=make();assert.equal(await runTry({cwd,words:['place-order'],options:{'--serve':'8080','--app-map':'../map files/my $literal.json'}},ports),125);
  const command=ports.stderr.text.split('Start a new Try with the selected app map: ')[1].trim();
  const bin=join(setup.home,'bin');mkdirSync(bin);writeFileSync(join(bin,'pdd'),'#!/bin/sh\nprintf \'%s\\n\' "$@"\n',{mode:0o700});
  const parsed=spawnSync('/bin/sh',['-c',command],{cwd,env:{...process.env,PATH:bin+':'+process.env.PATH},encoding:'utf8'});
  assert.equal(parsed.status,0,parsed.stderr);
  assert.deepEqual(parsed.stdout.trimEnd().split('\n'),['simulate','place-order','--serve','8080','--new','--app-map','../map files/my $literal.json']);
  assert.equal(fake.deletes.length,0);assert.equal(fake.posts.filter(p=>p.command==='try').length,1);
});
