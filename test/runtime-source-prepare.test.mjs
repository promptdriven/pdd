import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs, { existsSync, mkdirSync, readFileSync, symlinkSync, writeFileSync } from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
import { join } from 'node:path';
import { captureSource, sha256, tarFiles } from '../src/runtime-preflight.mjs';
import { fakeRuntime, harbor, PLACE } from './runtime-fake.mjs';

const ORDER = 'tests/place-order.json';
const STORY = 'user_stories/place-order.md';
const write = (repo, path, content) => { mkdirSync(join(repo, path, '..'), { recursive: true }); writeFileSync(join(repo, path), content); };
const extract = (tar, path) => {
  const result = spawnSync('tar', ['-xOf', '-', path], { input: tar });
  assert.equal(result.status, 0, result.stderr.toString());
  return result.stdout;
};
const refuse = action => assert.throws(action, error => error.exitCode === 4 && !error.message.includes('PRIVATE-CONTENT'));

test('PREPARE keeps exact existing tar and synchronous return with no output', t => {
  const { repo } = harbor(t, repo => write(repo,'auth.json','{"token":"PRIVATE-CONTENT"}')), expected = captureSource(repo, { tests: [ORDER] });
  let calls = 0;
  const actual = captureSource(repo, { tests: [ORDER], prepareSource(ports) {
    calls++;
    assert.deepEqual(Object.keys(ports).sort(), ['readFile', 'statFile']);
    return [];
  } });
  assert.equal(calls, 1);
  assert.deepEqual(actual, expected);
  assert.equal(actual.then, undefined);
  assert.deepEqual(captureSource(repo,{prepareSource:()=>[]}),captureSource(repo));
});

test('PREPARE selects virtual files and discovers replacement calls, map assets and effective config', t => {
  const { repo } = harbor(t), original = readFileSync(join(repo, PLACE));
  const text = original.toString().replace('"calls": []', '"calls": [{"target":"prompts/child.prompt.md"}]');
  assert.notEqual(text, original.toString());
  const scenario = JSON.parse(readFileSync(join(repo, ORDER)));
  const binary = new Uint8Array([0, 255, 128, 4]);
  const outputs = [
    { path: PLACE, bytes: text }, { path: 'prompts/child.prompt.md', bytes: original },
    { path: 'tests/virtual.json', bytes: JSON.stringify(scenario) },
    { path: 'app/map.json', bytes: JSON.stringify({ screens: [{ prompt_path: PLACE }], stylesheets: ['app/style.css'] }) },
    { path: 'app/style.css', bytes: 'body {color: blue}' },
    { path: 'assets/binary.bin', bytes: binary },
    { path: 'pdd-source.json', bytes: JSON.stringify({ include: ['docs/virtual.md'] }) },
    { path: 'docs/virtual.md', bytes: '# Virtual\n## Dependencies\n[Asset](../assets/binary.bin)' },
  ];
  const capture = captureSource(repo, { tests: ['tests/virtual.json'], appMap: 'app/map.json', prepareSource: () => outputs });
  const entries = [...outputs.map(file => ({ path: file.path, bytes: Buffer.from(file.bytes) })), { path: STORY, bytes: readFileSync(join(repo, STORY)) }].sort((a,b) => a.path < b.path ? -1 : 1);
  assert.deepEqual(capture.tar, tarFiles(entries));
  assert.equal(capture.sha256, sha256(capture.tar));
  assert.equal(capture.bytes, entries.reduce((n, file) => n + file.bytes.length, 0));
  assert.deepEqual(extract(capture.tar, 'assets/binary.bin'), Buffer.from(binary));
  assert.deepEqual(readFileSync(join(repo, PLACE)), original);
  assert.equal(existsSync(join(repo, 'tests/virtual.json')), false);
});

test('PREPARE default discovery uses effective replaced and virtual scenario bytes', t => {
  const { repo } = harbor(t), scenario = readFileSync(join(repo, ORDER));
  const capture = captureSource(repo, { prepareSource: () => [
    { path: ORDER, bytes: '{}' }, { path: 'generated/test.json', bytes: scenario },
  ] });
  assert.ok(capture.files.some(file => file.path === 'generated/test.json'));
  assert.ok(capture.files.some(file => file.path === STORY));
  assert.equal(extract(capture.tar, ORDER).toString(), '{}');
  for (const schema_version of [1,{},null]) {
    const opaque=JSON.stringify({schema_version,note:'prompt-runtime.program-scenario',story_path:'literal-not-a-dependency.md'});
    const only=captureSource(repo,{prepareSource:()=>[{path:'opaque.json',bytes:opaque},{path:ORDER,bytes:'{}'},{path:'tests/unknown-item.json',bytes:'{}'}]});
    assert.equal(extract(only.tar,'opaque.json').toString(),opaque);
    assert.equal(only.files.some(file=>file.path==='literal-not-a-dependency.md'),false);
  }
});

test('PREPARE raw ports copy buffers/stats and leave input files out of payload', t => {
  const { repo } = harbor(t);
  write(repo, 'parts/one.json', '{"x":1}');
  let retained, leaked;
  const capture = captureSource(repo, { tests: [], prepareSource(ports) {
    retained = ports;
    const before = ports.readFile('parts/one.json'); before.fill(0);
    const stat = ports.statFile('parts/one.json'); stat.size = 999;
    assert.deepEqual(ports.statFile('parts/one.json'), { exists: true, is_symlink: false, size: 7 });
    assert.deepEqual(ports.statFile('missing.json'), { exists: false, is_symlink: false, size: 0 });
    leaked = ports.readFile('parts/one.json');
    return [{ path: 'joined.json', bytes: leaked }];
  } });
  leaked.fill(0);
  assert.deepEqual(capture.files, [{ path: 'joined.json', size: 7 }]);
  assert.equal(extract(capture.tar, 'joined.json').toString(), '{"x":1}');
  refuse(() => retained.readFile('parts/one.json'));
  refuse(() => retained.statFile('parts/one.json'));
});

test('PREPARE copies Uint8Array view boundaries and UTF-8 without a newline', t => {
  const { repo } = harbor(t), backing = new Uint8Array([9, 0, 255, 8]);
  const capture = captureSource(repo, { tests: [], prepareSource: () => [
    { path: 'view.bin', bytes: backing.subarray(1,3) }, { path: 'unicode.txt', bytes: 'é雪' },
  ] });
  backing.fill(7);
  assert.deepEqual(extract(capture.tar, 'view.bin'), Buffer.from([0,255]));
  assert.equal(extract(capture.tar, 'unicode.txt').toString(), 'é雪');
  assert.equal(capture.bytes, 7);
});

test('PREPARE exact effective archive survives the actual multipart loopback transport', async t => {
  const { repo } = harbor(t);
  const capture = captureSource(repo, { tests: [], prepareSource: () => [{ path: 'joined/seed.json', bytes: '{"stock":0}' }] });
  const runtime = await fakeRuntime(t, entry => {
    assert.deepEqual(entry.tar, capture.tar);
    assert.equal(entry.request.source_sha256, sha256(entry.tar));
    assert.equal(extract(entry.tar, 'joined/seed.json').toString(), '{"stock":0}');
    return { status: 200, json: { accepted: true } };
  });
  const form = new FormData();
  form.set('request', new Blob([JSON.stringify({ source_sha256: capture.sha256 })]), 'request.json');
  form.set('source', new Blob([capture.tar]), 'source.tar');
  const reply = await fetch(`${runtime.origin}/v1/check`, { method: 'POST', body: form });
  assert.equal(reply.status, 200);
  assert.deepEqual(await reply.json(), { accepted: true });
  assert.equal(runtime.posts.length, 1);
});

test('PREPARE rebuilds from changed raw inputs and missing observations', t => {
  for (const kind of ['raw', 'absent']) {
    const { repo } = harbor(t); write(repo, 'part.txt', 'first');
    let calls = 0;
    const capture = captureSource(repo, { tests: [], prepareSource({ readFile, statFile }) {
      calls++;
      const bytes = readFile('part.txt');
      statFile('later.txt');
      if (calls === 1) write(repo, kind === 'raw' ? 'part.txt' : 'later.txt', 'second');
      return [{ path: 'joined.txt', bytes }];
    } });
    assert.equal(calls, 2);
    assert.equal(extract(capture.tar, 'joined.txt').toString(), kind === 'raw' ? 'second' : 'first');
  }
});

test('PREPARE changing a replaced original still retries and exhaustion exits 5', t => {
  const { repo } = harbor(t); let calls = 0;
  assert.throws(() => captureSource(repo, { tests: [], attempts: 2, prepareSource({ readFile }) {
    calls++;
    readFile(PLACE);
    write(repo, PLACE, `# Changed ${calls}`);
    return [{ path: PLACE, bytes: '# Effective' }];
  } }), error => error.exitCode === 5 && /2 times/.test(error.message));
  assert.equal(calls, 2);
});

test('PREPARE a callback cannot swallow an unstable read to return a mixed snapshot', t => {
  const { repo } = harbor(t); write(repo, 'part.txt', 'marker');
  const original = fs.readFileSync; let writes = 0, calls = 0;
  t.after(() => { fs.readFileSync = original; syncBuiltinESMExports(); });
  fs.readFileSync = (...args) => {
    const bytes = original(...args);
    if (typeof args[0] === 'number' && bytes.toString() === 'marker') write(repo, 'part.txt', `changed-${++writes}`);
    return bytes;
  };
  syncBuiltinESMExports();
  const capture = captureSource(repo, { tests: [], prepareSource({ readFile }) {
    calls++;
    try { return [{ path: 'result.txt', bytes: readFile('part.txt') }]; }
    catch { return [{ path: 'result.txt', bytes: 'incorrect fallback' }]; }
  } });
  assert.equal(calls, 2);
  assert.equal(extract(capture.tar, 'result.txt').toString(), 'changed-1');
});

test('PREPARE output destinations appearing or becoming symlink ancestors invalidate the attempt', t => {
  for (const kind of ['leaf', 'ancestor']) {
    const { repo, sandbox } = harbor(t); let calls = 0;
    const original = fs.readFileSync;
    t.after(() => { fs.readFileSync = original; syncBuiltinESMExports(); });
    fs.readFileSync = (...args) => {
      const bytes = original(...args);
      if (typeof args[0] === 'number' && bytes.toString().includes('Harbor') && calls === 1) {
        if (kind === 'leaf') write(repo, 'generated/a.txt', 'disk');
        else { mkdirSync(join(sandbox, 'elsewhere')); symlinkSync(join(sandbox, 'elsewhere'), join(repo, 'generated')); }
      }
      return bytes;
    };
    syncBuiltinESMExports();
    const action = () => captureSource(repo, { tests: [ORDER], prepareSource() { calls++; return [{ path: 'generated/a.txt', bytes: 'virtual' }]; } });
    if (kind === 'ancestor') { refuse(action); assert.equal(calls, 2); }
    else { const capture = action(); assert.equal(calls, 2); assert.equal(extract(capture.tar, 'generated/a.txt').toString(), 'virtual'); }
    fs.readFileSync = original; syncBuiltinESMExports();
  }
});

test('PREPARE all access modes reject unsafe paths and unsafe original entries', t => {
  for (const mode of ['read', 'stat', 'return']) {
    const { repo, sandbox } = harbor(t);
    write(repo, 'ignored.txt', 'PRIVATE-CONTENT'); write(repo, '.gitignore', 'ignored.txt\n');
    write(repo, 'secret-source.txt', 'PRIVATE-CONTENT');
    symlinkSync(join(repo, 'secret-source.txt'), join(repo, 'link.txt'));
    symlinkSync(sandbox, join(repo, 'linked'));
    mkdirSync(join(repo, 'directory'));
    for (const path of ['../outside', '/absolute', 'bad\\path', 'bad\npath', '.git/config', '.env.local', 'secrets/a.txt', '.aws/a.txt', 'ignored.txt', 'link.txt', 'linked/a.txt', 'directory']) {
      refuse(() => captureSource(repo, { tests: [], prepareSource({ readFile, statFile }) {
        if (mode === 'read') readFile(path);
        if (mode === 'stat') statFile(path);
        return mode === 'return' ? [{ path, bytes: 'safe replacement' }] : [];
      } }));
    }
    refuse(() => captureSource(repo, { tests: [], prepareSource: ({ readFile }) => { readFile('missing.txt'); return []; } }));
  }
});

test('PREPARE duplicate normalized paths and ancestor conflicts refuse without choosing an output', t => {
  const { repo } = harbor(t);
  for (const paths of [['same.txt','./same.txt'], ['a','a/b'], ['a/b','a']]) refuse(() => captureSource(repo, {
    tests: [], prepareSource: () => paths.map(path => ({ path, bytes: 'same' })),
  }));
});

test('PREPARE invalid callbacks and results refuse with no contents disclosure', t => {
  const { repo } = harbor(t);
  for (const prepareSource of [false, 'PRIVATE-CONTENT', () => null, () => ({}), () => Promise.resolve([]), () => [{ path: 'x', bytes: 1 }], () => [{ bytes: 'PRIVATE-CONTENT' }]]) {
    refuse(() => captureSource(repo, { tests: [], prepareSource }));
  }
  const failure = new Error('caller failed');
  assert.throws(() => captureSource(repo, { tests: [], prepareSource: () => { throw failure; } }), error => error === failure);
});

test('PREPARE applies effective file, payload and framed PAX tar limits', t => {
  const { repo } = harbor(t);
  refuse(() => captureSource(repo, { tests: [], prepareSource: () => [{ path: PLACE, bytes: Buffer.alloc(10_485_761) }] }));
  refuse(() => captureSource(repo, { tests: [], prepareSource: () => Array.from({ length: 10_001 }, (_, i) => ({ path: `generated/${i}.txt`, bytes: '' })) }));
  // Under the raw byte limit, but framing a long Unicode path exceeds it.
  refuse(() => captureSource(repo, { tests: [], prepareSource: () => [{ path: `${'雪'.repeat(100)}.txt`, bytes: Buffer.alloc(10_484_000) }] }));
  const before = readFileSync(join(repo, PLACE));
  const capture = captureSource(repo, { tests: [], prepareSource: () => [{ path: PLACE, bytes: '' }] });
  assert.equal(capture.bytes, 0);
  assert.deepEqual(readFileSync(join(repo, PLACE)), before);
});

test('PREPARE app-map role chooses the attempt-local map and follows its dependencies', t => {
  const { repo } = harbor(t);
  const original = readFileSync(join(repo, PLACE));
  const mapPath = 'app/maps/virtual_1.json';
  const capture = captureSource(repo, { tests: [ORDER], prepareSource: () => [
    { path: mapPath, role: 'app-map', bytes: JSON.stringify({ schema_version: 'prompt-runtime.app-map.v1', screens: [{ prompt_path: 'prompts/map-only.prompt.md' }], stylesheets: ['app/map-only.css'] }) },
    { path: 'prompts/map-only.prompt.md', bytes: original },
    { path: 'app/map-only.css', bytes: 'body{}' },
  ] });
  assert.ok(capture.stories[0].files.some(file => file.path === mapPath));
  assert.ok(capture.files.some(file => file.path === 'prompts/map-only.prompt.md'));
  assert.ok(capture.files.some(file => file.path === 'app/map-only.css'));
  assert.equal(capture.sha256, sha256(capture.tar));
  assert.equal(existsSync(join(repo, mapPath)), false);
  for (const outputs of [
    [{ path: mapPath, role: 'other', bytes: '{}' }],
    [{ path: mapPath, role: 'app-map', bytes: '{}' }],
    [{ path: mapPath, role: 'app-map', bytes: '{' }],
    ['one', 'two'].map(name => ({ path: `app/${name}.json`, role: 'app-map', bytes: '{"schema_version":"prompt-runtime.app-map.v1"}' })),
  ]) assert.throws(() => captureSource(repo, { tests: [ORDER], prepareSource: () => outputs }), error => error.exitCode === 4);
});
