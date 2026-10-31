import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, symlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { captureSource, sourceFilePort } from '../src/runtime-preflight.mjs';
import { runContracts } from '../src/contracts.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor, sha } from './runtime-fake.mjs';

const ORDER = 'tests/place-order.json';
const write = (repo, path, bytes) => { mkdirSync(join(repo, path, '..'), { recursive: true }); writeFileSync(join(repo, path), bytes); };
const include = (repo, path) => write(repo, 'pdd-source.json', JSON.stringify({ include: [path] }));
const bytes = Buffer.from('shared source\0exact bytes\n');
function linked(t, kind) {
  const setup = harbor(t), { repo } = setup;
  write(repo, 'shared/shared.md', bytes); mkdirSync(join(repo, 'services/api'), { recursive: true });
  const path = kind === 'direct' ? 'services/api/shared.md' : 'services/api/shared/shared.md';
  symlinkSync('../../shared' + (kind === 'direct' ? '/shared.md' : ''), join(repo, kind === 'direct' ? path : 'services/api/shared'));
  include(repo, path); return { ...setup, path };
}
function entry(tar, name) {
  for (let offset = 0; offset < tar.length; ) {
    const header = tar.subarray(offset, offset + 512);
    const path = header.subarray(0, 100).toString().replace(/\0.*$/s, '');
    const size = parseInt(header.subarray(124, 136).toString().replace(/\0.*$/s, '').trim(), 8) || 0;
    if (path === name) return { type: String.fromCharCode(header[156]), mode: parseInt(header.subarray(100, 108).toString(), 8), bytes: tar.subarray(offset + 512, offset + 512 + size) };
    offset += 512 + Math.ceil(size / 512) * 512;
  }
  assert.fail(`missing archive entry ${name}`);
}
for (const kind of ['direct', 'folder']) {
  test(`LINK upload ${kind}: server receives regular target bytes under authored path`, async t => {
    const setup = linked(t, kind);
    let capture;
    assert.doesNotThrow(() => { capture = captureSource(setup.repo, { tests: [ORDER] }); }, 'safe in-repository linked source must be accepted');
    const fake = await fakeRuntime(t, (request, server) => server.normal(request));
    const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: {} }, ports), 0, ports.stderr.text);
    assert.ok(fake.posts.length > 0, 'server observes an upload');
    for (const post of fake.posts) {
      const file = entry(post.tar, setup.path);
      assert.equal(file.type, '0'); assert.equal(file.mode, 0o600); assert.deepEqual(file.bytes, bytes);
      assert.equal(post.request.source_sha256, sha(post.tar)); assert.deepEqual(post.tar, capture.tar);
    }
    assert.deepEqual(captureSource(setup.repo, { tests: [ORDER] }).tar, capture.tar);
  });
  test(`LINK manifest ${kind}: offline arrow names canonical final target and byte size`, async t => {
    const setup = linked(t, kind);
    const { ports } = portsFor({ HOME: setup.home }, { gh: () => assert.fail('offline auth'), fetch: () => assert.fail('offline network') });
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--files': true } }, ports), 0, ports.stderr.text);
    const line = ports.stdout.text.split('\n').find(line => line.includes(`${setup.path} -> shared/shared.md`));
    assert.ok(line, ports.stdout.text); assert.ok(line.endsWith(`${bytes.length} bytes`), line);
  });
}
for (const [kind, target, reason] of [
  ['outside', '../../../outside.md', /outside the repository/i],
  ['broken', 'missing.md', /broken|missing|exist/i],
  ['loop', 'other.md', /loop|cycl/i],
  ['secret link', '../../shared/shared.md', /secret/i],
  ['secret target', '../../shared/.env', /secret/i],
  ['invisible target', '../../shared/ignored.md', /Git-visible|ignor/i],
]) {
  test(`LINK refusal ${kind}: names link and destination with reason before upload`, async t => {
    const setup = harbor(t), { repo } = setup;
    mkdirSync(join(repo, 'services/api'), { recursive: true });
    write(repo, 'shared/shared.md', bytes); write(repo, 'shared/.env', 'synthetic'); write(repo, 'shared/ignored.md', 'synthetic');
    write(repo, '.gitignore', 'shared/ignored.md\n'); writeFileSync(join(setup.sandbox, 'outside.md'), 'outside');
    const path = `services/api/${kind === 'secret link' ? '.env' : 'shared.md'}`;
    symlinkSync(target, join(repo, path));
    if (kind === 'loop') symlinkSync('shared.md', join(repo, 'services/api/other.md'));
    include(repo, path);
    const { ports } = portsFor({ HOME: setup.home }, { gh: () => assert.fail('refusal auth'), fetch: () => assert.fail('refusal upload') });
    assert.equal(await runCheck({ cwd: repo, words: ['place-order'], options: { '--files': true } }, ports), 4);
    assert.ok(ports.stderr.text.includes(path), ports.stderr.text);
    assert.ok(ports.stderr.text.includes(target) || ports.stderr.text.includes(target.replace('../../', '')), `missing target ${target}: ${ports.stderr.text}`);
    assert.match(ports.stderr.text, reason);
  });
}
test('LINK raw reads: safe source reads do not select reference-only input', t => {
  const setup = linked(t, 'direct');
  const port = sourceFilePort(setup.repo);
  let result;
  assert.doesNotThrow(() => { result = port.read({ path: setup.path }); }, 'raw reference adapter accepts the safe link');
  assert.equal(result.content, bytes.toString('utf8'));
  // Replace only local selection metadata; the linked source now remains reference-only.
  write(setup.repo, 'pdd-source.json', '{"include":[]}');
  let capture;
  assert.doesNotThrow(() => { capture = captureSource(setup.repo, { tests: [ORDER], prepareSource({ readFile }) {
    assert.deepEqual(readFile(setup.path), bytes); return [];
  } }); });
  assert.ok(!capture.files.some(file => file.path === setup.path));
});

test('LINK selection metadata: root config follows source-reading policy', t => {
  const { repo } = harbor(t);
  write(repo, 'selection.json', '{"include":["README.md"]}');
  symlinkSync('selection.json', join(repo, 'pdd-source.json'));
  let capture;
  assert.doesNotThrow(() => { capture = captureSource(repo, { tests: [ORDER] }); });
  assert.ok(capture.files.some(file => file.path === 'README.md'));
  assert.ok(!capture.files.some(file => file.path === 'selection.json' || file.path === 'pdd-source.json'));
});
test('LINK Markdown context: dependencies resolve from authored linked path', t => {
  const setup = linked(t, 'direct');
  write(setup.repo, 'shared/shared.md', '# Shared\n## Dependencies\n[Policy](policy.md)\n');
  write(setup.repo, 'services/api/policy.md', '# Authored policy');
  write(setup.repo, 'shared/policy.md', '# Physical policy must stay unselected');
  let capture;
  assert.doesNotThrow(() => { capture = captureSource(setup.repo, { tests: [ORDER] }); });
  assert.ok(capture.files.some(file => file.path === 'services/api/policy.md'));
  assert.ok(!capture.files.some(file => file.path === 'shared/policy.md'));
});


test('LINK authored eligibility: visible later chains cannot authorize ignored direct or folder paths', t => {
  const { repo } = harbor(t);
  write(repo, 'target.md', 'visible target');
  write(repo, 'target-dir/file.md', 'visible folder target');
  symlinkSync('target.md', join(repo, 'middle.md'));
  symlinkSync('target-dir', join(repo, 'middle-dir'));
  symlinkSync('middle.md', join(repo, 'hidden.md'));
  symlinkSync('middle-dir', join(repo, 'hidden-dir'));
  symlinkSync('target-dir', join(repo, 'visible-dir'));
  write(repo, '.gitignore', 'hidden.md\nhidden-dir\n');
  const port = sourceFilePort(repo);
  let accepted;
  assert.doesNotThrow(() => { accepted = port.read({ path: 'middle.md' }); }, 'safe visible source remains accepted');
  assert.equal(accepted.content, 'visible target');
  assert.equal(port.read({ path: 'visible-dir/file.md' }).content, 'visible folder target', 'visible authored symlink ancestor remains eligible');
  for (const path of ['hidden.md', 'hidden-dir/file.md']) {
    assert.throws(() => port.read({ path }), /Git-visible|ignor/i, `ignored authored path ${path} has no visible authored symlink ancestor`);
    assert.throws(() => port.stat({ path }), /Git-visible|ignor/i);
    include(repo, path);
    assert.throws(() => captureSource(repo, { tests: [ORDER] }), /Git-visible|ignor/i);
  }
});

test('LINK contracts boundary: safe source acceptance preserves standalone command no-follow refusal', t => {
  const setup = harbor(t), { repo } = setup;
  write(repo, 'contracts/order.json', '{"type":"object","properties":{},"required":[],"additionalProperties":false}');
  const target = readFileSync(join(repo, 'contracts/order.json'));
  symlinkSync('contracts/order.json', join(repo, 'safe-source.json'));
  let accepted;
  assert.doesNotThrow(() => { accepted = sourceFilePort(repo).read({ path: 'safe-source.json' }); }, 'safe linked source remains accepted');
  assert.equal(accepted.content, target.toString());
  symlinkSync('../contracts/order.json', join(repo, 'prompts/linked.prompt.md'));
  const original = readFileSync(join(repo, 'prompts/place_order.prompt.md'));
  for (const options of [{}, { '--write': true }]) {
    const stdout = { text: '', write(value) { this.text += value; } }, stderr = { text: '', write(value) { this.text += value; } };
    assert.equal(runContracts({ cwd: repo, words: ['sync'], options }, { env: { HOME: setup.home }, stdout, stderr }), 4, 'standalone contracts commands must refuse linked originals');
    assert.match(stderr.text, /link|unsafe/i);
    assert.deepEqual(readFileSync(join(repo, 'contracts/order.json')), target);
    assert.deepEqual(readFileSync(join(repo, 'prompts/place_order.prompt.md')), original);
  }
});
