import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
import { mkdirSync, readFileSync, symlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { captureSource, proseSha256 } from '../src/runtime-preflight.mjs';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { PLACE, fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

const ORDER = 'tests/place-order.json';
const STORY = 'user_stories/place-order.md';
const write = (repo, path, text) => { mkdirSync(join(repo, path, '..'), { recursive: true }); writeFileSync(join(repo, path), text); };
const json = (repo, path, value) => write(repo, path, JSON.stringify(value));
const load = (repo, path) => JSON.parse(readFileSync(join(repo, path), 'utf8'));
const names = tar => {
  const result = spawnSync('tar', ['-tf', '-'], { input: tar, encoding: 'utf8' });
  assert.equal(result.status, 0, result.stderr);
  return result.stdout.trim().split('\n');
};
function prompt(repo, path, prose, calls = []) {
  const original = readFileSync(join(repo, PLACE), 'utf8');
  const start = original.indexOf('<details>');
  const body = JSON.parse(original.slice(start).match(/```json\s*([\s\S]*?)```/)[1]);
  body.status = 'draft'; body.calls = calls;
  const text = `${prose}\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(body)}\n\`\`\`\n</details>\n`;
  body.prose_sha256 = proseSha256(text);
  write(repo, path, text.replace(/"prose_sha256":"[^"]*"/, `"prose_sha256":"${body.prose_sha256}"`));
}
function offline(setup) {
  const { ports, clock } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: 'http://127.0.0.1:9' }, {
    gh: () => assert.fail('offline preview must not sign in'), fetch: () => assert.fail('offline preview must not contact a server')
  });
  return { ports, clock };
}

// The issue's unrelated tracked file must not consume the selected Story's upload limit.
test('SOURCE1: --files scopes a Story offline, prints its exact manifest and byte sizes, and keeps original paths', async t => {
  const setup = harbor(t, repo => write(repo, 'unrelated-tracked.bin', Buffer.alloc(10_485_761)));
  write(setup.repo, 'unrelated-new.bin', Buffer.alloc(10_485_761));
  write(setup.repo, '.env.local', 'DO_NOT_SEND=anything');
  prompt(setup.repo, 'prompts/unselected.prompt.md', '# Not selected\n## Dependencies\n[Missing](missing.md)');
  const { ports } = offline(setup);
  const code = await runCheck({ cwd: join(setup.repo, 'prompts'), words: ['../tests/place-order.json'], options: { '--files': true } }, ports);
  assert.equal(code, 0, ports.stderr.text);
  const expected = [PLACE, ORDER, STORY].sort();
  const lines = ports.stdout.text.trimEnd().split('\n');
  assert.deepEqual(lines.slice(0, -1).map(line => line.trim().split(/\s{2,}/)[0]), expected);
  const bytes = expected.reduce((sum, path) => sum + readFileSync(join(setup.repo, path)).length, 0);
  assert.match(lines.at(-1), new RegExp(`3 files, .*\\(${bytes} bytes\\)`));
  for (const path of expected) assert.ok(lines.some(line => line.includes(path) && line.endsWith(`${readFileSync(join(setup.repo, path)).length} bytes`)), path);
  const first = captureSource(setup.repo, { tests: [ORDER] }), second = captureSource(setup.repo, { tests: [ORDER] });
  assert.deepEqual(names(first.tar), expected); assert.equal(first.bytes, bytes);
  assert.ok(first.tar.equals(second.tar)); assert.equal(first.sha256, second.sha256);
  const all = captureSource(setup.repo);
  assert.deepEqual(names(all.tar), [PLACE, ORDER, 'tests/unknown-item.json', STORY, 'user_stories/unknown-item.md'].sort());
});

function closure(setup) {
  const { repo } = setup;
  prompt(repo, PLACE, '# Entry\n[Navigation only](../navigation.md)\n## Dependencies\n- [Policy](../docs/policy.md#rule)\n- `data/menu.json`',
    [{ operation: 'quote', target: 'prompts/quote.prompt.md', target_operation: 'place_order', max_calls: 1 }]);
  prompt(repo, 'prompts/quote.prompt.md', '# Quote\n## Dependencies\n[Policy](../docs/policy.md#rule)',
    [{ operation: 'again', target: PLACE, target_operation: 'place_order', max_calls: 1 }]);
  write(repo, 'docs/policy.md', '# Policy\n## Dependencies\n[Shared](shared.md)\n[External](https://example.invalid/policy)');
  write(repo, 'docs/shared.md', '# Shared\n## Dependencies\n[Policy](policy.md#rule)\n[Reference policy][ref]\n\n[ref]: policy-reference.md');
  write(repo, 'docs/policy-reference.md', '# Reference policy');
  write(repo, 'data/menu.json', '{"price": 900}');
  write(repo, 'navigation.md', 'Do not send ordinary navigation links.');
  write(repo, 'docs/test-context.txt', 'Extra test context.');
  write(repo, STORY, readFileSync(join(repo, STORY), 'utf8') + '\n## Dependencies\n[Story policy](../docs/story-policy.md)\n');
  write(repo, 'docs/story-policy.md', '# Story policy');
  const doc = load(repo, ORDER);
  doc.context = [{ prompt_path: 'prompts/quote.prompt.md', paths: ['docs/test-context.txt'] }];
  json(repo, ORDER, doc);
  prompt(repo, 'prompts/shelf.prompt.md', '# Shelf\n![Shelf][shelf]\n\n[shelf]: views/shelf.ui.svg\n\n## Dependencies\nNone.');
  write(repo, 'prompts/views/shelf.ui.svg', '<svg xmlns="http://www.w3.org/2000/svg"/>');
  prompt(repo, 'prompts/action.prompt.md', '# Action\n## Dependencies\nNone.');
  write(repo, 'app/shelf.css', 'body { color: navy; }');
  json(repo, 'app/custom-map.json', { schema_version: 'prompt-runtime.app-map.v1', name: 'Bookshelf',
    screens: [{ prompt_path: 'prompts/shelf.prompt.md' }], stylesheets: ['app/shelf.css'],
    handlers: [{ handler: { prompt_path: 'prompts/action.prompt.md' }, after: [{ prompt_path: 'prompts/quote.prompt.md' }] }],
    initial_state: { prompt_path: 'not-a-dependency.md' } });
  write(repo, 'docs/extra.txt', 'Explicit extra context.');
  json(repo, 'pdd-source.json', { include: ['docs/extra.txt', 'docs/shared.md'] });
  return [PLACE, ORDER, STORY, 'prompts/quote.prompt.md', 'docs/policy.md', 'docs/shared.md', 'docs/story-policy.md', 'docs/policy-reference.md', 'data/menu.json', 'docs/test-context.txt',
    'prompts/shelf.prompt.md', 'prompts/views/shelf.ui.svg', 'prompts/action.prompt.md', 'app/shelf.css', 'app/custom-map.json', 'docs/extra.txt'].sort();
}

test('SOURCE2: calls, declared Markdown context, test context, app-map screens/actions/styles, and includes form one closure', async t => {
  const setup = harbor(t), expected = closure(setup);
  const capture = captureSource(setup.repo, { tests: [ORDER], appMap: 'app/custom-map.json' });
  assert.deepEqual(names(capture.tar), expected);
  const { ports } = offline(setup);
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--files': true, '--app-map': 'app/custom-map.json' } }, ports), 0, ports.stderr.text);
  assert.deepEqual(ports.stdout.text.trimEnd().split('\n').slice(0, -1).map(line => line.trim().split(/\s{2,}/)[0]), expected);
});

test('SOURCE3: incomplete context and invalid includes give actionable local diagnostics without sign-in', async t => {
  for (const [label, edit, expected] of [
    ['called prompt', r => prompt(r, PLACE, '# Entry', [{ target: 'prompts/missing.prompt.md' }]), /place_order\.prompt\.md.*prompts\/missing\.prompt\.md.*not a Git-visible file/],
    ['declared dependency', r => prompt(r, PLACE, '# Entry\n## Dependencies\n[Policy](../docs/missing.md)'), /place_order\.prompt\.md.*docs\/missing\.md.*not a Git-visible file/],
    ['context', r => { const doc = load(r, ORDER); doc.context = [{ prompt_path: PLACE, paths: ['missing.txt'] }]; json(r, ORDER, doc); }, /place-order\.json.*missing\.txt.*not a Git-visible file/],
    ['malformed config', r => write(r, 'pdd-source.json', '{'), /pdd-source\.json.*valid JSON/],
    ['unknown config key', r => json(r, 'pdd-source.json', { include: [], exclude: ['x'] }), /pdd-source\.json.*only.*include/],
    ['non-string', r => json(r, 'pdd-source.json', { include: [null] }), /pdd-source\.json.*path/],
    ['traversal', r => json(r, 'pdd-source.json', { include: ['../outside.txt'] }), /pdd-source\.json.*repository-relative/],
    ['absolute', r => json(r, 'pdd-source.json', { include: ['/tmp/outside.txt'] }), /pdd-source\.json.*repository-relative/],
    ['ignored', r => { write(r, '.gitignore', 'ignored.txt\n'); write(r, 'ignored.txt', 'x'); json(r, 'pdd-source.json', { include: ['ignored.txt'] }); }, /pdd-source\.json.*ignored\.txt.*not a Git-visible file/],
  ]) {
    const setup = harbor(t); edit(setup.repo); const { ports } = offline(setup);
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--files': true } }, ports), 4, label);
    assert.match(ports.stderr.text, expected, label);
  }
});

test('SOURCE4: optional includes preserve selected secret, symlink, non-regular, size and file-count protections', t => {
  for (const [label, path, edit, expected] of [
    ['secret', '.env.local', r => write(r, '.env.local', 'x'), /name looks like a secret/],
    ['secret directory', 'config/secrets/a.txt', r => write(r, 'config/secrets/a.txt', 'x'), /name looks like a secret/],
    ['symlink', 'link.md', r => symlinkSync('README.md', join(r, 'link.md')), /symbolic link/],
    ['directory', 'folder', r => mkdirSync(join(r, 'folder')), /regular file|Git-visible file/],
    ['size', 'big.bin', r => write(r, 'big.bin', Buffer.alloc(10_485_761)), /too big to send/],
  ]) {
    const setup = harbor(t); edit(setup.repo); json(setup.repo, 'pdd-source.json', { include: [path] });
    assert.throws(() => captureSource(setup.repo, { tests: [ORDER] }), expected, label);
  }
  const many = harbor(t), include = [];
  for (let i = 0; i < 10_000; i++) { const path = `many/${i}.txt`; write(many.repo, path, ''); include.push(path); }
  json(many.repo, 'pdd-source.json', { include });
  assert.throws(() => captureSource(many.repo, { tests: [ORDER] }), /too big to send.*1000[1-3] files/);
  const linked = harbor(t); write(linked.repo, 'config.json', '{"include": []}');
  symlinkSync('config.json', join(linked.repo, 'pdd-source.json'));
  assert.throws(() => captureSource(linked.repo, { tests: [ORDER] }), /pdd-source\.json.*symbolic link/);
});

test('SOURCE5: Check and lint upload precisely the offline selected manifest, sharing one tar per batch', async t => {
  for (const options of [{}, { '--lint': true }]) {
    const setup = harbor(t, repo => write(repo, 'large-tracked.bin', Buffer.alloc(10_485_761)));
    json(setup.repo, 'pdd-source.json', { include: ['README.md'] });
    const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
    const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options }, ports), 0, ports.stderr.text + ports.stdout.text);
    const preview = captureSource(setup.repo, { tests: [ORDER] });
    assert.deepEqual(fake.posts.map(post => post.command), options['--lint'] ? ['lint'] : ['lint', 'check']);
    for (const post of fake.posts) { assert.ok(post.tar.equals(preview.tar)); assert.equal(post.request.source_sha256, preview.sha256); }
    assert.deepEqual(names(preview.tar), ['README.md', PLACE, ORDER, STORY].sort());
  }
});

test('SOURCE6: scoped Try keeps its authored seed and adds saved cases to the original test file', async t => {
  const setup = harbor(t, repo => write(repo, 'large-tracked.bin', Buffer.alloc(10_485_761)));
  const before = load(setup.repo, ORDER), saved = structuredClone(before);
  saved.steps = [saved.steps[0]]; saved.steps[0].step_id = 'saved-scoped';
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.command === 'try') return { status: 200, json: f.tryJob(entry.request.requestId) };
    if (entry.url.endsWith('/tests')) return { status: 200, json: { tests: [{ id: 'saved-scoped', path: 'elsewhere/never.json', story_path: STORY, test: saved }] } };
    return { status: 404, json: {} };
  });
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--no-open': true, '--no-wait': true } }, ports), 0, ports.stderr.text + ports.stdout.text);
  assert.equal(fake.posts[1].request.seed, ORDER);
  assert.deepEqual(names(fake.posts[1].tar), [PLACE, ORDER, STORY].sort());
  const after = load(setup.repo, ORDER);
  assert.equal(after.steps.length, before.steps.length + 1);
  assert.equal(after.steps.at(-1).step_id, 'saved-scoped');
  assert.match(ports.stdout.text, /added to tests\/place-order\.json as step saved-scoped/);
});

// A changed include list must rebuild the graph, rather than stamp old bytes with a new manifest.
test('SOURCE7: capture retries changed selection metadata and refuses a payload that never becomes stable', t => {
  const setup = harbor(t);
  write(setup.repo, 'docs/a.txt', 'source-stability-marker-a');
  write(setup.repo, 'docs/b.txt', 'source-stability-marker-b');
  json(setup.repo, 'pdd-source.json', { include: ['docs/a.txt'] });
  const original = fs.readFileSync;
  let edits = 0;
  t.after(() => { fs.readFileSync = original; syncBuiltinESMExports(); });
  fs.readFileSync = (...args) => {
    const result = original(...args);
    if (typeof args[0] === 'number' && result.includes('source-stability-marker-a') && edits++ === 0) {
      json(setup.repo, 'pdd-source.json', { include: ['docs/b.txt'] });
    }
    return result;
  };
  syncBuiltinESMExports();
  const captured = captureSource(setup.repo, { tests: [ORDER] });
  assert.deepEqual(names(captured.tar), [PLACE, ORDER, STORY, 'docs/b.txt'].sort());
  assert.equal(edits, 1);
  let churn = 0;
  fs.readFileSync = (...args) => {
    const result = original(...args);
    if (typeof args[0] === 'number' && result.includes('source-stability-marker-b')) write(setup.repo, 'docs/b.txt', `source-stability-marker-b${++churn}`);
    return result;
  };
  syncBuiltinESMExports();
  assert.throws(() => captureSource(setup.repo, { tests: [ORDER] }), /files changed.*3 times/);
  assert.equal(churn, 3);
});

// Check has no screen to draw. A Try must additionally send the map and the screen/action closure it actually uses.
test('SOURCE8: Check ignores an unrelated default map, while Try and its explicit offline preview include map assets', async t => {
  const setup = harbor(t);
  json(setup.repo, 'app-map.json', { schema_version: 'prompt-runtime.app-map.v1', name: 'Bookshelf', screens: [{ prompt_path: 'prompts/not-ready.prompt.md' }] });
  const { ports: first } = offline(setup);
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--files': true } }, first), 0, first.stderr.text);
  assert.doesNotMatch(first.stdout.text, /app-map|not-ready/);
  const { ports: stopped } = offline(setup);
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: {} }, stopped), 4, stopped.stderr.text);
  assert.match(stopped.stderr.text, /app-map\.json.*prompts\/not-ready\.prompt\.md.*not a Git-visible file/);
  prompt(setup.repo, 'prompts/shelf.prompt.md', '# Shelf\n![View](views/shelf.ui.svg)\n## Dependencies\nNone.');
  prompt(setup.repo, 'prompts/books.prompt.md', '# Books\n## Dependencies\nNone.');
  write(setup.repo, 'prompts/views/shelf.ui.svg', '<svg xmlns="http://www.w3.org/2000/svg"/>');
  write(setup.repo, 'app/shelf.css', 'body { color: navy; }');
  json(setup.repo, 'app-map.json', { schema_version: 'prompt-runtime.app-map.v1', name: 'Bookshelf',
    screens: [{ prompt_path: 'prompts/shelf.prompt.md' }], handlers: [{ handler: { prompt_path: 'prompts/books.prompt.md' } }], stylesheets: ['app/shelf.css'] });
  const preview = captureSource(setup.repo, { tests: [ORDER], appMap: 'app-map.json' });
  assert.deepEqual(names(preview.tar), [PLACE, ORDER, STORY, 'app-map.json', 'prompts/shelf.prompt.md', 'prompts/books.prompt.md', 'prompts/views/shelf.ui.svg', 'app/shelf.css'].sort());
  const { ports: listed } = offline(setup);
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--files': true, '--app-map': 'app-map.json' } }, listed), 0, listed.stderr.text);
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.command === 'try') return { status: 200, json: f.tryJob(entry.request.requestId) };
    return { status: 404, json: {} };
  });
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--no-open': true, '--no-wait': true } }, ports), 0, ports.stderr.text);
  assert.equal(fake.posts[1].request.app_map, 'app-map.json');
  for (const post of fake.posts) assert.ok(post.tar.equals(preview.tar));
});
