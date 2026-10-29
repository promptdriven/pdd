import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
import { spawnSync } from 'node:child_process';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { createHash } from 'node:crypto';
import { findTests, selectTests, captureSource, preflight, proseSha256, LIMITS } from '../src/runtime-preflight.mjs';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { portsFor } from './runtime-fake.mjs';

// Native replay of the approved Story's concrete case plans. The Runtime anchor
// is empty (#2548); these finite fixtures do not claim executable Runtime replay.
const CAP = 1_048_576, INSPECTION = 10_485_760;
const CLI = new URL('../bin/pdd.mjs', import.meta.url).pathname;
const hash = bytes => createHash('sha256').update(bytes).digest('hex');
const write = (root, path, text) => { fs.mkdirSync(join(root, path, '..'), { recursive: true }); fs.writeFileSync(join(root, path), text); };
function fixture(t) {
  const sandbox = fs.mkdtempSync(join(tmpdir(), 'pdd-oversized-')), root = join(sandbox, 'repo');
  fs.mkdirSync(root); fs.mkdirSync(join(sandbox, 'home'));
  t.after(() => fs.rmSync(sandbox, { recursive: true, force: true }));
  assert.equal(spawnSync('git', ['init', '-q'], { cwd: root }).status, 0);
  const schema = { type: 'object', properties: { text: { type: 'string' } }, required: ['text'], additionalProperties: false };
  const body = { status: 'draft', prose_sha256: '', entries: [{ operation: 'echo', input_schema: schema, result_schema: schema, errors: [] }], calls: [], resources: [], limits: { max_steps: 1, max_model_calls: 1 }, conventions: [] };
  let prompt = '# Echo\nReturn the supplied text.\n\n<details><summary>Runtime interface</summary>\n\n```json\n' + JSON.stringify(body) + '\n```\n</details>\n';
  body.prose_sha256 = proseSha256(prompt);
  prompt = prompt.replace('"prose_sha256":""', `"prose_sha256":"${body.prose_sha256}"`);
  write(root, 'prompts/echo.prompt.md', prompt);
  function scenario(name, size, text = '') {
    write(root, `user_stories/${name}.md`, `# ${name}\n\n## Acceptance criteria\n\n1. The text is echoed.\n`);
    const doc = { schema_version: 'prompt-runtime.program-scenario.v1', story_path: `user_stories/${name}.md`, criteria: [{ id: 'AC1', text: 'The text is echoed.' }], initial_world: {}, steps: [{ step_id: 'echo', entry_path: 'prompts/echo.prompt.md', operation: 'echo', input: { text }, checks: [{ criterion_id: 'AC1', target: 'result', path: '/text', op: 'equals', value: text }] }] };
    // Whitespace padding is real serialized JSON, without adding unsupported fields.
    const serialized = JSON.stringify(doc);
    const bytes = Buffer.from(serialized + ' '.repeat(size === undefined ? 0 : size - Buffer.byteLength(serialized)));
    materialize(root, `tests/${name}.json`, bytes);
    return `tests/${name}.json`;
  }
  const normal = scenario('normal');
  return { root, normal, scenario };
}
function materialize(root, path, bytes) {
  write(root, path, bytes);
  const disk = fs.readFileSync(join(root, path));
  assert.equal(Buffer.byteLength(disk.toString('utf8'), 'utf8'), bytes.length);
  assert.equal(fs.statSync(join(root, path)).size, bytes.length);
  assert.equal(hash(disk), hash(bytes));
}
function aliases(name) { return [[], [name], [`user_stories/${name}.md`], [`tests/${name}.json`], [`./tests/${name}.json`]]; }
function limit(error, path, size, uncertain = false) {
  assert.equal(error.exitCode, 4);
  assert.ok(error.message.includes(path), error.message);
  assert.ok(error.message.includes(String(size)), error.message);
  assert.match(error.message, /1048576/);
  if (uncertain) assert.match(error.message, /10485760.*|inspection budget/);
  return true;
}
function offline(root) {
  const effects = { auth: 0, network: 0 };
  const { ports } = portsFor({ HOME: join(root, '..', 'home'), PDD_RUNTIME_URL: 'http://127.0.0.1:9' }, {
    gh: () => { effects.auth++; assert.fail('unexpected authentication'); },
    fetch: () => { effects.network++; assert.fail('unexpected network/AI request'); },
  });
  return { ports, effects };
}

test('AC1: real cap-1 and inclusive cap scenarios preserve native aliases and valid preflight', t => {
  const { root, scenario } = fixture(t);
  for (const [name, size] of [['below', CAP - 1], ['equal', CAP]]) {
    scenario(name, size);
    const found = findTests({ root });
    assert.ok(found.visible instanceof Set);
    for (const words of aliases(name)) assert.ok(selectTests(found, words).selected.some(row => row.path === `tests/${name}.json`));
    const selected = selectTests(found, [name]).selected;
    assert.equal(preflight({ root, found, selected }).rows[0].refusals.length, 0);
    assert.ok(captureSource(root, { tests: selected.map(row => row.path) }).files.some(row => row.path === `tests/${name}.json`));
  }
  assert.equal(LIMITS.test, CAP); assert.equal(LIMITS.bytes, INSPECTION); assert.equal(LIMITS.files, 10000);
});

test('AC2/3: mixed default and explicit oversize selection stop check/Try and actual --files before external effects', async t => {
  const { root, scenario } = fixture(t);
  scenario('second'); scenario('third');
  const path = scenario('oversized', CAP + 1), found = findTests({ root });
  for (const words of aliases('oversized')) {
    assert.throws(() => selectTests(found, words), error => limit(error, path, CAP + 1));
    for (const run of [runCheck, runTry]) {
      const { ports, effects } = offline(root);
      assert.equal(await run({ cwd: root, words, options: {} }, ports), 4, ports.stderr.text);
      assert.match(ports.stderr.text, /1048577.*1048576/);
      assert.deepEqual(effects, { auth: 0, network: 0 });
      assert.doesNotMatch(ports.stdout.text, /Stories:.*pass|files,/);
    }
  }
  const { ports, effects } = offline(root);
  assert.equal(await runCheck({ cwd: root, words: ['normal'], options: { '--files': true } }, ports), 0, ports.stderr.text);
  assert.deepEqual(effects, { auth: 0, network: 0 });
  assert.doesNotMatch(ports.stdout.text, /oversized/);
  for (const args of [['check', '--files'], ['check', '--files', 'oversized'], ['try', path]]) {
    const child = spawnSync(process.execPath, [CLI, ...args], { cwd: root, encoding: 'utf8', env: { ...process.env, HOME: join(root, '..', 'home'), PDD_RUNTIME_URL: 'http://127.0.0.1:9' } });
    assert.equal(child.status, 4, child.stderr); assert.match(child.stderr, /1048577.*1048576/);
    assert.doesNotMatch(child.stderr, /Unknown story|sign in/);
  }
  assert.throws(() => captureSource(root, { tests: [path] }), error => limit(error, path, CAP + 1));
  assert.throws(() => captureSource(root), error => limit(error, path, CAP + 1));
  assert.throws(() => preflight({ root, found, selected: found.tests }), error => limit(error, path, CAP + 1));
});

test('AC4: accepted one-MiB ASCII input and multibyte strings use actual serialized bytes', t => {
  const { root, scenario } = fixture(t);
  for (const [name, input] of [['payload', Buffer.alloc(CAP, 65).toString('ascii')], ['unicode', 'é'.repeat(270000)]]) {
    const path = scenario(name, undefined, input), bytes = fs.readFileSync(join(root, path));
    assert.ok(bytes.length > CAP);
    if (name === 'payload') assert.equal(Buffer.byteLength(JSON.parse(bytes).steps[0].input.text), CAP);
    else assert.ok(bytes.toString('utf8').length < CAP);
    assert.throws(() => selectTests(findTests({ root }), [name]), error => limit(error, path, bytes.length));
  }
});

test('AC5/6: full-document top-level late/duplicate identity wins and data markers are ignored', t => {
  const { root } = fixture(t);
  const pad = 'A'.repeat(CAP + 100);
  const cases = [
    ['late', `{"data":"${pad}","schema_version":"prompt-runtime.program-scenario.v1","story_path":"user_stories/late.md"}`, 'late'],
    ['last-scenario', `{"schema_version":"data","story_path":"user_stories/old.md","data":"${pad}","schema_version":"prompt-runtime.program-scenario.v1","story_path":"user_stories/new.md"}`, 'new'],
    ['last-data', `{"schema_version":"prompt-runtime.program-scenario.v1","data":"${pad}","schema_version":"data"}`, null],
    ['last-story', `{"schema_version":"prompt-runtime.program-scenario.v1","story_path":"user_stories/old.md","data":"${pad}","story_path":"user_stories/new.md"}`, 'new'],
    ['decoy', JSON.stringify({ data: pad, nested: { schema_version: 'prompt-runtime.program-scenario.v1' }, text: '{"schema_version":"prompt-runtime.program-scenario.v1"}' }), null],
  ];
  for (const [name, text, story] of cases) {
    const path = `data/${name}.json`; materialize(root, path, Buffer.from(text));
    const found = findTests({ root }), row = found.tests.find(row => row.path === path);
    if (story) {
      assert.equal(row.story, story);
      assert.throws(() => selectTests(found, [story]), error => limit(error, path, Buffer.byteLength(text)));
    } else assert.equal(row, undefined);
  }
  assert.deepEqual(selectTests(findTests({ root }), ['absent']).unknown, ['absent']);
});

test('AC6: unrelated object data above execution cap can be included under unchanged source limits', async t => {
  const { root, normal } = fixture(t);
  for (const [name, size] of [['one-over', CAP + 1], ['data', 1_363_148]]) {
    const prefix = '{"text":"', suffix = '"}';
    materialize(root, `${name}.json`, Buffer.from(prefix + 'A'.repeat(size - prefix.length - suffix.length) + suffix));
  }
  const found = findTests({ root }); assert.equal(found.tests.length, 1);
  write(root, 'pdd-source.json', JSON.stringify({ include: ['one-over.json', 'data.json'] }));
  const capture = captureSource(root, { tests: [normal] });
  assert.ok(capture.files.some(row => row.path === 'one-over.json' && row.size === CAP + 1));
  assert.ok(capture.files.some(row => row.path === 'data.json' && row.size === 1_363_148));
  assert.ok(capture.tar.length < INSPECTION);
  const { ports } = offline(root);
  assert.equal(await runCheck({ cwd: root, words: [], options: { '--files': true } }, ports), 0, ports.stderr.text);
});

test('AC7: inspection budget inclusive; partial objects stay uncertain despite early schema or Story', async t => {
  const { root } = fixture(t);
  const object = (size, prefix, suffix) => Buffer.from(prefix + ' '.repeat(size - Buffer.byteLength(prefix + suffix)) + suffix);
  const exact = object(INSPECTION, '{"data":0,', '"schema_version":"prompt-runtime.program-scenario.v1","story_path":"user_stories/exact.md"}');
  materialize(root, 'exact.json', exact);
  assert.equal(findTests({ root }).tests.find(row => row.path === 'exact.json').story, 'exact');
  fs.unlinkSync(join(root, 'exact.json'));
  for (const prefix of ['{"data":0,', '{"schema_version":"data",', '{"schema_version":"prompt-runtime.program-scenario.v1","story_path":"user_stories/early.md",']) {
    const bytes = object(INSPECTION + 1, prefix, '"schema_version":"prompt-runtime.program-scenario.v1","story_path":"user_stories/hidden.md"}');
    materialize(root, 'huge.json', bytes);
    const found = findTests({ root }), row = found.tests.find(row => row.path === 'huge.json');
    assert.ok(row.uncertain); assert.equal(row.storyPath, null);
    for (const words of [[], ['huge.json'], ['huge'], ['hidden'], ['user_stories/hidden.md']]) assert.throws(() => selectTests(found, words), error => limit(error, 'huge.json', bytes.length, true));
    assert.equal(selectTests(found, ['normal']).selected.length, 1);
    const { ports, effects } = offline(root);
    assert.equal(await runCheck({ cwd: root, words: ['hidden'], options: { '--files': true } }, ports), 4, ports.stderr.text);
    assert.match(ports.stderr.text, /10485760/); assert.doesNotMatch(ports.stderr.text, /Unknown story/);
    assert.deepEqual(effects, { auth: 0, network: 0 });
  }
  fs.unlinkSync(join(root, 'huge.json'));
  materialize(root, 'array.json', object(INSPECTION + 1, '[', ']'));
  assert.equal(findTests({ root }).tests.length, 1);
  const { ports } = offline(root);
  assert.equal(await runCheck({ cwd: root, words: ['absent'], options: {} }, ports), 2);
  assert.match(ports.stderr.text, /Unknown story/);
  materialize(root, 'whitespace.json', Buffer.from(' '.repeat(INSPECTION + 1)));
  assert.throws(() => selectTests(findTests({ root })), error => limit(error, 'whitespace.json', INSPECTION + 1, true));
});

test('AC8: discovery refuses symlinks, ancestors, unreadable and unstable snapshots with bounded descriptor reads', t => {
  const { root } = fixture(t);
  write(root, 'outside/object.json', '{"data":1}');
  fs.symlinkSync('outside/object.json', join(root, 'link.json'));
  assert.throws(() => selectTests(findTests({ root })), /unsafe.*symbolic link/);
  fs.unlinkSync(join(root, 'link.json'));
  fs.symlinkSync('outside', join(root, 'ancestor'));
  const ancestor = findTests({ root, files: ['ancestor/object.json'] });
  assert.throws(() => selectTests(ancestor), /symbolic link ancestor/);
  fs.unlinkSync(join(root, 'ancestor'));
  const originalOpen = fs.openSync, originalRead = fs.readSync;
  t.after(() => { fs.openSync = originalOpen; fs.readSync = originalRead; syncBuiltinESMExports(); });
  fs.openSync = (path, ...args) => { if (String(path).endsWith('/normal.json')) throw Object.assign(new Error('denied'), { code: 'EACCES' }); return originalOpen(path, ...args); };
  syncBuiltinESMExports();
  assert.throws(() => selectTests(findTests({ root })), /normal.json.*unreadable.*EACCES/);
  fs.openSync = originalOpen; syncBuiltinESMExports();
  let changed = false;
  fs.readSync = (fd, buffer, offset, length, position) => {
    const count = originalRead(fd, buffer, offset, length, position);
    if (!changed) { changed = true; fs.appendFileSync(join(root, 'tests/normal.json'), ' '); }
    return count;
  };
  syncBuiltinESMExports();
  assert.throws(() => selectTests(findTests({ root, files: ['tests/normal.json'] })), error => error.exitCode === 5 && /changed during discovery/.test(error.message));
  fs.readSync = originalRead; syncBuiltinESMExports();
  materialize(root, 'huge.json', Buffer.from('{"data":"' + 'A'.repeat(INSPECTION) + '"}'));
  let readBytes = 0;
  fs.readSync = (...args) => { readBytes += args[3]; return originalRead(...args); }; syncBuiltinESMExports();
  const found = findTests({ root, files: ['huge.json'] });
  assert.ok(found.tests[0].uncertain); assert.ok(readBytes > 0 && readBytes <= 65_536);
});
