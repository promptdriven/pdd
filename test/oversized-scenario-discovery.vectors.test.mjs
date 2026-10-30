import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
import { spawnSync } from 'node:child_process';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { createHash } from 'node:crypto';
import { findTests, selectTests, captureSource, preflight, proseSha256, whyNoTests, LIMITS } from '../src/runtime-preflight.mjs';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { portsFor } from './runtime-fake.mjs';

// Native replay of the approved Story's concrete case plans. The Runtime anchor
// is empty (#2548); these finite fixtures do not claim executable Runtime replay.
const CAP = 1_048_576, INSPECTION = 10_485_760, PREFIX = 65_536;
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
function limit(error, path, size) {
  assert.equal(error.exitCode, 4);
  assert.ok(error.message.includes(path), error.message);
  assert.ok(error.message.includes(String(size)), error.message);
  assert.match(error.message, /1048576/);
  assert.match(error.message, /PDD test/);
  assert.match(error.message, /split it into smaller test files/);
  assert.doesNotMatch(error.message, /uncertain|inspection budget/i);
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
      assert.match(ports.stderr.text, /PDD test.*split it into smaller test files/);
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
    assert.match(child.stderr, /PDD test.*split it into smaller test files/);
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

test('AC1/5/6: normal full-document identity and oversized prefix identity use their respective last values', t => {
  const { root } = fixture(t);
  const family = 'prompt-runtime.program-scenario.v1';
  for (const padding of [500, CAP + 100]) {
    const pad = 'A'.repeat(padding), oversized = padding > CAP;
    // Expected aliases are from the approved D2 table, before execution.
    const cases = [
      ['late', `{"data":"${pad}","schema_version":"${family}","story_path":"user_stories/late.md"}`, oversized ? null : 'late'],
      ['last-scenario', `{"schema_version":"data","story_path":"user_stories/old.md","data":"${pad}","schema_version":"${family}","story_path":"user_stories/new.md"}`, oversized ? null : 'new'],
      ['last-data', `{"schema_version":"${family}","data":"${pad}","schema_version":"data"}`, oversized ? 'last-data' : null],
      ['last-story', `{"schema_version":"${family}","story_path":"user_stories/old.md","data":"${pad}","story_path":"user_stories/new.md"}`, oversized ? 'old' : 'new'],
      ['decoy', JSON.stringify({ data: pad, nested: { schema_version: family }, text: `{"schema_version":"${family}"}` }), null],
    ];
    for (const [name, text, story] of cases) {
      const path = `data/${name}.json`; materialize(root, path, Buffer.from(text));
      const found = findTests({ root }), row = found.tests.find(row => row.path === path);
      if (story) {
        assert.equal(row.story, story);
        if (oversized) assert.throws(() => selectTests(found, [story]), error => limit(error, path, Buffer.byteLength(text)));
        else assert.ok(selectTests(found, [story]).selected.includes(row));
      } else assert.equal(row, undefined);
      fs.unlinkSync(join(root, path));
    }
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

test('AC2/5/7: early declarations above 10 MiB survive unseen duplicates and truncated bodies; hidden aliases stay unknown', async t => {
  const { root } = fixture(t);
  const prefix = '{"schema_version":"prompt-runtime.program-scenario.v9","story_path":"user_stories/early.md","data":"';
  for (const suffix of ['","schema_version":"ordinary.v1","story_path":"user_stories/hidden.md"}', '']) {
    const bytes = Buffer.from(prefix + 'A'.repeat(INSPECTION + 1 - Buffer.byteLength(prefix + suffix)) + suffix);
    materialize(root, 'huge.json', bytes);
    const found = findTests({ root }), row = found.tests.find(row => row.path === 'huge.json');
    assert.equal(row.storyPath, 'user_stories/early.md');
    assert.equal(row.uncertain, undefined);
    for (const words of [[], ['huge.json'], ['huge'], ['early'], ['user_stories/early.md']])
      assert.throws(() => selectTests(found, words), error => limit(error, 'huge.json', bytes.length));
    for (const words of [['hidden'], ['user_stories/hidden.md'], ['never-authored']]) {
      assert.deepEqual(selectTests(found, words).unknown, words);
      const { ports, effects } = offline(root);
      assert.equal(await runCheck({ cwd: root, words, options: { '--files': true } }, ports), 2, ports.stderr.text);
      assert.match(ports.stderr.text, /Unknown story/);
      assert.deepEqual(effects, { auth: 0, network: 0 });
    }
    assert.equal(selectTests(found, ['normal']).selected.length, 1);
  }
});

test('AC8: synthetic ancestor input, unreadable and unstable snapshots retain bounded safety guards', t => {
  const { root } = fixture(t);
  write(root, 'outside/object.json', '{"data":1}');
  fs.symlinkSync('outside/object.json', join(root, 'link.json'));
  assert.deepEqual(selectTests(findTests({ root })).selected.map(row => row.path), ['tests/normal.json']);
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
  assert.deepEqual(found.tests, []); assert.equal(readBytes, PREFIX);
});

test('AC8: small nonregular JSON is skipped without opening links or FIFOs; selected payloads still refuse', t => {
  const { root, normal } = fixture(t);
  // The link's own size controls discovery, even when its target is oversized.
  materialize(root, 'outside/large.data', Buffer.alloc(CAP + 1, 65));
  fs.symlinkSync('outside/large.data', join(root, 'tsconfig.json'));
  fs.symlinkSync('missing-target', join(root, 'dangling.json'));
  assert.equal(spawnSync('mkfifo', [join(root, 'pipe.json')]).status, 0);
  const originalOpen = fs.openSync, opened = [];
  t.after(() => { fs.openSync = originalOpen; syncBuiltinESMExports(); });
  fs.openSync = (path, ...args) => { opened.push(String(path)); return originalOpen(path, ...args); };
  syncBuiltinESMExports();
  const found = findTests({ root });
  assert.deepEqual(selectTests(found).selected.map(row => row.path), [normal]);
  assert.deepEqual(selectTests(found, ['typo']).unknown, ['typo']);
  assert.ok(!opened.some(path => /(?:tsconfig\.json|dangling\.json|pipe\.json|large\.data)$/.test(path)), opened.join('\n'));
  fs.openSync = originalOpen; syncBuiltinESMExports();
  for (const path of ['tsconfig.json', 'dangling.json', 'pipe.json']) {
    write(root, 'pdd-source.json', JSON.stringify({ include: [path] }));
    assert.throws(() => captureSource(root, { tests: [normal] }), error => error.exitCode === 4);
  }
  fs.unlinkSync(join(root, 'pdd-source.json'));
  fs.appendFileSync(join(root, 'prompts/echo.prompt.md'), '\n## Dependencies\n\n[Config](../tsconfig.json)\n');
  assert.throws(() => captureSource(root, { tests: [normal] }), error => error.exitCode === 4);
});

test('AC8: real offline CLI preserves default Check/Try, --files, unknown Story and no-tests guidance', t => {
  const { root, normal } = fixture(t);
  write(root, 'config/base.json', '{"compilerOptions":{}}');
  fs.symlinkSync('config/base.json', join(root, 'tsconfig.json'));
  fs.symlinkSync('missing-target', join(root, 'dangling.json'));
  assert.equal(spawnSync('mkfifo', [join(root, 'pipe.json')]).status, 0);
  const bin = join(root, '..', 'bin'), marker = join(root, '..', 'auth-attempts');
  fs.mkdirSync(bin);
  // Deterministic auth boundary: no token or network access is possible.
  write(bin, 'gh', '#!/bin/sh\nprintf "auth\\n" >> "$PDD_TEST_AUTH_LOG"\nexit 1\n');
  fs.chmodSync(join(bin, 'gh'), 0o755);
  const env = { HOME: join(root, '..', 'home'), PATH: `${bin}:/usr/bin:/bin`, PDD_RUNTIME_URL: 'http://127.0.0.1:9', PDD_TEST_AUTH_LOG: marker };
  const cli = args => {
    const child = spawnSync(process.execPath, [CLI, ...args], { cwd: root, encoding: 'utf8', env, timeout: 10000 });
    assert.equal(child.error, undefined, String(child.error));
    assert.doesNotMatch(child.stderr, /unsafe discovery|unreadable discovery/);
    return child;
  };
  const files = cli(['check', '--files']);
  assert.equal(files.status, 0, files.stderr); assert.match(files.stdout, /tests\/normal\.json/);
  assert.equal(fs.existsSync(marker), false);
  for (const command of ['check', 'try']) {
    const child = cli([command]);
    assert.equal(child.status, 5, child.stderr); assert.match(child.stderr, /gh auth login/);
  }
  assert.equal(fs.readFileSync(marker, 'utf8').trim().split('\n').length, 2);
  for (const args of [['check', 'typo'], ['check', '--files', 'typo'], ['try', 'typo']]) {
    const child = cli(args); assert.equal(child.status, 2, child.stderr); assert.match(child.stderr, /Unknown story/);
  }
  fs.unlinkSync(join(root, normal));
  for (const args of [['check'], ['check', '--files'], ['try']]) {
    const child = cli(args); assert.equal(child.status, 2, child.stderr); assert.match(child.stderr, /No tests found/);
  }
  assert.equal(fs.readFileSync(marker, 'utf8').trim().split('\n').length, 2);
});

test('AC8: inclusive own-metadata nonregular boundary does not relax oversized safety', t => {
  const { root } = fixture(t);
  fs.symlinkSync('missing-target', join(root, 'link.json'));
  const originalStat = fs.lstatSync;
  t.after(() => { fs.lstatSync = originalStat; syncBuiltinESMExports(); });
  // Host link lengths cannot reach 1 MiB: supply only that metadata boundary.
  for (const size of [CAP - 1, CAP, CAP + 1]) {
    fs.lstatSync = (path, ...args) => {
      const stat = originalStat(path, ...args);
      if (String(path).endsWith('/link.json')) stat.size = BigInt(size);
      return stat;
    };
    syncBuiltinESMExports();
    const found = findTests({ root });
    if (size <= CAP) assert.deepEqual(selectTests(found).selected.map(row => row.path), ['tests/normal.json']);
    else assert.throws(() => selectTests(found), error => error.exitCode === 4 && /unsafe discovery/.test(error.message));
  }
});

// These expectations are the D2 contract's lexical table, independent of output.
const FAMILY = 'prompt-runtime.program-scenario.v1';
const declaration = `"schema_version":"${FAMILY}"`;
const oversizedBytes = (prefix, suffix = '', size = CAP + 1) =>
  Buffer.from(prefix + ' '.repeat(size - Buffer.byteLength(prefix + suffix)) + suffix);
const atPrefixEnd = (tail, end = PREFIX) => '{' + ' '.repeat(end - 1 - Buffer.byteLength(tail)) + tail;

test('AC5: complete prefix declarations decode escapes and ignore root, string, nested and trailing decoys', t => {
  const { root } = fixture(t);
  const cases = [
    ['escaped', '{"schema_vers\\u0069on":"prompt-runtime.program-\\u0073cenario.v1"}', true],
    ['not-first', `{"first":1,"nested":[{"text":"\\\"}[,]"}],${declaration}}`, true],
    ['unsupported', '{"schema_version":"prompt-runtime.program-scenario.v999"}', true],
    ['truncated-body', `{${declaration},"data":"`, true],
    ['nested', `{"nested":{${declaration}}}`, false],
    ['string', JSON.stringify({ text: `\\"},${declaration},"story_path":"fake"` }), false],
    ['array', `[{${declaration}}]`, false],
    ['trailing', `{} {${declaration}}`, false],
    ['ordinary-trailing', `{"schema_version":"ordinary.v1"},{${declaration}}`, false],
    ['absent', '{"data":1}', false],
    ['ordinary', '{"schema_version":"ordinary.v1"}', false],
    ['whitespace', ' ', false],
    ['literal-root', 'null', false],
    ['string-root', JSON.stringify(`{${declaration}}`), false],
  ];
  for (const [name, prefix, detected] of cases) {
    const path = `tests/${name}.json`, bytes = oversizedBytes(prefix);
    materialize(root, path, bytes);
    const found = findTests({ root });
    assert.equal(found.tests.some(row => row.path === path), detected, name);
    if (detected) assert.throws(() => selectTests(found, [path]), error => limit(error, path, bytes.length));
    else assert.deepEqual(selectTests(found, [path]).unknown, [path], name);
    fs.unlinkSync(join(root, path));
  }
});

test('AC5: last complete schema duplicate wins, including nonstrings; incomplete duplicates retain prior identity', t => {
  const { root } = fixture(t);
  const cases = [
    ['family-ordinary', `{${declaration},"schema_version":"ordinary.v1"}`, false],
    ['ordinary-family', `{"schema_version":"ordinary.v1",${declaration}}`, true],
    ...['null', 'false', 'true', '1', '-1.5e2', '[]', '{}', '[{"schema_version":"nested"}]'].flatMap((value, i) => [
      [`family-nonstring-${i}`, `{${declaration},"schema_version":${value}}`, false],
      [`nonstring-family-${i}`, `{"schema_version":${value},${declaration}}`, true],
    ]),
    ['incomplete-key', `{${declaration},"schema_ver`, true],
    ['incomplete-string', `{${declaration},"schema_version":"ordinary`, true],
    ['incomplete-array', `{${declaration},"schema_version":[`, true],
    ['incomplete-object', `{${declaration},"schema_version":{"nested":`, true],
    ['incomplete-literal', `{${declaration},"schema_version":fals`, true],
    ['incomplete-number', `{${declaration},"schema_version":1e`, true],
  ];
  for (const [name, prefix, detected] of cases) {
    const path = 'case.json', bytes = oversizedBytes(prefix);
    materialize(root, path, bytes);
    const found = findTests({ root });
    assert.equal(found.tests.some(row => row.path === path), detected, name);
    if (detected) assert.throws(() => selectTests(found, ['case']), error => limit(error, path, bytes.length));
    else assert.deepEqual(selectTests(found, ['case']).unknown, ['case'], name);
  }
});

test('AC5: exact 65536-byte token completion, one-byte cuts and scalar delimiters decide only visible values', t => {
  const { root } = fixture(t);
  const complete = atPrefixEnd(declaration);
  assert.equal(Buffer.byteLength(complete), PREFIX);
  const cases = [
    ['string-exact', Buffer.from(complete), true],
    ['string-one-over', Buffer.from('{ ' + complete.slice(1)), false],
    ['cut-escape', Buffer.from(atPrefixEnd('"schema_version":"prompt-runtime.program-scenario\\u00')), false],
    ['cut-key', Buffer.from(atPrefixEnd('"schema_vers\\u00')), false],
    ['cut-utf8', Buffer.from(atPrefixEnd('"schema_version":"prompt-runtime.program-scenario', PREFIX - 1) + 'é'), false],
    ['prior-cut-utf8', Buffer.from(atPrefixEnd(`${declaration},"schema_version":"`, PREFIX - 1) + 'é'), true],
    ...['null', 'false', '1', '-1.5e2'].flatMap((value, i) => [
      [`scalar-no-delimiter-${i}`, Buffer.from(atPrefixEnd(`${declaration},"schema_version":${value}`)), true],
      [`scalar-delimiter-${i}`, Buffer.from(atPrefixEnd(`${declaration},"schema_version":${value} `)), false],
    ]),
    ['container-exact', Buffer.from(atPrefixEnd(`${declaration},"schema_version":[]`)), false],
    ['container-one-over', Buffer.from(atPrefixEnd(`${declaration},"schema_version":[ `) + ']'), true],
    ['incomplete-family-retains-ordinary', Buffer.from(atPrefixEnd(`"schema_version":"ordinary.v1",${declaration}`).slice(0, -1) + ' '), false],
  ];
  for (const [name, prefix, detected] of cases) {
    const path = 'boundary.json';
    // Preserve byte cuts (including half of a UTF-8 sequence), not string length.
    const bytes = Buffer.concat([prefix, Buffer.alloc(CAP + 1 - prefix.length, 32)]);
    materialize(root, path, bytes);
    const found = findTests({ root });
    assert.equal(found.tests.some(row => row.path === path), detected, name);
    if (detected) assert.throws(() => selectTests(found, ['boundary']), error => limit(error, path, bytes.length));
    else assert.deepEqual(selectTests(found, ['boundary']).unknown, ['boundary'], name);
  }
});

test('AC3/5/7: Story aliases use only the last complete prefix value independently of schema', t => {
  const { root } = fixture(t);
  const storyA = '"story_path":"user_stories/first.md"';
  const cases = [
    ['last-string', `${storyA},"story_path":"user_stories/last.md"}`, 'last'],
    ['escaped-story', '"story_p\\u0061th":"user_stories/esc\\u0061ped.md"}', 'escaped'],
    ['incomplete-string', `${storyA},"story_path":"user_stories/hidden`, 'first'],
    ['incomplete-container', `${storyA},"story_path":[`, 'first'],
    ...['null', 'false', '0', '[]', '{}'].map((value, i) => [`nonstring-${i}`, `${storyA},"story_path":${value}}`, null]),
    ['no-story', '"data":0}', null],
  ];
  for (const [name, tail, expected] of cases) {
    const path = 'different-basename.json', bytes = oversizedBytes(`{${declaration},${tail}`);
    materialize(root, path, bytes);
    const found = findTests({ root }), row = found.tests.find(row => row.path === path);
    assert.equal(row.storyPath, expected ? `user_stories/${expected}.md` : null, name);
    for (const words of [[path], ['different-basename'], ...(expected ? [[expected], [`user_stories/${expected}.md`]] : [])])
      assert.throws(() => selectTests(found, words), error => limit(error, path, bytes.length));
    for (const word of ['first', 'last', 'escaped', 'hidden', 'never-authored'].filter(word => word !== expected))
      assert.deepEqual(selectTests(found, [word]).unknown, [word], name);
    assert.deepEqual(selectTests(found, ['normal']).selected.map(row => row.path), ['tests/normal.json']);
  }
});

test('AC6/7: every oversized range silently skips absent or non-PDD identity in normal and no-tests native CLI', t => {
  const { root, normal } = fixture(t);
  for (const size of [CAP + 1, INSPECTION + 1]) {
    for (const [name, prefix, suffix] of [
      ['absent', '{"data":"', '"}'],
      ['ordinary', '{"schema_version":"ordinary.v1","data":"', '"}'],
      ['late', '{"data":"', `",${declaration}}`],
      ['nested', `{"nested":{${declaration}},"data":"`, '"}'],
      ['string', '{"text":' + JSON.stringify(`{${declaration}}`) + ',"data":"', '"}'],
      ['array', '["', `",{${declaration}}]`],
    ]) {
      materialize(root, `tests/${name}-${size}.json`, oversizedBytes(prefix, suffix, size));
    }
  }
  const bin = join(root, '..', 'bin'), marker = join(root, '..', 'auth-attempts');
  fs.mkdirSync(bin);
  write(bin, 'gh', '#!/bin/sh\nprintf "auth\\n" >> "$PDD_TEST_AUTH_LOG"\nexit 1\n');
  fs.chmodSync(join(bin, 'gh'), 0o755);
  const env = { HOME: join(root, '..', 'home'), PATH: `${bin}:/usr/bin:/bin`, PDD_RUNTIME_URL: 'http://127.0.0.1:9', PDD_TEST_AUTH_LOG: marker };
  const cli = args => {
    const child = spawnSync(process.execPath, [CLI, ...args], { cwd: root, encoding: 'utf8', env, timeout: 10000 });
    assert.equal(child.error, undefined);
    assert.doesNotMatch(child.stdout + child.stderr, /uncertain|inspection budget|tests\/(?:absent|ordinary|late|nested|string|array)-/i);
    return child;
  };
  for (const words of [[], ['normal']]) {
    const child = cli(['check', '--files', ...words]);
    assert.equal(child.status, 0, child.stderr); assert.match(child.stdout, /tests\/normal.json/);
  }
  assert.equal(fs.existsSync(marker), false);
  for (const command of ['check', 'try']) {
    const child = cli([command]);
    assert.equal(child.status, 5, child.stderr); assert.match(child.stderr, /gh auth login/);
  }
  assert.equal(fs.readFileSync(marker, 'utf8').trim().split('\n').length, 2);
  for (const args of [['check', 'never-authored'], ['check', '--files', 'never-authored'], ['try', 'never-authored']]) {
    const child = cli(args); assert.equal(child.status, 2, child.stderr); assert.match(child.stderr, /Unknown story/);
  }
  fs.unlinkSync(join(root, normal));
  write(root, 'tests/small-data.json', '{"data":1}');
  for (const args of [['check'], ['check', '--files'], ['try']]) {
    const child = cli(args); assert.equal(child.status, 2, child.stderr);
    assert.match(child.stderr, /No tests found/);
    assert.match(child.stderr, /tests\/small-data.json is not a PDD test file/);
    assert.doesNotMatch(child.stderr, /gh auth|sign in/);
  }
  assert.equal(fs.readFileSync(marker, 'utf8').trim().split('\n').length, 2);
});

test('AC6/8: discovery reads only bytes [0,65536) at cap+1 and above 10 MiB; no-tests guidance never rereads skipped JSON', async t => {
  const { root, normal } = fixture(t);
  fs.unlinkSync(join(root, normal));
  const paths = [];
  for (const size of [CAP + 1, INSPECTION + 1]) {
    const path = `tests/large-${size}.json`;
    materialize(root, path, oversizedBytes('{"data":"', '"}', size)); paths.push(path);
  }
  const originalOpen = fs.openSync, originalRead = fs.readSync, originalReadFile = fs.readFileSync;
  const descriptors = new Map(), reads = new Map();
  t.after(() => { fs.openSync = originalOpen; fs.readSync = originalRead; fs.readFileSync = originalReadFile; syncBuiltinESMExports(); });
  fs.openSync = (path, ...args) => {
    const fd = originalOpen(path, ...args);
    descriptors.set(fd, paths.find(file => String(path) === join(root, file)));
    return fd;
  };
  fs.readSync = (fd, buffer, offset, length, position) => {
    const path = descriptors.get(fd);
    if (path) {
      assert.ok(position >= 0 && position + length <= PREFIX, `${path}: ${position}+${length}`);
      reads.set(path, (reads.get(path) ?? 0) + length);
    }
    return originalRead(fd, buffer, offset, length, position);
  };
  fs.readFileSync = (path, ...args) => {
    assert.ok(!paths.some(file => String(path) === join(root, file)), `unbounded read: ${path}`);
    return originalReadFile(path, ...args);
  };
  syncBuiltinESMExports();
  const found = findTests({ root });
  assert.deepEqual(found.tests, []);
  for (const path of paths) assert.equal(reads.get(path), PREFIX, path);
  assert.deepEqual(whyNoTests(root, found.visible), []);
  for (const path of paths) assert.equal(reads.get(path), PREFIX, `no-tests reread ${path}`);
  for (const run of [runCheck, runTry]) {
    reads.clear();
    const { ports, effects } = offline(root);
    assert.equal(await run({ cwd: root, words: [], options: {} }, ports), 2, ports.stderr.text);
    assert.match(ports.stderr.text, /No tests found/);
    assert.doesNotMatch(ports.stderr.text, /large-|not a PDD test/);
    assert.deepEqual(effects, { auth: 0, network: 0 });
    for (const path of paths) assert.equal(reads.get(path), PREFIX, path);
  }
});
