import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { pathToFileURL } from 'node:url';
import { createHash } from 'node:crypto';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { temp, fakeRuntime, portsFor } from './runtime-fake.mjs';

// The optional test-only module selects the old capture boundary for the
// mutation control. It does not change production module loading or requests.
const preflight = await import(process.env.PDD803_PREFLIGHT_MODULE
  ? pathToFileURL(process.env.PDD803_PREFLIGHT_MODULE).href : '../src/runtime-preflight.mjs');
const { captureSource, interfaceBlocks, proseSha256, readPrompt, gitFiles } = preflight;
const SUBJECT = 'prompts/subject.prompt.md', STORY = 'user_stories/echo.md', SCENARIO = 'tests/echo.json';
const criterion = 'The selected operation returns the supplied text.';
const schema = { type: 'object', properties: { text: { type: 'string' } }, required: ['text'], additionalProperties: false };
const declaration = kind => ({ ...(kind === undefined ? {} : { kind }), status: 'draft', prose_sha256: '',
  entries: [{ operation: 'echo', input_schema: structuredClone(schema), result_schema: structuredClone(schema), errors: [] }], calls: [], resources: [], limits: { max_steps: 1, max_model_calls: 1 } });
const block = body => '<details><summary>Runtime interface</summary>\n```json\n' + body + '\n```\n</details>\n';
const textFor = body => {
  let text = '# Echo and uppercase\n\nEcho returns the supplied text. Uppercase returns it in uppercase. Only echo is declared here.\n\n' + block(body);
  return text.replace(/"prose_sha256"\s*:\s*""/, '"prose_sha256":"' + proseSha256(text) + '"');
};
function write(root, path, value) { mkdirSync(join(root, path, '..'), { recursive: true }); writeFileSync(join(root, path), value); }
function fixture(t, kind = 'partial') {
  const root = join(temp(t), 'repo');
  write(root, SUBJECT, textFor(JSON.stringify(declaration(kind))));
  write(root, STORY, '# Check echo\n\nAs a person, I want to check the selected operation.\n\n## Acceptance criteria\n\n1. ' + criterion + '\n');
  write(root, SCENARIO, JSON.stringify({ schema_version: 'prompt-runtime.program-scenario.v1', story_path: STORY,
    criteria: [{ id: 'AC1', text: criterion }], initial_world: {}, simulation: {}, context: [], steps: [{ step_id: 'echo',
      entry_path: SUBJECT, operation: 'echo', input: { text: 'hello' }, checks: [{ criterion_id: 'AC1', target: 'result', path: '/text', op: 'equals', value: 'hello' }] }] }));
  const init = spawnSync('git', ['init', '-q'], { cwd: root, encoding: 'utf8' }); assert.equal(init.status, 0, init.stderr);
  return root;
}
const capture = (root, options = {}) => captureSource(root, { tests: [SCENARIO], ...options });
const source = (captured, path = SUBJECT) => captured.sources.find(file => file.path === path).bytes.toString('utf8');
const iface = text => JSON.parse(interfaceBlocks(text)[0][1]);
const digest = bytes => createHash('sha256').update(bytes).digest('hex');
function projected(root, captured = capture(root), expectedText = readFileSync(join(root, SUBJECT), 'utf8')) {
  const raw = readFileSync(join(root, SUBJECT), 'utf8'), uploaded = source(captured);
  const wanted = iface(expectedText); delete wanted.kind;
  assert.equal(Object.hasOwn(iface(uploaded), 'kind'), false, 'PDD bookkeeping kind must not enter executable Runtime interface');
  assert.deepEqual(iface(uploaded), wanted, 'retain every executable declaration');
  assert.equal(captured.raw_prompt_hashes[SUBJECT], digest(Buffer.from(raw)));
  assert.equal(captured.files.find(file => file.path === SUBJECT).size, Buffer.byteLength(uploaded));
  assert.equal(captured.sha256, digest(captured.tar));
  const unpacked = spawnSync('tar', ['-xOf', '-', SUBJECT], { input: captured.tar }); assert.equal(unpacked.status, 0);
  assert.equal(unpacked.stdout.toString(), uploaded);
  return uploaded;
}
const checks = [{ criterion_id: 'AC1', target: 'result', path: '/text', op: 'equals', expected: 'hello', actual: 'hello', passed: true }];
function fakePorts(root, fake) {
  return portsFor({ HOME: join(root, '..', 'home'), PDD_STATE_DIR: join(root, '..', 'state'), PDD_RUNTIME_URL: fake.origin }, {
    captureSource,
  }).ports;
}
async function transport(t) {
  const fake = await fakeRuntime(t, entry => {
    if (entry.command) {
      const unpacked = spawnSync('tar', ['-xOf', '-', SUBJECT], { input: entry.tar }); assert.equal(unpacked.status, 0);
      assert.equal(Object.hasOwn(iface(unpacked.stdout.toString()), 'kind'), false, 'server accepts executable declarations without PDD metadata');
      assert.equal(entry.request.source_sha256, digest(entry.tar));
    }
    if (entry.command === 'lint') return { status: 200, json: fake.lint(entry.request.requestId, [{ path: SUBJECT, state: 'draft', admission_state: 'draft', interface: { calls: [] } }]) };
    if (entry.command === 'try') return { status: 200, json: fake.tryJob(entry.request.requestId) };
    return { status: 200, json: fake.check(entry.request?.requestId ?? entry.url.split('/').at(-1), 'passed', checks) };
  });
  return fake;
}
const actions = {
  'partial-upload'(t) {
    const root = fixture(t), raw = readFileSync(join(root, SUBJECT));
    const captured = capture(root), uploaded = projected(root, captured);
    assert.equal(iface(uploaded).entries.length, 1);
    assert.equal(readPrompt(root, new Set(gitFiles(root)), SUBJECT).interface.kind, 'partial');
    assert.deepEqual(readFileSync(join(root, SUBJECT)), raw);
    assert.deepEqual(JSON.parse(source(captured, SCENARIO)).steps[0].input, { text: 'hello' });
    assert.equal(JSON.parse(source(captured, SCENARIO)).steps[0].checks[0].value, 'hello');
  },
  'explicit-full-and-legacy'(t) {
    const root = fixture(t, 'full'); projected(root);
    write(root, SUBJECT, textFor(JSON.stringify(declaration(undefined))));
    const raw = readFileSync(join(root, SUBJECT)), first = capture(root), second = capture(root);
    assert.deepEqual(first.sources.find(file => file.path === SUBJECT).bytes, raw);
    assert.deepEqual(first.tar, second.tar);
  },
  'json-member-position'(t) {
    const root = fixture(t);
    for (const kind of ['full', 'partial']) for (const position of ['first', 'middle', 'last']) for (const newline of ['', '\n', '\r\n']) for (const key of ['"kind"', '"\\u006bind"']) {
      const members = Object.entries(declaration(undefined)).map(([k, value]) => JSON.stringify(k) + ':' + JSON.stringify(value));
      const index = position === 'first' ? 0 : position === 'last' ? members.length : 3;
      members.splice(index, 0, key + ' : "' + kind + '"');
      const body = '{' + newline + members.join(',' + newline) + newline + '}';
      const raw = textFor(body); write(root, SUBJECT, raw);
      const uploaded = projected(root);
      const originalBody = interfaceBlocks(raw)[0][1], actualBody = interfaceBlocks(uploaded)[0][1];
      const marker = key + ' : "' + kind + '"', start = originalBody.indexOf(marker), end = start + marker.length;
      const expected = index ? originalBody.slice(0, originalBody.lastIndexOf(',', start)) + originalBody.slice(end)
        : originalBody.slice(0, start) + originalBody.slice(originalBody.indexOf(',', end) + 1);
      assert.equal(actualBody, expected, kind + ':' + position + ':' + JSON.stringify(newline) + ':' + key);
      assert.equal(uploaded.replace(interfaceBlocks(uploaded)[0][0], ''), raw.replace(interfaceBlocks(raw)[0][0], ''));
    }
  },
  'nested-kinds-and-text'(t) {
    const root = fixture(t), d = declaration('partial');
    d.entries[0].input_schema = { ...schema, description: 'Literal "kind":"partial" stays.', properties: { kind: { type: 'string', const: 'partial' } }, required: ['kind'] };
    d.resources = [{ name: 'audit', kind: 'port', access: 'read', operations: [] }];
    write(root, SUBJECT, textFor(JSON.stringify(d)));
    const got = iface(projected(root));
    assert.equal(got.resources[0].kind, 'port');
    assert.equal(got.entries[0].input_schema.properties.kind.const, 'partial');
    assert.equal(got.entries[0].input_schema.description, d.entries[0].input_schema.description);
  },
  'number-and-escape-spelling'(t) {
    const root = fixture(t), d = declaration('partial');
    d.entries[0].input_schema.description = 'é and an escaped "kind"';
    const raw = textFor(JSON.stringify(d).replace('"max_steps":1', '"max_steps":9007199254740993123456789').replace('"type":"string"', '"type":"string","minLength":1e0').replace('é', '\\u00e9'));
    write(root, SUBJECT, raw); const got = projected(root);
    for (const literal of ['9007199254740993123456789', '1e0', '\\u00e9', '\\"kind\\"']) assert.ok(got.includes(literal), literal);
    const malformed = Buffer.concat([Buffer.from(raw.slice(0, 4)), Buffer.from([0xff]), Buffer.from(raw.slice(4))]);
    write(root, SUBJECT, malformed);
    assert.deepEqual(capture(root).sources.find(file => file.path === SUBJECT).bytes, malformed,
      'projection must not repair invalid UTF-8 outside the interface');
  },
  async 'preview-and-upload-consistency'(t) {
    const root = fixture(t), expected = capture(root).tar, raw = readFileSync(join(root, SUBJECT));
    const fake = await transport(t), preview = fakePorts(root, fake);
    preview.gh = () => assert.fail('preview must not sign in');
    assert.equal(await runCheck({ cwd: root, words: ['echo'], options: { '--files': true, '--json': true } }, preview), 0, preview.stderr.text);
    for (const lint of [true, false]) {
      const ports = fakePorts(root, fake);
      assert.equal(await runCheck({ cwd: root, words: ['echo'], options: { '--json': true, ...(lint ? { '--lint': true } : {}) } }, ports), 0, ports.stderr.text);
      const result = JSON.parse(ports.stdout.text); assert.equal(result.rows.length, 1);
      if (!lint) assert.equal(result.rows[0].checks.total, 1, 'one exact check is reported, not whole-module coverage');
    }
    const ports = fakePorts(root, fake);
    assert.equal(await runTry({ cwd: root, words: ['echo'], options: { '--no-open': true, '--no-wait': true } }, ports), 0, ports.stderr.text);
    for (const post of fake.posts) assert.deepEqual(post.tar, expected);
    assert.ok(fake.posts.some(post => post.command === 'check'));
    assert.ok(fake.posts.some(post => post.command === 'try'));
    assert.deepEqual(readFileSync(join(root, SUBJECT)), raw);
  },
  'prepared-and-referenced-declaration'(t) {
    const root = fixture(t), d = declaration('partial');
    write(root, 'contracts/text.json', JSON.stringify(schema));
    d.entries[0].input_schema = { $contract: 'contracts/text.json#' };
    write(root, SUBJECT, textFor(JSON.stringify(d)));
    const expected = textFor(JSON.stringify({ ...d, entries: [{ ...d.entries[0], input_schema: schema }] }));
    let got = capture(root); assert.deepEqual(iface(projected(root, got, expected)).entries[0].input_schema, schema);
    assert.ok(!got.files.some(file => file.path === 'contracts/text.json'));
    got = capture(root, { prepareSource: () => [{ path: SUBJECT, bytes: textFor(JSON.stringify(declaration('partial'))) }] });
    projected(root, got, textFor(JSON.stringify(declaration('partial'))));
  },
  'authored-kind-freshness'(t) {
    const root = fixture(t), before = capture(root);
    const full = readFileSync(join(root, SUBJECT), 'utf8').replace('"kind":"partial"', '"kind":"full"');
    write(root, SUBJECT, full); const after = capture(root);
    assert.notEqual(before.raw_file_hashes[SUBJECT], after.raw_file_hashes[SUBJECT]);
    assert.notEqual(before.raw_prompt_hashes[SUBJECT], after.raw_prompt_hashes[SUBJECT]);
    assert.equal(readPrompt(root, new Set(gitFiles(root)), SUBJECT).interface.kind, 'full');
    assert.deepEqual(before.tar, after.tar, 'local classification is separate from executable bytes');
  },
  async 'saved-source-recovery'(t) {
    const root = fixture(t), fake = await transport(t), ports = fakePorts(root, fake);
    assert.equal(await runCheck({ cwd: root, words: ['echo'], options: { '--json': true } }, ports), 0, ports.stderr.text);
    const batch = JSON.parse(ports.stdout.text).batch, posts = fake.posts.length;
    write(root, SUBJECT, readFileSync(join(root, SUBJECT), 'utf8').replace('Echo returns', 'Echo now returns'));
    const retry = fakePorts(root, fake);
    assert.notEqual(await runCheck({ cwd: root, options: { '--retry': batch, '--json': true } }, retry), 0);
    assert.equal(fake.posts.length, posts, 'changed source cannot authorize a resend');
  },
  async 'invalid-and-native-only'(t) {
    for (const mutation of ['unknown', 'malformed', 'multiple', 'missing-operation', 'bad-limit', 'stale', 'native', 'native-call']) {
      const root = fixture(t), d = declaration('partial'); let raw;
      if (mutation === 'unknown') d.kind = 'invented';
      if (mutation === 'missing-operation') d.entries[0].operation = 'other';
      if (mutation === 'bad-limit') d.limits.max_steps = 0;
      if (mutation === 'native') Object.assign(d, { kind: 'native-only', reason: 'Real kernel process identity cannot be faked by this port.' });
      if (mutation === 'native-call') {
        d.calls = [{ operation: 'kernel', target: 'prompts/kernel.prompt.md', target_operation: 'kernel', max_calls: 1 }];
        write(root, 'prompts/kernel.prompt.md', textFor(JSON.stringify({ kind: 'native-only', status: 'draft', prose_sha256: '', reason: 'Real kernel process identity.' })));
      }
      raw = textFor(JSON.stringify(d));
      if (mutation === 'malformed') raw = raw.replace('"kind":"partial"', '"kind":');
      if (mutation === 'multiple') raw += block(JSON.stringify(d));
      if (mutation === 'stale') raw += '\nChanged prose.\n';
      write(root, SUBJECT, raw);
      const { ports } = portsFor({ HOME: join(root, '..', 'home'), PDD_STATE_DIR: join(root, '..', 'state') }, {
        captureSource, gh: () => assert.fail('refused or native-only work must not sign in'), fetch: () => assert.fail('must not dispatch'),
      });
      const result = await runCheck({ cwd: root, words: ['echo'], options: { '--json': true } }, ports);
      assert.notEqual(result, 0, mutation);
      const row = JSON.parse(ports.stdout.text).rows[0];
      assert.equal(row.calls, 0, mutation);
      if (mutation.startsWith('native')) { assert.equal(row.state, 'not run'); assert.ok(row.native_only.length); }
      else {
        // The client reports an unsent broken-test row as "not run" while
        // retaining the preflight refusal. Assert the documented rule itself.
        const code = { unknown: 'interface-kind-invalid', malformed: 'invalid-json', multiple: 'pdd-two-interfaces',
          'missing-operation': 'entry-operation-missing', 'bad-limit': 'invalid-limits', stale: 'interface-stale' }[mutation];
        assert.equal(row.unsent, true, mutation);
        assert.ok(row.refusals.some(refusal => refusal.code === code), mutation + ': ' + JSON.stringify(row));
      }
    }
  },
  'unrelated-root-field'(t) {
    const root = fixture(t), d = declaration('partial'); d.unknown = { kind: 'partial' };
    write(root, SUBJECT, textFor(JSON.stringify(d)));
    assert.deepEqual(iface(projected(root)).unknown, d.unknown, 'unknown fields are not filtered to force admission');
    const duplicate = readFileSync(join(root, SUBJECT), 'utf8').replace('"kind":"partial"', '"kind":"partial","kind":"partial"');
    write(root, SUBJECT, duplicate);
    assert.equal(source(capture(root)), duplicate, 'duplicate metadata retains original diagnostics');
  },
};
const cases = JSON.parse(readFileSync(new URL('./fixtures/runtime-interface-transport/cases.json', import.meta.url), 'utf8')).cases;
for (const record of cases) test('interface transport: ' + record.id + ' (' + record.criteria.join(',') + ')', t => actions[record.id](t));
