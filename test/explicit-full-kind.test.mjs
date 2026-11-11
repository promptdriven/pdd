import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fillHashes, interfaceBlocks, interfaceFormatWarnings, interfaceKindProblems } from '../src/runtime-preflight.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { fakeRuntime, harbor, PLACE, portsFor, sink } from './runtime-fake.mjs';

const prefix = '# Synthetic contract\n\nKeep this prose exactly.\n\n';
const suffix = '\nAfter the interface.\n';
const hash = createHash('sha256').update(prefix + suffix).digest('hex');
const source = body => prefix + '<details><summary>Runtime interface</summary>\n\n```json\n' + body + '\n```\n</details>' + suffix;
function fixture(t, body) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-full-kind-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const path = 'subject.prompt.md', before = source(body);
  writeFileSync(join(root, path), before);
  return { root, path, before, read: () => readFileSync(join(root, path), 'utf8') };
}
function offline(setup) {
  return { stdout: sink(), stderr: sink(), env: { HOME: setup.home, PDD_STATE_DIR: setup.state },
    gh: () => assert.fail('local refusal must precede authentication'),
    fetch: () => assert.fail('local operation must not contact the Runtime') };
}
function draft(repo, called = false, explicit = true) {
  const file = join(repo, PLACE), before = readFileSync(file, 'utf8'), block = interfaceBlocks(before)[0];
  const iface = { ...JSON.parse(block[1]), status: 'draft', ...(explicit ? { kind: 'full' } : {}) };
  if (called) {
    const target = 'prompts/called.prompt.md';
    writeFileSync(join(repo, target), before.replace(block[1], JSON.stringify(iface)));
    delete iface.kind;
    iface.calls = [{ target, target_operation: 'place_order', max_calls: 1 }];
  }
  writeFileSync(file, before.replace(block[1], JSON.stringify(iface)));
}

test('explicit full draft warning names /kind and the local repair; it is no kind refusal', () => {
  const [warning] = interfaceFormatWarnings({ status: 'draft', kind: 'full' });
  assert.equal(warning?.code, 'interface-kind-explicit-full');
  assert.equal(warning.pointer, '/kind');
  assert.match(warning.rule, /omit.*kind/);
  assert.match(warning.rule, /pdd test --fill-hash/);
  assert.deepEqual(interfaceKindProblems({ status: 'draft', kind: 'full' }), []);
  for (const iface of [{ status: 'draft' }, { status: 'approved', kind: 'full' }, { kind: 'full' },
    { status: 'draft', kind: 'partial' }, { status: 'draft', kind: 'native-only', reason: 'Kernel ownership.' }]) {
    assert.deepEqual(interfaceKindProblems(iface), []);
    assert.deepEqual(interfaceFormatWarnings(iface), []);
  }
  assert.equal(interfaceKindProblems({ status: 'draft', kind: 'unknown' })[0].code, 'interface-kind-invalid');
});

// The same selection with an implicit full draft is the control: the warning changes no state, exit code or upload.
async function run(t, options, explicit, called = false) {
  const setup = harbor(t, repo => draft(repo, called, explicit)), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  const code = await runCheck({ cwd: setup.repo, options }, ports), json = JSON.parse(ports.stdout.text);
  return { code, json, text: ports.stdout.text + ports.stderr.text,
    rows: (json.rows ?? []).map(row => [row.test, row.state, row.reason ?? null]), files: json.files ?? null,
    uploads: fake.posts.map(post => [post.command, post.request.source_sha256]) };
}
for (const [name, options] of [
  ['files', { '--files': true, '--json': true }],
  ['local lint', { '--lint': true, '--local': true, '--json': true }],
  ['hosted lint', { '--lint': true, '--json': true }],
  ['test', { '--json': true }],
]) test(`${name} warns about an explicit full draft and keeps its state, exit code and upload`, async t => {
  const control = await run(t, options, false), warned = await run(t, options, true);
  assert.match(warned.text, /interface-kind-explicit-full/);
  assert.match(warned.text, /\/kind/);
  assert.match(warned.text, /pdd test --fill-hash/);
  assert.doesNotMatch(control.text, /interface-kind-explicit-full/);
  assert.equal(warned.code, control.code);
  assert.equal(warned.json.state ?? warned.json.lint_state ?? null, control.json.state ?? control.json.lint_state ?? null);
  assert.deepEqual(warned.rows, control.rows);
  assert.deepEqual(warned.files, control.files);
  assert.deepEqual(warned.uploads, control.uploads);
  assert.ok(!warned.rows.some(row => row[1] === 'refused'), JSON.stringify(warned.rows));
});

test('a warning names an explicit full draft reached through a call', async t => {
  const control = await run(t, { '--files': true, '--json': true }, false, true), warned = await run(t, { '--files': true, '--json': true }, true, true);
  assert.equal(warned.code, control.code);
  assert.deepEqual(warned.files, control.files);
  assert.ok(warned.json.warnings.some(line => /prompts\/called.prompt.md \/kind interface-kind-explicit-full/.test(line)), JSON.stringify(warned.json.warnings));
});

test('fill hash removes root full members while preserving nested values and exact remaining tokens', t => {
  for (const current of [false, true]) for (const compact of [false, true]) {
    const hashMember = `"prose_sha256": "${current ? hash : ''}"`;
    const body = `{ "kind": "full", "status": "draft", ${hashMember}, "data": {"kind":"full","n":1e+02}, "label":"kind, full \\"quoted\\"", "dup":1, "dup":2, "k\\u0069nd":"f\\u0075ll" }`;
    // Literal expected bytes remove only the first and last root kind members.
    const expected = `{ "status": "draft", "prose_sha256": "${hash}", "data": {"kind":"full","n":1e+02}, "label":"kind, full \\"quoted\\"", "dup":1, "dup":2 }`;
    const state = fixture(t, body), result = fillHashes({ root: state.root, files: [state.path], compact });
    assert.equal(result.refused.length, 0);
    assert.deepEqual(result[current ? 'current' : 'filled'], [{ path: state.path }]);
    assert.equal(result.warnings.length, 1);
    assert.match(result.warnings[0].message, /subject.prompt.md.*\/kind.*removed/);
    if (!compact) assert.equal(state.read(), source(expected));
    else {
      assert.deepEqual(JSON.parse(interfaceBlocks(state.read())[0][1]), JSON.parse(expected));
      assert.match(state.read(), /"n":1e\+02/);
      assert.match(state.read(), /"dup":1,"dup":2/);
    }
    const after = state.read(), again = fillHashes({ root: state.root, files: [state.path], compact });
    assert.equal(state.read(), after);
    assert.deepEqual(again.warnings, []);
    assert.deepEqual(again.current, [{ path: state.path }]);
  }
});

test('fill hash removes a full member and reports its repair through the command handler', async t => {
  const setup = harbor(t, repo => draft(repo)), ports = offline(setup);
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--fill-hash': true } }, ports), 0);
  const iface = JSON.parse(interfaceBlocks(readFileSync(join(setup.repo, PLACE), 'utf8'))[0][1]);
  assert.equal(Object.hasOwn(iface, 'kind'), false);
  assert.equal(iface.status, 'draft');
  assert.match(ports.stdout.text, /\/kind.*removed/);
});

test('fill hash never edits approved, invalid-status or unsafe-hash interfaces', t => {
  for (const compact of [false, true]) for (const [status, digest, expected] of [
    ['approved', hash, 'current'], ['approved', '', 'stale'],
    ['draft', undefined, 'refused'], ['draft', 42, 'refused'],
    ['pending', '', 'refused'], [undefined, '', 'refused'],
  ]) {
    const value = { kind: 'full', ...(status === undefined ? {} : { status }), ...(digest === undefined ? {} : { prose_sha256: digest }) };
    const state = fixture(t, JSON.stringify(value)), result = fillHashes({ root: state.root, files: [state.path], compact });
    assert.equal(state.read(), state.before);
    assert.equal(result[expected].length, 1);
    assert.deepEqual(result.warnings, []);
  }
});

test('fill hash preserves partial and native-only declarations', t => {
  for (const kind of ['partial', 'native-only']) {
    const value = { status: 'draft', prose_sha256: '', kind, ...(kind === 'native-only' ? { reason: 'Kernel ownership.' } : {}) };
    const body = JSON.stringify(value), state = fixture(t, body);
    const result = fillHashes({ root: state.root, files: [state.path] });
    assert.equal(state.read(), source(body.replace('"prose_sha256":""', `"prose_sha256":"${hash}"`)));
    assert.deepEqual(result.warnings, []);
  }
});
