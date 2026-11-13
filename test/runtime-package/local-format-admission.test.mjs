import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { interfaceBlocks, interfaceSchemaProblems } from '../../src/runtime-seam.mjs';
import { runCheck } from '../../src/runtime-seam.mjs';
import { fakeRuntime, harbor, PLACE, portsFor, sink } from './runtime-fake.mjs';

const closed = properties => ({ type: 'object', properties, required: Object.keys(properties), additionalProperties: false });
const nullable = keyword => ({ [keyword]: [closed({ x: { type: 'integer' }, y: { type: 'integer' } }), { type: 'null' }] });
const state = keyword => closed({ food: nullable(keyword) });
const read = path => readFileSync(path, 'utf8');
function rewrite(repo, path, change) {
  const file = join(repo, path), text = read(file), block = interfaceBlocks(text)[0];
  const iface = JSON.parse(block[1]);
  change(iface);
  writeFileSync(file, text.replace(block[1], JSON.stringify(iface)));
}
function unsupported(repo, called = false, keyword = 'anyOf') {
  const target = called ? 'prompts/child.prompt.md' : PLACE;
  if (called) {
    writeFileSync(join(repo, target), read(join(repo, PLACE)));
    rewrite(repo, PLACE, iface => { iface.calls = [{ target, target_operation: 'place_order', max_calls: 1 }]; });
  }
  rewrite(repo, target, iface => {
    iface.entries[0].input_schema.properties.state = state(keyword);
    iface.entries[0].result_schema.properties.food = nullable(keyword);
  });
  return target;
}
function offline(setup) {
  return { stdout: sink(), stderr: sink(), env: { HOME: setup.home, PDD_STATE_DIR: setup.state },
    gh: () => assert.fail('format refusal must precede authentication'),
    fetch: () => assert.fail('format refusal must precede upload') };
}

// Synthetic nullable coordinate schema: the evidence identifies anyOf, rather
// than optional properties, as the hosted invalid-schema refusal's cause.
test('local format diagnostics name nested anyOf and its oneOf recovery without changing schemas', () => {
  const iface = { limits: { max_steps: 1, max_model_calls: 1 }, entries: [
    { input_schema: closed({ state: state('anyOf') }), result_schema: state('anyOf') },
  ], resources: [{ operations: [{ arguments_schema: state('anyOf'), result_schema: closed({}) }] }] };
  const before = structuredClone(iface), problems = interfaceSchemaProblems(iface);
  for (const pointer of ['/entries/0/input_schema/properties/state/properties/food',
    '/entries/0/result_schema/properties/food', '/resources/0/operations/0/arguments_schema/properties/food']) {
    const problem = problems.find(item => item.code === 'graph-schema-unsupported-keyword' && item.pointer === pointer);
    assert.ok(problem, JSON.stringify(problems));
    assert.match(problem.rule, /anyOf/);
    assert.match(problem.rule, /oneOf/);
  }
  assert.deepEqual(iface, before);
});

// The same selection with oneOf is the control: in lint and the files preview the anyOf advice is a
// warning that changes no state, exit code or upload (the interpreter is the one place that refuses).
async function run(t, options, keyword, { called = false, words = ['place-order'], stories = true } = {}) {
  const setup = harbor(t, repo => unsupported(repo, called, keyword)), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  if (!stories) for (const folder of ['tests', 'user_stories']) rmSync(join(setup.repo, folder), { recursive: true });
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  const file = join(setup.repo, PLACE), before = read(file), code = await runCheck({ cwd: setup.repo, words, options }, ports);
  const json = ports.stdout.text ? JSON.parse(ports.stdout.text) : {};
  assert.equal(read(file), before);
  return { code, json, text: ports.stdout.text + ports.stderr.text, rows: (json.rows ?? []).map(row => [row.test, row.state]),
    uploads: fake.posts.map(post => post.command), files: (json.files ?? []).map(item => item.path) };
}
function sameOutcome(warned, control) {
  assert.equal(warned.code, control.code);
  assert.equal(warned.json.state ?? warned.json.lint_state ?? null, control.json.state ?? control.json.lint_state ?? null);
  assert.deepEqual(warned.rows, control.rows);
  assert.deepEqual(warned.uploads, control.uploads);
  assert.deepEqual(warned.files, control.files);
  assert.ok(!warned.rows.some(row => row[1] === 'refused'), JSON.stringify(warned.rows));
}

for (const [mode, options] of [
  ['files', { '--files': true, '--json': true }],
  ['local lint', { '--lint': true, '--local': true, '--json': true }],
  ['hosted lint', { '--lint': true, '--json': true }],
]) for (const selected of [false, true]) test(`${mode} warns about an unsupported schema keyword and keeps its state, exit code and upload (selected=${selected})`, async t => {
  const words = selected ? ['place-order'] : [];
  const control = await run(t, options, 'oneOf', { words }), warned = await run(t, options, 'anyOf', { words });
  assert.match(warned.text, /graph-schema-unsupported-keyword/);
  assert.match(warned.text, /\/entries\/0\/(?:input_schema|result_schema)\/properties\/(?:state\/properties\/)?food/);
  assert.match(warned.text, /anyOf/);
  assert.match(warned.text, /oneOf/);
  assert.doesNotMatch(control.text, /graph-schema-unsupported-keyword/);
  sameOutcome(warned, control);
});

// A check keeps the schema rules it had before the format advice: the engine's executable schema subset.
test('test refuses an unsupported schema keyword before transport, as its schema rules say', async t => {
  const setup = harbor(t, repo => unsupported(repo)), ports = offline(setup);
  const file = join(setup.repo, PLACE), before = read(file);
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, ports), 4);
  const out = ports.stdout.text + ports.stderr.text;
  assert.match(out, /graph-schema-unsupported-keyword/);
  assert.match(out, /anyOf/);
  assert.match(out, /oneOf/);
  assert.equal(read(file), before);
});

for (const local of [false, true]) test(`lint warns about an unsupported schema in called prompts (local=${local})`, async t => {
  const options = { '--lint': true, '--json': true, ...(local ? { '--local': true } : {}) };
  const control = await run(t, options, 'oneOf', { called: true }), warned = await run(t, options, 'anyOf', { called: true });
  assert.match(warned.text, /prompts\/child.prompt.md/);
  assert.match(warned.text, /anyOf/);
  sameOutcome(warned, control);
});

test('hosted lint warns about an unsupported schema without any Stories', async t => {
  const control = await run(t, { '--lint': true, '--json': true }, 'oneOf', { words: [], stories: false });
  const warned = await run(t, { '--lint': true, '--json': true }, 'anyOf', { words: [], stories: false });
  assert.deepEqual(warned.json.problems ?? [], control.json.problems ?? []);
  assert.match(warned.text, /graph-schema-unsupported-keyword/);
  assert.doesNotMatch(control.text, /graph-schema-unsupported-keyword/);
  sameOutcome(warned, control);
});

test('closed nullable oneOf and optional properties remain valid local schemas', () => {
  const input = closed({ state: state('oneOf'), optional: { type: 'string' } });
  input.required = ['state'];
  assert.deepEqual(interfaceSchemaProblems({ limits: { max_steps: 1, max_model_calls: 1 },
    entries: [{ input_schema: input, result_schema: state('oneOf') }] }), []);
});

for (const skill of ['pdd-feature', 'pdd-bug']) test(`${skill} recommends drafting only with a commit and provides the no-commit route`, () => {
  const step = read(new URL(`../../skills/${skill}/steps/prompt-story.md`, import.meta.url));
  const rule = step.split('\n').find(line => line.includes('pdd interface draft PROMPT'));
  assert.match(rule, /[Rr]ecommend/);
  assert.match(rule, /at least one commit/);
  assert.match(rule, /[Oo]therwise.*(?:write|author).*Runtime block/);
  assert.doesNotMatch(rule, /required|must|need/);
});
