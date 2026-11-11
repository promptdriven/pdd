import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { interfaceBlocks, interfaceSchemaProblems } from '../src/runtime-preflight.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, PLACE, sink } from './runtime-fake.mjs';

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
function unsupported(repo, called = false) {
  const target = called ? 'prompts/child.prompt.md' : PLACE;
  if (called) {
    writeFileSync(join(repo, target), read(join(repo, PLACE)));
    rewrite(repo, PLACE, iface => { iface.calls = [{ target, target_operation: 'place_order', max_calls: 1 }]; });
  }
  rewrite(repo, target, iface => {
    iface.entries[0].input_schema.properties.state = state('anyOf');
    iface.entries[0].result_schema.properties.food = nullable('anyOf');
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

for (const [mode, options] of [
  ['files', { '--files': true, '--json': true }],
  ['local lint', { '--lint': true, '--local': true, '--json': true }],
  ['hosted lint', { '--lint': true, '--json': true }],
  ['test', { '--json': true }],
]) for (const selected of [false, true]) test(`${mode} catches unsupported schema before transport (selected=${selected})`, async t => {
  const setup = harbor(t, repo => unsupported(repo)), ports = offline(setup);
  const file = join(setup.repo, PLACE), before = read(file);
  assert.equal(await runCheck({ cwd: setup.repo, words: selected ? ['place-order'] : [], options }, ports), 4);
  const out = ports.stdout.text + ports.stderr.text;
  assert.match(out, /graph-schema-unsupported-keyword/);
  assert.match(out, /\/entries\/0\/(?:input_schema|result_schema)\/properties\/(?:state\/properties\/)?food/);
  assert.match(out, /anyOf/);
  assert.match(out, /oneOf/);
  assert.equal(read(file), before);
});

for (const local of [false, true]) test(`lint catches unsupported schema in called prompts (local=${local})`, async t => {
  const setup = harbor(t, repo => unsupported(repo, true)), ports = offline(setup);
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--lint': true, '--json': true, ...(local ? { '--local': true } : {}) } }, ports), 4);
  assert.match(ports.stdout.text + ports.stderr.text, /prompts\/child.prompt.md/);
  assert.match(ports.stdout.text + ports.stderr.text, /anyOf/);
});

test('hosted lint catches unsupported schema without any Stories', async t => {
  const setup = harbor(t, repo => unsupported(repo)), ports = offline(setup);
  rmSync(join(setup.repo, 'tests'), { recursive: true });
  rmSync(join(setup.repo, 'user_stories'), { recursive: true });
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--lint': true, '--json': true } }, ports), 4);
  const report = JSON.parse(ports.stdout.text);
  assert.deepEqual(report.rows, []);
  assert.ok(report.problems.some(problem => problem.code === 'graph-schema-unsupported-keyword'));
});

test('closed nullable oneOf and optional properties remain valid local schemas', () => {
  const input = closed({ state: state('oneOf'), optional: { type: 'string' } });
  input.required = ['state'];
  assert.deepEqual(interfaceSchemaProblems({ limits: { max_steps: 1, max_model_calls: 1 },
    entries: [{ input_schema: input, result_schema: state('oneOf') }] }), []);
});

for (const skill of ['pdd-feature', 'pdd-bug']) test(`${skill} recommends drafting only with a commit and provides the no-commit route`, () => {
  const step = read(new URL(`../skills/${skill}/steps/prompt-story.md`, import.meta.url));
  const rule = step.split('\n').find(line => line.includes('pdd interface draft PROMPT'));
  assert.match(rule, /[Rr]ecommend/);
  assert.match(rule, /at least one commit/);
  assert.match(rule, /[Oo]therwise.*(?:write|author).*Runtime block/);
  assert.doesNotMatch(rule, /required|must|need/);
});
