import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { Readable } from 'node:stream';
import { runPdd } from '../src/pdd-cli.mjs';
import { runApprove, approvePromptText, askApproval } from '../src/prompt-approve.mjs';
import { runCheck } from '../src/runtime/runtime-client.mjs';
import { interfaceBlocks } from '../src/runtime/runtime-preflight.mjs';
import { fakeRuntime, harbor, PLACE, portsFor, root, sink } from './runtime-fake.mjs';

const fileText = (repo, path) => readFileSync(join(repo, path), 'utf8');
function editInterface(repo, edit, path = PLACE) {
  const text = fileText(repo, path), block = interfaceBlocks(text)[0], [start, end] = block.indices[1];
  const value = JSON.parse(block[1]);
  edit(value);
  writeFileSync(join(repo, path), text.slice(0, start) + JSON.stringify(value) + text.slice(end));
}
function sharedInput(repo, { nested = false } = {}) {
  mkdirSync(join(repo, 'contracts'));
  const input = JSON.parse(interfaceBlocks(fileText(repo, PLACE))[0][1]).entries[0].input_schema;
  writeFileSync(join(repo, 'contracts/order.json'), JSON.stringify(nested ? input.properties.items : input));
  editInterface(repo, value => {
    value.status = 'draft';
    if (nested) value.entries[0].input_schema.properties.items = { $contract: 'contracts/order.json#' };
    else value.entries[0].input_schema = { $contract: 'contracts/order.json#' };
  });
}
async function approval(setup) {
  const stdout = sink(), stderr = sink();
  const code = await runApprove({ cwd: setup.repo, words: [PLACE] }, {
    stdout, stderr, stdin: Readable.from(['n\n']), interactive: true, env: { HOME: setup.home },
  });
  return { code, text: stdout.text + stderr.text };
}
async function rejectedCommands(setup) {
  const replies = [];
  for (const lint of [false, true]) {
    const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state }, {
      gh: () => assert.fail('a local refusal must precede authentication'),
      fetch: () => assert.fail('a local refusal must precede upload'),
    });
    const code = await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true, ...(lint ? { '--lint': true } : {}) } }, ports);
    assert.equal(code, 4, ports.stdout.text + ports.stderr.text);
    replies.push({ text: ports.stdout.text + ports.stderr.text, data: ports.stdout.text ? JSON.parse(ports.stdout.text) : null });
  }
  return replies;
}

for (const nested of [false, true]) test(`shared reader: contract ${nested ? 'field' : 'root'} schema reaches lint, test and approval view`, async t => {
  const setup = harbor(t, repo => sharedInput(repo, { nested }));
  const before = fileText(setup.repo, PLACE);
  const fake = await fakeRuntime(t, entry => fake.normal(entry));
  for (const lint of [true, false]) {
    const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
    const code = await runCheck({ cwd: setup.repo, words: ['place-order'], options: { ...(lint ? { '--lint': true } : {}) } }, ports);
    assert.equal(code, 0, ports.stdout.text + ports.stderr.text);
  }
  const result = await approval(setup);
  assert.equal(result.code, 1, 'a valid shared schema must reach the person, who declines in this test: ' + result.text);
  assert.match(result.text, /customerName: string/);
  assert.match(result.text, /quantity: integer/);
  assert.match(result.text, /\b1 to 20\b/);
  assert.equal(fileText(setup.repo, PLACE), before);
  const edited = approvePromptText(before);
  assert.equal(edited, before.replace('"status":"draft"', '"status":"approved"'));
  assert.ok(edited.includes('"$contract":"contracts/order.json#"'));
});

for (const token of ['1.0', '1e0', '9007199254740992.5']) {
  for (const status of ['draft', 'approved']) test(`shared reader: ${status} prompt retains rejected limits token ${token} on all commands`, async t => {
    const setup = harbor(t, repo => {
      editInterface(repo, value => { value.status = status; value.limits.max_steps = 1; });
      writeFileSync(join(repo, PLACE), fileText(repo, PLACE).replace('"max_steps":1', `"max_steps":${token}`));
    });
    const before = fileText(setup.repo, PLACE), replies = await rejectedCommands(setup);
    for (const reply of replies) {
      assert.equal(reply.data.rows[0].refusals[0].code, 'invalid-limits');
      assert.equal(reply.data.rows[0].refusals[0].section, '/limits/max_steps');
    }
    const result = await approval(setup);
    assert.equal(result.code, 4, 'approval must retain the same number-token refusal: ' + result.text);
    assert.match(result.text, /invalid-limits/);
    assert.match(result.text, /\/limits\/max_steps/);
    assert.equal(fileText(setup.repo, PLACE), before);
  });
}

test('shared reader: called prompt schema refusal reaches approval with the same reason', async t => {
  const child = 'prompts/child.prompt.md';
  const setup = harbor(t, repo => {
    writeFileSync(join(repo, child), fileText(repo, PLACE));
    editInterface(repo, value => { value.limits.max_model_calls = 0; }, child);
    editInterface(repo, value => { value.calls = [{ operation: 'child', target: child, target_operation: 'place_order', max_calls: 1 }]; });
  });
  const replies = await rejectedCommands(setup), result = await approval(setup);
  assert.equal(result.code, 4, 'approval must check the called prompt: ' + result.text);
  for (const reply of replies) {
    const problem = reply.data.rows[0].refusals[0];
    assert.equal(problem.path, child);
    assert.ok(result.text.includes(problem.message));
  }
});

test('shared reader: missing contract gives the same source reason before approval', async t => {
  const setup = harbor(t, repo => {
    editInterface(repo, value => { value.status = 'draft'; value.entries[0].input_schema = { $contract: 'contracts/missing.json#' }; });
  });
  const replies = await rejectedCommands(setup), result = await approval(setup);
  assert.equal(result.code, 4);
  assert.match(result.text, /contract-missing/);
  const callback = await askApproval({ root: setup.repo, path: PLACE, stdout: sink(), answers: { ask: () => assert.fail('a bad reference must not ask') } });
  assert.equal(callback.state, 'declined');
  assert.equal(callback.exitCode, 4);
  assert.match(callback.message, /contract-missing/);
  for (const reply of replies) assert.match(reply.text, /contract-missing/);
});

const inventory = (setup, ...args) => spawnSync(process.execPath, [join(root, 'bin/pdd.mjs'), 'files', ...args], {
  cwd: setup.repo, env: { PATH: process.env.PATH, HOME: setup.home }, encoding: 'utf8', timeout: 20000,
});
function snapshot(repo) {
  return new Map(readdirSync(repo, { recursive: true, withFileTypes: true }).filter(entry => entry.isFile() && !join(entry.parentPath, entry.name).includes('/.git/'))
    .map(entry => { const path = join(entry.parentPath, entry.name); return [path, readFileSync(path)]; }));
}

test('shared reader: files JSON lists resolved references and name-based Story/test pairs without writes', t => {
  const setup = harbor(t, repo => sharedInput(repo));
  const before = snapshot(setup.repo), reply = inventory(setup, '--json');
  assert.equal(reply.status, 0, 'files --json must be an available local inventory: ' + reply.stderr);
  const view = JSON.parse(reply.stdout);
  assert.deepEqual(Object.keys(view).sort(), ['schema_version', 'prompts', 'stories', 'tests', 'orphans', 'refusals', 'warnings'].sort());
  assert.equal(view.schema_version, 'pdd.files.v1');
  assert.deepEqual(view.prompts.map(row => row.path), [PLACE]);
  const prompt = view.prompts[0];
  assert.equal(prompt.has_interface, true);
  assert.deepEqual(prompt.tests, ['tests/place-order.json', 'tests/unknown-item.json']);
  assert.deepEqual(prompt.stories, ['user_stories/place-order.md', 'user_stories/unknown-item.md']);
  assert.ok(prompt.references.some(ref => ref.target === 'contracts/order.json#'));
  assert.deepEqual(prompt.refusals, []);
  assert.deepEqual(view.refusals, []);
  assert.deepEqual(view.stories[0].tests, ['tests/place-order.json']);
  assert.deepEqual(view.tests[0].prompts, [PLACE]);
  assert.deepEqual(view.tests[0].stories, ['user_stories/place-order.md']);
  assert.deepEqual(snapshot(setup.repo), before);
  assert.equal(inventory(setup, '--json').stdout, reply.stdout);
});

test('shared reader: files reports bad prompts, mismatched tests, untested Stories and orphan data separately', t => {
  const setup = harbor(t, repo => {
    writeFileSync(join(repo, 'prompts/notes.prompt.md'), '# Notes\n');
    writeFileSync(join(repo, 'prompts/bad.prompt.md'), fileText(repo, PLACE).replace('"max_steps": 4', '"max_steps": 1.0'));
    writeFileSync(join(repo, 'user_stories/untested.md'), '# Untested\n\n## Acceptance criteria\n\n1. I can inspect files.\n');
    writeFileSync(join(repo, 'tests/data.json'), '{orphan, deliberately not parsed');
    const path = 'tests/place-order.json', doc = JSON.parse(fileText(repo, path));
    doc.story_path = 'user_stories/unknown-item.md';
    writeFileSync(join(repo, path), JSON.stringify(doc));
  });
  const reply = inventory(setup, '--json');
  assert.equal(reply.status, 0, 'file problems must be listed, not abort inventory: ' + reply.stderr);
  const view = JSON.parse(reply.stdout);
  assert.equal(view.prompts.find(row => row.path === 'prompts/notes.prompt.md').has_interface, false);
  assert.ok(view.refusals.some(row => row.path === 'prompts/notes.prompt.md' && row.code === 'interface-missing'));
  assert.ok(view.refusals.some(row => row.path === 'prompts/bad.prompt.md' && row.code === 'invalid-limits'));
  assert.deepEqual(view.tests.find(row => row.path === 'tests/place-order.json').stories, ['user_stories/place-order.md']);
  assert.equal(view.tests[0].refusals[0].code, 'pdd-story-mismatch');
  assert.deepEqual(view.stories.find(row => row.path === 'user_stories/untested.md').tests, []);
  assert.deepEqual(view.orphans.map(row => row.path), ['tests/data.json']);
  const text = inventory(setup);
  assert.equal(text.status, 0);
  for (const path of [PLACE, 'prompts/notes.prompt.md', 'tests/place-order.json', 'tests/data.json', 'user_stories/untested.md']) assert.ok(text.stdout.includes(path));
  assert.match(text.stdout, /invalid-limits/);
});

test('shared reader: files keeps inspecting independent tests after a contract failure', t => {
  const setup = harbor(t, repo => {
    const child = 'prompts/broken.prompt.md';
    writeFileSync(join(repo, child), fileText(repo, PLACE));
    editInterface(repo, value => { value.entries[0].input_schema = { $contract: 'contracts/missing.json#' }; }, child);
    const path = 'tests/place-order.json', doc = JSON.parse(fileText(repo, path));
    doc.steps[0].entry_path = child;
    writeFileSync(join(repo, path), JSON.stringify(doc));
  });
  const reply = inventory(setup, '--json');
  assert.equal(reply.status, 0, 'a broken reference must not hide other files: ' + reply.stderr);
  const view = JSON.parse(reply.stdout);
  assert.equal(view.tests.length, 2);
  assert.ok(view.refusals.some(row => row.path === 'prompts/broken.prompt.md' && row.code === 'contract-missing'));
  assert.deepEqual(view.tests.find(row => row.path === 'tests/unknown-item.json').refusals, []);
});

test('shared reader: files works from a subdirectory and exposes its help and completion route', async t => {
  const setup = harbor(t), stdout = sink(), stderr = sink();
  const code = await runPdd(['files', '--json'], { cwd: join(setup.repo, 'prompts'), stdout, stderr, env: { HOME: setup.home } });
  assert.equal(code, 0, 'files must resolve the Git root from cwd: ' + stderr.text);
  assert.deepEqual(JSON.parse(stdout.text).prompts.map(row => row.path), [PLACE]);
  const help = inventory(setup, '--help');
  assert.equal(help.status, 0);
  assert.match(help.stdout, /pdd files \[--json\]/);
  const completion = spawnSync(process.execPath, [join(root, 'bin/pdd.mjs'), 'completion', 'bash'], { encoding: 'utf8' });
  assert.equal(completion.status, 0);
  assert.match(completion.stdout, /\bfiles\b/);
});
