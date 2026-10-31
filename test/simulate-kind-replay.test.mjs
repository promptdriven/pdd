import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, renameSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { findTests, gitFiles, proseSha256 } from '../src/runtime-preflight.mjs';
import { runTry } from '../src/runtime-client.mjs';
import { openCli } from '../src/try-doors.mjs';
import { openServe } from '../src/try-http.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';

// Independent replays of whole-project safety and authored HTTP request examples.
test('2760 replay: an invalid non-seed Story refuses the whole project before authentication', async t => {
  const setup = harbor(t, root => {
    const file = join(root, 'tests/unknown-item.json'), doc = JSON.parse(readFileSync(file));
    doc.steps[0].input.items[0].quantity = 0;
    writeFileSync(file, JSON.stringify(doc));
  });
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state }, { gh: () => assert.fail('invalid selected source must not authenticate') });
  assert.equal(await runTry({ cwd: setup.repo }, ports), 4);
  assert.match(ports.stdout.text, /unknown-item/);
});

test('2760 replay: opening the whole project cannot reuse a narrower named session', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.command === 'try') return { status: 200, json: f.tryJob(entry.request.requestId) };
    if (entry.url.endsWith('/tests')) return { status: 404, json: { error: { code: 'not-found' } } };
    return { status: 200, json: f.tryJob(entry.url.split('/').at(-1)) };
  });
  const io = () => portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }, { openUrl: async () => true }).ports;
  const named = io();
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'] }, named), 0, named.stderr.text);
  const whole = io(), posts = fake.posts.length;
  assert.equal(await runTry({ cwd: setup.repo }, whole), 2);
  assert.match(whole.stderr.text, /whole project.*pdd simulate --new/);
  assert.equal(fake.posts.length, posts);
});

test('2760 replay: HTTP example uses authored path, query and body with safe shell quoting', async () => {
  const entry = { entry_path: 'prompts/books.prompt.md', operation: 'add', http: { method: 'POST', path: '/books/:id' }, input_schema: { type: 'object', required: ['body'], properties: { params: { type: 'object', properties: { id: { type: 'string' } } }, query: { type: 'object', properties: { shelf: { type: 'string' } }, required: ['shelf'] }, body: { type: 'object' } } } };
  const { ports } = portsFor({}, { serve: async () => {} });
  const scenario = { doc: { steps: [{ entry_path: entry.entry_path, operation: 'add', input: { params: { id: 'book 7' }, query: { shelf: 'read next' }, body: { title: "Sam's book" } } }] } };
  await openServe({ ports, runtime: { send: async () => ({ status: 200, json: { entries: [entry] } }) } }, scenario, 'synthetic', { '--serve': '0' });
  assert.match(ports.stdout.text, /curl -X POST .*\/books\/book%207\?shelf=read\+next/);
  assert.match(ports.stdout.text, /--data/);
  assert.ok(ports.stdout.text.includes("Sam'\\''s book"), 'single quotes in authored JSON are shell escaped');
  const missing = portsFor({}, { serve: async () => {} }).ports;
  await openServe({ ports: missing, runtime: { send: async () => ({ status: 200, json: { entries: [entry] } }) } }, {}, 'synthetic', { '--serve': '0' });
  assert.match(missing.stdout.text, /<required:id>/);
  assert.match(missing.stdout.text, /required%3Ashelf/);
  assert.match(missing.stdout.text, /<required:body>/);
});


function typedReplay(t, story = 'place-order') {
  return harbor(t, root => {
    const promptPath = join(root, 'prompts/place_order.prompt.md');
    const original = readFileSync(promptPath, 'utf8');
    const iface = JSON.parse(original.match(/```json\s*([\s\S]*?)```/)[1]);
    const object = properties => ({ type: 'object', properties, required: Object.keys(properties), additionalProperties: false });
    const commands = { type: 'array', items: { type: 'string' } };
    iface.entries = [{ operation: 'resolve_command', input_schema: object({ commands }), result_schema: object({ commands }), errors: [] }];
    iface.conventions = [];
    const content = () => `# Resolve typed commands\n\nReturn the supplied commands as structured data.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\x60\x60\x60json\n${JSON.stringify(iface)}\n\x60\x60\x60\n</details>\n`;
    iface.prose_sha256 = proseSha256(content());
    writeFileSync(promptPath, content());
    const file = join(root, 'tests/place-order.json'), doc = JSON.parse(readFileSync(file));
    if (story !== 'place-order') {
      renameSync(join(root, doc.story_path), join(root, `user_stories/${story}.md`));
      doc.story_path = `user_stories/${story}.md`;
    }
    doc.criteria = [{ id: 'AC1', text: 'The typed command stays available.' }];
    writeFileSync(join(root, doc.story_path), '# Typed command\n\nI can classify a command.\n\n## Acceptance criteria\n\n1. The typed command stays available.\n');
    doc.steps = [{ step_id: 'resolve', entry_path: 'prompts/place_order.prompt.md', operation: 'resolve_command', input: { commands: ['industry-sim day status'] }, checks: [{ criterion_id: 'AC1', target: 'result', path: '/commands', op: 'equals', value: ['industry-sim day status'] }] }];
    writeFileSync(file, JSON.stringify(doc));
  });
}

test('2760 replay: explicit world tab on typed input keeps its tab and never claims Form', async t => {
  const setup = typedReplay(t);
  const fake = await fakeRuntime(t, (entry, f) => entry.command === 'lint' ? { status: 200, json: f.lint(entry.request.requestId) } : entry.command === 'try' ? { status: 200, json: f.tryJob(entry.request.requestId) } : { status: 404, json: {} });
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }, { openUrl: async () => true });
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--tab': 'world' } }, ports), 0, ports.stderr.text + ports.stdout.text);
  assert.equal(fake.posts.find(entry => entry.command === 'try').request.tab, 'world');
  assert.doesNotMatch(ports.stdout.text + ports.stderr.text, /opens on the Form tab/);
  assert.equal(fake.jsonPosts.length, 0);
});

test('2760 replay: no CLI choices explains quoted typed Story recovery before sign-in', async t => {
  const story = "resolver's input", setup = typedReplay(t, story);
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state }, { gh: () => assert.fail('local mismatch must not authenticate'), fetch: () => assert.fail('local mismatch must not contact runtime') });
  assert.equal(await runTry({ cwd: setup.repo, words: [story], options: { '--shell': true } }, ports), 125);
  assert.match(ports.stderr.text, /This Story is not a command-line program\. No Stories are command-line programs\./);
  assert.ok(ports.stderr.text.includes("pdd simulate 'resolver'\\''s input' opens its Form tab."), ports.stderr.text);
  assert.doesNotMatch(ports.stderr.text, /RUNBOOK|convention|adapter/);
});

function malformedReplay(t, change) {
  return harbor(t, root => {
    const source = readFileSync(join(root, 'prompts/place_order.prompt.md'), 'utf8');
    const iface = JSON.parse(source.match(/```json\s*([\s\S]*?)```/)[1]);
    change(iface);
    writeFileSync(join(root, 'prompts/broken.prompt.md'), source.replace(/(```json\s*)[\s\S]*?(```)/, (_, open, close) => open + JSON.stringify(iface) + '\n' + close));
    const path = join(root, 'tests/unknown-item.json'), doc = JSON.parse(readFileSync(path));
    for (const step of doc.steps) step.entry_path = 'prompts/broken.prompt.md';
    writeFileSync(path, JSON.stringify(doc));
  });
}

// Eligibility is an advisory inspection of authored source before validation.
// A broken unselected prompt cannot prevent a valid named Story from opening.
for (const [shape, change] of [
  ['non-array entries', iface => { iface.entries = {}; }],
  ['null entry', iface => { iface.entries = [null]; }],
  ['non-array conventions', iface => { iface.conventions = {}; }],
  ['null convention', iface => { iface.conventions = [null]; }],
]) {
  test(`2760 replay: unrelated ${shape} cannot crash named selection or direct CLI choices`, async t => {
    const setup = malformedReplay(t, change);
    const fake = await fakeRuntime(t, (entry, f) => entry.command === 'lint' ? { status: 200, json: f.lint(entry.request.requestId) } : entry.command === 'try' ? { status: 200, json: f.tryJob(entry.request.requestId) } : { status: 404, json: {} });
    const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }, { openUrl: async () => true });
    assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'] }, ports), 0, ports.stderr.text + ports.stdout.text);
    assert.equal(fake.posts.filter(entry => entry.command === 'try').length, 1);
    const visible = new Set(gitFiles(setup.repo)), found = findTests({ root: setup.repo, files: [...visible] });
    await assert.rejects(openCli({ root: setup.repo, visible, found, ports }, found.tests.find(row => row.story === 'place-order'), 'unused', {}), error => error.exitCode === 125 && /This Story is not a command-line program/.test(error.message));
  });
}

test('2760 replay: selected malformed entries retain local preflight refusal without authentication', async t => {
  const setup = malformedReplay(t, iface => { iface.entries = {}; });
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state }, { gh: () => assert.fail('malformed selected source must not authenticate'), fetch: () => assert.fail('malformed selected source must not contact runtime') });
  assert.equal(await runTry({ cwd: setup.repo, words: ['unknown-item'] }, ports), 4);
  assert.match(ports.stdout.text, /refused/i);
  assert.match(ports.stdout.text, /broken\.prompt\.md.*no operation/);
  const visible = new Set(gitFiles(setup.repo)), found = findTests({ root: setup.repo, files: [...visible] });
  await assert.rejects(openCli({ root: setup.repo, visible, found, ports }, found.tests.find(row => row.story === 'unknown-item'), 'unused', {}), error => error.exitCode === 125 && /This Story is not a command-line program/.test(error.message));
});
