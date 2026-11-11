import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { Readable } from 'node:stream';
import { applyPendingCaseWithHandoff, runTry } from '../src/runtime-client.mjs';
import { findTests, gitFiles, proseSha256 } from '../src/runtime-preflight.mjs';
import { openCli, runShim } from '../src/try-doors.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';

// Requirements: simulate-program-kind's saved-session and selection rules, plus
// the executable-interface transport contract. These fakes make no AI calls.
const object = properties => ({ type: 'object', properties, required: Object.keys(properties), additionalProperties: false });
const text = { type: 'string' };
function program(root, name, mode, classification, dependency) {
  const cli = mode === 'cli', http = mode === 'http';
  const input = cli ? object({ argv: { type: 'array', items: text } }) : object({});
  if (http) input.title = 'HTTP GET /health';
  const result = cli ? object({ stdout: text, stderr: text, exit_code: { type: 'integer' } }) : http ? object({ status: { type: 'integer' }, body: text }) : object({ value: text });
  const iface = { ...(classification ? { kind: classification } : {}), status: 'draft', prose_sha256: '', entries: [{ operation: 'main', input_schema: input, result_schema: result, errors: [] }], calls: [], resources: [], limits: { max_steps: 1, max_model_calls: 1 }, conventions: cli ? ['input_schema', 'result_schema'].map(key => ({ path: `/entries/0/${key}`, convention: 'cli' })) : [] };
  const content = () => `# ${name}tool\n\n${cli ? 'Print ready followed by a newline to stdout, empty stderr and exit code 0.' : http ? 'Return status 200 and body healthy.' : 'Return value ready.'}\n\n## Dependencies\n\n${dependency ? `[Shared context](${dependency}).` : 'None.'}\n\n<details><summary>Runtime interface</summary>\n\n\x60\x60\x60json\n${JSON.stringify(iface)}\n\x60\x60\x60\n</details>\n`;
  iface.prose_sha256 = proseSha256(content());
  writeFileSync(join(root, `prompts/${name}.prompt.md`), content());
  const criterion = `${name} is ready.`;
  writeFileSync(join(root, `user_stories/${name}.md`), `# ${name}\n\nI can use ${name}.\n\n## Acceptance criteria\n\n1. ${criterion}\n`);
  writeFileSync(join(root, `tests/${name}.json`), JSON.stringify({ schema_version: 'prompt-runtime.program-scenario.v1', story_path: `user_stories/${name}.md`, criteria: [{ id: 'AC1', text: criterion }], initial_world: {}, simulation: {}, context: [], steps: [{ step_id: 'ready', entry_path: `prompts/${name}.prompt.md`, operation: 'main', input: cli ? { argv: [] } : {}, checks: [{ criterion_id: 'AC1', target: 'result', path: cli ? '/stdout' : http ? '/body' : '/value', op: 'equals', value: cli ? 'ready\n' : http ? 'healthy' : 'ready' }] }] }));
}
function project(t, entries) {
  return harbor(t, root => {
    for (const name of ['prompts', 'tests', 'user_stories']) {
      rmSync(join(root, name), { recursive: true }); mkdirSync(join(root, name));
    }
    for (const [name, mode, classification, dependency] of entries) program(root, name, mode, classification, dependency);
  });
}
function saved(setup) {
  const folder = join(setup.state, 'repos');
  return JSON.parse(readFileSync(join(folder, readdirSync(folder).find(path => path.endsWith('.json')))));
}
function appMap(root, name) {
  const path = join(root, 'app-map.json');
  const map = { schema_version: 'prompt-runtime.app-map.v1', name: 'Saved screens', initial_screen: 'view', initial_route: null, initial_state: {}, state_schema: object({}), synthetic: true, router: null, routes: [], stylesheets: [], handlers: [], screens: [{ id: 'view', source: 'operation', prompt_path: `prompts/${name}.prompt.md`, operation: 'main', input: {}, format: 'html', result_pointer: name.endsWith('http') ? '/body' : '/value' }] };
  writeFileSync(path, JSON.stringify(map));
  return path;
}
async function harness(t, setup) {
  const events = [];
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.url.endsWith('/reopen')) {
      const answer = f.jobs.get(entry.url.split('/').at(-2));
      answer.result.session.state = 'running'; return { status: 200, json: answer };
    }
    if (entry.json) {
      const answer = { ...f.job(entry.json.requestId, 'call', 'passed', { program_result: { stdout: 'ready\n', stderr: '', exit_code: 0 }, report: { remaining_calls: 6, input_world: {}, world: {} } }), session_id: entry.url.split('/')[3] };
      f.jobs.set(entry.json.requestId, answer); return { status: 200, json: answer };
    }
    if (entry.url.endsWith('/model')) return { status: 200, json: { entries: [{ entry_path: 'prompts/z-http.prompt.md', operation: 'main', input_schema: object({}), http: { method: 'GET', path: '/health' } }], calls: { cap: 7, remaining: 6 }, app_map: false } };
    if (entry.method === 'DELETE') return { status: 200, json: f.stopJob(entry.headers['x-request-id'], entry.url.split('/').at(-1)) };
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId, readdirSync(join(setup.repo, 'prompts')).map(name => ({ path: `prompts/${name}`, state: 'draft', admission_state: 'draft', interface: { calls: [] } }))) };
    if (entry.command === 'try') {
      const answer = f.tryJob(entry.request.requestId);
      Object.assign(answer.result.session, { max_calls: entry.request.max_calls, remaining_calls: entry.request.max_calls });
      f.jobs.set(entry.request.requestId, answer); return { status: 200, json: answer };
    }
    const answer = f.jobs.get(entry.url.split('/').at(-1));
    return answer ? { status: 200, json: answer } : { status: 404, json: { error: { code: 'not-found' } } };
  });
  const io = extra => portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }, {
    stdin: Readable.from([]), shell: async () => { events.push('shell'); return 0; }, serve: async () => { events.push('serve'); }, openUrl: async () => { events.push('page'); return true; }, ...extra,
  }).ports;
  const run = async (name, options = {}, extra) => {
    const ports = io(extra), code = await runTry({ cwd: setup.repo, words: name ? [name] : [], options }, ports);
    return { code, ports };
  };
  return { fake, events, io, run };
}

for (const state of ['running', 'paused']) {
  test(`812 review: named recovery preserves an unchanged whole-project HTTP session (${state})`, async t => {
    const setup = project(t, [['a-http', 'http'], ['z-http', 'http']]), h = await harness(t, setup);
    const first = await h.run(); assert.equal(first.code, 0, first.ports.stderr.text);
    const original = Object.entries(saved(setup).tries)[0], id = original[1].id;
    h.fake.jobs.get(id).result.session.state = state;
    const posts = h.fake.posts.length;
    const repeat = await h.run(original[0], { '--no-open': true, '--no-wait': true });
    assert.equal(repeat.code, 0, repeat.ports.stderr.text);
    assert.equal(h.fake.posts.length, posts, 'named recovery cannot submit another setup or lint');
    assert.equal(h.fake.deletes.length, 0);
    assert.equal(h.fake.jsonPosts.length, state === 'paused' ? 1 : 0);
    if (state === 'paused') assert.ok(h.fake.jsonPosts[0].url.endsWith(`/${id}/reopen`));
    assert.deepEqual(Object.entries(saved(setup).tries), [original]);
    writeFileSync(join(setup.repo, 'prompts/z-http.prompt.md'), readFileSync(join(setup.repo, 'prompts/z-http.prompt.md'), 'utf8') + '\nChanged independent source.\n');
    const stale = await h.run(original[0], { '--no-open': true, '--no-wait': true });
    assert.equal(stale.code, 125);
    assert.match(stale.ports.stderr.text, /changed.*--new/);
    assert.equal(h.fake.posts.length, posts);
  });
}

test('812 review: named recovery refuses a map-only change against the saved whole-project pin', async t => {
  const setup = project(t, [['a-http', 'http'], ['z-http', 'http']]), path = appMap(setup.repo, 'z-http');
  const h = await harness(t, setup), first = await h.run();
  assert.equal(first.code, 0, first.ports.stderr.text);
  const [seed] = Object.keys(saved(setup).tries);
  const unchanged = await h.run(seed, { '--serve': '0' });
  assert.equal(unchanged.code, 0, unchanged.ports.stderr.text);
  const before = readFileSync(path, 'utf8'), map = JSON.parse(before), posts = h.fake.posts.length;
  map.screens[0].id = 'edited-view'; map.initial_screen = 'edited-view';
  writeFileSync(path, JSON.stringify(map));
  const named = await h.run(seed, { '--serve': '0' });
  assert.equal(named.code, 125, named.ports.stderr.text);
  assert.match(named.ports.stderr.text, /app map.*changed.*--new/);
  const whole = await h.run();
  assert.equal(whole.code, 2);
  assert.equal(h.fake.posts.length, posts);
  assert.equal(h.fake.deletes.length, 0);
  writeFileSync(path, before);
  const restored = await h.run(seed, { '--serve': '0' });
  assert.equal(restored.code, 0, restored.ports.stderr.text);
});

for (const [references, withMap] of [[false, false], [true, false], [false, true]]) {
  test(`812 review: delayed whole-project CLI case handoff retains all source pins (references: ${references}, map: ${withMap})`, async t => {
    const setup = project(t, [['cli', 'cli'], ['other', 'typed']]);
    const target = join(setup.repo, 'tests/cli.json'), doc = JSON.parse(readFileSync(target));
    doc.steps[0].checks.push({ criterion_id: 'AC1', target: 'world', path: '', op: 'equals', value: {} });
    writeFileSync(target, JSON.stringify(doc));
    if (references) {
      mkdirSync(join(setup.repo, 'contracts'));
      writeFileSync(join(setup.repo, 'contracts/input.json'), JSON.stringify(object({})));
      const path = join(setup.repo, 'prompts/other.prompt.md'), source = readFileSync(path, 'utf8');
      const iface = JSON.parse(source.match(/```json\s*([\s\S]*?)```/)[1]);
      iface.entries[0].input_schema = { $contract: 'contracts/input.json#' };
      writeFileSync(path, source.replace(/(```json\s*)[\s\S]*?(```)/, (_, open, close) => open + JSON.stringify(iface) + '\n' + close));
    }
    const mapPath = withMap ? appMap(setup.repo, 'other') : null;
    const h = await harness(t, setup), first = await h.run(undefined, withMap ? { '--cli': true } : {});
    assert.equal(first.code, 0, first.ports.stderr.text);
    const descriptor = join(setup.state, 'tries', readdirSync(join(setup.state, 'tries')).find(path => path.endsWith('.door.json')));
    const command = h.io(); assert.equal(await runShim(descriptor, ['ready'], command), 0, command.stderr.text);
    const before = readFileSync(target, 'utf8');
    const pending = await h.run(undefined, { '--save-last': true });
    assert.equal(pending.code, 125, pending.ports.stderr.text);
    assert.equal(readFileSync(target, 'utf8'), before);
    const receiptPath = readdirSync(setup.state, { recursive: true }).find(path => path.endsWith('.received.json'));
    assert.ok(receiptPath, pending.ports.stderr.text);
    const receipt = JSON.parse(readFileSync(join(setup.state, receiptPath)));
    const local = { env: h.io().env, gh: () => assert.fail('local handoff cannot authenticate'), fetch: () => assert.fail('local handoff cannot submit') };
    if (mapPath) {
      const originalMap = readFileSync(mapPath, 'utf8'), map = JSON.parse(originalMap);
      map.screens[0].id = 'edited-view'; map.initial_screen = 'edited-view'; writeFileSync(mapPath, JSON.stringify(map));
      const stale = await applyPendingCaseWithHandoff({ cwd: setup.repo, pendingId: receipt.pendingId, handoff: { kind: 'closed-editor', testPath: 'tests/cli.json' } }, local);
      assert.equal(stale.result?.state, 'pending', stale.message);
      assert.match(stale.message, /app map.*changed/);
      assert.equal(readFileSync(target, 'utf8'), before);
      writeFileSync(mapPath, originalMap);
    }
    const applied = await applyPendingCaseWithHandoff({ cwd: setup.repo, pendingId: receipt.pendingId, handoff: { kind: 'closed-editor', testPath: 'tests/cli.json' } }, local);
    assert.equal(applied.result?.state, 'committed', applied.message);
    const after = JSON.parse(readFileSync(target));
    assert.deepEqual(after.criteria, doc.criteria);
    assert.deepEqual(after.steps[0], doc.steps[0]);
    assert.equal(after.steps.length, 2);
    assert.deepEqual(after.steps[1].input, { argv: ['ready'] });
    const duplicate = await applyPendingCaseWithHandoff({ cwd: setup.repo, pendingId: receipt.pendingId, handoff: { kind: 'closed-editor', testPath: 'tests/cli.json' } }, local);
    assert.equal(duplicate.result?.duplicate, true);
    assert.equal(JSON.parse(readFileSync(target)).steps.length, 2);
  });
}

for (const [label, entryKind, dependencyKind] of [
  ['implicit full', undefined, undefined], ['explicit full entry', 'full', undefined], ['partial entry', 'partial', undefined], ['explicit full dependency', undefined, 'full'], ['partial dependency', undefined, 'partial'],
]) {
  test(`812 review: unchanged ${label} opens, reuses and invokes the CLI`, async t => {
    const entries = [['cli', 'cli', entryKind, dependencyKind ? 'shared.prompt.md' : undefined]];
    if (dependencyKind) entries.push(['shared', 'typed', dependencyKind]);
    const setup = project(t, entries), h = await harness(t, setup);
    const first = await h.run('cli');
    assert.equal(first.code, 0, first.ports.stderr.text);
    assert.deepEqual(h.events, ['shell']);
    const again = await h.run('cli', { '--cli': true });
    assert.equal(again.code, 0, again.ports.stderr.text);
    assert.equal(h.fake.posts.filter(entry => entry.command === 'try').length, 1);
    const descriptor = join(setup.state, 'tries', readdirSync(join(setup.state, 'tries')).find(path => path.endsWith('.door.json')));
    const command = h.io();
    assert.equal(await runShim(descriptor, ['ready'], command), 0, command.stderr.text);
    assert.equal(command.stdout.text, 'ready\n');
    assert.equal(h.fake.jsonPosts.length, 1);
    const changed = join(setup.repo, `prompts/${dependencyKind ? 'shared' : 'cli'}.prompt.md`);
    writeFileSync(changed, readFileSync(changed, 'utf8') + '\nChanged authored source.\n');
    const stale = h.io();
    assert.equal(await runShim(descriptor, ['ready'], stale), 125);
    assert.equal(stale.stdout.text, '');
    assert.equal(h.fake.jsonPosts.length, 1, 'changed authored bytes still refuse before a call');
  });
}

test('812 review: an unrelated missing contract cannot block a named Story or eligible-name advice', async t => {
  const setup = project(t, [['typed', 'typed'], ['cli', 'cli'], ['broken', 'typed']]);
  const path = join(setup.repo, 'prompts/broken.prompt.md'), source = readFileSync(path, 'utf8');
  const iface = JSON.parse(source.match(/```json\s*([\s\S]*?)```/)[1]);
  iface.entries[0].input_schema = { $contract: 'contracts/missing.json#' };
  writeFileSync(path, source.replace(/(```json\s*)[\s\S]*?(```)/, (_, open, close) => open + JSON.stringify(iface) + '\n' + close));
  const h = await harness(t, setup);
  for (const options of [{}, { '--page': true }]) {
    const result = await h.run('typed', options);
    assert.equal(result.code, 0, result.ports.stderr.text);
  }
  const localOnly = { gh: () => assert.fail('local refusal must not authenticate'), fetch: () => assert.fail('local refusal must not submit') };
  const refused = await h.run('typed', { '--cli': true }, localOnly);
  assert.equal(refused.code, 125);
  assert.match(refused.ports.stderr.text, /This Story is not a command-line program\. These are: cli\./);
  const visible = new Set(gitFiles(setup.repo)), found = findTests({ root: setup.repo, files: [...visible] });
  await assert.rejects(openCli({ root: setup.repo, visible, found }, found.tests.find(row => row.story === 'typed'), 'unused', {}), error => error.exitCode === 125 && /These are: cli\./.test(error.message));
  const selectedBroken = await h.run('broken', {}, localOnly);
  assert.equal(selectedBroken.code, 4, selectedBroken.ports.stderr.text);
  assert.match(selectedBroken.ports.stdout.text, /contract-missing|missing\.json/);
});

for (const [mode, firstPage] of [['http', false], ['http', true], ['cli', false], ['cli', true]]) {
  test(`812 review: whole-project ${mode} and page preserve one session and budget (page first: ${firstPage})`, async t => {
    const setup = project(t, [['a-typed', 'typed'], [mode === 'http' ? 'z-http' : 'z-cli', mode]]), h = await harness(t, setup);
    const first = await h.run(undefined, { '--max-calls': '7', ...(firstPage ? { '--page': true } : {}) });
    assert.equal(first.code, 0, first.ports.stderr.text);
    const original = Object.entries(saved(setup).tries)[0], id = original[1].id;
    h.fake.jobs.get(id).result.session.remaining_calls = 5;
    h.events.length = 0;
    const repeat = await h.run(undefined, firstPage ? {} : { '--page': true, '--no-wait': true });
    assert.equal(repeat.code, 0, repeat.ports.stderr.text);
    assert.deepEqual(h.events, [firstPage ? mode === 'http' ? 'serve' : 'shell' : 'page']);
    assert.equal(h.fake.posts.filter(entry => entry.command === 'try').length, 1);
    assert.equal(h.fake.deletes.length, 0);
    assert.equal(h.fake.jsonPosts.length, 0);
    assert.deepEqual(Object.entries(saved(setup).tries), [original]);
    assert.match(repeat.ports.stdout.text + repeat.ports.stderr.text, /Try budget 7 calls; 5 remaining/);
  });
}

for (const removeOriginal of [false, true]) {
test(`812 review: a changed seed refuses scope reuse and --new stops the original (removed: ${removeOriginal})`, async t => {
  const setup = project(t, [['z-http', 'http']]), h = await harness(t, setup);
  const first = await h.run(undefined, { '--max-calls': '7' });
  assert.equal(first.code, 0, first.ports.stderr.text);
  const original = Object.entries(saved(setup).tries)[0];
  program(setup.repo, 'a-http', 'http');
  if (removeOriginal) for (const path of ['prompts/z-http.prompt.md', 'tests/z-http.json', 'user_stories/z-http.md']) rmSync(join(setup.repo, path));
  const added = spawnSync('git', ['add', '-A'], { cwd: setup.repo, encoding: 'utf8' });
  assert.equal(added.status, 0, added.stderr);
  const posts = h.fake.posts.length;
  const repeat = await h.run();
  assert.equal(repeat.code, 2, repeat.ports.stderr.text);
  assert.match(repeat.ports.stderr.text, /whole project.*pdd simulate --new/);
  assert.equal(h.fake.posts.length, posts);
  assert.equal(h.fake.deletes.length, 0);
  assert.deepEqual(Object.entries(saved(setup).tries), [original]);
  const replacement = await h.run(undefined, { '--new': true, '--max-calls': '7' });
  assert.equal(replacement.code, 0, replacement.ports.stderr.text);
  assert.equal(h.fake.deletes.length, 1);
  assert.ok(h.fake.deletes[0].url.endsWith(original[1].id));
  const records = Object.entries(saved(setup).tries);
  assert.equal(records.length, 1);
  assert.equal(records[0][0], 'tests/a-http.json');
  assert.notEqual(records[0][1].id, original[1].id);
});
}
