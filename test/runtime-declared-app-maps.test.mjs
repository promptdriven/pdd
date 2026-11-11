import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { spawnSync } from 'node:child_process';

// Consumer tests of the public source API and actual CLI process.
// All files are synthetic; the files preview makes no network or model call.
const source = resolve(fileURLToPath(new URL('..', import.meta.url)));
const { captureSource, scenarioShapeRefusal, proseSha256 } =
  await import(pathToFileURL(join(source, 'src/runtime/runtime-preflight.mjs')));
const cli = join(source, 'bin/pdd.mjs');
const empty = { type: 'object', properties: {}, required: [], additionalProperties: false };
const object = properties => ({ type: 'object', properties, required: Object.keys(properties), additionalProperties: false });
const criterion = 'Opening the shell shows Home without sending a screen request.';
const fence = String.fromCharCode(96).repeat(3);
const mapPath = 'app/home.app-map.json';

function fixture(t) {
  const root = mkdtempSync(join(tmpdir(), 'issue-3196-check-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const write = (path, value) => {
    mkdirSync(dirname(join(root, path)), { recursive: true });
    writeFileSync(join(root, path), typeof value === 'string' ? value : JSON.stringify(value, null, 2) + '\n');
  };
  const prompt = (path, prose, operation, result = empty, resources = [], calls = []) => {
    const iface = { status: 'draft', prose_sha256: '', entries: [{ operation, input_schema: empty, result_schema: result, errors: [] }],
      resources, calls, limits: { max_steps: 6, max_model_calls: 3 } };
    const render = () => prose + '\n\n<details><summary>Runtime interface</summary>\n\n' + fence + 'json\n' +
      JSON.stringify(iface) + '\n' + fence + '\n</details>\n';
    iface.prose_sha256 = proseSha256(render());
    write(path, render());
  };
  assert.equal(spawnSync('git', ['init', '--quiet', root]).status, 0);
  write('user_stories/shell.md', '# Open the shell\n\nAs a reader, I want the shell to open independently.\n\n## Acceptance criteria\n\n1. ' + criterion + '\n');
  prompt('prompts/shell.prompt.md', '# Shell\n\nReturn the title Home. Make no resource call.\n\n## Dependencies\n\nNone.',
    'open', object({ title: { type: 'string' } }));
  prompt('prompts/screen.prompt.md', '# Screen\n\nRender Home. Its send control uses the declared action.\n\n![Home](../views/home.ui.svg)\n\n## Dependencies\n\n- [Labels](../docs/labels.md)\n- [Format](format.prompt.md)',
    'render', object({ html: { type: 'string' } }));
  prompt('prompts/action.prompt.md', '# Send\n\nSend once through sink.send.\n\n## Dependencies\n\nNone.', 'send', empty,
    [{ name: 'sink', kind: 'port', access: 'write', operations: [{ name: 'send', access: 'write', arguments_schema: empty, result_schema: empty }] }]);
  prompt('prompts/format.prompt.md', '# Format\n\nReturn an empty result.\n\n## Dependencies\n\nNone.', 'format');
  prompt('prompts/tester.prompt.md', '# Unselected tester\n\nReturn an empty result.\n\n## Dependencies\n\nNone.', 'open');
  write('docs/labels.md', '# Labels\n\nHome.\n');
  write('views/home.ui.svg', '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 160 60"><title>Home</title><desc>Home screen</desc><text id="home" x="8" y="24">Home</text></svg>\n');
  write('styles/home.css', 'body { color: #172033; }\n');
  const map = {
    schema_version: 'prompt-runtime.app-map.v1', name: 'Synthetic Home', initial_screen: 'home',
    initial_route: null, initial_state: {}, state_schema: empty, synthetic: true,
    screens: [{ id: 'home', prompt_path: 'prompts/screen.prompt.md', operation: 'render',
      source: 'operation', format: 'html', input: {}, result_pointer: '/html' }],
    router: null, routes: [], handlers: [{ screen: 'home', kind: 'click', match: { id: 'send' },
      handler: { prompt_path: 'prompts/action.prompt.md', operation: 'send' }, input: {},
      next: { kind: 'same', screen: null, route_pointer: null }, state: null }],
    stylesheets: ['styles/home.css'],
  };
  write(mapPath, map);
  write('app/unrelated.app-map.json', { schema_version: 'prompt-runtime.app-map.v1', screens: [{ prompt_path: 'prompts/tester.prompt.md' }] });
  const doc = {
    schema_version: 'prompt-runtime.program-scenario.v1', story_path: 'user_stories/shell.md',
    criteria: [{ id: 'AC1', text: criterion }], initial_world: { requests: [] },
    simulation: { 'sink.send': { action: 'port.write', world_pointer: '/requests', result_template: {} } },
    steps: [{ step_id: 'shell-only', entry_path: 'prompts/shell.prompt.md', operation: 'open', input: {},
      checks: [{ criterion_id: 'AC1', target: 'result', path: '/title', op: 'equals', value: 'Home' },
        { criterion_id: 'AC1', target: 'world', path: '/requests', op: 'equals', value: [] }] }],
    app_maps: [mapPath],
  };
  write('tests/shell.json', doc);
  const expected = [mapPath, 'docs/labels.md', 'prompts/action.prompt.md', 'prompts/format.prompt.md',
    'prompts/screen.prompt.md', 'prompts/shell.prompt.md', 'styles/home.css',
    'tests/shell.json', 'user_stories/shell.md', 'views/home.ui.svg'].sort();
  const paths = selection => captureSource(root, { tests: ['tests/shell.json'], ...selection }).files.map(file => file.path);
  return { root, doc, map, write, expected, paths };
}

test('AC1: the Runtime-supported declaration is accepted locally', t => {
  const f = fixture(t);
  assert.equal(scenarioShapeRefusal(f.doc, 'tests/shell.json'), null);
  assert.equal(f.doc.steps.length, 1);
  assert.equal(f.doc.steps[0].entry_path, 'prompts/shell.prompt.md');
});

test('AC2: declared map source closure is complete, exact and excludes decoys', t => {
  const f = fixture(t);
  assert.deepEqual(f.paths(), f.expected);
});

test('control: explicit appMap already captures the expected source closure', t => {
  const f = fixture(t);
  assert.deepEqual(f.paths({ appMap: mapPath }), f.expected);
});

test('AC2: mockup screen prompt and Appearance source remain captured', t => {
  const f = fixture(t);
  f.map.screens[0].source = 'mockup';
  f.map.screens[0].operation = null;
  f.write(mapPath, f.map);
  assert.deepEqual(f.paths(), f.expected);
});

for (const missing of [mapPath, 'prompts/screen.prompt.md', 'prompts/action.prompt.md', 'styles/home.css']) {
  test('AC3: missing required source refuses before incomplete capture: ' + missing, t => {
    const f = fixture(t);
    rmSync(join(f.root, missing));
    assert.throws(() => f.paths(), error => error.exitCode === 4 && error.message.includes(missing));
  });
}

test('AC3: a declared map cannot escape the repository', t => {
  const f = fixture(t);
  f.doc.app_maps = ['../outside.app-map.json'];
  f.write('tests/shell.json', f.doc);
  assert.throws(() => f.paths(), /outside|escape|relative|unsafe|invalid-app-maps/i);
});

test('AC3: a map symlink cannot expose an outside file', t => {
  const f = fixture(t);
  const outside = mkdtempSync(join(tmpdir(), 'issue-3196-outside-'));
  t.after(() => rmSync(outside, { recursive: true, force: true }));
  writeFileSync(join(outside, 'secret.json'), JSON.stringify(f.map));
  rmSync(join(f.root, mapPath));
  symlinkSync(join(outside, 'secret.json'), join(f.root, mapPath));
  assert.throws(() => f.paths(), /outside|escape|symbolic|link|unsafe/i);
});

test('AC4: unknown test keys remain refused', t => {
  const f = fixture(t);
  const { app_maps, ...doc } = f.doc;
  doc.app_mpas = app_maps;
  assert.equal(scenarioShapeRefusal(doc, 'tests/shell.json')?.code, 'invalid-document');
});

test('AC4: malformed JSON in a declared map is not silently omitted', t => {
  const f = fixture(t);
  f.write(mapPath, '{');
  assert.throws(() => f.paths(), /app-map.*JSON|JSON.*app-map/i);
});

for (const selection of [null, 'app/home.app-map.json', {}, [null], [42], [''],
  ['/absolute.json'], ['../outside.json'], ['./app/home.app-map.json'], ['app//home.json'],
  ['app\\home.json'], ['C:home.json'], ['app/\u0085.json'], [mapPath, mapPath]]) {
  test('AC4: malformed selection refuses: ' + JSON.stringify(selection), t => {
    const f = fixture(t);
    f.doc.app_maps = selection;
    f.write('tests/shell.json', f.doc);
    assert.equal(scenarioShapeRefusal(f.doc, 'tests/shell.json')?.code, 'invalid-app-maps');
    assert.throws(() => f.paths(), error => error.exitCode === 4 && error.code === 'invalid-app-maps');
  });
}

test('AC2: timer, after and host-region references are captured without scanning input data', t => {
  const f = fixture(t);
  for (const name of ['tick', 'after', 'owner', 'helper']) {
    f.write('prompts/' + name + '.prompt.md', '# ' + name + '\n\nNo dependencies.\n');
  }
  f.map.timers = [{ handler: { prompt_path: 'prompts/tick.prompt.md', operation: 'tick' },
    after: [{ handler: { prompt_path: 'prompts/after.prompt.md', operation: 'after' } }],
    input: { prompt_path: 'prompts/missing-input-decoy.prompt.md', stylesheets: ['missing.css'] } }];
  f.map.host_regions = [{ owner_prompt: 'prompts/owner.prompt.md',
    helpers: [{ prompt_path: 'prompts/helper.prompt.md', operation: 'help',
      input: { prompt_path: 'prompts/missing-helper-input-decoy.prompt.md' } }] }];
  f.write(mapPath, f.map);
  assert.deepEqual(f.paths(), [...f.expected, 'prompts/tick.prompt.md', 'prompts/after.prompt.md',
    'prompts/owner.prompt.md', 'prompts/helper.prompt.md'].sort());
});

test('AC3: a declaration does not bypass the authored workspace', t => {
  const f = fixture(t);
  f.write('pdd-workspace.json', { allowed_paths: ['tests/', 'user_stories/', 'prompts/'] });
  assert.throws(() => f.paths(), error => error.exitCode === 4 && /app\/home\.app-map\.json/.test(error.message));
});

test('AC3: an excluded Story boundary does not gain a declared screen interface', t => {
  const f = fixture(t);
  const story = readFileSync(join(f.root, 'user_stories/shell.md'), 'utf8');
  f.write('user_stories/shell.md', story + '\n' + fence + 'pdd-boundary\nprompts/shell.prompt.md\n' + fence + '\n');
  const captured = captureSource(f.root, { tests: ['tests/shell.json'] });
  const screen = captured.sources.find(file => file.path === 'prompts/screen.prompt.md');
  assert.ok(screen);
  assert.ok(!screen.bytes.toString('utf8').includes('<summary>Runtime interface</summary>'));
});

test('AC5: an absent declaration preserves existing source selection', t => {
  const f = fixture(t);
  delete f.doc.app_maps;
  f.write('tests/shell.json', f.doc);
  assert.equal(scenarioShapeRefusal(f.doc, 'tests/shell.json'), null);
  assert.deepEqual(f.paths(), ['prompts/shell.prompt.md', 'tests/shell.json', 'user_stories/shell.md']);
});

test('AC5: an empty declaration preserves existing source selection', t => {
  const f = fixture(t);
  f.doc.app_maps = [];
  f.write('tests/shell.json', f.doc);
  assert.equal(scenarioShapeRefusal(f.doc, 'tests/shell.json'), null);
  assert.deepEqual(f.paths(), ['prompts/shell.prompt.md', 'tests/shell.json', 'user_stories/shell.md']);
});

test('AC5: a two-Story upload keeps map dependencies in their own footprints', t => {
  const f = fixture(t);
  f.write('user_stories/second.md', '# Second\n\nAs a reader, I want a second shell.\n\n## Acceptance criteria\n\n1. ' + criterion + '\n');
  const second = { ...f.doc, story_path: 'user_stories/second.md', app_maps: [] };
  f.write('tests/second.json', second);
  const captured = captureSource(f.root, { tests: ['tests/shell.json', 'tests/second.json'] });
  const first = captured.stories.find(s => s.story_path === 'user_stories/shell.md');
  const other = captured.stories.find(s => s.story_path === 'user_stories/second.md');
  assert.ok(first.files.some(file => file.path === mapPath));
  assert.ok(!other.files.some(file => file.path === mapPath));
});

test('AC2: source CLI files preview reaches the same complete capture', t => {
  const f = fixture(t);
  const env = { ...process.env, PATH: dirname(cli) + ':' + process.env.PATH };
  const result = spawnSync(process.execPath, [cli, 'test', '--files', 'user_stories/shell.md', '--json'],
    { cwd: f.root, env, encoding: 'utf8', timeout: 30000 });
  assert.equal(result.status, 0, result.stderr || result.stdout);
  const answer = JSON.parse(result.stdout);
  assert.deepEqual(answer.files.map(file => file.path), f.expected);
});
