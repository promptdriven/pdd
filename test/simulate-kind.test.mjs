import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runTry } from '../src/runtime-client.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { renderHelp } from '../src/pdd-cli.mjs';
import { proseSha256, captureSource } from '../src/runtime-preflight.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';

// Synthetic expectations come from #2760: no real interpreter, browser or shell.
const object = properties => ({ type: 'object', properties, required: Object.keys(properties), additionalProperties: false });
const text = { type: 'string' };
function project(t, kinds = ['cli', 'http', 'screen'], map = kinds.includes('http') && kinds.includes('screen')) {
  return harbor(t, root => {
    for (const dir of ['tests', 'prompts', 'user_stories']) {
      rmSync(join(root, dir), { recursive: true }); mkdirSync(join(root, dir));
    }
    for (const kind of kinds) {
      const cli = kind.startsWith('cli'), http = kind.startsWith('http');
      const program = kind === 'cli-again' ? 'cli' : kind;
      const input = cli ? object({ argv: { type: 'array', items: text } }) : object({});
      if (http) input.title = `HTTP GET /${kind === 'http' ? 'health' : 'other'}`;
      const result = cli ? object({ stdout: text, stderr: text, exit_code: { type: 'integer' } }) : http ? object({ status: { type: 'integer' }, body: text }) : object({ html: text });
      const iface = { status: 'draft', prose_sha256: '', entries: [{ operation: 'main', input_schema: input, result_schema: result, errors: [] }], calls: [], resources: [], limits: { max_steps: 1, max_model_calls: 1 }, conventions: cli ? ['input_schema', 'result_schema'].map(key => ({ path: `/entries/0/${key}`, convention: 'cli' })) : [] };
      const content = () => `# ${cli ? program + 'tool' : kind}\n\n${cli ? 'Print ready. Every line written to stdout or stderr ends with one newline.' : http ? 'Return status 200 and body healthy.' : 'Render the screen.'}\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\x60\x60\x60json\n${JSON.stringify(iface)}\n\x60\x60\x60\n</details>\n`;
      iface.prose_sha256 = proseSha256(content());
      writeFileSync(join(root, `prompts/${program}.prompt.md`), content());
      const criterion = `${kind} is ready.`;
      writeFileSync(join(root, `user_stories/${kind}.md`), `# ${kind}\n\nI can use ${kind}.\n\n## Acceptance criteria\n\n1. ${criterion}\n`);
      writeFileSync(join(root, `tests/${kind}.json`), JSON.stringify({ schema_version: 'prompt-runtime.program-scenario.v1', story_path: `user_stories/${kind}.md`, criteria: [{ id: 'AC1', text: criterion }], initial_world: {}, simulation: {}, context: [], steps: [{ step_id: 'ready', entry_path: `prompts/${program}.prompt.md`, operation: 'main', input: cli ? { argv: [] } : {}, checks: [{ criterion_id: 'AC1', target: 'result', path: cli ? '/stdout' : http ? '/body' : '/html', op: 'equals', value: cli ? 'ready\n' : http ? 'healthy' : '<p>Ready</p>' }] }] }));
    }
    if (map) writeFileSync(join(root, 'app-map.json'), JSON.stringify({ schema_version: 'prompt-runtime.app-map.v1', name: 'All screens', initial_screen: 'screen', initial_route: null, initial_state: {}, state_schema: object({}), synthetic: true, router: null, routes: [], stylesheets: [], handlers: [], screens: kinds.filter(k => !k.startsWith('cli') && !k.startsWith('http')).map(k => ({ id: k, source: 'operation', prompt_path: `prompts/${k}.prompt.md`, operation: 'main', input: {}, format: 'html', result_pointer: '/html' })) }));
  });
}
async function harness(t, setup) {
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.url.endsWith('/model')) return { status: 200, json: { entries: ['http', 'http-two'].filter(k => existsSync(join(setup.repo, `prompts/${k}.prompt.md`))).map(k => ({ entry_path: `prompts/${k}.prompt.md`, operation: 'main', input_schema: object({}), http: { method: 'GET', path: k === 'http' ? '/health' : '/other' } })), calls: { cap: 400, remaining: 400 }, app_map: existsSync(join(setup.repo, 'app-map.json')) } };
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId, ['cli', 'http', 'screen', 'screen-two', 'cli-two'].map(k => ({ path: `prompts/${k}.prompt.md`, admission_state: 'draft', state: 'draft', interface: { calls: [] } }))) };
    if (entry.command === 'try') { const job = f.tryJob(entry.request.requestId); f.jobs.set(entry.request.requestId, job); return { status: 200, json: job }; }
    return { status: 200, json: f.jobs.get(entry.url.split('/').at(-1)) };
  });
  const events = [], captures = [];
  const io = extra => portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }, {
    openUrl: async url => { events.push({ kind: 'page', url }); return true; },
    shell: async (shell, env) => { events.push({ kind: 'shell', shell, path: env.PATH }); return 0; },
    serve: async server => { events.push({ kind: 'serve', address: server.address() }); },
    captureSource: (root, options) => { const source = captureSource(root, options); captures.push(source.files.map(f => typeof f === 'string' ? f : f.path)); return source; },
    ...extra,
  }).ports;
  const run = async (story, options = {}, extra) => { const ports = io(extra); const code = await runTry({ cwd: setup.repo, words: story ? [story] : [], options }, ports); return { code, ports }; };
  return { fake, events, captures, run };
}

test('2760: explicit CLI remains available and automatic CLI opens its ready shell', async t => {
  const setup = project(t), h = await harness(t, setup);
  const pathOnly = await h.run('cli', { '--cli': true });
  assert.equal(pathOnly.code, 0, pathOnly.ports.stderr.text);
  assert.match(pathOnly.ports.stdout.text, /export PATH=/);
  assert.deepEqual(h.events, []);
  const explicit = await h.run('cli', { '--cli': true, '--shell': true });
  assert.equal(explicit.code, 0, explicit.ports.stderr.text);
  assert.equal(h.events.at(-1)?.kind, 'shell');
  h.events.length = 0;
  const automatic = await h.run('cli');
  assert.equal(automatic.code, 0, automatic.ports.stderr.text);
  assert.deepEqual(h.events.map(e => e.kind), ['shell']);
  assert.ok(h.events[0].path.startsWith(join(setup.repo, '.pdd/try/bin') + ':'));
  assert.equal(h.fake.posts.filter(p => p.command === 'try').length, 1, 'preserve saved session');
  h.events.length = 0;
  const shell = await h.run('cli', { '--shell': true });
  assert.equal(shell.code, 0, shell.ports.stderr.text);
  assert.deepEqual(h.events.map(e => e.kind), ['shell']);
});

test('2760: explicit HTTP remains available and automatic HTTP prints localhost plus a curl example', async t => {
  const h = await harness(t, project(t));
  const explicit = await h.run('http', { '--serve': '0' });
  assert.equal(explicit.code, 0, explicit.ports.stderr.text);
  assert.equal(h.events.at(-1)?.kind, 'serve');
  // No explicit mode or port: the ordinary invocation must itself select HTTP.
  h.events.length = 0;
  const automatic = await h.run('http');
  assert.equal(automatic.code, 0, automatic.ports.stderr.text);
  assert.deepEqual(h.events.map(e => e.kind), ['serve']);
  assert.equal(h.events[0].address.address, '127.0.0.1');
  assert.match(automatic.ports.stdout.text, /http:\/\/127\.0\.0\.1:\d+/);
  assert.match(automatic.ports.stdout.text, /curl\b[^\n]*http:\/\/127\.0\.0\.1:\d+\/health/);
});

test('2760: screen auto opens page and --page can force the page for a CLI Story', async t => {
  const h = await harness(t, project(t));
  const screen = await h.run('screen');
  assert.equal(screen.code, 0, screen.ports.stderr.text);
  assert.deepEqual(h.events.map(e => e.kind), ['page']);
  assert.equal(h.fake.posts.find(p => p.command === 'try').request.app_map, 'app-map.json');
  let plan;
  assert.doesNotThrow(() => { plan = parseArgv(['simulate', 'cli', '--page']); });
  assert.equal(plan.options['--page'], true);
  h.events.length = 0;
  const page = await h.run('cli', plan.options);
  assert.equal(page.code, 0, page.ports.stderr.text);
  assert.deepEqual(h.events.map(e => e.kind), ['page']);
});

test('2760: no Story opens the whole app and captures every mapped screen', async t => {
  const h = await harness(t, project(t, ['cli', 'http', 'screen', 'screen-two'], true));
  const result = await h.run();
  assert.equal(result.code, 0, result.ports.stderr.text);
  assert.deepEqual(h.events.map(e => e.kind), ['page']);
  const request = h.fake.posts.find(p => p.command === 'try')?.request;
  assert.equal(request.app_map, 'app-map.json');
  assert.equal(request.tab, 'screen');
  assert.ok(h.captures.at(-1).includes('prompts/screen.prompt.md'));
  assert.ok(h.captures.at(-1).includes('prompts/screen-two.prompt.md'));
});

test('2760: no Story opens the unique main CLI across multiple Stories', async t => {
  const setup = project(t, ['cli', 'cli-again', 'screen']), h = await harness(t, setup);
  const result = await h.run();
  assert.equal(result.code, 0, result.ports.stderr.text);
  assert.deepEqual(h.events.map(e => e.kind), ['shell']);
  assert.ok(h.events[0].path.startsWith(join(setup.repo, '.pdd/try/bin') + ':'));
});

test('2760: forcing CLI on a screen explains the mismatch and lists eligible Stories before sign-in', async t => {
  const h = await harness(t, project(t));
  const result = await h.run('screen', { '--cli': true }, { gh: () => assert.fail('local mismatch must not authenticate') });
  assert.notEqual(result.code, 0);
  assert.match(result.ports.stderr.text, /This Story is not a command-line program\. These are: cli\./);
  assert.doesNotMatch(result.ports.stderr.text, /RUNBOOK|schema|convention/);
  assert.equal(h.fake.posts.length, 0);
  assert.deepEqual(h.events, []);
});

test('2760: ambiguous main CLI lists choices instead of picking a program', async t => {
  const h = await harness(t, project(t, ['cli', 'cli-two']));
  const result = await h.run();
  assert.equal(result.code, 2);
  assert.match(result.ports.stderr.text, /more than one command-line program/i);
  assert.match(result.ports.stderr.text, /cli.*cli-two/);
  assert.equal(h.fake.posts.length, 0);
  assert.deepEqual(h.events, []);
});

test('2760: help and feature/bug guidance explain automatic choice, optional Story and explicit page', () => {
  const help = renderHelp(['simulate']);
  assert.match(help, /pdd simulate \[STORY\]/);
  assert.match(help, /--cli/); assert.match(help, /--shell/); assert.match(help, /--serve/);
  assert.match(help, /--page/);
  assert.match(help, /shell/); assert.match(help, /localhost/); assert.match(help, /whole project/i);
  for (const name of ['feature', 'bug']) {
    const skill = readFileSync(new URL(`../skills/pdd-${name}/SKILL.md`, import.meta.url), 'utf8');
    assert.match(skill, /pdd simulate <story>/);
    assert.match(skill, /automatically/i); assert.match(skill, /shell/); assert.match(skill, /localhost/);
    assert.match(skill, /whole project/i);
  }
});

test('2760: no Story without screens or CLI serves all project HTTP routes', async t => {
  const h = await harness(t, project(t, ['http', 'http-two']));
  const result = await h.run();
  assert.equal(result.code, 0, result.ports.stderr.text);
  assert.deepEqual(h.events.map(e => e.kind), ['serve']);
  assert.ok(h.captures.at(-1).includes('prompts/http.prompt.md'));
  assert.ok(h.captures.at(-1).includes('prompts/http-two.prompt.md'));
  assert.match(result.ports.stdout.text, /GET \/health/);
  assert.match(result.ports.stdout.text, /GET \/other/);
});
