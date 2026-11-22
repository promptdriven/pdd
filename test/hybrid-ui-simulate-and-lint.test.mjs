import './helpers/test-home.mjs';
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { parseArgv } from '../src/argument-parser.mjs';
import { PUBLIC_COMMAND_MANIFEST, PUBLIC_COMMAND_ROUTES } from '../src/command-catalog.mjs';
import { renderHelp, runPdd } from '../src/pdd-cli.mjs';
import { lintRepoProject } from '../src/repo-hygiene-lint.mjs';
import { captureSource, gitFiles, proseSha256, runTry, simulate } from '../src/runtime-seam.mjs';
import { lintSvgLayouts } from '../src/svg-layout.mjs';
import { fakeRuntime, portsFor } from './helpers/runtime-fake.mjs';

function makeRepo(t, entries, { commit = false } = {}) {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-hybrid-ui-')));
  t.after(() => rmSync(base, { recursive: true, force: true }));
  const root = join(base, 'repo');
  const home = join(base, 'home');
  const state = join(base, 'state');
  mkdirSync(root, { recursive: true });
  mkdirSync(home, { recursive: true });
  mkdirSync(state, { recursive: true });
  const git = (...args) => execFileSync('git', args, { cwd: root, encoding: 'utf8' }).trim();
  git('init', '-q');
  for (const [rel, body] of Object.entries(entries)) {
    const abs = join(root, rel);
    mkdirSync(dirname(abs), { recursive: true });
    writeFileSync(abs, typeof body === 'string' ? body : `${JSON.stringify(body, null, 2)}\n`);
  }
  git('add', '.');
  if (commit) {
    git('-c', 'user.name=Test', '-c', 'user.email=test@example.invalid', 'commit', '-qm', 'init');
  }
  return { base, root, home, state, git };
}

function captureStreams() {
  let out = '';
  let err = '';
  return {
    stdout: { write(chunk) { out += String(chunk); } },
    stderr: { write(chunk) { err += String(chunk); } },
    get out() { return out; },
    get err() { return err; },
  };
}

test('3595/3596 CLI catalog & parser accept PROMPT.md targets, --stop PROMPT.md, --fresh, and test --read --details', () => {
  const tryRoute = PUBLIC_COMMAND_ROUTES.find(item => item.id === 'try');
  assert.ok(tryRoute);
  assert.ok(tryRoute.options.some(option => option.name === '--fresh' && option.kind === 'flag'));

  assert.deepEqual(parseArgv(['simulate', 'prompts/app.prompt.md']), {
    commandId: 'try',
    local: 'runtime-try',
    operands: ['prompts/app.prompt.md'],
    options: {},
  });
  assert.deepEqual(parseArgv(['sim', 'prompts/app.prompt.md', '--fresh']), {
    commandId: 'try',
    local: 'runtime-try',
    operands: ['prompts/app.prompt.md'],
    options: { '--fresh': true },
  });
  assert.deepEqual(parseArgv(['simulate', '--stop', 'prompts/app.prompt.md']), {
    commandId: 'try',
    local: 'runtime-try',
    operands: ['prompts/app.prompt.md'],
    options: { '--stop': true },
  });
  assert.deepEqual(parseArgv(['simulate', 'prompts/app.prompt.md', '--page', '--new', '--fresh']), {
    commandId: 'try',
    local: 'runtime-try',
    operands: ['prompts/app.prompt.md'],
    options: { '--page': true, '--new': true, '--fresh': true },
  });
  assert.deepEqual(parseArgv(['simulate', 'prompts/app.prompt.md', '--cli', '--fresh']), {
    commandId: 'try',
    local: 'runtime-try',
    operands: ['prompts/app.prompt.md'],
    options: { '--cli': true, '--fresh': true },
  });
  assert.deepEqual(parseArgv(['simulate', 'prompts/app.prompt.md', '--serve', '8080', '--fresh']), {
    commandId: 'try',
    local: 'runtime-try',
    operands: ['prompts/app.prompt.md'],
    options: { '--serve': '8080', '--fresh': true },
  });
  assert.deepEqual(parseArgv(['test', '--read', 'batch-1', '--details']), {
    commandId: 'check',
    local: 'runtime-check',
    operands: ['batch-1'],
    options: { '--read': true, '--details': true },
  });

  assert.ok(PUBLIC_COMMAND_MANIFEST.some(({ form }) => form.includes('pdd simulate [STORY|PROMPT.md]') && form.includes('[--fresh]')));
  assert.ok(PUBLIC_COMMAND_MANIFEST.some(({ form }) => form === 'pdd simulate --stop [STORY|PROMPT.md]'));
  assert.ok(PUBLIC_COMMAND_MANIFEST.some(({ form }) => form === 'pdd test --read [BATCH|CALL_ID] [--json] [--details] [--timeout MIN]'));

  const simHelp = renderHelp(['simulate']);
  assert.match(simHelp, /\[STORY\|PROMPT\.md\]/);
  assert.match(simHelp, /--stop \[STORY\|PROMPT\.md\]/);
  assert.match(simHelp, /--fresh/);
  assert.match(renderHelp(['test']), /--details/);
});

test('3596 CLI & runtime-seam forward prompts/app.prompt.md, --stop prompts/app.prompt.md, and --fresh intact', async t => {
  const { root, home, state } = makeRepo(t, {
    'prompts/app.prompt.md': '# Counter\n\nExpose `render({ state })` and `handle_event({ state, event })`.\n\n## Dependencies\n\nNone.\n',
  });

  const forwarded = [];
  const mockClientRunTry = async (input, ports) => {
    forwarded.push({
      cwd: input.cwd,
      words: input.words,
      options: input.options,
      hasRunTryPort: Object.hasOwn(ports, 'runTry'),
    });
    ports.stdout?.write('ok\n');
    return 0;
  };
  const streamsA = captureStreams();
  assert.equal(
    await runTry({ cwd: root, words: ['prompts/app.prompt.md'], options: { '--fresh': true } }, { ...streamsA, runTry: mockClientRunTry }),
    0,
  );
  const streamsB = captureStreams();
  assert.equal(
    await runTry({ cwd: root, words: ['prompts/app.prompt.md'], options: { '--stop': true } }, { ...streamsB, runTry: mockClientRunTry }),
    0,
  );
  assert.deepEqual(forwarded, [
    { cwd: root, words: ['prompts/app.prompt.md'], options: { '--fresh': true }, hasRunTryPort: false },
    { cwd: root, words: ['prompts/app.prompt.md'], options: { '--stop': true }, hasRunTryPort: false },
  ]);

  const simStreams = captureStreams();
  assert.equal(
    await simulate({ cwd: root, prompt: 'prompts/app.prompt.md', fresh: true }, { ...simStreams, runTry: mockClientRunTry }),
    0,
  );
  assert.equal(simStreams.out, 'ok\n');
  assert.deepEqual(forwarded.at(-1), {
    cwd: root,
    words: ['prompts/app.prompt.md'],
    options: { '--fresh': true },
    hasRunTryPort: false,
  });

  const stopSimStreams = captureStreams();
  assert.equal(
    await simulate({ cwd: root, prompt: 'prompts/app.prompt.md', mode: 'stop' }, { ...stopSimStreams, runTry: mockClientRunTry }),
    0,
  );
  assert.deepEqual(forwarded.at(-1), {
    cwd: root,
    words: ['prompts/app.prompt.md'],
    options: { '--stop': true },
    hasRunTryPort: false,
  });

  // With @promptdriven/runtime-client@1.1.1, `pdd simulate prompts/app.prompt.md` is accepted natively
  // and proceeds past Story discovery to runtime authentication (exit 5 without gh sign-in, no old-client refusal).
  const cliStreams = captureStreams();
  const env = { HOME: home, PDD_RUNTIME_URL: 'https://runtime.example', PDD_STATE_DIR: state };
  const cliCode = await runPdd(['simulate', 'prompts/app.prompt.md'], { cwd: root, env, stdout: cliStreams.stdout, stderr: cliStreams.stderr });
  assert.equal(cliCode, 5, cliStreams.err);
  assert.doesNotMatch(cliStreams.err, /No tests found|Unknown story|No Stories are available/);
});

test('3596 pdd lint --local passes with 0 warnings on 1-file and 3-file plain-prose HTML UI apps (zero app-map.json, zero Runtime interface)', async t => {
  const { root, home, state } = makeRepo(t, {
    'prompts/tictactoe.prompt.md': [
      '# Tic-Tac-Toe UI',
      '',
      'A single-file plain-prose interactive Tic-Tac-Toe screen with zero `app-map.json` and zero `Runtime interface`.',
      '',
      '## Operations',
      '',
      '- `render({ state })` -> `{ state, html }`: initializes a 3x3 empty board when `state` is empty, renders semantic HTML with an inline `<style>` block, status banner, nine `<button id="cell-0" value="0" data-pdd-op="move">` cells, and a Reset `<button id="reset" value="reset" data-pdd-op="reset">Reset</button>`.',
      '- `handle_event({ state, event })` -> `{ state, html }`: applies clicks on empty cells for the active player (`X` then `O`), detects 3-in-a-row wins or draws, resets on `reset`, and returns the updated state and HTML.',
      '',
      '## Domain decisions',
      '',
      '- Never emit `<script>` or inline `on*=` attributes.',
      '- Keep all styling in an inline sanitized `<style>` tag.',
      '',
      '## Dependencies',
      '',
      'None.',
      '',
    ].join('\n'),
  });

  assert.deepEqual(lintSvgLayouts({ root, files: gitFiles(root) }), []);

  const env = { HOME: home, PDD_RUNTIME_URL: 'invalid', PDD_STATE_DIR: state };
  const jsonStreams = captureStreams();
  assert.equal(await runPdd(['lint', '--local', '--json'], { cwd: root, env, stdout: jsonStreams.stdout, stderr: jsonStreams.stderr }), 0, jsonStreams.err);
  const parsed = JSON.parse(jsonStreams.out);
  assert.equal(parsed.exit_code, 0);
  assert.deepEqual(parsed.problems, []);
  assert.deepEqual(parsed.warnings, []);
  assert.match(parsed.summary_line, /0 AI calls/);

  const textStreams = captureStreams();
  assert.equal(await runPdd(['lint', '--local'], { cwd: root, env, stdout: textStreams.stdout, stderr: textStreams.stderr }), 0, textStreams.err);
  assert.equal(textStreams.err, '');
  assert.doesNotMatch(textStreams.out, /Warning:/);

  // 3-file plain-prose UI app (prompt + Story + Short JSON, zero app-map.json, zero Runtime interface)
  const f3 = makeRepo(t, {
    'prompts/counter.prompt.md': [
      '# Counter UI',
      '',
      'Single-file plain-prose counter screen.',
      '',
      '## Operations and ports',
      '',
      '- `sync render({ state }) -> { state, html }` — renders `<style>`, `<span id="count">`, `<button id="inc" value="inc">+1</button>`.',
      '- `sync handle_event({ state, event }) -> { state, html }` — increments count on `inc`.',
      '',
      '## Domain decisions',
      '',
      '| Event | Next count |',
      '|---|---|',
      '| `inc` | `state.count + 1` |',
      '| other | unchanged |',
      '',
      '## Dependencies',
      '',
      'None.',
      '',
    ].join('\n'),
    'user_stories/counter.md': [
      '# Tap counter',
      '',
      'As a shopper counting items, I want to tap +1 on the counter screen, so that I see the updated total.',
      '',
      '## Acceptance criteria',
      '',
      '1. Opening the screen displays 0.',
      '2. Tapping +1 changes the count to 1.',
      '',
    ].join('\n'),
    'tests/counter.json': {
      entry_path: 'prompts/counter.prompt.md',
      steps: [
        { id: 'open', op: 'render', input: { state: { count: 0 } }, checks: { '1': [['result', '/state/count', '=', 0], ['html_text', 'span#count', '=', '0']] } },
        { id: 'inc', op: 'handle_event', input: { state: { count: 0 }, event: { kind: 'button', value: 'inc' } }, checks: { '2': [['result', '/state/count', '=', 1], ['html_exists', 'button#inc']] } },
      ],
    },
  }, { commit: true });

  const files3 = gitFiles(f3.root);
  assert.deepEqual(lintSvgLayouts({ root: f3.root, files: files3 }), []);
  const projectLint3 = lintRepoProject({ root: f3.root, files: files3 });
  assert.deepEqual(projectLint3.errors, []);
  assert.deepEqual(projectLint3.warnings, []);
});

test('3595/3596 pdd lint --local passes with 0 warnings on compact and v1 app-map.json apps whose prompts omit Runtime interface', async t => {
  const { root: compactRoot, home: compactHome, state: compactState } = makeRepo(t, {
    'prompts/counter_ui.prompt.md': [
      '# Counter UI',
      '',
      'Plain-prose interactive counter with zero `Runtime interface` block.',
      '',
      '## Operations',
      '',
      '- `render({ state })` -> `{ state, html }`: displays `state.count` with inline `<style>` and `+1` / `Reset` buttons.',
      '- `handle_event({ state, event })` -> `{ state, html }`: increments or resets `state.count` and returns updated HTML.',
      '- `tick({ state, generation })` -> `{ state }`: advances auto-counter while `state.polling` is true.',
      '',
      '## Dependencies',
      '',
      'None.',
      '',
    ].join('\n'),
    'app-map.json': {
      initial_state: { count: 0, polling: true, generation: 0 },
      screens: [
        {
          prompt_path: 'prompts/counter_ui.prompt.md',
          operation: 'render',
          input: { state: { $ref: '/state' } },
          result_pointer: '/html',
        },
      ],
      handlers: [
        {
          screen: 'main',
          kind: 'button',
          match: { value: '*' },
          handler: { prompt_path: 'prompts/counter_ui.prompt.md', operation: 'handle_event' },
          input: { state: { $ref: '/state' }, event: { $ref: '/event' } },
          state: { $ref: '/result/state' },
          next: { kind: 'same', screen: null, route_pointer: null },
        },
      ],
      timers: [
        {
          id: 'auto-tick',
          screen: 'main',
          interval_ms: 1500,
          enabled_pointer: '/polling',
          generation_pointer: '/generation',
          handler: { prompt_path: 'prompts/counter_ui.prompt.md', operation: 'tick' },
          input: { state: { $ref: '/state' }, generation: { $ref: '/event/generation' } },
          state: { $ref: '/result/state' },
          next: { kind: 'same', screen: null, route_pointer: null },
        },
      ],
    },
  });

  assert.deepEqual(lintSvgLayouts({ root: compactRoot, files: gitFiles(compactRoot) }), []);
  const compactEnv = { HOME: compactHome, PDD_RUNTIME_URL: 'invalid', PDD_STATE_DIR: compactState };
  const compactStreams = captureStreams();
  assert.equal(await runPdd(['lint', '--local', '--json'], { cwd: compactRoot, env: compactEnv, stdout: compactStreams.stdout, stderr: compactStreams.stderr }), 0, compactStreams.err);
  const compactParsed = JSON.parse(compactStreams.out);
  assert.equal(compactParsed.exit_code, 0);
  assert.deepEqual(compactParsed.problems, []);
  assert.deepEqual(compactParsed.warnings, []);

  const { root: v1Root, home: v1Home, state: v1State } = makeRepo(t, {
    'prompts/desk.prompt.md': [
      '# Desk Screen',
      '',
      'Plain-prose screen prompt with zero `Runtime interface`.',
      '',
      '- `render({ draft })` -> `{ html }`',
      '- `send({ draft })` -> `{ sent }`',
      '',
      '## Dependencies',
      '',
      'None.',
      '',
    ].join('\n'),
    'app-map.json': {
      schema_version: 'prompt-runtime.app-map.v1',
      name: 'Desk',
      initial_screen: 'desk',
      initial_route: null,
      initial_state: { draft: 'hi', sent: 0 },
      state_schema: {
        type: 'object',
        properties: { draft: { type: 'string' }, sent: { type: 'integer' } },
        required: ['draft', 'sent'],
        additionalProperties: false,
      },
      synthetic: true,
      router: null,
      routes: [],
      stylesheets: [],
      screens: [
        {
          id: 'desk',
          prompt_path: 'prompts/desk.prompt.md',
          operation: 'render',
          source: 'operation',
          format: 'html',
          input: { draft: { $ref: '/state/draft' } },
          result_pointer: '/html',
        },
      ],
      handlers: [
        {
          screen: 'desk',
          kind: 'button',
          match: { value: 'send' },
          handler: { prompt_path: 'prompts/desk.prompt.md', operation: 'send' },
          input: { draft: { $ref: '/state/draft' } },
          state: { draft: '', sent: { $ref: '/result/sent' } },
          next: { kind: 'same', screen: null, route_pointer: null },
        },
      ],
    },
  });

  assert.deepEqual(lintSvgLayouts({ root: v1Root, files: gitFiles(v1Root) }), []);
  const v1Env = { HOME: v1Home, PDD_RUNTIME_URL: 'invalid', PDD_STATE_DIR: v1State };
  const v1Streams = captureStreams();
  assert.equal(await runPdd(['lint', '--local', '--json'], { cwd: v1Root, env: v1Env, stdout: v1Streams.stdout, stderr: v1Streams.stderr }), 0, v1Streams.err);
  const v1Parsed = JSON.parse(v1Streams.out);
  assert.equal(v1Parsed.exit_code, 0);
  assert.deepEqual(v1Parsed.problems, []);
  assert.deepEqual(v1Parsed.warnings, []);
});

test('3595/3596 compact app-map.json local lint still flags invalid schema_version, empty screens, missing prompt_path, and bad timers', t => {
  const { root: badRoot } = makeRepo(t, {
    'prompts/counter_ui.prompt.md': '# Counter\n\n## Dependencies\n\nNone.\n',
    'app-map.json': {
      schema_version: 'prompt-runtime.app-map.v99',
      initial_state: { count: 0 },
      screens: [
        { prompt_path: 'prompts/missing.prompt.md', operation: 'render', result_pointer: '/html' },
      ],
      timers: [
        {
          id: 'too-fast',
          screen: 'main',
          interval_ms: 500,
          enabled_pointer: '/polling',
          generation_pointer: '/generation',
          handler: { prompt_path: 'prompts/counter_ui.prompt.md', operation: 'tick' },
          input: {},
          state: { $ref: '/state' },
          next: { kind: 'same', screen: null, route_pointer: null },
        },
      ],
    },
  });

  const warnings = lintSvgLayouts({ root: badRoot, files: gitFiles(badRoot) });
  assert.ok(warnings.some(line => /schema_version/.test(line)), warnings.join('\n'));
  assert.ok(warnings.some(line => /prompts\/missing\.prompt\.md/.test(line)), warnings.join('\n'));
  assert.ok(warnings.some(line => /interval_ms/.test(line)), warnings.join('\n'));
  assert.ok(warnings.some(line => /enabled_pointer/.test(line)), warnings.join('\n'));
  assert.ok(warnings.some(line => /generation_pointer/.test(line)), warnings.join('\n'));

  const { root: emptyScreensRoot } = makeRepo(t, {
    'prompts/counter_ui.prompt.md': '# Counter\n\n## Dependencies\n\nNone.\n',
    'app-map.json': { initial_state: { count: 0 }, screens: [] },
  });
  const emptyWarnings = lintSvgLayouts({ root: emptyScreensRoot, files: gitFiles(emptyScreensRoot) });
  assert.ok(emptyWarnings.some(line => /non-empty "screens"/.test(line)), emptyWarnings.join('\n'));
});

test('3596 runTry auto-selects tab=screen for Story-backed plain-prose render/handle_event UI without app-map.json, preserves reopen and explicit --tab', async t => {
  const f = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\n## Operations and ports\n\n- `sync render({ state }) -> { state, html }`\n- `sync handle_event({ state, event }) -> { state, html }`\n',
    'prompts/math.prompt.md': '# Math\n\n## Operations and ports\n\n- `sync add({ a, b }) -> { sum }`\n',
    'user_stories/counter.md': '# Tap counter\n\nAs a shopper, I want to tap +1, so that the count updates.\n\n## Acceptance criteria\n\n1. Starts at 0.\n',
    'user_stories/math.md': '# Add numbers\n\nAs a clerk, I want to add numbers, so that totals match.\n\n## Acceptance criteria\n\n1. 1 + 2 = 3.\n',
    'tests/counter.json': {
      entry_path: 'prompts/counter.prompt.md',
      steps: [{ id: 'open', op: 'render', input: { state: { count: 0 } }, checks: { '1': [['result', '/state/count', '=', 0]] } }],
    },
    'tests/math.json': {
      entry_path: 'prompts/math.prompt.md',
      steps: [{ id: 'sum', op: 'add', input: { a: 1, b: 2 }, checks: { '1': [['result', '/sum', '=', 3]] } }],
    },
  }, { commit: true });

  const fake = await fakeRuntime(t, entry => {
    if (entry.method === 'POST' && entry.command === 'lint') {
      return {
        status: 200,
        json: fake.lint(entry.request.requestId, [
          { path: 'prompts/counter.prompt.md', state: 'approved', admission_state: 'approved', interface: { calls: [] } },
          { path: 'prompts/math.prompt.md', state: 'approved', admission_state: 'approved', interface: { calls: [] } },
          { path: 'prompts/prose-only.prompt.md', state: 'approved', admission_state: 'approved', interface: { calls: [] } },
        ]),
      };
    }
    if (entry.method === 'POST' && entry.command === 'try') {
      const job = fake.tryJob(entry.request.requestId);
      job.result.session.tab = entry.request.tab;
      fake.jobs.set(entry.request.requestId, job);
      return { status: 200, json: job };
    }
    if (entry.method === 'DELETE' && entry.url.startsWith('/v1/try/')) {
      const tryId = entry.url.slice('/v1/try/'.length);
      return { status: 200, json: fake.stopJob(entry.headers['x-request-id'] || 'stop-1', tryId) };
    }
    if (entry.method === 'GET' && entry.url.startsWith('/v1/runs/')) {
      const id = entry.url.slice('/v1/runs/'.length);
      return { status: 200, json: fake.jobs.get(id) ?? fake.tryJob(id) };
    }
    if (entry.method === 'GET' && entry.url.endsWith('/tests')) {
      return { status: 200, json: { tests: [] } };
    }
    return { status: 404, json: { error: { code: 'not-found' } } };
  });
  fake.capacity = () => ({
    status: 200,
    json: { ok: true, maintenance: false, engine_sha: 'eae2202a68d00ab762fcbbf1eba0d8607a132a15', features: ['lazy-interfaces', 'lint-tests'] },
  });
  const env = { ...process.env, PDD_STATE_DIR: f.state, PDD_RUNTIME_URL: fake.origin };

  const p1 = portsFor(env);
  const code1 = await runTry({ cwd: f.root, words: ['counter'], options: { '--no-open': true, '--no-wait': true } }, p1.ports);
  assert.equal(code1, 0, `${p1.ports.stdout.text}\n${p1.ports.stderr.text}`);
  const tryPosts = () => fake.posts.filter(p => p.command === 'try').map(p => ({ seed: p.request.seed, tab: p.request.tab }));
  assert.deepEqual(tryPosts(), [{ seed: 'tests/counter.json', tab: 'screen' }]);
  assert.doesNotMatch(p1.ports.stderr.text, /Form tab/);

  const p2 = portsFor(env);
  const code2 = await runTry({ cwd: f.root, words: ['counter'], options: { '--no-open': true, '--no-wait': true } }, p2.ports);
  assert.equal(code2, 0, `${p2.ports.stdout.text}\n${p2.ports.stderr.text}`);
  assert.equal(tryPosts().length, 1);
  assert.doesNotMatch(p2.ports.stderr.text, /--tab apply only to a new Try|Form tab/);

  const p3 = portsFor(env);
  const code3 = await runTry({ cwd: f.root, words: ['counter'], options: { '--new': true, '--tab': 'call', '--no-open': true, '--no-wait': true } }, p3.ports);
  assert.equal(code3, 0, `${p3.ports.stdout.text}\n${p3.ports.stderr.text}`);
  assert.deepEqual(tryPosts()[1], { seed: 'tests/counter.json', tab: 'call' });

  const p4 = portsFor(env);
  const code4 = await runTry({ cwd: f.root, words: ['math'], options: { '--no-open': true, '--no-wait': true } }, p4.ports);
  assert.equal(code4, 0, `${p4.ports.stdout.text}\n${p4.ports.stderr.text}`);
  assert.deepEqual(tryPosts()[2], { seed: 'tests/math.json', tab: 'call' });

  const p5 = portsFor(env);
  const code5 = await runTry({ cwd: f.root, words: ['counter'], options: { '--shell': true, '--no-open': true, '--no-wait': true } }, p5.ports);
  assert.equal(code5, 125);
  assert.doesNotMatch(p5.ports.stderr.text, /Choose one of --cli/);

  writeFileSync(join(f.root, 'prompts/prose-only.prompt.md'), '# Notes\n\n## Operations and ports\n\n- `sync sum({ a, b }) -> { total }` — do not call render() or handle_event() here.\n');
  writeFileSync(join(f.root, 'user_stories/prose-only.md'), '# Sum\n\nAs a clerk, I want sums, so that numbers match.\n\n## Acceptance criteria\n\n1. 2 + 2 = 4.\n');
  writeFileSync(join(f.root, 'tests/prose-only.json'), JSON.stringify({
    entry_path: 'prompts/prose-only.prompt.md',
    steps: [{ id: 's1', op: 'sum', input: { a: 2, b: 2 }, checks: { '1': [['result', '/total', '=', 4]] } }],
  }));
  f.git('add', '.');
  const p6 = portsFor(env);
  const code6 = await runTry({ cwd: f.root, words: ['prose-only'], options: { '--no-open': true, '--no-wait': true } }, p6.ports);
  assert.equal(code6, 0, `${p6.ports.stdout.text}\n${p6.ports.stderr.text}`);
  assert.deepEqual(tryPosts()[3], { seed: 'tests/prose-only.json', tab: 'call' });

  const p7 = portsFor(env);
  const code7 = await runTry({ cwd: join(f.root, 'tests'), words: ['counter.json'], options: { '--new': true, '--no-open': true, '--no-wait': true } }, p7.ports);
  assert.equal(code7, 0, `${p7.ports.stdout.text}\n${p7.ports.stderr.text}`);
  assert.deepEqual(tryPosts()[4], { seed: 'tests/counter.json', tab: 'screen' });

  const p8 = portsFor(env);
  p8.ports.stderr.isTTY = true;
  p8.ports.stdout.isTTY = true;
  const observedBridgeStderrIsTty = [];
  p8.ports.loadAgentDefinitions = () => [{ id: 'codex', name: 'Codex', kind: 'codex', command: 'codex', env: {} }];
  p8.ports.agentBridge = context => {
    observedBridgeStderrIsTty.push(context.ports.stderr.isTTY);
    return { run: async () => 0, close: async () => {} };
  };
  p8.ports.captureSource = (rootArg, optsArg) => {
    const cap = captureSource(rootArg, optsArg);
    return { ...cap, warnings: ['Synthetic capture notice for reopen test'] };
  };
  const code8 = await runTry({ cwd: f.root, words: ['counter'], options: { '--no-open': true } }, p8.ports);
  assert.equal(code8, 0, `${p8.ports.stdout.text}\n${p8.ports.stderr.text}`);
  assert.deepEqual(observedBridgeStderrIsTty, [true]);
  assert.equal((p8.ports.stderr.text.match(/Synthetic capture notice for reopen test/g) ?? []).length, 1);
  assert.doesNotMatch(p8.ports.stderr.text, /--tab apply only to a new Try|Form tab/);
});

test('3596 runTry does not hijack mixed CLI+UI or HTTP+UI whole-project sessions to tab=screen and defers to Git-visible app-map.json', async t => {
  const makePromptWithIface = (prose, ifaceObj) => {
    const base = { ...ifaceObj, limits: { max_steps: 1, max_model_calls: 1 }, status: 'approved' };
    const stub = `${prose}\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify({ ...base, prose_sha256: '0'.repeat(64) })}\n\`\`\`\n</details>\n`;
    const hashVal = proseSha256(stub);
    return `${prose}\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify({ ...base, prose_sha256: hashVal })}\n\`\`\`\n</details>\n`;
  };
  const cliPrompt = makePromptWithIface('# Tool\n\nCLI tool.', {
    schema_version: 'prompt-runtime.prompt-interface.v1',
    entries: [{
      operation: 'main',
      input_schema: { type: 'object', properties: { argv: { type: 'array', items: { type: 'string' } } }, required: ['argv'], additionalProperties: false },
      result_schema: { type: 'object', properties: { exit_code: { type: 'integer' }, stdout: { type: 'string' }, stderr: { type: 'string' } }, required: ['exit_code', 'stdout', 'stderr'], additionalProperties: false },
    }],
    conventions: [
      { path: '/entries/0/input_schema', convention: 'cli' },
      { path: '/entries/0/result_schema', convention: 'cli' },
    ],
  });
  const httpPrompt = makePromptWithIface('# API\n\nHTTP API.', {
    schema_version: 'prompt-runtime.prompt-interface.v1',
    entries: [{
      operation: 'ping',
      input_schema: { title: 'HTTP GET /ping', type: 'object', properties: {}, required: [], additionalProperties: false },
      result_schema: { type: 'object', properties: { status: { type: 'integer' }, body: { type: 'string' } }, required: ['status', 'body'], additionalProperties: false },
    }],
    conventions: [],
  });

  const fCli = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\n## Operations and ports\n\n- `sync render({ state }) -> { state, html }`\n- `sync handle_event({ state, event }) -> { state, html }`\n',
    'prompts/tool.prompt.md': cliPrompt,
    'user_stories/counter.md': '# Counter\n\nAs a shopper, I want to count, so that totals match.\n\n## Acceptance criteria\n\n1. Starts at 0.\n',
    'user_stories/tool.md': '# Tool\n\nAs an operator, I want ping, so that health checks work.\n\n## Acceptance criteria\n\n1. Prints ok.\n',
    'tests/counter.json': { entry_path: 'prompts/counter.prompt.md', steps: [{ id: 'open', op: 'render', input: { state: { count: 0 } }, checks: { '1': [['result', '/state/count', '=', 0]] } }] },
    'tests/tool.json': { entry_path: 'prompts/tool.prompt.md', steps: [{ id: 'run', op: 'main', input: { argv: ['ping'] }, checks: { '1': [['result', '/exit_code', '=', 0]] } }] },
  }, { commit: true });

  const fakeCli = await fakeRuntime(t, entry => {
    if (entry.method === 'POST' && entry.command === 'lint') {
      return {
        status: 200,
        json: fakeCli.lint(entry.request.requestId, [
          { path: 'prompts/counter.prompt.md', state: 'approved', admission_state: 'approved', interface: { calls: [] } },
          { path: 'prompts/tool.prompt.md', state: 'approved', admission_state: 'approved', interface: { calls: [] } },
        ]),
      };
    }
    if (entry.method === 'POST' && entry.command === 'try') {
      const job = fakeCli.tryJob(entry.request.requestId);
      job.result.session.tab = entry.request.tab;
      fakeCli.jobs.set(entry.request.requestId, job);
      return { status: 200, json: job };
    }
    if (entry.method === 'GET' && entry.url.startsWith('/v1/runs/')) {
      const id = entry.url.slice('/v1/runs/'.length);
      return { status: 200, json: fakeCli.jobs.get(id) ?? fakeCli.tryJob(id) };
    }
    if (entry.method === 'GET' && entry.url.endsWith('/tests')) return { status: 200, json: { tests: [] } };
    return { status: 404, json: { error: { code: 'not-found' } } };
  });
  fakeCli.capacity = () => ({ status: 200, json: { ok: true, maintenance: false, engine_sha: 'eae2202a68d00ab762fcbbf1eba0d8607a132a15', features: ['lazy-interfaces', 'lint-tests'] } });
  const pCli = portsFor({ ...process.env, PDD_STATE_DIR: fCli.state, PDD_RUNTIME_URL: fakeCli.origin }, { shell: () => 0 });
  const codeCli = await runTry({ cwd: fCli.root, words: [], options: { '--no-open': true, '--no-wait': true } }, pCli.ports);
  assert.equal(codeCli, 0, `${pCli.ports.stdout.text}\n${pCli.ports.stderr.text}`);
  assert.equal(fakeCli.posts.find(p => p.command === 'try').request.tab, 'terminal');

  const fHttp = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\n## Operations and ports\n\n- `sync render({ state }) -> { state, html }`\n- `sync handle_event({ state, event }) -> { state, html }`\n',
    'prompts/api.prompt.md': httpPrompt,
    'user_stories/counter.md': '# Counter\n\nAs a shopper, I want to count, so that totals match.\n\n## Acceptance criteria\n\n1. Starts at 0.\n',
    'user_stories/api.md': '# API\n\nAs a client, I want ping, so that health checks work.\n\n## Acceptance criteria\n\n1. Returns 200.\n',
    'tests/counter.json': { entry_path: 'prompts/counter.prompt.md', steps: [{ id: 'open', op: 'render', input: { state: { count: 0 } }, checks: { '1': [['result', '/state/count', '=', 0]] } }] },
    'tests/api.json': { entry_path: 'prompts/api.prompt.md', steps: [{ id: 'ping', op: 'ping', input: {}, checks: { '1': [['result', '/status', '=', 200]] } }] },
  }, { commit: true });

  const fakeHttp = await fakeRuntime(t, entry => {
    if (entry.method === 'POST' && entry.command === 'lint') {
      return {
        status: 200,
        json: fakeHttp.lint(entry.request.requestId, [
          { path: 'prompts/counter.prompt.md', state: 'approved', admission_state: 'approved', interface: { calls: [] } },
          { path: 'prompts/api.prompt.md', state: 'approved', admission_state: 'approved', interface: { calls: [] } },
        ]),
      };
    }
    if (entry.method === 'POST' && entry.command === 'try') {
      const job = fakeHttp.tryJob(entry.request.requestId);
      job.result.session.tab = entry.request.tab;
      return { status: 200, json: job };
    }
    if (entry.method === 'GET' && entry.url.endsWith('/tests')) return { status: 200, json: { tests: [] } };
    if (entry.method === 'GET' && entry.url.endsWith('/model')) {
      return {
        status: 200,
        json: {
          entries: [{
            entry_path: 'prompts/api.prompt.md',
            operation: 'ping',
            http: { method: 'GET', path: '/ping' },
            input_schema: { title: 'HTTP GET /ping', type: 'object', properties: {} },
            result_schema: { type: 'object', properties: { status: { type: 'integer' }, body: { type: 'string' } } },
          }],
        },
      };
    }
    return { status: 404, json: { error: { code: 'not-found' } } };
  });
  fakeHttp.capacity = () => ({ status: 200, json: { ok: true, maintenance: false, engine_sha: 'eae2202a68d00ab762fcbbf1eba0d8607a132a15', features: ['lazy-interfaces', 'lint-tests'] } });
  let servedHttp = false;
  const pHttp = portsFor({ ...process.env, PDD_STATE_DIR: fHttp.state, PDD_RUNTIME_URL: fakeHttp.origin }, {
    serve: async () => { servedHttp = true; return 0; },
  });
  const codeHttp = await runTry({ cwd: fHttp.root, words: [], options: { '--no-open': true, '--no-wait': true } }, pHttp.ports);
  assert.equal(codeHttp, 0, `${pHttp.ports.stdout.text}\n${pHttp.ports.stderr.text}`);
  assert.equal(fakeHttp.posts.find(p => p.command === 'try').request.tab, 'call');
  assert.equal(servedHttp, true);

  writeFileSync(join(fCli.root, 'app-map.json'), JSON.stringify({
    schema_version: 'prompt-runtime.app-map.v1',
    name: 'OtherScreen',
    initial_screen: 'other',
    initial_route: null,
    initial_state: { count: 0 },
    state_schema: { type: 'object', properties: { count: { type: 'integer' } }, required: ['count'], additionalProperties: false },
    synthetic: true,
    router: null,
    routes: [],
    stylesheets: [],
    screens: [{ id: 'other', prompt_path: 'prompts/tool.prompt.md', operation: 'render', source: 'operation', format: 'html', input: { state: { $ref: '/state' } }, result_pointer: '/html' }],
    handlers: [],
  }, null, 2));
  fCli.git('add', 'app-map.json');
  const pMap = portsFor({ ...process.env, PDD_STATE_DIR: fCli.state, PDD_RUNTIME_URL: fakeCli.origin });
  const codeMap = await runTry({ cwd: fCli.root, words: ['counter'], options: { '--no-open': true, '--no-wait': true } }, pMap.ports);
  assert.equal(codeMap, 0, `${pMap.ports.stdout.text}\n${pMap.ports.stderr.text}`);
  const mapPost = fakeCli.posts.filter(p => p.command === 'try').at(-1);
  assert.equal(mapPost.request.app_map, 'app-map.json');
  assert.equal(mapPost.request.tab, 'call');

  const runsBeforeReopen = fakeCli.gets.filter(g => g.url.startsWith('/v1/runs/')).length;
  const pMapReopen = portsFor({ ...process.env, PDD_STATE_DIR: fCli.state, PDD_RUNTIME_URL: fakeCli.origin });
  const codeMapReopen = await runTry({ cwd: fCli.root, words: ['counter'], options: { '--no-open': true, '--no-wait': true } }, pMapReopen.ports);
  assert.equal(codeMapReopen, 0, `${pMapReopen.ports.stdout.text}\n${pMapReopen.ports.stderr.text}`);
  const runsAfterReopen = fakeCli.gets.filter(g => g.url.startsWith('/v1/runs/')).length;
  assert.equal(runsAfterReopen - runsBeforeReopen, 1);
});

test('3596 R1-3/4: plain-prose CLI+UI and HTTP+UI repos, scenario app_maps, and runtime-client@1.1.0 reopen error wording', async t => {
  // 1. Mixed plain-prose CLI + UI repo (no Runtime interface blocks anywhere)
  const fPlainCli = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\n## Operations and ports\n\n- `sync render({ state }) -> { state, html }`\n- `sync handle_event({ state, event }) -> { state, html }`\n',
    'prompts/tool.prompt.md': '# tool\n\n## Operations and ports\n\n- `sync main({ argv }) -> { exit_code, stdout, stderr }`\n',
    'user_stories/counter.md': '# Counter\n\nAs a shopper, I want to count, so that totals match.\n\n## Acceptance criteria\n\n1. Starts at 0.\n',
    'user_stories/tool.md': '# Tool\n\nAs an operator, I want ping, so that health checks work.\n\n## Acceptance criteria\n\n1. Prints ok.\n',
    'tests/counter.json': { entry_path: 'prompts/counter.prompt.md', steps: [{ id: 'open', op: 'render', input: { state: { count: 0 } }, checks: { '1': [['result', '/state/count', '=', 0]] } }] },
    'tests/tool.json': { entry_path: 'prompts/tool.prompt.md', steps: [{ id: 'run', op: 'main', input: { argv: ['ping'] }, checks: { '1': [['result', '/exit_code', '=', 0]] } }] },
  }, { commit: true });

  const seenPlainCli = [];
  await runTry(
    { cwd: fPlainCli.root, words: [], options: {} },
    {
      ...captureStreams(),
      env: { ...process.env, PDD_STATE_DIR: fPlainCli.state },
      runTry: async input => {
        seenPlainCli.push(input.options);
        return 0;
      },
    },
  );
  assert.deepEqual(seenPlainCli, [{}]);

  // 2. Mixed plain-prose HTTP + UI repo (no Runtime interface blocks anywhere)
  const fPlainHttp = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\n## Operations and ports\n\n- `sync render({ state }) -> { state, html }`\n- `sync handle_event({ state, event }) -> { state, html }`\n',
    'prompts/api.prompt.md': '# API\n\n## Operations and ports\n\n- `sync ping({}) -> { status, body }` — handles `HTTP GET /ping`.\n',
    'user_stories/counter.md': '# Counter\n\nAs a shopper, I want to count, so that totals match.\n\n## Acceptance criteria\n\n1. Starts at 0.\n',
    'user_stories/api.md': '# API\n\nAs a client, I want ping, so that health checks work.\n\n## Acceptance criteria\n\n1. Returns 200.\n',
    'tests/counter.json': { entry_path: 'prompts/counter.prompt.md', steps: [{ id: 'open', op: 'render', input: { state: { count: 0 } }, checks: { '1': [['result', '/state/count', '=', 0]] } }] },
    'tests/api.json': { entry_path: 'prompts/api.prompt.md', steps: [{ id: 'ping', op: 'ping', input: {}, checks: { '1': [['result', '/status', '=', 200]] } }] },
  }, { commit: true });

  const seenPlainHttp = [];
  await runTry(
    { cwd: fPlainHttp.root, words: [], options: {} },
    {
      ...captureStreams(),
      env: { ...process.env, PDD_STATE_DIR: fPlainHttp.state },
      runTry: async input => {
        seenPlainHttp.push(input.options);
        return 0;
      },
    },
  );
  assert.deepEqual(seenPlainHttp, [{}]);

  // 3. Scenario declaring app_maps (without root app-map.json) bails out of seam --tab screen injection
  const fScenarioMap = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\n## Operations and ports\n\n- `sync render({ state }) -> { state, html }`\n- `sync handle_event({ state, event }) -> { state, html }`\n',
    'app/maps/custom.json': { initial_state: { count: 0 }, screens: [{ prompt_path: 'prompts/counter.prompt.md' }] },
    'user_stories/counter.md': '# Counter\n\nAs a shopper, I want to count, so that totals match.\n\n## Acceptance criteria\n\n1. Starts at 0.\n',
    'tests/counter.json': {
      entry_path: 'prompts/counter.prompt.md',
      app_maps: ['app/maps/custom.json'],
      steps: [{ id: 'open', op: 'render', input: { state: { count: 0 } }, checks: { '1': [['result', '/state/count', '=', 0]] } }],
    },
  }, { commit: true });

  const seenScenarioMap = [];
  await runTry(
    { cwd: fScenarioMap.root, words: ['counter'], options: {} },
    {
      ...captureStreams(),
      env: { ...process.env, PDD_STATE_DIR: fScenarioMap.state },
      runTry: async input => {
        seenScenarioMap.push(input.options);
        return 0;
      },
    },
  );
  assert.deepEqual(seenScenarioMap, [{}]);

  // 4. Reopened Try fallback with updated runtime-client@1.1.0 stderr wording (--app-map, --tab, and --fresh apply only to a new Try)
  const fReopen11 = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\n## Operations and ports\n\n- `sync render({ state }) -> { state, html }`\n- `sync handle_event({ state, event }) -> { state, html }`\n',
    'user_stories/counter.md': '# Counter\n\nAs a shopper, I want to count, so that totals match.\n\n## Acceptance criteria\n\n1. Starts at 0.\n',
    'tests/counter.json': { entry_path: 'prompts/counter.prompt.md', steps: [{ id: 'open', op: 'render', input: { state: { count: 0 } }, checks: { '1': [['result', '/state/count', '=', 0]] } }] },
  }, { commit: true });

  const reopenStreams = captureStreams();
  const reopenCalls = [];
  const reopenCode = await runTry(
    { cwd: fReopen11.root, words: ['counter'], options: {} },
    {
      ...reopenStreams,
      env: { ...process.env, PDD_STATE_DIR: fReopen11.state },
      runTry: async (input, ports) => {
        reopenCalls.push(input.options);
        ports.stderr?.write('Capture notice once\n');
        if (input.options['--tab'] === 'screen') {
          ports.stderr?.write('A Try for "Counter" is already open. --app-map, --tab, and --fresh apply only to a new Try: run pdd simulate counter --new (it stops the open Try first).\n');
          return 2;
        }
        ports.stderr?.write("This Story's operation takes typed input, so it opens on the Form tab.\n");
        ports.stdout?.write('Try budget 400 calls; 400 remaining.\n');
        return 0;
      },
    },
  );
  assert.equal(reopenCode, 0);
  assert.deepEqual(reopenCalls, [{ '--tab': 'screen' }, {}]);
  assert.equal((reopenStreams.err.match(/Capture notice once/g) ?? []).length, 1);
  assert.doesNotMatch(reopenStreams.err, /apply only to a new Try|Form tab/);
});

test('3595/3596 R1-5/6: malformed non-object state_schema warns, screens[] keeps original indices, and docs advertise 4 top-level targets with input as ref_target only', t => {
  for (const badSchema of ['bad', [], null]) {
    const { root } = makeRepo(t, {
      'prompts/screen.prompt.md': '# Screen\n\n- `render({ state })` -> `{ state, html }`\n\n## Dependencies\n\nNone.\n',
      'app-map.json': {
        initial_state: { count: 0 },
        state_schema: badSchema,
        screens: [{ prompt_path: 'prompts/screen.prompt.md', operation: 'render', result_pointer: '/html' }],
      },
    });
    const warnings = lintSvgLayouts({ root, files: gitFiles(root) });
    assert.ok(
      warnings.some(line => line === 'Warning: app-map.json: state_schema must be a JSON Schema object (or omit it for compact app-map.json).'),
      `expected state_schema warning for ${JSON.stringify(badSchema)}, got:\n${warnings.join('\n')}`,
    );
  }

  // Leading non-object entry in screens[] must not shift screen-2 down to main
  const { root: idxRoot } = makeRepo(t, {
    'prompts/second.prompt.md': [
      '# Second Screen',
      '',
      '## Appearance',
      '',
      '![Second](views/second__desktop.ui.svg)',
      '',
      'Render `<button id="go">Go</button>`.',
      '',
      '## Dependencies',
      '',
      'None.',
      '',
    ].join('\n'),
    'prompts/views/second__desktop.ui.svg': '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 100 50"><title>Second</title><desc>Second screen</desc><g id="go"><rect width="80" height="30"/><text x="10" y="20">Go</text></g></svg>\n',
    'app-map.json': {
      initial_state: {},
      screens: [
        null,
        { prompt_path: 'prompts/second.prompt.md', operation: 'render', result_pointer: '/html' },
        { prompt_path: 'prompts/missing.prompt.md', operation: 'render', result_pointer: '/html' },
      ],
    },
  });
  const idxWarnings = lintSvgLayouts({ root: idxRoot, files: gitFiles(idxRoot) });
  assert.ok(idxWarnings.some(line => /screen "screen-3".*prompts\/missing\.prompt\.md/.test(line)), idxWarnings.join('\n'));
  assert.ok(idxWarnings.some(line => /screen-2/.test(line)), `expected screen-2 in stylesheet warning, got:\n${idxWarnings.join('\n')}`);
  assert.ok(!idxWarnings.some(line => /\bscreen "main"\b/.test(line)), idxWarnings.join('\n'));

  // R1-6: docs document 4 top-level check targets and input as ref_target only
  for (const rel of [
    '../skills/pdd-prompting/RUNBOOK.md',
    '../skills/pdd-prompting/guide.md',
    '../skills/pdd-prompting/story-guide.md',
    '../skills/pdd-prompting/runbook/checks-and-budgets.md',
  ]) {
    const content = readFileSync(new URL(rel, import.meta.url), 'utf8');
    assert.doesNotMatch(content, /5-target|5 targets|five core check targets/i, `${rel} must not advertise 5 top-level targets`);
    assert.match(content, /ref_target/, `${rel} must clarify input as ref_target`);
  }
});

test('3596 R2-1/2: whole-project plain-prose UI injects --tab screen when only non-seed Story has saved Try, and post-startup --tab stderr never triggers spurious retry', async t => {
  // R2-1: 2-Story plain-prose UI repo (alpha, beta) with saved per-Story Try ONLY on non-seed tests/beta.json
  const fTwo = makeRepo(t, {
    'prompts/alpha.prompt.md': '# Alpha\n\n## Operations and ports\n\n- `sync render({ state }) -> { state, html }`\n- `sync handle_event({ state, event }) -> { state, html }`\n',
    'prompts/beta.prompt.md': '# Beta\n\n## Operations and ports\n\n- `sync render({ state }) -> { state, html }`\n- `sync handle_event({ state, event }) -> { state, html }`\n',
    'user_stories/alpha.md': '# Alpha screen\n\nAs a shopper, I want alpha, so that alpha renders.\n\n## Acceptance criteria\n\n1. Starts at 0.\n',
    'user_stories/beta.md': '# Beta screen\n\nAs a shopper, I want beta, so that beta renders.\n\n## Acceptance criteria\n\n1. Starts at 0.\n',
    'tests/alpha.json': { entry_path: 'prompts/alpha.prompt.md', steps: [{ id: 'open', op: 'render', input: { state: { count: 0 } }, checks: { '1': [['result', '/state/count', '=', 0]] } }] },
    'tests/beta.json': { entry_path: 'prompts/beta.prompt.md', steps: [{ id: 'open', op: 'render', input: { state: { count: 0 } }, checks: { '1': [['result', '/state/count', '=', 0]] } }] },
  }, { commit: true });

  const { createHash } = await import('node:crypto');
  const repoKey = createHash('sha256').update(realpathSync(fTwo.root)).digest('hex').slice(0, 16);
  const reposDir = join(fTwo.state, 'repos');
  mkdirSync(reposDir, { recursive: true });
  writeFileSync(
    join(reposDir, `${repoKey}.json`),
    JSON.stringify({
      root: realpathSync(fTwo.root),
      last_batch: null,
      tries: {
        'tests/beta.json': { id: 'saved-beta-try', story: 'beta', storyPath: 'user_stories/beta.md' },
      },
    }),
  );

  const seenWhole = [];
  const wholeCode = await runTry(
    { cwd: fTwo.root, words: [], options: {} },
    {
      ...captureStreams(),
      env: { ...process.env, PDD_STATE_DIR: fTwo.state },
      runTry: async input => {
        seenWhole.push(input.options);
        return 0;
      },
    },
  );
  assert.equal(wholeCode, 0);
  assert.deepEqual(seenWhole, [{ '--tab': 'screen' }]);

  // Named beta still detects its saved Try and reopens without injecting --tab
  const seenBeta = [];
  const betaCode = await runTry(
    { cwd: fTwo.root, words: ['beta'], options: {} },
    {
      ...captureStreams(),
      env: { ...process.env, PDD_STATE_DIR: fTwo.state },
      runTry: async input => {
        seenBeta.push(input.options);
        return 0;
      },
    },
  );
  assert.equal(betaCode, 0);
  assert.deepEqual(seenBeta, [{}]);

  // R2-2: post-startup stderr matching /--tab\b[^\n]*new/i passes through and NEVER triggers a second invoke even on exit 2
  const postStartupStreams = captureStreams();
  const postStartupCalls = [];
  const postStartupCode = await runTry(
    { cwd: fTwo.root, words: ['alpha'], options: {} },
    {
      ...postStartupStreams,
      env: { ...process.env, PDD_STATE_DIR: fTwo.state },
      runTry: async (input, ports) => {
        postStartupCalls.push(input.options);
        ports.stdout?.write('Try budget 400 calls; 400 remaining.\n');
        ports.stderr?.write('Post-startup note: pass --tab screen with --new next time.\n');
        return 2;
      },
    },
  );
  assert.equal(postStartupCode, 2);
  assert.deepEqual(postStartupCalls, [{ '--tab': 'screen' }]);
  assert.match(postStartupStreams.err, /Post-startup note: pass --tab screen with --new next time\./);
});
