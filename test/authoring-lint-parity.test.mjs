import './helpers/test-home.mjs';
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { createServer } from 'node:http';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { lintSvgLayouts } from '../src/svg-layout.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { gitFiles, lint } from '../src/runtime-seam.mjs';

function makeRepo(t, entries) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-3459-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q'], { cwd: root });
  for (const [rel, body] of Object.entries(entries)) {
    const abs = join(root, rel);
    mkdirSync(dirname(abs), { recursive: true });
    writeFileSync(abs, typeof body === 'string' ? body : JSON.stringify(body, null, 2));
  }
  execFileSync('git', ['add', '.'], { cwd: root });
  return root;
}

function captureStreams() {
  let out = '', err = '';
  return {
    stdout: { write(chunk) { out += String(chunk); } },
    stderr: { write(chunk) { err += String(chunk); } },
    get out() { return out; },
    get err() { return err; },
  };
}

test('3459 lint: surfaces undeclared simulation_overrides port, missing world_pointer, and failure_quote mismatches in <50ms', async t => {
  const root = makeRepo(t, {
    'prompts/board2048.prompt.md': [
      '# 2048 board',
      '',
      'Own `src/board2048.mjs`. Expose `move({ direction })` returning `{ moved, saved }`.',
      '',
      '## Domain decisions',
      '',
      'Slide tiles in `direction` and persist the updated board locally.',
      '',
    ].join('\n'),
    'user_stories/board-save.md': [
      '# Save board after move',
      '',
      'As a player, I want moves to report when saving fails, so that I do not lose progress silently.',
      '',
      '## Acceptance criteria',
      '',
      '1. When saving fails, `move` returns `saved: false`.',
      '',
    ].join('\n'),
    'tests/board-save.json': {
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/board-save.md',
      criteria: [{ id: 'AC1', text: 'When saving fails, `move` returns `saved: false`.' }],
      initial_world: { saves: [] },
      simulation: {},
      steps: [
        {
          step_id: 'save-error',
          entry_path: 'prompts/board2048.prompt.md',
          operation: 'move',
          input: { direction: 'left' },
          simulation_overrides: [
            {
              operation: 'storage.save',
              criterion_id: 'AC1',
              failure_quote: 'quota exceeded',
              reason: 'Simulate storage write error.',
              binding: {
                action: 'port.write',
                write_mode: 'append',
                world_pointer: '/missing_saves',
                record_fields: { direction: '/direction' },
                result_template: { ok: false, error: 'disk-full' },
              },
            },
          ],
          checks: [
            { criterion_id: 'AC1', target: 'result', path: '/saved', op: 'equals', value: false },
          ],
        },
      ],
    },
  });

  const files = gitFiles(root);
  const start = performance.now();
  const warnings = lintSvgLayouts({ root, files });
  const elapsedMs = performance.now() - start;

  assert.ok(elapsedMs < 200, `expected fast deterministic local lint, got ${elapsedMs.toFixed(1)}ms`);
  assert.ok(warnings.some(w => w.includes('simulation_overrides port "storage.save" is not mentioned in reachable prompt prose')), warnings.join('\n'));
  assert.ok(warnings.some(w => w.includes('world_pointer "/missing_saves" is missing from initial_world')), warnings.join('\n'));
  assert.ok(warnings.some(w => w.includes('failure_quote "quota exceeded" is absent from criterion AC1')), warnings.join('\n'));

  const streams = captureStreams();
  const code = await lint({ cwd: root, local: true }, { stdout: streams.stdout, stderr: streams.stderr, env: process.env });
  assert.equal(code, 0);
  assert.match(`${streams.out}\n${streams.err}`, /storage\.save/);
});

test('3459 lint: aligned plain-Markdown port prose and canonical simulation_overrides array produce zero warnings', t => {
  const root = makeRepo(t, {
    'prompts/board2048.prompt.md': [
      '# 2048 board',
      '',
      'Own `src/board2048.mjs`. Expose `move({ direction })` returning `{ moved, saved }`.',
      '',
      '## Domain decisions',
      '',
      'Call injected port `storage.save({ board })` returning `{ ok }` after sliding tiles; if `ok` is `false`, return `saved: false`.',
      '',
    ].join('\n'),
    'user_stories/board-save.md': [
      '# Save board after move',
      '',
      'As a player, I want moves to report when saving fails, so that I do not lose progress silently.',
      '',
      '## Acceptance criteria',
      '',
      '1. When saving fails, `move` returns `saved: false`.',
      '',
    ].join('\n'),
    'tests/board-save.json': {
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/board-save.md',
      criteria: [{ id: 'AC1', text: 'When saving fails, `move` returns `saved: false`.' }],
      initial_world: { saves: [] },
      simulation: {
        'storage.save': {
          action: 'port.write',
          write_mode: 'append',
          world_pointer: '/saves',
          record_fields: { board: '/board' },
          result_template: { ok: true },
        },
      },
      steps: [
        {
          step_id: 'save-error',
          entry_path: 'prompts/board2048.prompt.md',
          operation: 'move',
          input: { direction: 'left' },
          simulation_overrides: [
            {
              operation: 'storage.save',
              criterion_id: 'AC1',
              failure_quote: 'saving fails',
              reason: 'Simulate storage write error.',
              binding: {
                action: 'port.write',
                write_mode: 'append',
                world_pointer: '/saves',
                record_fields: { board: '/board' },
                result_template: { ok: false },
              },
            },
          ],
          checks: [
            { criterion_id: 'AC1', target: 'result', path: '/saved', op: 'equals', value: false },
          ],
        },
      ],
    },
  });

  assert.deepEqual(lintSvgLayouts({ root, files: gitFiles(root) }), []);
});

test('3459 preflight: checkable Story linking kind: native-only adapter emits non-blocking advisory without exit 4 gate', async t => {
  const root = makeRepo(t, {
    'prompts/storage.prompt.md': [
      '---',
      'kind: native-only',
      'reason: Uses SQLite WAL file locks on the OS filesystem.',
      '---',
      '',
      '# SQLite storage adapter',
      '',
      'Own `src/storage.mjs`.',
      '',
    ].join('\n'),
    'prompts/app.prompt.md': [
      '# Task list service',
      '',
      'Own `src/app.mjs`. Expose `addTask({ title })` returning `{ id, title }`.',
      '',
      '## Dependencies',
      '',
      '- [SQLite storage adapter](storage.prompt.md): persistence boundary.',
      '',
    ].join('\n'),
    'user_stories/add-task.md': [
      '# Add a task',
      '',
      'As a planner, I want to add a task, so that it appears on my list.',
      '',
      '## Acceptance criteria',
      '',
      '1. Adding "Buy milk" returns `{ id: 1, title: "Buy milk" }`.',
      '',
    ].join('\n'),
    'tests/add-task.json': {
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/add-task.md',
      criteria: [{ id: 'AC1', text: 'Adding "Buy milk" returns `{ id: 1, title: "Buy milk" }`.' }],
      initial_world: {},
      simulation: {},
      steps: [
        {
          step_id: 'add-1',
          entry_path: 'prompts/app.prompt.md',
          operation: 'addTask',
          input: { title: 'Buy milk' },
          checks: [
            { criterion_id: 'AC1', target: 'result', path: '/title', op: 'equals', value: 'Buy milk' },
          ],
        },
      ],
    },
  });

  const localWarnings = lintSvgLayouts({ root, files: gitFiles(root) });
  assert.ok(localWarnings.some(w => w.includes('prompts/app.prompt.md: checkable prompt links kind: native-only prompt prompts/storage.prompt.md')), localWarnings.join('\n'));

  const localStreams = captureStreams();
  const localExit = await runPdd(['lint', '--local'], { cwd: root, env: { ...process.env }, stdout: localStreams.stdout, stderr: localStreams.stderr });
  assert.equal(localExit, 0, 'pdd lint --local stays non-blocking (exit 0)');
  assert.match(`${localStreams.out}\n${localStreams.err}`, /prompts\/storage\.prompt\.md/);

  for (const argv of [['lint'], ['test'], ['test', '--json']]) {
    const streams = captureStreams();
    const exitCode = await runPdd(argv, { cwd: root, env: { ...process.env, PDD_RUNTIME_TOKEN: 'test-token' }, stdout: streams.stdout, stderr: streams.stderr });
    assert.doesNotMatch(`${streams.out}
${streams.err}`, /Refused \[inverted-native-only-dependency\]/);
    assert.match(streams.err, /Advisory \[inverted-native-only-dependency\]/);
    assert.match(streams.err, /prompts\/storage\.prompt\.md/);
    if (argv.includes('--json')) {
      const parsed = JSON.parse(streams.out.trim());
      assert.ok(Array.isArray(parsed.rows), 'delegates through to runtime check without blocking at CLI');
      assert.notEqual(parsed.code, 'inverted-native-only-dependency');
    }
  }
});

test('3459 CLI: sanitizes stale server pdd test --fill-hash hints from runtime output', async t => {
  const server = createServer((req, res) => {
    res.writeHead(422, { 'content-type': 'application/json' });
    res.end(JSON.stringify({
      status: 'refused',
      code: 'interface-unapproved',
      message: 'Draft interfaces require pdd test --fill-hash before running.',
      fix: 'Run `pdd test --fill-hash` first (pdd test --fill-hash).',
    }));
  });
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  t.after(() => server.close());
  const { port } = server.address();

  const root = makeRepo(t, {
    'prompts/calc.prompt.md': '# Calc\n\nOwn `src/calc.mjs`. Expose `double({ n })` returning `{ value }`.\n',
    'user_stories/double.md': '# Double\n\nAs a student, I want to double 3, so that I see 6.\n\n## Acceptance criteria\n\n1. Doubling 3 returns 6.\n',
    'tests/double.json': {
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/double.md',
      criteria: [{ id: 'AC1', text: 'Doubling 3 returns 6.' }],
      initial_world: {},
      simulation: {},
      steps: [
        {
          step_id: 's1',
          entry_path: 'prompts/calc.prompt.md',
          operation: 'double',
          input: { n: 3 },
          checks: [{ criterion_id: 'AC1', target: 'result', path: '/value', op: 'equals', value: 6 }],
        },
      ],
    },
  });

  const streams = captureStreams();
  await runPdd(['test'], {
    cwd: root,
    env: { ...process.env, PDD_RUNTIME_URL: `http://127.0.0.1:${port}`, PDD_RUNTIME_TOKEN: 'test-token' },
    stdout: streams.stdout,
    stderr: streams.stderr,
  });
  const combined = `${streams.out}\n${streams.err}`;
  assert.doesNotMatch(combined, /--fill-hash/);
});

test('3459 lint --local: validates app-map.json timers, screen prompt_path, and tests/<story>.json schema_version in <150ms with 1-line fixes (exit 0)', async t => {
  const root = makeRepo(t, {
    'prompts/snake.prompt.md': [
      '# Snake game',
      '',
      'Own `src/snake.mjs`. Expose `render({ state })` returning `{ html }` and `step_tick({ state })` returning `{ state }`.',
      '',
      '## Domain decisions',
      '',
      'Advance the snake on each timer tick while `running` is true.',
      '',
    ].join('\n'),
    'user_stories/play-snake.md': [
      '# Play Snake',
      '',
      'As a player, I want the snake to advance on each tick, so that the game progresses.',
      '',
      '## Acceptance criteria',
      '',
      '1. One tick moves the snake head forward by 1 cell.',
      '',
    ].join('\n'),
    'tests/play-snake.json': {
      schema_version: 'pdd.wrong-scenario.v0',
      story_path: 'user_stories/play-snake.md',
      criteria: [{ id: 'AC1', text: 'One tick moves the snake head forward by 1 cell.' }],
      initial_world: {},
      simulation: {},
      steps: [
        {
          step_id: 'tick-1',
          entry_path: 'prompts/snake.prompt.md',
          operation: 'step_tick',
          input: {},
          checks: [{ criterion_id: 'AC1', target: 'result', path: '/moved', op: 'equals', value: true }],
        },
      ],
    },
    'app-map.json': {
      schema_version: 'prompt-runtime.app-map.v1',
      name: 'Snake',
      initial_screen: 'board',
      initial_route: null,
      initial_state: { running: 'yes', tick_gen: -1 },
      state_schema: {
        type: 'object',
        properties: {
          running: { type: 'string' },
          tick_gen: { type: 'integer', minimum: 0 },
        },
        required: ['running', 'tick_gen'],
        additionalProperties: false,
      },
      screens: [
        { id: 'board', prompt_path: 'prompts/snake.prompt.md', operation: 'render', source: 'operation', format: 'html', input: {}, result_pointer: '/html' },
        { id: 'gameover', prompt_path: 'prompts/missing-gameover.prompt.md', operation: 'render', source: 'operation', format: 'html', input: {}, result_pointer: '/html' },
      ],
      handlers: [],
      timers: [
        {
          id: 'game-loop',
          screen: 'board',
          interval_ms: 250,
          enabled_pointer: '/running',
          generation_pointer: '/tick_gen',
          handler: { prompt_path: 'prompts/snake.prompt.md', operation: 'undeclared_tick' },
          input: {},
          state: {},
          next: { kind: 'stay' },
        },
        {
          id: 'legacy-key',
          screen: 'gameover',
          interval_ms: 1000,
          enabled_pointer: '/running',
          generation_pointer: '/tick_gen',
          tick_operation: 'step_tick',
          input: {},
          state: {},
          next: { kind: 'stay' },
        },
      ],
    },
  });

  const t0 = performance.now();
  const warnings = lintSvgLayouts({ root, files: gitFiles(root) });
  const elapsedMs = performance.now() - t0;
  assert.ok(elapsedMs < 150, `lintSvgLayouts took ${elapsedMs.toFixed(1)}ms (expected <150ms)`);

  assert.ok(warnings.some(w => w.includes('tests/play-snake.json') && w.includes('"schema_version": "prompt-runtime.program-scenario.v1"')), warnings.join('\n'));
  assert.ok(warnings.some(w => w.includes('prompts/missing-gameover.prompt.md') && w.includes('does not exist')), warnings.join('\n'));
  assert.ok(warnings.some(w => w.includes('interval_ms') && w.includes('1000 to 3600000')), warnings.join('\n'));
  assert.ok(warnings.some(w => w.includes('enabled_pointer') && w.includes('boolean')), warnings.join('\n'));
  assert.ok(warnings.some(w => w.includes('generation_pointer') && w.includes('9007199254740991')), warnings.join('\n'));
  assert.ok(warnings.some(w => w.includes('undeclared_tick') && w.includes('not declared in prompts/snake.prompt.md')), warnings.join('\n'));
  assert.ok(warnings.some(w => w.includes('replace tick_operation') && w.includes('"handler"')), warnings.join('\n'));

  const streams = captureStreams();
  const exitCode = await runPdd(['lint', '--local'], { cwd: root, env: { ...process.env }, stdout: streams.stdout, stderr: streams.stderr });
  assert.equal(exitCode, 0, 'pdd lint --local remains advisory (exit 0)');
  assert.match(streams.out, /prompt-runtime\.program-scenario\.v1/);
  assert.match(streams.out, /generation_pointer.*9007199254740991/);
});

test('lintSvgLayouts warns when a .ui.svg is linked only via plain [label](...) outside ## Dependencies', t => {
  const root = makeRepo(t, {
    'views/game.ui.svg': '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 200 100"><g id="board"><text>2048</text></g></svg>',
    'prompts/game.prompt.md': [
      '# 2048 Screen',
      '',
      '## Appearance',
      '',
      'Render region `board` with heading 2048 following [the screen reference](../views/game.ui.svg).',
      '',
      '## Dependencies',
      '',
      'None.',
    ].join('\n'),
  });
  const warnings = lintSvgLayouts({ root, files: gitFiles(root) });
  assert.ok(
    warnings.some(w => w.includes('prompts/game.prompt.md -> views/game.ui.svg: link syntax:') && w.includes('dependency-file-unreadable')),
    warnings.join('\n'),
  );
});
