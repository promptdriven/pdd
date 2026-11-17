import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { chmodSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import {
  SHORT_SCENARIO_SCHEMA,
  V1_SCENARIO_SCHEMA,
  compileScenario,
  compileScenarioText,
  isShortScenarioDoc,
  parseExactScenarioJson,
} from '../src/scenario-compile.mjs';
import * as seam from '../src/runtime-seam.mjs';
import { runCompiledTest } from '../src/compiled-test.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { PLACE, fakeRuntime, harbor, portsFor, sink } from './helpers/runtime-fake.mjs';

const SAMPLE_STORY = `# Finish a task

As a person who keeps a to-do list in the terminal, I want to mark a task as done, so that I see what is left.

## Acceptance criteria

1. \`todo done 4\` prints "Done #4: Call mom", exits with code 0 and saves task #4 as done.
2. Task #1 stays not done.
3. \`todo done 9\` prints "todo: no task #9" to stderr, exits with code 1 and saves nothing.
`;

test('Short scenario compiler passes standard program-scenario.v1 documents and BigInt integers through unchanged', () => {
  const v1Raw = [
    '{',
    '  "schema_version": "prompt-runtime.program-scenario.v1",',
    '  "story_path": "user_stories/exact.md",',
    '  "criteria": [{"id": "AC1", "text": "Keeps exact integer 9007199254740993."}],',
    '  "initial_world": {"seed_id": 9007199254740993},',
    '  "steps": [',
    '    {',
    '      "step_id": "s1",',
    '      "entry_path": "prompts/exact.prompt.md",',
    '      "operation": "echo",',
    '      "input": {"n": 9007199254740993},',
    '      "checks": [{"criterion_id": "AC1", "target": "result", "path": "/n", "op": "equals", "value": 9007199254740993}]',
    '    }',
    '  ]',
    '}',
  ].join('\n');

  const parsed = parseExactScenarioJson(v1Raw);
  assert.equal(isShortScenarioDoc(parsed), false);
  const res = compileScenarioText(v1Raw, { path: 'tests/exact.json', storyPath: 'user_stories/exact.md' });
  assert.equal(res.refusal, null);
  assert.equal(res.changed, false);
  assert.equal(res.text, v1Raw);
  assert.equal(res.exactDoc.initial_world.seed_id, 9007199254740993n);
});

test('Short scenario compiler auto-binds Story criteria, verifies optional labels, and tolerates curly-quote Story edits', () => {
  const shortDoc = {
    entry_path: 'prompts/todo.prompt.md',
    steps: [
      {
        id: 'done-4',
        op: 'main',
        input: { argv: ['done', '4'] },
        checks: {
          1: [['result', '/stdout', '=', 'Done #4: Call mom\n']],
          '2: Task #1 stays': [['world', '/kv/todos/0/done', '=', false]],
        },
      },
      {
        id: 'done-9',
        op: 'main',
        input: { argv: ['done', '9'] },
        checks: [
          ['3', 'result', '/stderr', '=', 'todo: no task #9\n'],
          ['AC3', 'calls', 'store.save', '=', 0],
        ],
      },
    ],
  };

  const compiled = compileScenario(shortDoc, {
    path: 'tests/finish-task.json',
    storyPath: 'user_stories/finish-task.md',
    storySource: SAMPLE_STORY,
  });
  assert.equal(compiled.refusal, null);
  assert.equal(compiled.changed, true);
  assert.equal(compiled.doc.schema_version, V1_SCENARIO_SCHEMA);
  assert.equal(compiled.doc.story_path, 'user_stories/finish-task.md');
  assert.deepEqual(compiled.doc.initial_world, {});
  assert.equal(compiled.doc.criteria.length, 3);
  assert.equal(compiled.doc.criteria[0].id, 'AC1');
  assert.equal(compiled.doc.steps[1].checks[1].path, '/resources/todo-store-save');

  // Harmless Story wording and curly-quote edit does not break Short JSON compilation.
  const curlyEditedStory = `# Finish a task

As a person who keeps Sam’s to-do list, I want to mark a task as done, so that I see what’s left.

## Acceptance criteria

1. \`todo done 4\` prints “Done #4: Call mom”, exits with code 0, and marks task #4 done.
2. Task #1 stays untouched (not done).
3. \`todo done 9\` writes “todo: no task #9” to stderr, exits 1, and saves nothing.
`;
  const afterEdit = compileScenario(shortDoc, {
    path: 'tests/finish-task.json',
    storyPath: 'user_stories/finish-task.md',
    storySource: curlyEditedStory,
  });
  assert.equal(afterEdit.refusal, null);
  assert.match(afterEdit.doc.criteria[0].text, /“Done #4: Call mom”/);

  // Contradicted criterion label fails loudly with story-criterion-mismatch.
  const mismatched = compileScenario(
    {
      entry_path: 'prompts/todo.prompt.md',
      steps: [
        {
          op: 'main',
          checks: { '2: prints no task #9': [['result', '/exit_code', '=', 1]] },
        },
      ],
    },
    { storyPath: 'user_stories/finish-task.md', storySource: SAMPLE_STORY },
  );
  assert.equal(mismatched.refusal?.code, 'story-criterion-mismatch');

  // Out-of-range criterion index fails loudly with unknown-criterion.
  const outOfRange = compileScenario(
    {
      entry_path: 'prompts/todo.prompt.md',
      steps: [
        {
          op: 'main',
          checks: { 9: [['result', '/exit_code', '=', 0]] },
        },
      ],
    },
    { storyPath: 'user_stories/finish-task.md', storySource: SAMPLE_STORY },
  );
  assert.equal(outOfRange.refusal?.code, 'unknown-criterion');
});

test('Short scenario compiler expands seeds, $use/$from/patch/set, $json BigInt strings, $step refs, HTML/error/calls tuples, and refuses cycles', () => {
  const rawShort = JSON.stringify({
    schema_version: SHORT_SCENARIO_SCHEMA,
    entry_path: 'prompts/snake.prompt.md',
    seeds: {
      base_state: {
        score: 0,
        paused: false,
        snake: [[5, 5], [5, 4], [5, 3]],
        food: [5, 6],
        drop_me: 'gone',
      },
      port_payload: {
        schema: 'v1',
        turn: 1,
        exact_token: '__BIGINT__',
      },
    },
    initial_world: {
      saved: { $use: 'base_state', patch: { drop_me: null, score: 2 }, set: { '/snake/0': [4, 5] } },
      external_ref: { $seed: 'contracts/shared-world.json' },
    },
    simulation: {
      'telemetry.read': {
        result: {
          content: {
            $json: { $use: 'port_payload', patch: { turn: 2 } },
          },
        },
      },
    },
    steps: [
      {
        id: 'eat',
        op: 'step',
        from: 'base_state',
        patch: { drop_me: null },
        checks: {
          1: [
            ['result', '/score', '=', 1],
            ['result', '/score', '>=', 1],
            ['result', '/snake', 'len>=', 4],
            ['result', '/banner', 'contains_all', ['Score', '1']],
            ['calls', 'telemetry.read', '<=', 1],
            ['calls', 'board.rng.next', '=', 1],
            ['calls', 'internal:scorer', '=', 1],
          ],
        },
      },
      {
        id: 'next-tick',
        op: 'step',
        input: {
          state: { $step: 'eat#/next_state' },
          full_prev: { $step: 'eat' },
        },
        checks: {
          1: [
            ['html_exists', 'div#board'],
            ['html_text', 'span.score', '=', '1'],
            ['html_attr', 'button[data-action=pause]', 'aria-pressed', '=', 'false'],
            ['html', 'button', 'labels_include', ['Start', 'Pause', 'Restart']],
          ],
        },
      },
      {
        id: 'bad-move',
        op: 'step',
        from: 'eat',
        patch: { dir: 'invalid' },
        error: 'bad-direction',
        checks: {
          1: [['error', '=', 'bad-direction']],
        },
      },
    ],
  }).replace('"__BIGINT__"', '9007199254740993');

  const res = compileScenarioText(rawShort, {
    path: 'tests/snake.json',
    storyPath: 'user_stories/snake.md',
    storySource: '# Snake\n\nAs a player, I want to play Snake, so that I score points.\n\n## Acceptance criteria\n\n1. Snake eats food, renders controls, and rejects bad directions.\n',
  });
  assert.equal(res.refusal, null);
  assert.equal(res.changed, true);

  const doc = res.exactDoc;
  assert.equal(doc.schema_version, V1_SCENARIO_SCHEMA);
  assert.equal(Object.hasOwn(doc, 'seeds'), false);
  assert.equal(Object.hasOwn(doc, 'entry_path'), false);
  assert.equal(Object.hasOwn(doc.initial_world.saved, 'drop_me'), false);
  assert.equal(doc.initial_world.saved.score, 2);
  assert.deepEqual(doc.initial_world.saved.snake[0], [4, 5]);
  // External file $seed not in doc.seeds must pass through untouched for contract-refs expansion!
  assert.deepEqual(doc.initial_world.external_ref, { $seed: 'contracts/shared-world.json' });
  // $json stringifies nested macro with BigInt exact digits intact!
  assert.equal(
    doc.simulation['telemetry.read'].result.content,
    '{"schema":"v1","turn":2,"exact_token":9007199254740993}',
  );

  const [eat, nextTick, badMove] = doc.steps;
  assert.deepEqual(eat.checks[1], {
    criterion_id: 'AC1',
    target: 'result',
    path: '/score',
    op: 'at_least',
    value: 1,
    measure: 'value',
  });
  assert.deepEqual(eat.checks[2], {
    criterion_id: 'AC1',
    target: 'result',
    path: '/snake',
    op: 'at_least',
    value: 4,
    measure: 'length',
  });
  assert.equal(eat.checks[3].op, 'contains');
  assert.equal(eat.checks[4].op, 'contains');
  assert.equal(eat.checks[5].path, '/resources/snake-telemetry-read');
  assert.equal(eat.checks[6].path, '/resources/board-rng-next');
  assert.equal(eat.checks[7].path, '/internal/scorer');

  assert.deepEqual(nextTick.input.state, { $step_result: { step_id: 'eat', path: '/next_state' } });
  assert.deepEqual(nextTick.input.full_prev, { $step_result: { step_id: 'eat', path: '' } });
  assert.equal(nextTick.checks[0].html.kind, 'element');
  assert.deepEqual(nextTick.checks[0].html.selector, { tag: 'div', attributes: { id: 'board' } });
  assert.deepEqual(nextTick.checks[2].html, {
    selector: { tag: 'button', attributes: { 'data-action': 'pause' } },
    kind: 'attribute',
    attribute: 'aria-pressed',
  });
  // labels_include expands into 1 exact html element exists check + 3 contains checks on /html
  assert.equal(nextTick.checks.length, 3 + 4);
  assert.equal(nextTick.checks[3].op, 'exists');
  assert.equal(nextTick.checks[4].value, 'Start');
  assert.equal(nextTick.checks[6].value, 'Restart');

  assert.equal(badMove.expected_error, 'bad-direction');
  assert.equal(badMove.input.dir, 'invalid');
  assert.deepEqual(badMove.checks, [
    { criterion_id: 'AC1', target: 'error', path: '/code', op: 'equals', value: 'bad-direction' },
  ]);

  // Seed cycle detection
  const cyclic = compileScenario({
    entry_path: 'prompts/snake.prompt.md',
    seeds: {
      a: { $use: 'b' },
      b: { $use: 'a' },
    },
    steps: [{ op: 'step', from: 'a', checks: { 1: [['result', '/ok', '=', true]] } }],
  });
  assert.equal(cyclic.refusal?.code, 'seed-cycle');

  // Unknown operator detection
  const badOp = compileScenario({
    entry_path: 'prompts/snake.prompt.md',
    steps: [{ op: 'step', checks: { 1: [['result', '/ok', 'approx_equals', true]] } }],
  });
  assert.equal(badOp.refusal?.code, 'invalid-check');
});

test('End-to-end seam integration: Short JSON works across findTests, preflight, captureSource (clean git dirty_files), lint --local, lint --emit-v1, check + saved.results, and test --target code', async t => {
  const setup = harbor(t, repo => {
    rmSync(join(repo, 'tests/unknown-item.json'));
    mkdirSync(join(repo, 'bin'), { recursive: true });
    writeFileSync(
      join(repo, 'bin/echo-cli.mjs'),
      '#!/usr/bin/env node\nprocess.stdout.write(`Order: ${process.argv.slice(2).join(" ")}\\n`);\n',
    );
    chmodSync(join(repo, 'bin/echo-cli.mjs'), 0o755);

    const inputSchema = {
      type: 'object',
      properties: { argv: { type: 'array', items: { type: 'string' } } },
      required: ['argv'],
      additionalProperties: false,
    };
    const resultSchema = {
      type: 'object',
      properties: {
        stdout: { type: 'string' },
        stderr: { type: 'string' },
        exit_code: { type: 'integer' },
      },
      required: ['stdout', 'stderr', 'exit_code'],
      additionalProperties: false,
    };
    const iface = {
      status: 'approved',
      prose_sha256: '',
      entries: [
        {
          operation: 'main',
          implementation: { kind: 'cli', command: 'node bin/echo-cli.mjs' },
          input_schema: inputSchema,
          result_schema: resultSchema,
          errors: [],
        },
      ],
      calls: [],
      resources: [],
      limits: { max_steps: 2, max_model_calls: 2 },
      conventions: [
        { path: '/entries/0/input_schema', convention: 'cli' },
        { path: '/entries/0/result_schema', convention: 'cli' },
      ],
    };
    const buildPrompt = () =>
      `# Order CLI\n\nPrint order arguments.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(iface)}\n\`\`\`\n</details>\n`;
    iface.prose_sha256 = seam.proseSha256(buildPrompt());
    writeFileSync(join(repo, PLACE), buildPrompt());
    writeFileSync(
      join(repo, 'user_stories/place-order.md'),
      '# Place order\n\nAs a café customer, I want to place an order from the CLI, so that I see my order line.\n\n## Acceptance criteria\n\n1. Passing `latte` prints `Order: latte` and exits 0.\n2. Passing `espresso` prints `Order: espresso` and exits 0.\n',
    );
    // Author tests/place-order.json in Short JSON (omitted schema_version, story_path, criteria, initial_world)
    writeFileSync(
      join(repo, 'tests/place-order.json'),
      JSON.stringify(
        {
          entry_path: PLACE,
          seeds: { base_cmd: { argv: ['latte'] } },
          steps: [
            {
              id: 'order-latte',
              op: 'main',
              from: 'base_cmd',
              checks: {
                1: [
                  ['result', '/stdout', '=', 'Order: latte\n'],
                  ['result', '/exit_code', '=', 0],
                ],
              },
            },
            {
              id: 'order-espresso',
              op: 'main',
              from: 'base_cmd',
              patch: { argv: ['espresso'] },
              checks: {
                2: [
                  ['result', '/stdout', '=', 'Order: espresso\n'],
                  ['result', '/exit_code', '=', 0],
                ],
              },
            },
          ],
        },
        null,
        2,
      ) + '\n',
    );
  });

  // 1. findTests + preflight
  const found = seam.findTests({ root: setup.repo });
  assert.equal(found.tests.length, 1);
  assert.equal(found.tests[0].error, undefined);
  assert.equal(found.tests[0].doc.schema_version, V1_SCENARIO_SCHEMA);
  assert.equal(found.tests[0].doc.criteria.length, 2);
  const pf = seam.preflight({ root: setup.repo, found, selected: found.tests });
  assert.deepEqual(pf.rows[0].refusals, []);
  assert.deepEqual(pf.rows[0].not_checked ?? [], []);

  // 2. captureSource uploads compiled v1 JSON while keeping committed Short JSON clean (source_dirty === false)
  const emptySnap = seam.captureSource(setup.repo, { tests: [] });
  assert.equal(emptySnap.files.some(f => f.path === 'tests/place-order.json'), false, 'tests: [] must not include Short JSON files');

  const snap = seam.captureSource(setup.repo, { tests: ['tests/place-order.json'] });
  assert.equal(snap.source_dirty, false, `committed Short JSON must not appear dirty: ${JSON.stringify(snap.dirty_files)}`);
  assert.deepEqual(snap.dirty_files, []);
  const uploadedEntry = snap.sources.find(f => f.path === 'tests/place-order.json');
  assert.ok(uploadedEntry, 'tests/place-order.json must be present in uploaded sources');
  const uploadedScenario = JSON.parse(uploadedEntry.bytes.toString('utf8'));
  assert.equal(uploadedScenario.schema_version, V1_SCENARIO_SCHEMA);
  assert.equal(uploadedScenario.steps[1].input.argv[0], 'espresso');

  // 3. pdd lint --emit-v1 (single Story & --json)
  const emitOut = sink();
  const emitErr = sink();
  const emitCode = await runPdd(['lint', '--emit-v1', 'place-order'], {
    cwd: setup.repo,
    stdout: emitOut,
    stderr: emitErr,
    env: { HOME: setup.home, PDD_STATE_DIR: setup.state, PATH: process.env.PATH },
  });
  assert.equal(emitCode, 0, emitErr.text);
  const emittedDoc = JSON.parse(emitOut.text);
  assert.equal(emittedDoc.schema_version, V1_SCENARIO_SCHEMA);
  assert.equal(emittedDoc.criteria.length, 2);

  const emitJsonOut = sink();
  const emitJsonCode = await runPdd(['lint', '--emit-v1', '--json'], {
    cwd: setup.repo,
    stdout: emitJsonOut,
    stderr: sink(),
    env: { HOME: setup.home, PDD_STATE_DIR: setup.state, PATH: process.env.PATH },
  });
  assert.equal(emitJsonCode, 0);
  const emittedEnvelope = JSON.parse(emitJsonOut.text);
  assert.equal(emittedEnvelope.ok, true);
  assert.equal(emittedEnvelope.scenarios[0].changed, true);

  // 4. pdd lint --local passes with 0 Short JSON errors on valid file
  const localOut = sink();
  const localCode = await runPdd(['lint', '--local', '--json'], {
    cwd: setup.repo,
    stdout: localOut,
    stderr: sink(),
    env: { HOME: setup.home, PDD_STATE_DIR: setup.state, PATH: process.env.PATH },
  });
  assert.equal(localCode, 0);
  const localReport = JSON.parse(localOut.text);
  assert.equal(
    localReport.warnings.some(w => String(w).includes('tests/place-order.json')),
    false,
    `unexpected warning on valid Short JSON: ${JSON.stringify(localReport.warnings)}`,
  );

  // 5. seam.check against fakeRuntime + saved.results source_sha256 verification
  const passedTwoCriteriaChecks = [
    { criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', expected: 'Order: latte\n', actual: 'Order: latte\n', passed: true },
    { criterion_id: 'AC1', target: 'result', path: '/exit_code', op: 'equals', expected: 0, actual: 0, passed: true },
    { criterion_id: 'AC2', target: 'result', path: '/stdout', op: 'equals', expected: 'Order: espresso\n', actual: 'Order: espresso\n', passed: true },
    { criterion_id: 'AC2', target: 'result', path: '/exit_code', op: 'equals', expected: 0, actual: 0, passed: true },
  ];
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'GET') {
      return { status: 200, json: f.check(entry.url.split('/').at(-1), 'passed', passedTwoCriteriaChecks) };
    }
    return f.normal(entry);
  });
  const { ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  const checkCode = await seam.check({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, ports);
  assert.equal(checkCode, 0, ports.stderr.text);
  const savedEvidence = await seam.saved.results(
    { root: setup.repo },
    { env: { ...process.env, HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin } },
  );
  const savedStory = savedEvidence.stories.find(s => s.story === 'user_stories/place-order.md');
  assert.equal(savedStory?.pass, true);
  assert.equal(savedStory?.current, true);

  // 6. pdd test --target code (runCompiledTest) executes CLI implementation directly against Short JSON!
  const codeOut = sink();
  const codeErr = sink();
  const targetCodeExit = await runCompiledTest(
    { root: setup.repo, words: ['place-order'], json: true },
    { stdout: codeOut, stderr: codeErr },
  );
  assert.equal(targetCodeExit, 0, codeErr.text);
  const codeReport = JSON.parse(codeOut.text);
  assert.equal(codeReport.stories[0].status, 'passed');

  // 7. Broken Short JSON surfaces clearly in both pdd lint --emit-v1 (exit 4) and pdd lint --local warnings
  const savedGood = readFileSync(join(setup.repo, 'tests/place-order.json'), 'utf8');
  writeFileSync(
    join(setup.repo, 'tests/place-order.json'),
    JSON.stringify({
      entry_path: PLACE,
      steps: [{ op: 'main', checks: { 1: [['result', '/stdout', 'not_a_real_op', 'x']] } }],
    }) + '\n',
  );
  const badEmitErr = sink();
  const badEmitCode = await runPdd(['lint', '--emit-v1', 'place-order'], {
    cwd: setup.repo,
    stdout: sink(),
    stderr: badEmitErr,
    env: { HOME: setup.home, PDD_STATE_DIR: setup.state, PATH: process.env.PATH },
  });
  assert.equal(badEmitCode, 4);
  assert.match(badEmitErr.text, /Unknown check operator "not_a_real_op"/);

  const badLocalOut = sink();
  await runPdd(['lint', '--local', '--json'], {
    cwd: setup.repo,
    stdout: badLocalOut,
    stderr: sink(),
    env: { HOME: setup.home, PDD_STATE_DIR: setup.state, PATH: process.env.PATH },
  });
  assert.ok(
    JSON.parse(badLocalOut.text).warnings.some(w => String(w).includes('not_a_real_op')),
    'pdd lint --local must surface Short JSON syntax warnings offline',
  );
  writeFileSync(join(setup.repo, 'tests/place-order.json'), savedGood);
});

test('Short JSON auto-infers expected_error from error /code = checks and normalizes {code} error objects', () => {
  const shortDoc = {
    entry_path: 'prompts/task-manager.prompt.md',
    steps: [
      {
        id: 'blank-shorthand',
        op: 'add_task',
        input: { title: '' },
        checks: { 1: [['error', '=', 'blank-title'], ['calls', 'tasks.write_all', '=', 0]] },
      },
      {
        id: 'whitespace-explicit-path',
        op: 'add_task',
        input: { title: '   ' },
        checks: { 1: [['error', '/code', '=', 'blank-title']] },
      },
      {
        id: 'object-code-error',
        op: 'add_task',
        input: { title: '\t' },
        error: { code: 'blank-title' },
        checks: { 1: [['error', '=', 'blank-title']] },
      },
    ],
  };
  const { doc, changed, refusal } = compileScenario(shortDoc, {
    path: 'tests/task-manager.json',
    storyPath: 'user_stories/task-manager.md',
    storySource: '# Tasks\n\n## Acceptance criteria\n\n1. Blank titles fail with blank-title.\n',
  });
  assert.equal(refusal, null);
  assert.equal(changed, true);
  assert.equal(doc.steps[0].expected_error, 'blank-title');
  assert.equal(doc.steps[1].expected_error, 'blank-title');
  assert.equal(doc.steps[2].expected_error, 'blank-title');
});
