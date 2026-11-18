import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { chmodSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import {
  SHORT_SCENARIO_SCHEMA,
  V1_SCENARIO_SCHEMA,
  bindScenarioCriteriaText,
  compileScenario,
  compileScenarioText,
  criterionContentId,
  isShortScenarioDoc,
  needsScenarioCompile,
  parseExactScenarioJson,
} from '../src/scenario-compile.mjs';
import * as seam from '../src/runtime-seam.mjs';
import { lintSvgLayouts } from '../src/svg-layout.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { associateEvidenceWorkspace } from '../src/workflow-runner.mjs';
import { evidenceFixture } from './helpers/workspace-evidence-fixture.mjs';
import { PLACE, fakeRuntime, harbor, portsFor, sink } from './helpers/runtime-fake.mjs';

const SAMPLE_STORY = `# Finish a task

As a person who keeps a to-do list in the terminal, I want to mark a task as done, so that I see what is left.

## Acceptance criteria

1. \`todo done 4\` prints "Done #4: Call mom", exits with code 0 and saves task #4 as done.
2. Task #1 stays not done.
3. \`todo done 9\` prints "todo: no task #9" to stderr, exits with code 1 and saves nothing.
`;

const ECHO_STORY = `# Echo

As a caller, I want echo to return "hello", so that I see a greeting.

## Acceptance criteria

1. The echo returns "hello".
`;
const ECHO_HASH = 'ac-sha256-2300ea1200dead8c2a60353d2bdde6b58241a7a8f3492422';

function makeEchoPrompt() {
  const schema = {
    type: 'object',
    properties: { text: { type: 'string' } },
    required: ['text'],
    additionalProperties: false,
  };
  const iface = {
    status: 'approved',
    prose_sha256: '',
    entries: [
      {
        operation: 'echo',
        input_schema: { type: 'object', properties: {}, required: [], additionalProperties: false },
        result_schema: schema,
        errors: [],
      },
    ],
    calls: [],
    resources: [],
    limits: { max_steps: 2, max_model_calls: 2 },
  };
  const renderPrompt = () =>
    `# Echo\n\nReturn \`{"text": "hello"}\` from \`echo()\`.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(iface)}\n\`\`\`\n</details>\n`;
  iface.prose_sha256 = seam.proseSha256(renderPrompt());
  return renderPrompt();
}

test('Scenario compiler passes explicit program-scenario.v1 documents and BigInt integers through unchanged without silent rewrite', () => {
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
  assert.equal(needsScenarioCompile(parsed), false);
  const res = compileScenarioText(v1Raw, {
    path: 'tests/exact.json',
    storyPath: 'user_stories/exact.md',
    storySource: '## Acceptance criteria\n\n1. Keeps exact integer 9007199254740993.\n',
  });
  assert.equal(res.refusal, null);
  assert.equal(res.changed, false);
  assert.equal(res.text, v1Raw);
  assert.equal(res.exactDoc.initial_world.seed_id, 9007199254740993n);
  assert.equal(res.exactDoc.criteria[0].id, 'AC1');
});

test('Short scenario compiler auto-binds Story criteria to ac-sha256 content IDs, verifies optional labels, and tolerates curly-quote Story edits', () => {
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
  const expectedAc1 = criterionContentId(
    '`todo done 4` prints "Done #4: Call mom", exits with code 0 and saves task #4 as done.',
    'user_stories/finish-task.md',
  );
  assert.equal(compiled.doc.criteria[0].id, expectedAc1);
  assert.equal(compiled.doc.steps[0].checks[0].criterion_id, expectedAc1);
  assert.equal(compiled.doc.steps[1].checks[1].path, '/resources/todo-store-save');

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
  assert.match(afterEdit.doc.criteria[0].id, /^ac-sha256-/);

  const mismatched = compileScenario(
    {
      entry_path: 'prompts/todo.prompt.md',
      steps: [{ op: 'main', checks: { '2: prints no task #9': [['result', '/exit_code', '=', 1]] } }],
    },
    { storyPath: 'user_stories/finish-task.md', storySource: SAMPLE_STORY },
  );
  assert.equal(mismatched.refusal?.code, 'story-criterion-mismatch');

  const outOfRange = compileScenario(
    {
      entry_path: 'prompts/todo.prompt.md',
      steps: [{ op: 'main', checks: { 9: [['result', '/exit_code', '=', 0]] } }],
    },
    { storyPath: 'user_stories/finish-task.md', storySource: SAMPLE_STORY },
  );
  assert.equal(outOfRange.refusal?.code, 'unknown-criterion');
});

test('Short scenario compiler expands seeds, $use/$from/patch/set, $json BigInt strings, $step refs, HTML/error/calls tuples, auto expected_error, and refuses cycles', () => {
  const storyLine = 'Order flow scores items, renders checkout controls, and rejects bad coupons.';
  const expectedId = criterionContentId(storyLine, 'user_stories/checkout.md');
  const rawShort = JSON.stringify({
    schema_version: SHORT_SCENARIO_SCHEMA,
    entry_path: 'prompts/checkout.prompt.md',
    seeds: {
      base_state: {
        score: 0,
        paused: false,
        rows: [[5, 5], [5, 4], [5, 3]],
        drop_me: 'gone',
      },
      port_payload: {
        schema: 'v1',
        turn: 1,
        exact_token: '__BIGINT__',
      },
    },
    initial_world: {
      saved: { $use: 'base_state', patch: { drop_me: null, score: 2 }, set: { '/rows/0': [4, 5] } },
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
        id: 'price',
        op: 'step',
        from: 'base_state',
        patch: { drop_me: null },
        checks: {
          1: [
            ['result', '/score', '=', 1],
            ['result', '/score', '>=', 1],
            ['result', '/rows', 'len>=', 4],
            ['result', '/banner', 'contains_all', ['Total', '1']],
            ['calls', 'telemetry.read', '<=', 1],
            ['calls', 'ledger.rng.next', '=', 1],
            ['calls', 'internal:scorer', '=', 1],
          ],
        },
      },
      {
        id: 'render-ui',
        op: 'step',
        input: {
          state: { $step: 'price#/next_state' },
          full_prev: { $step: 'price' },
        },
        checks: {
          1: [
            ['html_exists', 'div#summary'],
            ['html_text', 'span.total', '=', '1'],
            ['html_attr', 'button[data-action=hold]', 'aria-pressed', '=', 'false'],
            ['html', 'button', 'labels_include', ['Pay', 'Hold', 'Cancel']],
          ],
        },
      },
      {
        id: 'bad-coupon',
        op: 'step',
        from: 'price',
        patch: { coupon: 'invalid' },
        checks: {
          1: [['error', '=', 'bad-coupon']],
        },
      },
    ],
  }).replace('"__BIGINT__"', '9007199254740993');

  const res = compileScenarioText(rawShort, {
    path: 'tests/checkout.json',
    storyPath: 'user_stories/checkout.md',
    storySource: `# Checkout\n\nAs a shopper, I want checkout totals.\n\n## Acceptance criteria\n\n1. ${storyLine}\n`,
  });
  assert.equal(res.refusal, null);
  assert.equal(res.changed, true);

  const doc = res.exactDoc;
  assert.equal(doc.schema_version, V1_SCENARIO_SCHEMA);
  assert.equal(Object.hasOwn(doc, 'seeds'), false);
  assert.equal(Object.hasOwn(doc, 'entry_path'), false);
  assert.equal(Object.hasOwn(doc.initial_world.saved, 'drop_me'), false);
  assert.equal(doc.initial_world.saved.score, 2);
  assert.deepEqual(doc.initial_world.saved.rows[0], [4, 5]);
  assert.deepEqual(doc.initial_world.external_ref, { $seed: 'contracts/shared-world.json' });
  assert.equal(
    doc.simulation['telemetry.read'].result.content,
    '{"schema":"v1","turn":2,"exact_token":9007199254740993}',
  );

  const [price, renderUi, badCoupon] = doc.steps;
  assert.deepEqual(price.checks[1], {
    criterion_id: expectedId,
    target: 'result',
    path: '/score',
    op: 'at_least',
    value: 1,
    measure: 'value',
  });
  assert.deepEqual(price.checks[2], {
    criterion_id: expectedId,
    target: 'result',
    path: '/rows',
    op: 'at_least',
    value: 4,
    measure: 'length',
  });
  assert.equal(price.checks[5].path, '/resources/checkout-telemetry-read');
  assert.equal(price.checks[6].path, '/resources/ledger-rng-next');
  assert.equal(price.checks[7].path, '/internal/scorer');

  assert.deepEqual(renderUi.input.state, { $step_result: { step_id: 'price', path: '/next_state' } });
  assert.deepEqual(renderUi.input.full_prev, { $step_result: { step_id: 'price', path: '' } });
  assert.equal(renderUi.checks.length, 3 + 4);
  assert.equal(badCoupon.expected_error, 'bad-coupon', 'expected_error must be auto-inferred from single error /code = check');
  assert.deepEqual(badCoupon.checks, [
    { criterion_id: expectedId, target: 'error', path: '/code', op: 'equals', value: 'bad-coupon' },
  ]);

  const cyclic = compileScenario({
    entry_path: 'prompts/checkout.prompt.md',
    seeds: { a: { $use: 'b' }, b: { $use: 'a' } },
    steps: [{ op: 'step', from: 'a', checks: { 1: [['result', '/ok', '=', true]] } }],
  });
  assert.equal(cyclic.refusal?.code, 'seed-cycle');

  const badOp = compileScenario({
    entry_path: 'prompts/checkout.prompt.md',
    steps: [{ op: 'step', checks: { 1: [['result', '/ok', 'approx_equals', true]] } }],
  });
  assert.equal(badOp.refusal?.code, 'invalid-check');
});

test('#3522 all 3 variants: omitted criteria compiles deterministically on pass 1 (exact echo hash, single pass, matching source_sha256), Variant 1 gives accurate --bind-criteria diagnostic, and stale ac-sha256 refuses', async t => {
  assert.equal(criterionContentId('The echo returns "hello".', 'user_stories/echo.md'), ECHO_HASH);

  const setup = harbor(t, repo => {
    rmSync(join(repo, 'tests/place-order.json'));
    rmSync(join(repo, 'tests/unknown-item.json'));
    rmSync(join(repo, 'user_stories/place-order.md'));
    rmSync(join(repo, 'user_stories/unknown-item.md'));
    writeFileSync(join(repo, 'prompts/echo.prompt.md'), makeEchoPrompt());
    writeFileSync(join(repo, 'user_stories/echo.md'), ECHO_STORY);
  });

  let lintPostCount = 0;
  let checkPostCount = 0;
  let lastUploadedScenario = null;
  const lintVerdictById = new Map();
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && (entry.command === 'lint' || entry.command === 'check')) {
      const extracted = spawnSync('tar', ['-xOf', '-', 'tests/echo.json'], { input: entry.tar, encoding: 'utf8' });
      assert.equal(extracted.status, 0, extracted.stderr);
      const uploaded = JSON.parse(extracted.stdout);
      lastUploadedScenario = uploaded;
      const crit = uploaded.criteria?.[0];
      const validBinding = crit?.id === ECHO_HASH && crit?.text === 'The echo returns "hello".';
      if (entry.command === 'lint') {
        lintPostCount += 1;
        if (!validBinding) {
          lintVerdictById.set(
            entry.request.requestId,
            f.job(
              entry.request.requestId,
              'lint',
              'refused',
              {
                exitCode: 4,
                refusals: [
                  {
                    code: 'story-criterion-mismatch',
                    section: 'criteria[0].id',
                    message: 'The Story criterion has no current content binding.',
                  },
                ],
              },
              0,
            ),
          );
        } else {
          lintVerdictById.set(
            entry.request.requestId,
            f.lint(entry.request.requestId, [
              { path: 'prompts/echo.prompt.md', state: 'approved', admission_state: 'approved', interface: { calls: [] } },
            ]),
          );
        }
        return { status: 202, json: f.job(entry.request.requestId, 'lint', 'queued', null, 0) };
      }
      checkPostCount += 1;
      if (!validBinding) {
        return {
          status: 200,
          json: f.check(entry.request.requestId, 'refused', [], [
            {
              code: 'story-criterion-mismatch',
              section: 'criteria[0].id',
              message: 'The Story criterion has no current content binding.',
            },
          ]),
        };
      }
      return { status: 202, json: f.check(entry.request.requestId, 'queued') };
    }
    const id = entry.url.split('/').at(-1);
    if (lintVerdictById.has(id)) return { status: 200, json: lintVerdictById.get(id) };
    return {
      status: 200,
      json: f.check(id, 'passed', [
        { criterion_id: ECHO_HASH, target: 'result', path: '/text', op: 'equals', expected: 'hello', actual: 'hello', passed: true },
      ]),
    };
  });

  // --- Variant 2A: program-scenario.v1 omitting top-level criteria (and omitting check.criterion_id on 1-criterion Story) ---
  const v1OmittedCriteria = {
    schema_version: V1_SCENARIO_SCHEMA,
    story_path: 'user_stories/echo.md',
    initial_world: {},
    steps: [
      {
        step_id: 'call-echo',
        entry_path: 'prompts/echo.prompt.md',
        operation: 'echo',
        input: {},
        checks: [{ target: 'result', path: '/text', op: 'equals', value: 'hello' }],
      },
    ],
  };
  writeFileSync(join(setup.repo, 'tests/echo.json'), JSON.stringify(v1OmittedCriteria, null, 2) + '\n');

  const filesOut = sink();
  assert.equal(
    await runPdd(['test', '--files', 'echo', '--json'], {
      cwd: setup.repo,
      stdout: filesOut,
      stderr: sink(),
      env: { HOME: setup.home, PDD_STATE_DIR: setup.state, PATH: process.env.PATH },
    }),
    0,
  );
  const filesSha = JSON.parse(filesOut.text).source_sha256;
  assert.equal(seam.captureSource(setup.repo, { tests: ['tests/echo.json'] }).sha256, filesSha);

  const { ports: v2LintPorts } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  assert.equal(await seam.lint({ cwd: setup.repo, words: ['echo'], options: { '--json': true } }, v2LintPorts), 0, v2LintPorts.stderr.text);
  assert.equal(lintPostCount, 1, 'Variant 2 must pass hosted lint in a single pass with zero retry');
  assert.equal(lastUploadedScenario?.criteria?.[0]?.id, ECHO_HASH);
  assert.equal(lastUploadedScenario?.steps?.[0]?.checks?.[0]?.criterion_id, ECHO_HASH);
  assert.equal(JSON.parse(v2LintPorts.stdout.text).exit_code, 0);

  const { ports: v2CheckPorts } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  assert.equal(await seam.check({ cwd: setup.repo, words: ['echo'], options: { '--json': true } }, v2CheckPorts), 0, v2CheckPorts.stderr.text);
  assert.equal(checkPostCount, 1, 'Variant 2 must pass hosted check in a single pass');
  assert.equal(JSON.parse(v2CheckPorts.stdout.text).source_sha256, filesSha);
  const savedAfterV2 = await seam.saved.results(
    { root: setup.repo },
    { env: { ...process.env, HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin } },
  );
  assert.equal(savedAfterV2.stories.find(s => s.story === 'user_stories/echo.md')?.current, true);
  assert.doesNotMatch(readFileSync(join(setup.repo, 'tests/echo.json'), 'utf8'), /ac-sha256-/);

  // --- Variant 2B: Short JSON omitting criteria ---
  writeFileSync(
    join(setup.repo, 'tests/echo.json'),
    JSON.stringify({
      entry_path: 'prompts/echo.prompt.md',
      steps: [{ id: 'call-echo', op: 'echo', checks: { 1: [['result', '/text', '=', 'hello']] } }],
    }, null, 2) + '\n',
  );
  const { ports: shortLintPorts } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  assert.equal(await seam.lint({ cwd: setup.repo, words: ['echo'], options: { '--json': true } }, shortLintPorts), 0, shortLintPorts.stderr.text);
  assert.equal(lastUploadedScenario?.criteria?.[0]?.id, ECHO_HASH);

  // --- Variant 1: Explicit legacy criterion ID ("AC1") with matching text -> NOT silently rewritten; accurate diagnostic ---
  const variant1Raw = [
    '{',
    '  "schema_version": "prompt-runtime.program-scenario.v1",',
    '  "story_path": "user_stories/echo.md",',
    '  "criteria": [{"id": "AC1", "text": "The echo returns \\"hello\\"."}],',
    '  "initial_world": {"exact_seed": 9007199254740993},',
    '  "steps": [',
    '    {',
    '      "step_id": "call-echo",',
    '      "entry_path": "prompts/echo.prompt.md",',
    '      "operation": "echo",',
    '      "input": {},',
    '      "checks": [{"criterion_id": "AC1", "target": "result", "path": "/text", "op": "equals", "value": "hello"}]',
    '    }',
    '  ]',
    '}',
    '',
  ].join('\n');
  writeFileSync(join(setup.repo, 'tests/echo.json'), variant1Raw);

  // Text-mode pdd lint diagnostic
  const { ports: v1TextPorts } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  const v1TextCode = await seam.lint({ cwd: setup.repo, words: ['echo'] }, v1TextPorts);
  assert.equal(v1TextCode, 4);
  assert.equal(lastUploadedScenario?.criteria?.[0]?.id, 'AC1', 'Explicit legacy AC1 must NOT be rewritten silently in memory');
  const combinedText = v1TextPorts.stdout.text + v1TextPorts.stderr.text;
  assert.doesNotMatch(combinedText, /are not the story's acceptance criteria, word for word/i);
  assert.match(combinedText, /already matches user_stories\/echo\.md's Acceptance criteria word for word/i);
  assert.match(combinedText, /AC1/);
  assert.match(combinedText, /pdd lint --bind-criteria echo/);

  // JSON-mode pdd test diagnostic
  const { ports: v1JsonPorts } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  const v1JsonCode = await seam.check({ cwd: setup.repo, words: ['echo'], cache: false, options: { '--json': true } }, v1JsonPorts);
  assert.equal(v1JsonCode, 4);
  const v1Json = JSON.parse(v1JsonPorts.stdout.text);
  const refusalMsg = JSON.stringify(v1Json.rows[0]);
  assert.doesNotMatch(refusalMsg, /are not the story's acceptance criteria, word for word/i);
  assert.match(refusalMsg, /pdd lint --bind-criteria echo/);

  // --- Reviewable pdd lint --bind-criteria binds AC1 -> ECHO_HASH on disk while preserving check expectations & BigInt ---
  const bindOut = sink();
  const bindErr = sink();
  const bindCode = await runPdd(['lint', '--bind-criteria', 'echo'], {
    cwd: setup.repo,
    stdout: bindOut,
    stderr: bindErr,
    env: { HOME: setup.home, PDD_STATE_DIR: setup.state, PATH: process.env.PATH },
  });
  assert.equal(bindCode, 0, bindErr.text);
  assert.match(bindOut.text, /Bound 1 criterion ID in tests\/echo\.json/);
  const boundDiskRaw = readFileSync(join(setup.repo, 'tests/echo.json'), 'utf8');
  assert.match(boundDiskRaw, /9007199254740993/, '--bind-criteria must preserve exact BigInt tokens on disk');
  const boundDiskDoc = JSON.parse(boundDiskRaw);
  assert.equal(boundDiskDoc.criteria[0].id, ECHO_HASH);
  assert.equal(boundDiskDoc.steps[0].checks[0].criterion_id, ECHO_HASH);
  assert.deepEqual(boundDiskDoc.steps[0].checks[0], {
    criterion_id: ECHO_HASH,
    target: 'result',
    path: '/text',
    op: 'equals',
    value: 'hello',
  });

  // Idempotent second --bind-criteria --json run
  const bindJsonOut = sink();
  assert.equal(
    await runPdd(['lint', '--bind-criteria', 'echo', '--json'], {
      cwd: setup.repo,
      stdout: bindJsonOut,
      stderr: sink(),
      env: { HOME: setup.home, PDD_STATE_DIR: setup.state, PATH: process.env.PATH },
    }),
    0,
  );
  assert.equal(JSON.parse(bindJsonOut.text).files[0].changed, false);

  // Variant 3 (bound ac-sha256-... on disk) now passes hosted lint cleanly!
  const { ports: v3Ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  assert.equal(await seam.lint({ cwd: setup.repo, words: ['echo'], options: { '--json': true } }, v3Ports), 0, v3Ports.stderr.text);

  // --- STRICT SAFETY PRESERVATION: Story wording changes -> stale ac-sha256-... refuses BOTH pdd lint AND pdd lint --bind-criteria! ---
  writeFileSync(
    join(setup.repo, 'user_stories/echo.md'),
    '# Echo\n\nAs a caller, I want echo to return "goodbye", so that I see a farewell.\n\n## Acceptance criteria\n\n1. The echo returns "goodbye".\n',
  );
  const diskBeforeRefusal = readFileSync(join(setup.repo, 'tests/echo.json'), 'utf8');
  const staleBindErr = sink();
  const staleBindCode = await runPdd(['lint', '--bind-criteria', 'echo'], {
    cwd: setup.repo,
    stdout: sink(),
    stderr: staleBindErr,
    env: { HOME: setup.home, PDD_STATE_DIR: setup.state, PATH: process.env.PATH },
  });
  assert.equal(staleBindCode, 4, '--bind-criteria must refuse stale content-bound criteria');
  assert.equal(readFileSync(join(setup.repo, 'tests/echo.json'), 'utf8'), diskBeforeRefusal, 'refused --bind-criteria must not touch disk file');

  // Even if test text is manually edited to "goodbye" while keeping old stale ECHO_HASH, --bind-criteria STILL refuses stale hash!
  const staleHashMatchedText = JSON.stringify({
    ...boundDiskDoc,
    criteria: [{ id: ECHO_HASH, text: 'The echo returns "goodbye".' }],
  }, null, 2) + '\n';
  const staleRes = bindScenarioCriteriaText(staleHashMatchedText, {
    path: 'tests/echo.json',
    storyPath: 'user_stories/echo.md',
    storySource: readFileSync(join(setup.repo, 'user_stories/echo.md'), 'utf8'),
  });
  assert.equal(staleRes.refusal?.code, 'story-criterion-mismatch');
  assert.match(staleRes.refusal?.message ?? '', /stale content-bound ID/);

  // Normal pdd lint ALSO refuses stale ac-sha256-... without rewriting its message to --bind-criteria!
  writeFileSync(join(setup.repo, 'tests/echo.json'), staleHashMatchedText);
  const { ports: staleLintPorts } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  assert.equal(await seam.lint({ cwd: setup.repo, words: ['echo'] }, staleLintPorts), 4);
  assert.doesNotMatch(staleLintPorts.stdout.text + staleLintPorts.stderr.text, /--bind-criteria/);
});

test('End-to-end seam integration: Short JSON works across findTests, preflight, captureSource (clean git dirty_files), lint --local, lint --emit-v1, retry, and test --target code', async t => {
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

  const ac1 = criterionContentId('Passing `latte` prints `Order: latte` and exits 0.', 'user_stories/place-order.md');
  const ac2 = criterionContentId('Passing `espresso` prints `Order: espresso` and exits 0.', 'user_stories/place-order.md');

  const found = seam.findTests({ root: setup.repo });
  assert.equal(found.tests.length, 1);
  assert.equal(found.tests[0].error, undefined);
  assert.equal(found.tests[0].doc.schema_version, V1_SCENARIO_SCHEMA);
  assert.deepEqual(found.tests[0].doc.criteria.map(c => c.id), [ac1, ac2]);
  const pf = seam.preflight({ root: setup.repo, found, selected: found.tests });
  assert.deepEqual(pf.rows[0].refusals, []);

  const emptySnap = seam.captureSource(setup.repo, { tests: [] });
  assert.equal(emptySnap.files.some(f => f.path === 'tests/place-order.json'), false);

  const snap = seam.captureSource(setup.repo, { tests: ['tests/place-order.json'] });
  assert.equal(snap.source_dirty, false, `committed Short JSON must not appear dirty: ${JSON.stringify(snap.dirty_files)}`);
  assert.deepEqual(snap.dirty_files, []);
  const uploadedScenario = JSON.parse(snap.sources.find(f => f.path === 'tests/place-order.json').bytes.toString('utf8'));
  assert.equal(uploadedScenario.schema_version, V1_SCENARIO_SCHEMA);
  assert.equal(uploadedScenario.criteria[0].id, ac1);

  const emitOut = sink();
  assert.equal(
    await runPdd(['lint', '--emit-v1', 'place-order'], {
      cwd: setup.repo,
      stdout: emitOut,
      stderr: sink(),
      env: { HOME: setup.home, PDD_STATE_DIR: setup.state, PATH: process.env.PATH },
    }),
    0,
  );
  assert.equal(JSON.parse(emitOut.text).criteria[0].id, ac1);

  const localOut = sink();
  assert.equal(
    await runPdd(['lint', '--local', '--json'], {
      cwd: setup.repo,
      stdout: localOut,
      stderr: sink(),
      env: { HOME: setup.home, PDD_STATE_DIR: setup.state, PATH: process.env.PATH },
    }),
    0,
  );
  assert.equal(JSON.parse(localOut.text).warnings.some(w => String(w).includes('tests/place-order.json')), false);

  // Queued timeout followed by --read and --retry succeeds with zero source mismatch!
  let holdQueued = true;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'check') {
      return { status: 202, json: f.check(entry.request.requestId, 'queued') };
    }
    if (entry.method === 'GET') {
      const id = entry.url.split('/').at(-1);
      if (holdQueued) {
        return { status: 200, json: f.check(id, 'queued') };
      }
      return {
        status: 200,
        json: f.check(id, 'passed', [
          { criterion_id: ac1, target: 'result', path: '/stdout', op: 'equals', expected: 'Order: latte\n', actual: 'Order: latte\n', passed: true },
          { criterion_id: ac1, target: 'result', path: '/exit_code', op: 'equals', expected: 0, actual: 0, passed: true },
          { criterion_id: ac2, target: 'result', path: '/stdout', op: 'equals', expected: 'Order: espresso\n', actual: 'Order: espresso\n', passed: true },
          { criterion_id: ac2, target: 'result', path: '/exit_code', op: 'equals', expected: 0, actual: 0, passed: true },
        ]),
      };
    }
    return f.normal(entry);
  });

  const { ports, clock } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  assert.equal(
    await seam.check({ cwd: setup.repo, words: ['place-order'], options: { '--timeout': '1', '--json': true } }, ports),
    3,
  );
  const firstBatch = JSON.parse(ports.stdout.text).batch;
  assert.ok(firstBatch);

  holdQueued = false;
  clock.now += 10000;
  const readPorts = { ...ports, stdout: sink(), stderr: sink() };
  assert.equal(
    await seam.check({ cwd: setup.repo, words: [firstBatch], options: { '--read': true, '--json': true } }, readPorts),
    0,
    readPorts.stderr.text,
  );
  assert.equal(JSON.parse(readPorts.stdout.text).source_sha256, snap.sha256);

  const retryPorts = { ...ports, stdout: sink(), stderr: sink() };
  assert.equal(
    await seam.check({ cwd: setup.repo, words: [], options: { '--retry': firstBatch, '--json': true } }, retryPorts),
    0,
    retryPorts.stderr.text,
  );
  assert.equal(JSON.parse(retryPorts.stdout.text).source_sha256, snap.sha256);

  // pdd test --target code
  const codeOut = sink();
  const codeErr = sink();
  assert.equal(await runPdd(['test', '--target', 'code', 'place-order', '--json'], { cwd: setup.repo, stdout: codeOut, stderr: codeErr }), 0, codeErr.text);
  assert.equal(JSON.parse(codeOut.text).stories[0].status, 'passed');
});

test('Audit fixes: workflow-runner before-the-fix association, composeProductTry (--product), and Simulator case import handle Short JSON omitting story_path', async t => {
  // 1. workflow-runner associateEvidenceWorkspace (--stage before) with Short JSON omitting story_path
  const f = await evidenceFixture(t);
  writeFileSync(
    join(f.root, 'tests/place-order.json'),
    JSON.stringify({
      entry_path: 'prompts/place_order.prompt.md',
      steps: [
        {
          id: 's1',
          op: 'place_order',
          input: { customerName: 'Sam', pickupAt: '08:30', items: [{ itemId: 'espresso', size: 'S', quantity: 2 }] },
          checks: { 1: [['result', '/totalCents', '=', 550]] },
        },
      ],
    }, null, 2) + '\n',
  );
  f.git(f.root, 'add', 'tests/place-order.json');
  f.git(f.root, 'commit', '-qm', 'Use Short JSON without story_path');
  const shortBeforeHead = f.git(f.root, 'rev-parse', 'HEAD').trim();
  const beforeSha = seam.captureSource(f.root, {
    tests: ['tests/place-order.json'],
    appMap: null,
    allowMissingInterfaces: true,
  }).sha256;

  // Edit prompt on HEAD so current != before
  writeFileSync(join(f.root, 'prompts/place_order.prompt.md'), readFileSync(join(f.root, 'prompts/place_order.prompt.md'), 'utf8') + '\nUpdated rule.\n');
  f.git(f.root, 'commit', '-qam', 'Fix prompt');

  const assoc = await associateEvidenceWorkspace(
    { ref: '17', cwd: f.root, workspace: f.root, stage: 'before', commit: shortBeforeHead, tests: ['tests/place-order.json'] },
    f.ports,
  );
  assert.equal(assoc.exitCode, 0, assoc.message);
  assert.equal(f.read().evidenceAssociations.at(-1).source_sha256, beforeSha);

  // 2. composeProductTry (pdd simulate --product --journey) compiles Short JSON journey omitting story_path & initial_world
  const memFiles = new Map();
  const put = (p, v) => memFiles.set(`/project/${p}`, typeof v === 'string' ? v : JSON.stringify(v));
  const emptySchema = { type: 'object', properties: {}, required: [], additionalProperties: false };
  put('product/map.md', '# Shop: map\nSize: small\n## Parts\n| Part | Folder | What it is |\n|---|---|---|\n| phone | prompts/phone | Ordering |\n## Stories\n| Id | Part | Story | Tag |\n|---|---|---|---|\n| P01 | phone | Order | CORE |\n');
  put('contracts/seed-world.json', { orders: [] });
  put('app/maps/phone.json', {
    schema_version: 'prompt-runtime.app-map.v1',
    name: 'phone',
    initial_screen: 'home',
    initial_route: null,
    initial_state: { tab: 'menu' },
    state_schema: { type: 'object', properties: { tab: { type: 'string' } }, required: ['tab'], additionalProperties: false },
    synthetic: false,
    screens: [{ id: 'home', prompt_path: 'prompts/phone/view.prompt.md', operation: 'render', source: 'operation', format: 'html', input: {}, result_pointer: '/html' }],
    router: null,
    routes: [],
    stylesheets: [],
    handlers: [{ screen: 'home', kind: 'click', match: {}, handler: { prompt_path: 'prompts/phone/view.prompt.md', operation: 'tap' }, input: {}, next: { kind: 'screen', screen: 'home', route_pointer: null }, state: { tab: 'menu' } }],
  });
  put('prompts/phone/view.prompt.md', '<details><summary>Runtime interface</summary>\n```json\n' + JSON.stringify({ entries: [{ operation: 'render', result_schema: emptySchema }, { operation: 'tap', result_schema: emptySchema }] }) + '\n```\n</details>');
  put('user_stories/journeys/J1-order.md', '# Journey 1\n\n## Acceptance criteria\n\n1. Order works.\n');
  // Short JSON journey omitting schema_version and story_path, using seeds + $seed!
  put('tests/J1-order.json', {
    entry_path: 'prompts/phone/view.prompt.md',
    initial_world: { $seed: 'contracts/seed-world.json', set: { '/orders': ['latte'] } },
    steps: [{ id: 's1', op: 'render', checks: { 1: [['html_exists', 'div#menu']] } }],
  });
  const composed = seam.composeProductTry(
    { root: '/project', journey: 'J1', testPath: 'tests/J1-order.json' },
    {
      statFile: p => ({ exists: memFiles.has(p), is_symlink: false }),
      readFile: p => memFiles.get(p),
    },
  );
  assert.deepEqual(JSON.parse(composed.files[1].content).orders, ['latte']);

  // 3. Simulator case import (saveDoorCaseResult + applyPendingCase) on Short JSON
  const storyLine = 'Placing an order records the order in world state.';
  const simSetup = harbor(t, repo => {
    rmSync(join(repo, 'tests/unknown-item.json'));
    writeFileSync(
      join(repo, 'user_stories/place-order.md'),
      `# Place order\n\nAs a customer, I want orders saved.\n\n## Acceptance criteria\n\n1. ${storyLine}\n`,
    );
    writeFileSync(
      join(repo, 'tests/place-order.json'),
      JSON.stringify({
        entry_path: PLACE,
        seeds: { sim: { 'clock.now': { returns: { iso: '2026-11-17T00:00:00Z' } } } },
        simulation: { $use: 'sim' },
        steps: [
          {
            id: 'first-order',
            op: 'place_order',
            input: { customerName: 'Sam', pickupAt: '08:30', items: [{ itemId: 'latte', size: 'M', quantity: 1 }] },
            checks: { 1: [['world', '', '=', { orders: ['ord-1'] }]] },
          },
        ],
      }, null, 2) + '\n',
    );
  });
  const env = { ...process.env, HOME: simSetup.home, PDD_STATE_DIR: simSetup.state };
  const serverContentId = criterionContentId(storyLine, 'user_stories/place-order.md');
  const retained = seam.saveDoorCaseResult(
    simSetup.repo,
    {
      id: '11111111-1111-4111-8111-111111111111',
      name: 'second-order',
      story_path: 'user_stories/place-order.md',
      original_path: 'tests/place-order.json',
      world_before: { orders: ['ord-1'] },
      test: {
        schema_version: V1_SCENARIO_SCHEMA,
        story_path: 'user_stories/place-order.md',
        criteria: [{ id: serverContentId, text: storyLine }],
        initial_world: { orders: ['ord-1'] },
        simulation: { 'clock.now': { returns: { iso: '2026-11-17T00:00:00Z' } } },
        steps: [
          {
            step_id: 'second-order',
            entry_path: PLACE,
            operation: 'place_order',
            input: { customerName: 'Alex', pickupAt: '09:00', items: [{ itemId: 'tea', size: 'S', quantity: 1 }] },
            checks: [{ criterion_id: serverContentId, target: 'world', path: '', op: 'equals', value: { orders: ['ord-1', 'ord-2'] } }],
          },
        ],
      },
    },
    { env },
  );
  assert.equal(retained.result.state, 'pending');
  const lease = await seam.acquireCaseWriteOwnership(
    { root: simSetup.repo, testPath: 'tests/place-order.json', handoff: { kind: 'closed-editor', testPath: 'tests/place-order.json' } },
    { env },
  );
  try {
    const applied = await seam.applyPendingCase(
      { root: simSetup.repo, pendingId: retained.result.pendingId, writeOwnership: lease },
      { env },
    );
    assert.equal(applied.state, 'committed', applied.reason);
  } finally {
    lease.release();
  }
  const updatedText = readFileSync(join(simSetup.repo, 'tests/place-order.json'), 'utf8');
  const updatedDoc = JSON.parse(updatedText);
  assert.equal(updatedDoc.criteria[0].id, serverContentId);
  assert.equal(updatedDoc.steps.length, 2);
});

test('Graph-aware default --max-calls, lintSvgLayouts app-map /state checks, and __proto__ safety', async t => {
  const orderInput = {
    customerName: 'Sam',
    pickupAt: '08:30',
    items: [{ itemId: 'espresso', size: 'S', quantity: 2 }],
  };
  const storyLine = 'Every order has a total of 550 cents.';
  const acId = criterionContentId(storyLine, 'user_stories/place-order.md');
  const setup = harbor(t, repo => {
    writeFileSync(
      join(repo, 'user_stories/place-order.md'),
      `# Place a coffee order\n\nAs a customer, I want 15 quick checks, so that all orders total 550.\n\n## Acceptance criteria\n\n1. ${storyLine}\n`,
    );
    const steps = Array.from({ length: 15 }, (_, idx) => ({
      id: `step-${idx + 1}`,
      op: 'place_order',
      input: orderInput,
      checks: { 1: [['result', '/totalCents', '=', 550]] },
    }));
    writeFileSync(join(repo, 'tests/place-order.json'), JSON.stringify({ entry_path: PLACE, steps }, null, 2) + '\n');
    writeFileSync(
      join(repo, 'app-map.json'),
      JSON.stringify({
        schema_version: 'prompt-runtime.app-map.v1',
        name: 'Board',
        initial_screen: 'board',
        initial_route: null,
        initial_state: { score: 0, shared: { id: 'abc' }, user: { name: 'Ada' }, tags: ['fast'], dynamic: { k: 1 } },
        state_schema: {
          type: 'object',
          properties: {
            score: { type: 'integer' },
            shared: { $contract: 'contracts/shared.schema.json' },
            user: {
              oneOf: [
                { type: 'object', properties: { name: { type: 'string' } }, required: ['name'] },
                { type: 'null' },
              ],
            },
            tags: { type: 'array', items: { type: 'string' } },
            dynamic: { type: 'object', additionalProperties: { type: 'integer' } },
          },
          required: ['score'],
          additionalProperties: false,
        },
        screens: [
          {
            id: 'board',
            prompt_path: PLACE,
            operation: 'place_order',
            source: 'operation',
            format: 'html',
            input: {
              board: { $ref: '/state/missing_board' },
              sharedId: { $ref: '/state/shared/id' },
              userName: { $ref: '/state/user/name' },
              firstTag: { $ref: '/state/tags/0' },
              dynVal: { $ref: '/state/dynamic/k' },
            },
            result_pointer: '/totalCents',
          },
        ],
        handlers: [
          {
            id: 'move',
            screen: 'board',
            kind: 'button',
            match: { id: 'up' },
            handler: { prompt_path: PLACE, operation: 'place_order' },
            input: {},
            state: { wrong_target: { $ref: '/result/totalCents' } },
            next: { kind: 'same', screen: null, route_pointer: null },
          },
        ],
      }, null, 2) + '\n',
    );
  });

  let requestedMaxCalls = null;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'check') {
      requestedMaxCalls = entry.request.max_calls;
      return { status: 202, json: f.check(entry.request.requestId, 'queued') };
    }
    if (entry.method === 'GET') {
      return {
        status: 200,
        json: f.check(entry.url.split('/').at(-1), 'passed', [
          { criterion_id: acId, target: 'result', path: '/totalCents', op: 'equals', expected: 550, actual: 550, passed: true },
        ]),
      };
    }
    return f.normal(entry);
  });
  const { ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  assert.equal(await seam.check({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, ports), 0, ports.stderr.text);
  assert.ok(requestedMaxCalls !== null && requestedMaxCalls <= 85, `expected graph-aware max_calls <= 85, got ${requestedMaxCalls}`);

  const warnings = lintSvgLayouts({ root: setup.repo, files: [...seam.gitFiles(setup.repo), 'app-map.json'] });
  assert.equal(warnings.some(w => w.includes('tests/place-order.json') && w.includes('schema_version')), false);
  assert.ok(warnings.some(w => w.includes('/state/missing_board')));
  assert.ok(warnings.some(w => w.includes('wrong_target')));
  for (const validPtr of ['/state/shared/id', '/state/user/name', '/state/tags/0', '/state/dynamic/k']) {
    assert.equal(warnings.some(w => w.includes(validPtr)), false);
  }

  // __proto__ safety + shorthand criterion IDs in criteria_scope / check_exemptions / simulation_overrides
  const protoRes = compileScenarioText(
    JSON.stringify({
      entry_path: 'prompts/app.prompt.md',
      seeds: { base: { ok: 1 } },
      criteria_scope: ['1', 2],
      check_exemptions: [{ criterion_id: '2: Second rule', reason: 'covered separately' }],
      steps: [
        {
          id: 's1',
          op: 'render',
          input: { $use: 'base', set: { '/__proto__/polluted': 'yes' }, patch: { __proto__: { extra: 'safe' } } },
          simulation_overrides: [{ operation: 'clock.now', criterion_id: '1', returns: { now: 1 } }],
          checks: { 1: [['html_text', 'div#msg', '=', 'Hi']] },
        },
      ],
    }),
    {
      path: 'tests/app.json',
      storyPath: 'user_stories/app.md',
      storySource: '## Acceptance criteria\n\n1. First rule.\n2. Second rule.\n',
    },
  );
  assert.equal(protoRes.refusal, null);
  assert.equal(({}).polluted, undefined);
  assert.equal(({}).extra, undefined);
  assert.equal(
    protoRes.doc.steps[0].simulation_overrides[0].criterion_id,
    criterionContentId('First rule.', 'user_stories/app.md'),
  );
});

test('Review hardening: Short JSON explicit AC1 + numeric check "1", repo-boundary story_path guard, strict/contracts Short JSON access, and sibling captureSource exclusion', async t => {
  // 1. Short JSON with explicit "AC1" + numeric check key "1" and tuple ["1", ...] through --bind-criteria and --emit-v1 / compileScenario
  const echoText = 'The echo returns "hello".';
  const echoId = criterionContentId(echoText, 'user_stories/echo.md');
  const bindSetup = harbor(t, repo => {
    rmSync(join(repo, 'tests/unknown-item.json'));
    rmSync(join(repo, 'tests/place-order.json'));
    rmSync(join(repo, 'user_stories/place-order.md'));
    writeFileSync(
      join(repo, 'user_stories/echo.md'),
      `# Echo\n\nAs a user, I want echo.\n\n## Acceptance criteria\n\n1. ${echoText}\n`,
    );
    writeFileSync(
      join(repo, 'tests/echo.json'),
      JSON.stringify({
        entry_path: PLACE,
        criteria: [{ id: 'AC1', text: echoText }],
        steps: [
          {
            id: 's1',
            op: 'place_order',
            input: { customerName: 'Sam', pickupAt: '08:30', items: [{ itemId: 'espresso', size: 'S', quantity: 2 }] },
            checks: { '1': ['result', '/totalCents', '=', 550] },
          },
          {
            id: 's2',
            op: 'place_order',
            input: { customerName: 'Sam', pickupAt: '08:30', items: [{ itemId: 'espresso', size: 'S', quantity: 2 }] },
            checks: [['1', 'result', '/totalCents', '=', 550]],
          },
        ],
      }, null, 2) + '\n',
    );
  });
  const { ports: bindPorts } = portsFor({ HOME: bindSetup.home, PDD_STATE_DIR: bindSetup.state });
  assert.equal(
    await seam.lint({ cwd: bindSetup.repo, words: ['echo'], options: { '--bind-criteria': true, '--json': true } }, bindPorts),
    0,
    bindPorts.stderr.text,
  );
  const boundDisk = JSON.parse(readFileSync(join(bindSetup.repo, 'tests/echo.json'), 'utf8'));
  assert.equal(boundDisk.criteria[0].id, echoId);
  assert.deepEqual(boundDisk.steps[0].checks, { '1': ['result', '/totalCents', '=', 550] });
  const compiledAfterBind = compileScenario(boundDisk, { path: 'tests/echo.json', storyPath: 'user_stories/echo.md' });
  assert.equal(compiledAfterBind.refusal, null);
  assert.equal(compiledAfterBind.doc.steps[0].checks[0].criterion_id, echoId);
  assert.equal(compiledAfterBind.doc.steps[1].checks[0].criterion_id, echoId);
  const { ports: emitPorts } = portsFor({ HOME: bindSetup.home, PDD_STATE_DIR: bindSetup.state });
  assert.equal(
    await seam.lint({ cwd: bindSetup.repo, words: ['echo'], options: { '--emit-v1': true } }, emitPorts),
    0,
    emitPorts.stderr.text,
  );
  const emitted = JSON.parse(emitPorts.stdout.text);
  assert.equal(emitted.steps[0].checks[0].criterion_id, echoId);
  assert.equal(emitted.steps[1].checks[0].criterion_id, echoId);

  // 2. Repo-boundary guard in wrapCaseFilesForShortJson: "../../outside.md" cannot read outside realRoot
  const outsideStoryText = 'Outside secret criterion that must never be read.';
  const outsidePath = join(bindSetup.sandbox, 'outside.md');
  writeFileSync(outsidePath, `# Outside\n\n## Acceptance criteria\n\n1. ${outsideStoryText}\n`);
  const traversalSetup = harbor(t, repo => {
    rmSync(join(repo, 'tests/unknown-item.json'));
    // Unmatched test basename ("orphan-short.json") with traversal story_path pointing to ../outside.md
    writeFileSync(
      join(repo, 'tests/orphan-short.json'),
      JSON.stringify({
        story_path: '../outside.md',
        entry_path: PLACE,
        steps: [
          {
            id: 's1',
            op: 'place_order',
            input: { customerName: 'Sam', pickupAt: '08:30', items: [{ itemId: 'espresso', size: 'S', quantity: 2 }] },
            checks: { '1': ['result', '/totalCents', '=', 550] },
          },
        ],
      }, null, 2) + '\n',
    );
  });
  const traversalSaved = seam.saveDoorCaseResult(
    traversalSetup.repo,
    {
      id: '22222222-2222-4222-8222-222222222222',
      name: 'try-traversal',
      story_path: '../outside.md',
      original_path: 'tests/orphan-short.json',
      world_before: {},
      test: {
        schema_version: V1_SCENARIO_SCHEMA,
        story_path: '../outside.md',
        criteria: [{ id: 'AC1', text: 'Safe text.' }],
        initial_world: {},
        steps: [
          {
            step_id: 'try-traversal',
            entry_path: PLACE,
            operation: 'place_order',
            input: { customerName: 'Sam', pickupAt: '08:30', items: [{ itemId: 'espresso', size: 'S', quantity: 2 }] },
            checks: [{ criterion_id: 'AC1', target: 'result', path: '/totalCents', op: 'equals', value: 550 }],
          },
        ],
      },
    },
    { env: { ...process.env, HOME: traversalSetup.home, PDD_STATE_DIR: traversalSetup.state } },
  );
  // Ensure outsideStoryText was never leaked into any pending case artifact or message
  assert.equal(JSON.stringify(traversalSaved).includes(outsideStoryText), false);

  // 3 & 4. createStrictSourceAccess + runContracts on Short JSON, AND captureSource sibling exclusion
  const storyLine = 'Placing two small espressos returns totalCents 550.';
  const expectedOrderId = criterionContentId(storyLine, 'user_stories/place-order.md');
  const strictSetup = harbor(t, repo => {
    rmSync(join(repo, 'tests/unknown-item.json'));
    mkdirSync(join(repo, 'contracts'), { recursive: true });
    writeFileSync(
      join(repo, 'contracts/money.schema.json'),
      JSON.stringify({ type: 'integer', minimum: 0 }, null, 2) + '\n',
    );
    const origPrompt = readFileSync(join(repo, PLACE), 'utf8');
    const withContract = origPrompt.replace(
      '"totalCents": { "type": "integer" }',
      '"totalCents": { "$contract": "contracts/money.schema.json" }',
    );
    const updatedProsePrompt = withContract.replace(
      /"prose_sha256":\s*"[0-9a-f]{64}"/,
      `"prose_sha256": "${seam.proseSha256(withContract)}"`,
    );
    writeFileSync(join(repo, PLACE), updatedProsePrompt);
    writeFileSync(
      join(repo, 'user_stories/place-order.md'),
      `# Place order\n\nAs a customer, I want totals.\n\n## Acceptance criteria\n\n1. ${storyLine}\n`,
    );
    writeFileSync(
      join(repo, 'tests/place-order.json'),
      JSON.stringify({
        entry_path: PLACE,
        steps: [
          {
            id: 'main-step',
            op: 'place_order',
            input: { customerName: 'Sam', pickupAt: '08:30', items: [{ itemId: 'espresso', size: 'S', quantity: 2 }] },
            checks: { '1': [['result', '/totalCents', '=', 550]] },
          },
        ],
      }, null, 2) + '\n',
    );
    writeFileSync(
      join(repo, 'tests/place-order.extra.json'),
      JSON.stringify({
        entry_path: PLACE,
        steps: [
          {
            id: 'extra-step',
            op: 'place_order',
            input: { customerName: 'Alex', pickupAt: '09:00', items: [{ itemId: 'espresso', size: 'S', quantity: 2 }] },
            checks: { '1': [['result', '/totalCents', '=', 550]] },
          },
        ],
      }, null, 2) + '\n',
    );
  });

  // 4. Verify captureSource({ tests: ['tests/place-order.json'] }) excludes unselected sibling tests/place-order.extra.json
  const singleCap = seam.captureSource(strictSetup.repo, { tests: ['tests/place-order.json'] });
  const uploadedPaths = singleCap.files.map(f => f.path);
  assert.ok(uploadedPaths.includes('tests/place-order.json'));
  assert.equal(
    uploadedPaths.includes('tests/place-order.extra.json'),
    false,
    `unselected sibling test must not enter captured.files, got ${JSON.stringify(uploadedPaths)}`,
  );
  assert.deepEqual(singleCap.dirty_files, []);
  assert.equal(singleCap.source_dirty, false);

  // 3a. Verify createStrictSourceAccess compiles Short JSON across sourceFilePort, findTests, and captureSource
  const strictAccess = seam.createStrictSourceAccess(strictSetup.repo);
  const strictVisible = new Set(seam.gitFiles(strictSetup.repo));
  const strictPort = strictAccess.sourceFilePort(strictVisible);
  const strictRead = JSON.parse(strictPort.read({ path: 'tests/place-order.json' }).content);
  assert.equal(strictRead.schema_version, V1_SCENARIO_SCHEMA);
  assert.equal(strictRead.story_path, 'user_stories/place-order.md');
  assert.equal(strictRead.criteria[0].id, expectedOrderId);
  assert.equal(strictRead.steps[0].entry_path, PLACE);
  assert.equal(strictPort.stat({ path: 'tests/place-order.json' }).size, Buffer.byteLength(strictPort.read({ path: 'tests/place-order.json' }).content, 'utf8'));

  const strictFound = strictAccess.findTests({ files: [...strictVisible] });
  const foundMain = strictFound.tests.find(x => x.path === 'tests/place-order.json');
  assert.ok(foundMain && !foundMain.error, foundMain?.error);
  assert.equal(foundMain.doc.story_path, 'user_stories/place-order.md');
  assert.equal(foundMain.doc.criteria[0].id, expectedOrderId);

  const strictCap = strictAccess.captureSource({ tests: ['tests/place-order.json'] });
  assert.equal(strictCap.files.some(f => f.path === 'tests/place-order.extra.json'), false);
  assert.equal(strictCap.sha256, singleCap.sha256);

  // 3b. Verify runContracts (pdd contracts) succeeds cleanly with Short JSON tests and zero footprint warnings
  const contractsOut = sink();
  const contractsErr = sink();
  assert.equal(
    seam.runContracts(
      { cwd: strictSetup.repo, words: [], options: {} },
      { env: { ...process.env, HOME: strictSetup.home, PDD_STATE_DIR: strictSetup.state }, stdout: contractsOut, stderr: contractsErr },
    ),
    0,
    contractsErr.text,
  );
  assert.equal(contractsErr.text.includes('footprint unavailable'), false, contractsErr.text);
  assert.match(contractsOut.text, /contracts\/money\.schema\.json/);
});
