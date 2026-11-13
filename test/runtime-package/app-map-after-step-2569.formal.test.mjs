import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { Readable } from 'node:stream';
import { outcomeFor } from '../../src/runtime/runtime-outcome.mjs';
import { runTry, proseSha256 } from '../../src/runtime-seam.mjs';
import { PLACE, fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

// Bounded formal checks derived strictly from user_stories/app-map-after-step-2569.md ("## Rules to check").
const ENGINE_SHA = '088d558b937300e552386b0f81e0bd5e2ce782fb';
const TEST_PATH = 'tests/walk/spike-world.json';
const PROMPT_PATH = 'spike/machine_box.prompt.md';
const TEST_SHA = '1'.repeat(64);
const CLOSURE_SHA = '2'.repeat(64);
const PROMPT_SHA = '3'.repeat(64);
const APP_MAP_SHA = '4'.repeat(64);
const OTHER_MAP_SHA = '5'.repeat(64);

const SOURCE_FILES = [
  { path: 'app-map.json', sha256: APP_MAP_SHA },
  { path: 'other-map.json', sha256: OTHER_MAP_SHA },
  { path: PROMPT_PATH, sha256: PROMPT_SHA },
  { path: TEST_PATH, sha256: TEST_SHA },
];

function buildLintAnswer({ testVerdict, appMapVerdict, problemKind, genericRefusalWrapper }) {
  const problems = [];
  if (problemKind === 'specific-error-with-at' || problemKind === 'specific-error-null-at') {
    problems.push({
      code: 'invalid-after-step',
      severity: 'error',
      cause: 'test',
      file: 'app-map.json',
      at: problemKind === 'specific-error-with-at' ? 'handlers[0].after[0]' : null,
      pointer: null,
      reason: 'An after step has the wrong fields.',
      fix: 'Use exactly handler, input and bind for each step.',
      source: 'engine',
      where: 'app-map.json',
      message: 'An after step has the wrong fields. Use exactly handler, input and bind for each step.',
    });
  } else if (problemKind === 'warning-only') {
    problems.push({
      code: 'unused-state-field',
      severity: 'warning',
      cause: 'test',
      file: 'app-map.json',
      at: 'state_schema',
      pointer: null,
      reason: 'Unused state field.',
      fix: 'Remove unused field.',
      source: 'engine',
      where: 'app-map.json',
      message: 'Unused state field.',
    });
  }

  const refusals = genericRefusalWrapper
    ? [{
        code: 'lint-refused',
        reason: 'The runtime refused this run (lint-refused).',
        fix: 'Run pdd lint to look for problems. If it stays, tell the PDD team and give them the report link.',
        file: 'app-map.json',
        at: null,
        where: 'app-map.json',
        engine_message: 'Lint refused this test or app map.',
        path: 'app-map.json',
      }]
    : [];

  const hasRefusalSignal = testVerdict === 'refused'
    || appMapVerdict === 'refused'
    || problemKind === 'specific-error-with-at'
    || problemKind === 'specific-error-null-at'
    || genericRefusalWrapper;

  const result = {
    problems_complete: true,
    tests: [{ path: TEST_PATH, verdict: testVerdict }],
    refusals,
    problems,
    capabilities: [{
      path: TEST_PATH,
      report: {
        schema_version: 'prompt-runtime.program-capabilities.v1',
        capability_version: `program-capabilities.v1@${ENGINE_SHA}`,
        engine_build: ENGINE_SHA,
        source: {
          scenario_sha256: TEST_SHA,
          closure_sha256: CLOSURE_SHA,
          files: [
            { path: PROMPT_PATH, sha256: PROMPT_SHA },
            { path: TEST_PATH, sha256: TEST_SHA },
          ],
        },
        complete: true,
        verdict: 'supported',
        operations: [{
          selection: {
            step_id: 'send-ping',
            node_id: 'machine_box',
            prompt_path: PROMPT_PATH,
            operation: 'send',
          },
          feature: 'ordinary',
          binding_kind: 'none',
          resource_mode: 'simulated',
          evaluator_mode: 'model',
          execution_mode: 'ordinary',
          verdict: 'supported',
          reason_code: 'supported',
        }],
        edges: [],
        diagnostics: [],
        provider_calls: 0,
        resource_calls: 0,
      },
    }],
    report: {
      lint: { complete: true },
      program: {
        prompts: [{ path: PROMPT_PATH, admission_state: 'draft' }],
        refused_prompts: [],
      },
    },
  };

  if (appMapVerdict !== 'absent') {
    result.app_maps = [
      { path: 'app-map.json', verdict: appMapVerdict, problems: appMapVerdict === 'refused' ? 1 : 0 },
      { path: 'other-map.json', verdict: 'passed', problems: 0 },
    ];
  }

  return {
    command: 'lint',
    state: hasRefusalSignal ? 'refused' : 'passed',
    engine_sha: ENGINE_SHA,
    result,
  };
}

function storyOracleForOutcome({ appMapsParam, testVerdict, appMapVerdict, problemKind, genericRefusalWrapper }) {
  const appMapApplies = appMapsParam === undefined
    ? appMapVerdict !== 'absent'
    : appMapsParam.includes('app-map.json');
  const hasSpecificError = problemKind === 'specific-error-with-at' || problemKind === 'specific-error-null-at';
  const appMapRefused = appMapApplies && (appMapVerdict === 'refused' || hasSpecificError || genericRefusalWrapper);

  if (appMapRefused) {
    if (hasSpecificError) {
      return {
        state: 'refused',
        code: 'invalid-after-step',
        field: problemKind === 'specific-error-with-at' ? 'handlers[0].after[0]' : 'app-map.json',
        fix: 'Use exactly handler, input and bind for each step.',
      };
    }
    return {
      state: 'refused',
      code: 'lint-refused',
      field: 'app-map.json',
    };
  }

  if (testVerdict === 'refused') {
    return { state: 'refused' };
  }

  // testVerdict === 'passed' and no applicable app map was refused.
  if (appMapApplies && appMapVerdict === 'not-checked') {
    return { forbiddenState: 'passed', expectedState: 'not_run' };
  }
  if (appMapVerdict !== 'absent' && Array.isArray(appMapsParam) && appMapsParam.includes('unlisted-map.json')) {
    return { forbiddenState: 'passed', expectedState: 'not_run' };
  }

  return { state: 'passed' };
}

test('formal Rule 1 (bounded exhaustive, 320 combinations): outcomeFor enforces app_maps refusal precedence and never passes refused or unchecked applicable app maps', () => {
  const appMapsParams = [undefined, [], ['app-map.json'], ['other-map.json'], ['unlisted-map.json']];
  const testVerdicts = ['passed', 'refused'];
  const appMapVerdicts = ['absent', 'passed', 'refused', 'not-checked'];
  const problemKinds = ['none', 'specific-error-with-at', 'specific-error-null-at', 'warning-only'];
  const wrapperValues = [false, true];

  let checked = 0;
  for (const appMapsParam of appMapsParams) {
    for (const testVerdict of testVerdicts) {
      for (const appMapVerdict of appMapVerdicts) {
        for (const problemKind of problemKinds) {
          for (const genericRefusalWrapper of wrapperValues) {
            checked += 1;
            const label = JSON.stringify({ appMapsParam, testVerdict, appMapVerdict, problemKind, genericRefusalWrapper });
            const answer = buildLintAnswer({ testVerdict, appMapVerdict, problemKind, genericRefusalWrapper });
            const outcome = outcomeFor(answer, {
              test: TEST_PATH,
              steps: [{ entry_path: PROMPT_PATH }],
              ...(appMapsParam !== undefined ? { appMaps: appMapsParam } : {}),
              kind: 'lint',
              sourceFiles: SOURCE_FILES,
            });
            const expected = storyOracleForOutcome({ appMapsParam, testVerdict, appMapVerdict, problemKind, genericRefusalWrapper });

            if (expected.forbiddenState) {
              assert.notEqual(outcome.state, expected.forbiddenState, `Forbidden pass on ${label}: got ${JSON.stringify(outcome)}`);
              assert.equal(outcome.state, expected.expectedState, `Expected ${expected.expectedState} on ${label}: got ${JSON.stringify(outcome)}`);
              continue;
            }

            assert.equal(outcome.state, expected.state, `Wrong state on ${label}: got ${JSON.stringify(outcome)}`);
            if (expected.code !== undefined) {
              assert.equal(outcome.code, expected.code, `Wrong code on ${label}: got ${JSON.stringify(outcome)}`);
            }
            if (expected.field !== undefined) {
              assert.equal(outcome.field, expected.field, `Wrong field on ${label}: got ${JSON.stringify(outcome)}`);
            }
            if (expected.fix !== undefined) {
              assert.equal(outcome.fix, expected.fix, `Wrong fix on ${label}: got ${JSON.stringify(outcome)}`);
            }
          }
        }
      }
    }
  }
  assert.equal(checked, 320);
});

const APP_MAP_DOC = JSON.stringify({
  schema_version: 'prompt-runtime.app-map.v1',
  name: 'Harbor',
  initial_screen: 'menu',
  screens: [{
    id: 'menu',
    source: 'operation',
    prompt_path: PLACE,
    operation: 'place_order',
    input: { customerName: 'Sam', pickupAt: '08:30', items: [{ itemId: 'espresso', size: 'S', quantity: 1 }] },
    format: 'text',
    result_pointer: '/customerName',
  }],
});

function setupRepoForDoor(t, doorMode) {
  if (doorMode === 'screen') {
    return harbor(t, repo => {
      writeFileSync(join(repo, 'app-map.json'), `${APP_MAP_DOC}\n`);
    });
  }
  return harbor(t, repo => {
    rmSync(join(repo, 'tests/unknown-item.json'));
    const input = { type: 'object', properties: { argv: { type: 'array', items: { type: 'string' } }, stdin: { type: 'string' } }, required: ['argv'], additionalProperties: false };
    const result = { type: 'object', properties: { stdout: { type: 'string' }, stderr: { type: 'string' }, exit_code: { type: 'integer' } }, required: ['stdout', 'stderr', 'exit_code'], additionalProperties: false };
    const iface = {
      status: 'draft',
      prose_sha256: '',
      entries: [{ operation: 'main', input_schema: input, result_schema: result, errors: [] }],
      calls: [],
      resources: [],
      limits: { max_steps: 1, max_model_calls: 1 },
      conventions: ['input_schema', 'result_schema'].map(key => ({ path: `/entries/0/${key}`, convention: 'cli' })),
    };
    const content = () => `# paperclip\n\nPrint each argument on its own line.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\x60\x60\x60json\n${JSON.stringify(iface)}\n\x60\x60\x60\n</details>\n`;
    iface.prose_sha256 = proseSha256(content());
    writeFileSync(join(repo, PLACE), content());
    writeFileSync(join(repo, 'user_stories/place-order.md'), '# Arguments\n\nI can pass words.\n\n## Acceptance criteria\n\n1. Each argument prints on its own line.\n');
    const doc = {
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/place-order.md',
      criteria: [{ id: 'AC1', text: 'Each argument prints on its own line.' }],
      initial_world: {},
      simulation: {},
      context: [],
      steps: [{
        step_id: 'two-words',
        entry_path: PLACE,
        operation: 'main',
        input: { argv: ['say', 'two words'] },
        checks: [{ criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', value: 'say\ntwo words\n' }],
      }],
    };
    writeFileSync(join(repo, 'tests/place-order.json'), `${JSON.stringify(doc, null, 2)}\n`);
    const cliMap = JSON.parse(APP_MAP_DOC);
    cliMap.screens[0].operation = 'main';
    cliMap.screens[0].input = { argv: ['say'] };
    cliMap.screens[0].result_pointer = '/stdout';
    writeFileSync(join(repo, 'app-map.json'), `${JSON.stringify(cliMap)}\n`);
  });
}

test('formal Rule 2 (bounded exhaustive, 16 combinations): runTry pre-Try lint gate initializes warnings, never crashes with TypeError/exit 3, and stops refused app maps with exit 4 and zero /v1/try posts', async t => {
  const doorModes = ['screen', 'cli'];
  const appMapVerdicts = ['refused', 'passed'];
  const atPointers = ['handlers[0].after[0]', null];
  const extraWarnings = [false, true];

  let checked = 0;
  for (const doorMode of doorModes) {
    for (const appMapVerdict of appMapVerdicts) {
      for (const atPointer of atPointers) {
        for (const extraWarningOnTest of extraWarnings) {
          checked += 1;
          const label = `door=${doorMode}, appMap=${appMapVerdict}, at=${String(atPointer)}, extraWarning=${extraWarningOnTest}`;
          await t.test(label, async st => {
            const setup = setupRepoForDoor(st, doorMode);
            const fake = await fakeRuntime(st, (entry, f) => {
              if (entry.method === 'POST' && entry.command === 'lint') {
                const base = f.lint(entry.request.requestId);
                base.result.problems_complete = true;
                base.result.tests = base.result.report.lint.tests.map(({ path, verdict }) => ({ path, verdict }));
                base.result.app_maps = [{ path: 'app-map.json', verdict: appMapVerdict, problems: appMapVerdict === 'refused' ? 1 : 0 }];
                base.result.refusals = [];
                base.result.problems = [];

                if (appMapVerdict === 'refused') {
                  base.state = 'refused';
                  base.result.refusals.push({
                    code: 'lint-refused',
                    reason: 'The runtime refused this run (lint-refused).',
                    fix: 'Run pdd lint to look for problems. If it stays, tell the PDD team and give them the report link.',
                    file: 'app-map.json',
                    at: null,
                    where: 'app-map.json',
                    engine_message: 'Lint refused this test or app map.',
                    path: 'app-map.json',
                  });
                  base.result.problems.push({
                    code: 'invalid-after-step',
                    severity: 'error',
                    cause: 'test',
                    file: 'app-map.json',
                    at: atPointer,
                    pointer: null,
                    reason: 'An after step has the wrong fields.',
                    fix: 'Use exactly handler, input and bind for each step.',
                    source: 'engine',
                    where: 'app-map.json',
                    message: 'An after step has the wrong fields. Use exactly handler, input and bind for each step.',
                  });
                }

                if (extraWarningOnTest) {
                  base.state = 'refused';
                  base.result.refusals.push({
                    code: 'unrelated-input',
                    file: 'tests/other.json',
                    reason: 'An unselected test has invalid input.',
                  });
                  base.result.problems.push({
                    code: 'unused-field',
                    severity: 'warning',
                    file: 'tests/place-order.json',
                    at: atPointer,
                    reason: 'Advisory warning on test.',
                    message: 'Advisory warning on test.',
                  });
                }
                return { status: 200, json: base };
              }
              if (entry.url.endsWith('/model')) return { status: 200, json: { calls: { cap: 40, remaining: 40 } } };
              if (entry.method === 'POST' && entry.command === 'try') return { status: 200, json: f.tryJob(entry.request.requestId) };
              if (entry.url.endsWith('/tests')) return { status: 404, json: { error: { code: 'not-found' } } };
              return { status: 200, json: f.tryJob(entry.url.split('/').at(-1)) };
            });

            const env = { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state };
            const { ports } = portsFor(env, {
              stdin: Readable.from([]),
              openUrl: async () => true,
              shell: async () => 0,
            });
            const options = doorMode === 'cli'
              ? { '--cli': true, '--new': true }
              : { '--no-open': true, '--no-wait': true, '--new': true };

            let exitCode = null;
            let thrown = null;
            try {
              exitCode = await runTry({ words: ['place-order'], options, cwd: setup.repo }, ports);
            } catch (error) {
              thrown = error;
            }

            assert.equal(thrown, null, `Forbidden unhandled exception on ${label}: ${thrown?.stack ?? thrown}`);
            assert.notEqual(exitCode, 3, `Forbidden exit 3 on ${label}: stderr=${ports.stderr.text} stdout=${ports.stdout.text}`);
            assert.doesNotMatch(
              `${ports.stdout.text}\n${ports.stderr.text}`,
              /Cannot read properties of undefined/,
              `Forbidden TypeError text on ${label}`,
            );

            const tryPosts = fake.posts.filter(post => post.command === 'try').length;
            if (appMapVerdict === 'refused') {
              assert.equal(tryPosts, 0, `Forbidden POST /v1/try after refused app-map lint on ${label}`);
              if (doorMode === 'screen') {
                const expectedWhere = atPointer ? `app-map.json ${atPointer}` : 'app-map.json';
                assert.equal(exitCode, 4, `Expected exit 4 on ${label}: stderr=${ports.stderr.text} stdout=${ports.stdout.text}`);
                assert.doesNotMatch(ports.stdout.text, /Prompt tests|Runtime check|Story +Test|REFUSED/, `Forbidden Story check table on ${label}`);
                assert.deepEqual(ports.stdout.text.trimEnd().split('\n'), [
                  `The Try could not start: the app map was refused (invalid-after-step: An after step has the wrong fields.; at ${expectedWhere}).`,
                  'Use exactly handler, input and bind for each step. Write each after step as {"handler": {"prompt_path": "...", "operation": "..."}, "input": {...}, "bind": "/field"} (RUNBOOK §13). Then run pdd simulate place-order --new.',
                ]);
              } else {
                assert.equal(exitCode, 125, `Expected door refusal exit 125 on ${label}: stderr=${ports.stderr.text}`);
                assert.match(ports.stderr.text, /An after step has the wrong fields|invalid-after-step/);
              }
            } else {
              assert.equal(exitCode, 0, `Expected passing Try exit 0 on ${label}: stderr=${ports.stderr.text} stdout=${ports.stdout.text}`);
              assert.equal(tryPosts, 1, `Expected 1 POST /v1/try when app map passed on ${label}`);
              if (extraWarningOnTest) {
                assert.match(ports.stderr.text, /Lint diagnostic: unrelated-input/);
              }
            }
          });
        }
      }
    }
  }
  assert.equal(checked, 16);
});
