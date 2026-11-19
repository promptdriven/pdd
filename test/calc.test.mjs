import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { evaluateCalcExpression, runCalc } from '../src/calc.mjs';
import { parseArgv, CommandInputError } from '../src/argument-parser.mjs';
import { PUBLIC_COMMAND_ROUTES, PUBLIC_HELP_TEXT } from '../src/command-catalog.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import {
  checkDerivation,
  evaluateDerivation,
  parseScenarioJson,
  runtimePreflightSlice,
  runtimeScenarioJsonSlice,
  scenarioDerivationRefusal,
} from '../src/runtime-seam.mjs';
import { bindScenarioCriteriaText, compileScenarioText } from '../src/scenario-compile.mjs';
import { BOUNDARY_CARD_MAX_LINES, buildHumanBoundaryCard, formatApproveBoundaryCard } from '../src/human-boundary-card.mjs';
import { readablePrTop } from '../src/workflow-pr-body.mjs';
import { storyCard, storyFingerprint } from '../src/workflow-story-card.mjs';

function makeStream() {
  let buf = '';
  return {
    write(chunk) { buf += String(chunk); return true; },
    get text() { return buf; },
  };
}

function withTempRepo(fn) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-calc-test-'));
  try {
    execFileSync('git', ['init', '-q'], { cwd: dir });
    execFileSync('git', ['config', 'user.email', 'test@example.com'], { cwd: dir });
    execFileSync('git', ['config', 'user.name', 'Test'], { cwd: dir });
    return fn(dir);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

test('evaluateCalcExpression and runCalc compute exact rational arithmetic', () => {
  assert.equal(evaluateCalcExpression('4000 - floor(4000 * 540 / 10000)'), '3784');
  assert.equal(evaluateCalcExpression('0.1 + 0.2'), '0.3');
  assert.equal(evaluateCalcExpression('1e-3 + 2.5E+2'), '250.001');
  assert.equal(evaluateCalcExpression('-7 div 2'), '-3');
  assert.equal(evaluateCalcExpression('7 div -2'), '-3');
  assert.equal(evaluateCalcExpression('-7 div -2'), '3');
  assert.equal(evaluateCalcExpression('-7 mod 2'), '-1');
  assert.equal(evaluateCalcExpression('7 mod -2'), '1');
  assert.equal(evaluateCalcExpression('-7 mod -2'), '-1');
  assert.equal(evaluateCalcExpression('1 / 3'), '1/3');
  assert.equal(evaluateCalcExpression('-4 / 6'), '-2/3');
  assert.equal(evaluateCalcExpression('4 / -6'), '-2/3');
  assert.equal(evaluateCalcExpression('0 / 7'), '0');
  assert.equal(evaluateCalcExpression('round_half_up(2.5)'), '3');
  assert.equal(evaluateCalcExpression('round_half_up(-2.5)'), '-3');
  assert.equal(evaluateCalcExpression('round_half_even(2.5)'), '2');
  assert.equal(evaluateCalcExpression('round_half_even(3.5)'), '4');
  assert.equal(evaluateCalcExpression('round_half_even(-2.5)'), '-2');
  assert.equal(evaluateCalcExpression('round_half_even(-3.5)'), '-4');
  assert.equal(evaluateCalcExpression('max(ceil(1.2), trunc(-2.9), min(10, 5))'), '5');
  assert.equal(evaluateCalcExpression('floor(-1.2)'), '-2');

  const ok = runCalc({ expression: '4000 - floor(4000 * 540 / 10000)' });
  assert.deepEqual(ok, { exit_code: 0, stdout: '3784\n', stderr: '' });
});

test('evaluateCalcExpression and runCalc reject invalid, blank, divide-by-zero, and over-budget inputs', () => {
  for (const bad of ['', '   ', '1 / 0', '1 div 0', '1 mod 0', 'foo(1)', 'Floor(1)', '7 DIV 2', 'min()', 'floor(1, 2)', '(1 + 2', '1 +', '1 2', '1e10001', '('.repeat(129) + '1' + ')'.repeat(129), '1' + ' + 1'.repeat(3500)]) {
    assert.throws(
      () => evaluateCalcExpression(bad),
      err => err instanceof SyntaxError && err.code === 'scenario-derivation-invalid',
      `expected SyntaxError(scenario-derivation-invalid) for ${JSON.stringify(bad.slice(0, 40))}`,
    );
  }

  assert.deepEqual(runCalc({ expression: '   ' }), {
    exit_code: 2,
    stdout: '',
    stderr: 'pdd calc: missing expression\n',
  });
  const divZero = runCalc({ expression: '1 / 0' });
  assert.equal(divZero.exit_code, 2);
  assert.equal(divZero.stdout, '');
  assert.match(divZero.stderr, /^pdd calc: .+\n$/);
  assert.equal(divZero.stderr.trim().includes('\n'), false);
});

test('parseArgv, command catalog, and runPdd wire pdd calc offline with leading-minus support', async () => {
  const calcRoute = PUBLIC_COMMAND_ROUTES.find(r => r.id === 'calc');
  assert.ok(calcRoute);
  assert.equal(calcRoute.local, 'calc');
  for (const group of PUBLIC_HELP_TEXT.groups) {
    for (const helpLine of group.lines) {
      assert.ok(helpLine.length <= 80, `root help line > 80 cols: ${helpLine}`);
    }
  }

  assert.deepEqual(parseArgv(['calc', '-7 div 2']), {
    commandId: 'calc',
    local: 'calc',
    operands: ['-7 div 2'],
    options: {},
  });
  assert.deepEqual(parseArgv(['calc', '--', '-7 mod 2']), {
    commandId: 'calc',
    local: 'calc',
    operands: ['-7 mod 2'],
    options: {},
  });
  assert.equal(parseArgv(['calc', '--help']).local, 'help');
  assert.equal(parseArgv(['calc', '-h']).local, 'help');
  assert.throws(() => parseArgv(['calc']), CommandInputError);
  assert.throws(() => parseArgv(['calc', '--bogus']), CommandInputError);
  assert.throws(() => parseArgv(['calc', '1', '2']), CommandInputError);

  let skillSynced = false;
  let releaseChecked = false;
  const stdout = makeStream();
  const stderr = makeStream();
  const code = await runPdd(['calc', '-7 div 2'], {
    stdout,
    stderr,
    syncOwnedUserSkills: () => { skillSynced = true; return { updated: [] }; },
    releaseNotice: async () => { releaseChecked = true; return 'upgrade!'; },
  });
  assert.equal(code, 0);
  assert.equal(stdout.text, '-3\n');
  assert.equal(stderr.text, '');
  assert.equal(skillSynced, false);
  assert.equal(releaseChecked, false);

  const errOut = makeStream();
  const errErr = makeStream();
  const errCode = await runPdd(['calc', '1 / 0'], { stdout: errOut, stderr: errErr });
  assert.equal(errCode, 2);
  assert.equal(errOut.text, '');
  assert.match(errErr.text, /^pdd calc: .+\n$/);
});

test('runtime-seam exposes evaluateDerivation, checkDerivation, and scenarioDerivationRefusal', () => {
  assert.equal(typeof runtimeScenarioJsonSlice().evaluateDerivation, 'function');
  assert.equal(typeof runtimeScenarioJsonSlice().checkDerivation, 'function');
  assert.equal(typeof runtimePreflightSlice().scenarioDerivationRefusal, 'function');
  assert.equal(evaluateDerivation('0.1 + 0.2'), '0.3');

  assert.equal(checkDerivation({ op: 'equals', value: 3784, derivation: '4000 - floor(4000 * 540 / 10000)' }), null);
  const bigDoc = parseScenarioJson('{"value": 9007199254740993}');
  assert.equal(checkDerivation({ op: 'equals', value: bigDoc.value, derivation: '9007199254740992 + 1' }), null);

  const mismatchCheck = { op: 'equals', value: 3785, derivation: '4000 - floor(4000 * 540 / 10000)' };
  const mismatch = checkDerivation(mismatchCheck);
  assert.equal(mismatch?.code, 'scenario-derivation-mismatch');
  assert.equal(mismatchCheck.value, 3785); // Never mutates expected value.

  assert.equal(checkDerivation({ op: 'contains', value: '3784', derivation: '3784' })?.code, 'scenario-derivation-invalid');
  assert.equal(checkDerivation({ op: 'equals', ref_target: 'input', ref_path: '/x', derivation: '1' })?.code, 'scenario-derivation-invalid');

  const doc = {
    steps: [
      { checks: [{ op: 'equals', value: 3, derivation: '1 + 2' }] },
      { checks: [{ op: 'equals', value: 10, derivation: '2 * 4' }] },
    ],
  };
  const refusal = scenarioDerivationRefusal(doc);
  assert.equal(refusal?.code, 'scenario-derivation-mismatch');
  assert.equal(refusal?.section, 'steps[1].checks[0].derivation');
  assert.equal(refusal?.step, 2);
});

test('scenario-compile preserves derivation on objects, Short JSON tuples, and --bind-criteria', () => {
  const story = '# Discount\n\nAs a shopper, I want discounts.\n\n## Acceptance criteria\n\n1. Discounted total is 3784.\n';
  const shortDoc = {
    schema_version: 'pdd.scenario.short.v1',
    story_path: 'user_stories/discount.md',
    entry_path: 'prompts/discount.prompt.md',
    steps: [
      {
        id: 'tuple-step',
        op: 'price',
        input: { amount: 4000 },
        checks: {
          1: [['result', '/total', '=', 3784, { derivation: '4000 - floor(4000 * 540 / 10000)' }]],
        },
      },
      {
        id: 'array-step',
        op: 'price',
        input: { amount: 4000 },
        checks: [
          [1, 'result', '/total', '=', 3784, { derivation: '4000 - 216' }],
          { criterion_id: 1, target: 'result', path: '/fee', op: 'equals', value: 216, derivation: 'floor(4000 * 540 / 10000)' },
        ],
      },
    ],
  };
  const compiled = compileScenarioText(JSON.stringify(shortDoc, null, 2), {
    path: 'test/runtime/discount.json',
    storyPath: 'user_stories/discount.md',
    storySource: story,
  });
  assert.equal(compiled.refusal, null);
  assert.equal(compiled.doc.steps[0].checks[0].derivation, '4000 - floor(4000 * 540 / 10000)');
  assert.equal(compiled.doc.steps[1].checks[0].derivation, '4000 - 216');
  assert.equal(compiled.doc.steps[1].checks[1].derivation, 'floor(4000 * 540 / 10000)');

  const badMeta = {
    ...shortDoc,
    steps: [{
      id: 'bad',
      op: 'price',
      input: {},
      checks: { 1: [['result', '/total', '=', 3784, { derivation: '3784', extra: true }]] },
    }],
  };
  const badCompiled = compileScenarioText(JSON.stringify(badMeta), {
    path: 'test/runtime/discount.json',
    storyPath: 'user_stories/discount.md',
    storySource: story,
  });
  assert.equal(badCompiled.refusal?.code, 'invalid-check');

  const v1Text = JSON.stringify({
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/discount.md',
    criteria: [{ id: 'AC1', text: 'Discounted total is 3784.' }],
    initial_world: {},
    simulation: {},
    context: [],
    steps: [{
      step_id: 's1',
      entry_path: 'prompts/discount.prompt.md',
      operation: 'price',
      input: {},
      checks: [{ criterion_id: 'AC1', target: 'result', path: '/total', op: 'equals', value: 3784, derivation: '4000 - floor(4000 * 540 / 10000)' }],
    }],
  }, null, 2);
  const bound = bindScenarioCriteriaText(v1Text, {
    path: 'test/runtime/discount.json',
    storyPath: 'user_stories/discount.md',
    storySource: story,
  });
  assert.equal(bound.refusal, null);
  assert.equal(bound.changed, true);
  assert.equal(JSON.parse(bound.text).steps[0].checks[0].derivation, '4000 - floor(4000 * 540 / 10000)');
});

test('human-boundary-card, PR boundary section, and workflow-story-card surface derivations and hash them', () => {
  withTempRepo(dir => {
    mkdirSync(join(dir, 'prompts'), { recursive: true });
    mkdirSync(join(dir, 'user_stories'), { recursive: true });
    mkdirSync(join(dir, 'tests'), { recursive: true });

    writeFileSync(join(dir, 'prompts/discount.prompt.md'), '# Discount\n\nOwn `src/discount.mjs`. Computes discounted total `4000 - floor(4000 * 540 / 10000)`.\n');
    writeFileSync(join(dir, 'user_stories/discount.md'), [
      '# Discount',
      '',
      'As a shopper, I want a 5.4% discount.',
      '',
      '## Acceptance criteria',
      '',
      '1. Discounted total for 4000 is 3784.',
      '',
      '```pdd-boundary',
      'prompts/discount.prompt.md',
      '```',
    ].join('\n'));
    const makeScenario = derivation => JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/discount.md',
      criteria: [{ id: 'AC1', text: 'Discounted total for 4000 is 3784.' }],
      initial_world: {},
      simulation: {},
      context: [],
      steps: [{
        step_id: 'discount-4000',
        entry_path: 'prompts/discount.prompt.md',
        operation: 'price',
        input: { amount: 4000 },
        checks: [{
          criterion_id: 'AC1',
          target: 'result',
          path: '/total',
          op: 'equals',
          value: 3784,
          ...(derivation !== undefined ? { derivation } : {}),
        }],
      }],
    }, null, 2);

    writeFileSync(join(dir, 'tests/discount.json'), makeScenario(undefined));
    execFileSync('git', ['add', '.'], { cwd: dir });
    execFileSync('git', ['commit', '-qm', 'init'], { cwd: dir });

    const fpWithout = storyFingerprint({ root: dir, changed: ['user_stories/discount.md', 'tests/discount.json'] });
    const cardWithout = buildHumanBoundaryCard({ root: dir, focusPrompt: 'prompts/discount.prompt.md' });
    assert.deepEqual(cardWithout.derivationRows, []);
    assert.equal(formatApproveBoundaryCard(cardWithout).some(l => l.includes('Derivations:')), false);

    writeFileSync(join(dir, 'tests/discount.json'), makeScenario('4000 - floor(4000 * 540 / 10000)'));
    const cardWith = buildHumanBoundaryCard({ root: dir, focusPrompt: 'prompts/discount.prompt.md' });
    assert.equal(cardWith.derivationRows.length, 1);
    assert.deepEqual(cardWith.derivationRows[0], {
      criterionLabel: 'AC1',
      path: '/total',
      value: '3784',
      derivation: '4000 - floor(4000 * 540 / 10000)',
    });

    const approveLines = formatApproveBoundaryCard(cardWith);
    assert.ok(approveLines.length <= BOUNDARY_CARD_MAX_LINES);
    assert.ok(approveLines.some(l => l.trim() === 'Derivations:'));
    assert.ok(approveLines.some(l => l.includes('AC1 /total: 3784 = 4000 - floor(4000 * 540 / 10000)')));

    const prBody = readablePrTop({
      layout: 'spec',
      title: 'Add discount',
      summary: 'Adds discount formula.',
      boundary: cardWith,
      issue: { number: 1, title: 'Discount' },
    });
    assert.match(prBody.text, /- \*\*Derivations:\*\*/);
    assert.match(prBody.text, /3784 = 4000 - floor\(4000 \* 540 \/ 10000\)/);

    const sCard = storyCard({
      root: dir,
      changed: ['user_stories/discount.md', 'tests/discount.json'],
      run: { repo: 'o/r', number: 1, issue: { title: 'Discount', url: 'https://github.com/o/r/issues/1' } },
    });
    assert.match(sCard, /3784 \(from 4000 - floor\(4000 \* 540 \/ 10000\)\)/);

    const fpWithA = storyFingerprint({ root: dir, changed: ['user_stories/discount.md', 'tests/discount.json'] });
    assert.notEqual(fpWithA.tests[0].sha256, fpWithout.tests[0].sha256);

    writeFileSync(join(dir, 'tests/discount.json'), makeScenario('4000 - 216'));
    const fpWithB = storyFingerprint({ root: dir, changed: ['user_stories/discount.md', 'tests/discount.json'] });
    assert.notEqual(fpWithB.tests[0].sha256, fpWithA.tests[0].sha256);
  });
});
