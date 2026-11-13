import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { outcomeFor } from '../src/runtime-outcome.mjs';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { PLACE, fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

// Replay the approved app-map-after-step-2569 Story vectors on outcomeFor and verify runTry/runCheck boundaries (RUNBOOK §17).
const scenario = JSON.parse(readFileSync(new URL('./runtime/app-map-after-step-2569.json', import.meta.url), 'utf8'));
const pointer = (value, path) => path === '' ? value : path.slice(1).split('/').reduce(
  (current, key) => current?.[key.replace(/~1/g, '/').replace(/~0/g, '~')], value);
const compare = {
  equals: (actual, value) => assert.deepEqual(actual, value),
  not_equals: (actual, value) => assert.notDeepEqual(actual, value),
  contains: (actual, value) => { assert.equal(typeof actual, 'string'); assert.ok(actual.includes(value), JSON.stringify(actual)); },
  not_contains: (actual, value) => { assert.equal(typeof actual, 'string'); assert.ok(!actual.includes(value), JSON.stringify(actual)); },
  count: (actual, value) => { assert.ok(Array.isArray(actual), JSON.stringify(actual)); assert.equal(actual.length, value); },
};

test('replay approved app-map-after-step-2569 Story vectors through outcomeFor', async t => {
  assert.ok(scenario.steps.length > 0);
  const seen = new Set();
  for (const step of scenario.steps) {
    await t.test(step.step_id, async st => {
      assert.equal(step.operation, 'outcomeFor', `Not replayed: unmapped operation ${step.operation}`);
      const { answer, ...options } = structuredClone(step.input);
      const result = outcomeFor(answer, options);
      for (const check of step.checks) {
        assert.equal(check.target, 'result', `Not replayed: unmapped target ${check.target}`);
        assert.ok(compare[check.op], `Not replayed: unmapped comparison ${check.op}`);
        seen.add(check.criterion_id);
        await st.test(`${check.criterion_id} ${check.path} ${check.op} ${JSON.stringify(check.value)}`,
          () => compare[check.op](pointer(result, check.path), check.value));
      }
    });
  }
  assert.deepEqual([...seen].sort(), scenario.criteria.map(criterion => criterion.id).sort());
});

test('outcomeFor scopes appMaps per row and holds unchecked or missing app-map verdicts at not_run', () => {
  const refusedStep = structuredClone(scenario.steps[0].input);
  // Empty appMaps means no app map applies to this row, even when result.app_maps has a refused map.
  const scopedOut = outcomeFor(refusedStep.answer, { ...refusedStep, appMaps: [] });
  assert.equal(scopedOut.state, 'passed');

  // Applicable app map marked not-checked holds the row at not_run (deadline / lint did not finish).
  const passingStep = structuredClone(scenario.steps[2].input);
  passingStep.answer.result.app_maps = [{ path: 'app-map.json', verdict: 'not-checked', problems: 0 }];
  const notChecked = outcomeFor(passingStep.answer, { ...passingStep, appMaps: ['app-map.json'] });
  assert.equal(notChecked.state, 'not_run');
  assert.equal(notChecked.code, 'deadline');
  assert.equal(notChecked.reason, 'lint did not finish');

  // Complete lint with no verdict entry (or conflicting entries) for an applicable app map holds at not_run (no-server-verdict).
  const missingEntry = structuredClone(scenario.steps[2].input);
  missingEntry.answer.result.app_maps = [];
  const noVerdict = outcomeFor(missingEntry.answer, { ...missingEntry, appMaps: ['app-map.json'] });
  assert.equal(noVerdict.state, 'not_run');
  assert.equal(noVerdict.code, 'no-server-verdict');
  assert.equal(noVerdict.reason, 'lint gave no verdict for this app map');

  const conflicting = structuredClone(scenario.steps[2].input);
  conflicting.answer.result.app_maps = [
    { path: 'app-map.json', verdict: 'passed', problems: 0 },
    { path: 'app-map.json', verdict: 'not-checked', problems: 0 },
  ];
  const conflictOutcome = outcomeFor(conflicting.answer, { ...conflicting, appMaps: ['app-map.json'] });
  assert.equal(conflictOutcome.state, 'not_run');

  // Refused app map without problem/refusal items synthesizes lint-refused naming the app-map path.
  const bareRefused = structuredClone(scenario.steps[2].input);
  bareRefused.answer.state = 'refused';
  bareRefused.answer.result.app_maps = [{ path: 'app-map.json', verdict: 'refused', problems: 1 }];
  const bareOutcome = outcomeFor(bareRefused.answer, { ...bareRefused, appMaps: ['app-map.json'] });
  assert.equal(bareOutcome.state, 'refused');
  assert.equal(bareOutcome.code, 'lint-refused');
  assert.equal(bareOutcome.field, 'app-map.json');
  assert.equal(bareOutcome.message, 'app-map.json was refused by complete lint.');

  // Hosted-shape receipt (problems: [invalid-after-step] + refusals: [lint-refused]) omits generic lint-refused from outcome.refusals.
  const hostedOutcome = outcomeFor(refusedStep.answer, refusedStep);
  assert.deepEqual(hostedOutcome.refusals.map(item => item.code), ['invalid-after-step']);
  assert.ok(!hostedOutcome.refusals.some(item => item.code === 'lint-refused'));

  // Paired-runtime receipt (problems: [invalid-after-step] + refusals: [invalid-after-step]) deduplicates identical records and preserves fix from a duplicate without mutating input.
  const pairedStep = structuredClone(scenario.steps[0].input);
  pairedStep.answer.result.problems[0].fix = null;
  pairedStep.answer.result.refusals = [{
    code: 'invalid-after-step',
    reason: 'An after step has the wrong fields.',
    fix: 'Use exactly handler, input and bind for each step.',
    file: 'app-map.json',
    at: 'handlers[0].after[0]',
    where: 'app-map.json, handlers[0].after[0]',
    path: 'app-map.json',
  }];
  const pairedOutcome = outcomeFor(pairedStep.answer, pairedStep);
  assert.equal(pairedStep.answer.result.problems[0].fix, null, 'must not mutate caller input');
  assert.equal(pairedOutcome.refusals.length, 1);
  assert.deepEqual(pairedOutcome.refusals.map(item => item.code), ['invalid-after-step']);
  assert.equal(pairedOutcome.fix, 'Use exactly handler, input and bind for each step.');
  assert.equal(pairedOutcome.refusals[0].fix, 'Use exactly handler, input and bind for each step.');
});

const APP_MAP = JSON.stringify({
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

function lintRefusingAppMap(base, { at = 'handlers[0].after[0]', where = 'app-map.json', code = 'invalid-after-step', reason = 'An after step has the wrong fields.', fix = 'Use exactly handler, input and bind for each step.', appMap = 'app-map.json', pairedRefusal = false } = {}) {
  base.state = 'refused';
  base.result.problems_complete = true;
  base.result.tests = base.result.report.lint.tests.map(({ path, verdict }) => ({ path, verdict }));
  base.result.app_maps = [{ path: appMap, verdict: 'refused', problems: 1 }];
  base.result.refusals = pairedRefusal
    ? [{
        code,
        reason,
        fix,
        file: appMap,
        at,
        ...(where !== undefined ? { where } : {}),
        engine_message: reason,
        path: appMap,
      }]
    : [{
        code: 'lint-refused',
        reason: 'The runtime refused this run (lint-refused).',
        fix: 'Run pdd lint to look for problems. If it stays, tell the PDD team and give them the report link.',
        file: appMap,
        at: null,
        where: appMap,
        engine_message: 'Lint refused this test or app map.',
        path: appMap,
      }];
  base.result.problems = [{
    code,
    severity: 'error',
    cause: 'test',
    file: appMap,
    at,
    pointer: null,
    reason,
    fix,
    source: 'engine',
    ...(where !== undefined ? { where } : {}),
    message: [reason, fix].filter(Boolean).join(' '),
  }];
  return base;
}

test('2569 regression: runTry stops before POST /v1/try on refused pre-Try app-map lint with exit 4 and nested handler guidance', async t => {
  for (const [label, opts, expectedLocation] of [
    ['hosted receipt with handler after location', { at: 'handlers[0].after[0]', where: 'app-map.json', pairedRefusal: false }, 'app-map.json handlers[0].after[0]'],
    ['paired-runtime receipt with matching problem and refusal', { at: 'handlers[0].after[0]', where: 'app-map.json, handlers[0].after[0]', pairedRefusal: true }, 'app-map.json, handlers[0].after[0]'],
    ['with null location', { at: null, where: 'app-map.json' }, 'app-map.json'],
    ['with omitted where and null location', { at: null, where: undefined }, 'app-map.json'],
  ]) {
    await t.test(label, async st => {
      const setup = harbor(st, repo => writeFileSync(join(repo, 'app-map.json'), `${APP_MAP}\n`));
      const fake = await fakeRuntime(st, (entry, f) => {
        if (entry.method === 'POST' && entry.command === 'lint') {
          return { status: 200, json: lintRefusingAppMap(f.lint(entry.request.requestId), opts) };
        }
        return { status: 500, json: { error: { code: 'unexpected-try-post', message: 'Should not reach /v1/try.' } } };
      });
      const { ports } = portsFor(
        { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state },
        { openUrl: async () => true },
      );
      const code = await runTry({ words: ['place-order'], options: { '--no-open': true }, cwd: setup.repo }, ports);
      assert.equal(code, 4, `${ports.stderr.text}\n${ports.stdout.text}`);
      assert.equal(fake.posts.filter(post => post.command === 'try').length, 0, 'must send zero /v1/try requests');
      assert.equal((ports.stdout.text.match(/invalid-after-step/g) ?? []).length, 1, ports.stdout.text);
      assert.doesNotMatch(ports.stdout.text, /lint-refused/);
      assert.deepEqual(ports.stdout.text.trimEnd().split('\n'), [
        `The Try could not start: the app map was refused (invalid-after-step: An after step has the wrong fields.; at ${expectedLocation}).`,
        'Use exactly handler, input and bind for each step. Write each after step as {"handler": {"prompt_path": "...", "operation": "..."}, "input": {...}, "bind": "/field"} (RUNBOOK §13). Then run pdd simulate place-order --new.',
      ]);
      assert.doesNotMatch(ports.stdout.text + ports.stderr.text, /Prompt tests|Runtime check|Story +Test|REFUSED|Cannot read properties of undefined/);
    });
  }

  await t.test('trySetupRefused deduplicates repeated refusal clauses and omits generic lint-refused wrapper on Try job refusal', async st => {
    const setup = harbor(st, repo => writeFileSync(join(repo, 'app-map.json'), `${APP_MAP}\n`));
    const fake = await fakeRuntime(st, (entry, f) => {
      if (entry.method === 'POST' && entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
      if (entry.method === 'POST' && entry.command === 'try') {
        const id = entry.request.requestId;
        const dup = {
          code: 'invalid-after-step',
          reason: 'An after step has the wrong fields.',
          fix: 'Use exactly handler, input and bind for each step.',
          file: 'app-map.json',
          at: 'handlers[0].after[0]',
          where: 'app-map.json, handlers[0].after[0]',
          path: 'app-map.json',
        };
        const wrapper = {
          code: 'lint-refused',
          reason: 'The runtime refused this run (lint-refused).',
          file: 'app-map.json',
          where: 'app-map.json',
          path: 'app-map.json',
        };
        return {
          status: 200,
          json: f.job(id, 'try', 'refused', {
            exitCode: 1,
            refusals: [dup, { ...dup }, wrapper],
            report: { verdict: 'refused', refusal: { code: 'invalid-after-step' } },
            session: { id, state: 'stopped' },
          }),
        };
      }
      return { status: 404, json: { error: { code: 'not-found' } } };
    });
    const { ports } = portsFor(
      { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state },
      { openUrl: async () => true },
    );
    const code = await runTry({ words: ['place-order'], options: { '--no-open': true }, cwd: setup.repo }, ports);
    assert.equal(code, 4, `${ports.stderr.text}\n${ports.stdout.text}`);
    assert.equal((ports.stdout.text.match(/invalid-after-step/g) ?? []).length, 1, ports.stdout.text);
    assert.doesNotMatch(ports.stdout.text, /lint-refused/);
    assert.deepEqual(ports.stdout.text.trimEnd().split('\n'), [
      'The Try could not start: the app map was refused (invalid-after-step: An after step has the wrong fields.; at app-map.json, handlers[0].after[0]).',
      'Use exactly handler, input and bind for each step. Write each after step as {"handler": {"prompt_path": "...", "operation": "..."}, "input": {...}, "bind": "/field"} (RUNBOOK §13). Then run pdd simulate place-order --new.',
    ]);
  });
});

test('2569 regression: runTry initializes warnings before lintDiagnostics runs on unrelated lint refusals and classifies broadened app-map codes', async t => {
  const setup = harbor(t, repo => writeFileSync(join(repo, 'app-map.json'), `${APP_MAP}\n`));
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'lint') {
      const base = f.lint(entry.request.requestId);
      base.state = 'refused';
      base.result.app_maps = [{ path: 'app-map.json', verdict: 'passed', problems: 0 }];
      base.result.refusals = [{ code: 'unrelated-input', file: 'tests/other.json', reason: 'An unselected test has invalid input.' }];
      return { status: 200, json: base };
    }
    if (entry.method === 'POST' && entry.command === 'try') return { status: 200, json: f.tryJob(entry.request.requestId) };
    if (entry.url.endsWith('/tests')) return { status: 404, json: { error: { code: 'not-found' } } };
    return { status: 200, json: f.tryJob(entry.url.split('/').at(-1)) };
  });
  const { ports } = portsFor(
    { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state },
    { openUrl: async () => true },
  );
  const code = await runTry({ words: ['place-order'], options: { '--no-open': true }, cwd: setup.repo }, ports);
  assert.equal(code, 0, ports.stderr.text);
  assert.match(ports.stderr.text, /Lint diagnostic: unrelated-input/);

  for (const refusalCode of ['after-input-invalid', 'invalid-clipboard-action', 'invalid-app-map-screen']) {
    const codeFake = await fakeRuntime(t, (entry, f) => {
      if (entry.method === 'POST' && entry.command === 'lint') {
        return { status: 200, json: lintRefusingAppMap(f.lint(entry.request.requestId), { code: refusalCode, reason: 'Bad map field.', fix: '' }) };
      }
      return { status: 500, json: {} };
    });
    const run = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: codeFake.origin, PDD_STATE_DIR: join(setup.state, refusalCode) }, { openUrl: async () => true });
    const exit = await runTry({ words: ['place-order'], options: { '--no-open': true }, cwd: setup.repo }, run.ports);
    assert.equal(exit, 4, run.ports.stderr.text);
    assert.equal(codeFake.posts.filter(post => post.command === 'try').length, 0);
    assert.match(run.ports.stdout.text, new RegExp(`the app map was refused \\(${refusalCode}: Bad map field\\.; at app-map\\.json handlers\\[0\\]\\.after\\[0\\]\\)`));
  }
});

test('2569 regression: runCheck --lint refuses scenarios declaring app_maps when the app map is refused while scenarios without app_maps pass', async t => {
  const setup = harbor(t, repo => {
    writeFileSync(join(repo, 'app-map.json'), `${APP_MAP}\n`);
    const file = join(repo, 'tests/place-order.json');
    const doc = JSON.parse(readFileSync(file, 'utf8'));
    doc.app_maps = ['app-map.json'];
    writeFileSync(file, `${JSON.stringify(doc, null, 2)}\n`);
  });
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'lint') {
      return { status: 200, json: lintRefusingAppMap(f.lint(entry.request.requestId)) };
    }
    return { status: 500, json: {} };
  });
  const env = { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state };

  const declaredPorts = portsFor(env);
  const declaredExit = await runCheck({ words: ['place-order'], options: { '--lint': true, '--json': true }, cwd: setup.repo }, declaredPorts.ports);
  assert.equal(declaredExit, 4, declaredPorts.ports.stderr.text);
  const declaredJson = JSON.parse(declaredPorts.ports.stdout.text);
  assert.equal(declaredJson.rows[0].state, 'refused');
  assert.equal(declaredJson.rows[0].reason.code, 'invalid-after-step');

  const checkPorts = portsFor(env);
  const checkExit = await runCheck({ words: ['place-order'], options: { '--json': true }, cwd: setup.repo }, checkPorts.ports);
  assert.equal(checkExit, 4, checkPorts.ports.stderr.text);
  assert.equal(fake.posts.filter(post => post.command === 'check').length, 0);

  // tests/unknown-item.json does not declare app_maps, so the refused app-map.json does not refuse it.
  const plainPorts = portsFor(env);
  const plainExit = await runCheck({ words: ['unknown-item'], options: { '--lint': true, '--json': true }, cwd: setup.repo }, plainPorts.ports);
  assert.equal(plainExit, 0, plainPorts.ports.stderr.text);
  const plainJson = JSON.parse(plainPorts.ports.stdout.text);
  assert.equal(plainJson.rows[0].state, 'passed');
});
