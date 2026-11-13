import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { outcomeFor } from '../src/runtime-outcome.mjs';
import { proseSha256 } from '../src/runtime-preflight.mjs';
import { PLACE, fakeRuntime, harbor, ordinaryCapabilities, portsFor, sha } from './runtime-fake.mjs';

const TEST_WITH_MAP = 'tests/place-order.json';
const TEST_PLAIN = 'tests/unknown-item.json';
const MAP_PATH = 'app/maps/b8.json';

const MAP_DOC = {
  schema_version: 'prompt-runtime.app-map.v1',
  name: 'B8 Replay Shell',
  initial_screen: 'replay',
  initial_route: null,
  initial_state: {},
  state_schema: { type: 'object', properties: {}, required: [], additionalProperties: false },
  screens: [{
    id: 'replay',
    prompt_path: PLACE,
    operation: 'place_order',
    source: 'operation',
    format: 'html',
    input: { customerName: 'Sam', pickupAt: '08:30', items: [{ itemId: 'espresso', size: 'S', quantity: 1 }] },
    result_pointer: '/customerName',
  }],
  router: null,
  routes: [],
  handlers: [],
  stylesheets: [],
};

const MAP_PROBLEM = {
  code: 'template-reference-unprovable',
  file: MAP_PATH,
  at: 'initial_world',
  reason: 'A screen field reads /state/attempt/match_code, which is absent from initial_world.',
  fix: 'Initialize /state/attempt/match_code in initial_world or change the screen $ref.',
  cause: 'prompt',
  severity: 'error',
};

const GENERIC_MAP_REFUSAL = {
  code: 'lint-refused',
  path: MAP_PATH,
  message: 'Lint refused this test or app map.',
};

function harborWithDeclaredMap(t, { declareOnPlaceOrder = true, doorMode = null } = {}) {
  return harbor(t, repo => {
    mkdirSync(join(repo, 'app/maps'), { recursive: true });
    writeFileSync(join(repo, MAP_PATH), `${JSON.stringify(MAP_DOC, null, 2)}\n`);
    if (doorMode) {
      const promptPath = join(repo, PLACE), source = readFileSync(promptPath, 'utf8');
      const block = source.match(/```json\s*([\s\S]*?)```/), iface = JSON.parse(block[1]);
      if (doorMode === '--cli') {
        iface.entries[0].input_schema.properties.argv = { type: 'array', items: { type: 'string' } };
        Object.assign(iface.entries[0].result_schema.properties, { stdout: { type: 'string' }, stderr: { type: 'string' }, exit_code: { type: 'integer' } });
        iface.conventions = ['input_schema', 'result_schema'].map(key => ({ path: `/entries/0/${key}`, convention: 'cli' }));
      } else iface.entries[0].input_schema.title = 'HTTP POST /orders';
      const content = () => source.replace(/^# .*/m, '# harbor-orders').replace(block[0], '```json\n' + JSON.stringify(iface) + '\n```');
      iface.prose_sha256 = proseSha256(content());
      writeFileSync(promptPath, content());
    }
    if (declareOnPlaceOrder) {
      const file = join(repo, TEST_WITH_MAP);
      const doc = JSON.parse(readFileSync(file, 'utf8'));
      doc.app_maps = [MAP_PATH];
      writeFileSync(file, `${JSON.stringify(doc, null, 2)}\n`);
    }
  });
}

function applyMapLintShape(answer, shape) {
  const publicTests = answer.result.report.lint.tests.map(({ path, verdict }) => ({ path, verdict, problems: 0 }));
  switch (shape) {
    case 'map-refused':
      answer.state = 'refused';
      answer.result.exitCode = 4;
      answer.result.tests = publicTests;
      answer.result.app_maps = [{ path: MAP_PATH, verdict: 'refused', problems: 1 }];
      answer.result.problems = [MAP_PROBLEM];
      answer.result.problems_complete = true;
      answer.result.refusals = [GENERIC_MAP_REFUSAL];
      answer.result.report.verdict = 'refused';
      answer.result.report.refusal = GENERIC_MAP_REFUSAL;
      answer.result.report.problems = [MAP_PROBLEM];
      answer.result.report.lint.app_maps = [{
        path: MAP_PATH,
        verdict: 'refused',
        errors: [{ code: MAP_PROBLEM.code, detail: MAP_PROBLEM.reason }],
      }];
      break;
    case 'map-refused-behind-other-test': {
      const otherRefusal = { code: 'lint-refused', path: 'tests/broken.json', message: 'Lint refused this test or app map.' };
      answer.state = 'refused';
      answer.result.exitCode = 4;
      answer.result.tests = [...publicTests, { path: 'tests/broken.json', verdict: 'refused', problems: 1 }];
      answer.result.app_maps = [{ path: MAP_PATH, verdict: 'refused', problems: 1 }];
      answer.result.problems = [
        { code: 'invalid-input', file: 'tests/broken.json', at: 'steps[0]', reason: 'Broken test.', severity: 'error' },
        MAP_PROBLEM,
      ];
      answer.result.problems_complete = true;
      answer.result.refusals = [otherRefusal];
      answer.result.report.verdict = 'refused';
      answer.result.report.refusal = otherRefusal;
      answer.result.report.lint.app_maps = [{ path: MAP_PATH, verdict: 'refused', errors: [{ code: MAP_PROBLEM.code }] }];
      break;
    }
    case 'map-worker-stopped':
      answer.state = 'refused';
      answer.result.exitCode = 4;
      answer.result.tests = publicTests;
      answer.result.app_maps = [{ path: MAP_PATH, verdict: 'refused', problems: 0, error: 'lint-worker-stopped', reason: 'the lint check exceeded its limits' }];
      answer.result.problems = [];
      answer.result.problems_complete = true;
      answer.result.refusals = [GENERIC_MAP_REFUSAL];
      answer.result.report.verdict = 'refused';
      answer.result.report.refusal = GENERIC_MAP_REFUSAL;
      answer.result.report.lint.app_maps = [{ path: MAP_PATH, verdict: 'refused', errors: [], error: 'lint-worker-stopped', reason: 'the lint check exceeded its limits' }];
      break;
    case 'map-not-checked':
      answer.state = 'passed';
      answer.result.tests = publicTests;
      answer.result.app_maps = [{ path: MAP_PATH, verdict: 'not-checked', problems: 0 }];
      answer.result.problems_complete = false;
      answer.result.report.lint.complete = false;
      answer.result.report.lint.app_maps = [{ path: MAP_PATH, verdict: 'not-checked', errors: [] }];
      break;
    case 'map-unlisted':
      answer.state = 'passed';
      answer.result.tests = publicTests;
      answer.result.app_maps = [];
      answer.result.problems_complete = true;
      answer.result.report.lint.complete = true;
      answer.result.report.lint.app_maps = [];
      break;
    case 'map-passed':
      answer.result.tests = publicTests;
      answer.result.app_maps = [{ path: MAP_PATH, verdict: 'passed', problems: 0 }];
      answer.result.problems_complete = true;
      answer.result.report.lint.app_maps = [{ path: MAP_PATH, verdict: 'passed', errors: [] }];
      break;
    case 'legacy-no-map-list':
      break;
  }
  return answer;
}

async function setupHarness(t, shape = 'map-refused', { pending = false, checkState = 'passed', declareOnPlaceOrder = true, doorMode = null } = {}) {
  const h = harborWithDeclaredMap(t, { declareOnPlaceOrder, doorMode });
  let lintDone = !pending;
  let currentShape = shape;
  let now;
  const f = await fakeRuntime(t, (entry, fake) => {
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    if (entry.command === 'lint' || fake.posts.some(p => p.command === 'lint' && p.request.requestId === id)) {
      return { status: 200, json: lintDone ? applyMapLintShape(fake.lint(id), currentShape) : fake.job(id, 'lint', 'running') };
    }
    if (entry.command === 'try' || fake.posts.some(p => p.command === 'try' && p.request.requestId === id)) {
      return { status: 200, json: fake.tryJob(id) };
    }
    if (checkState === 'busy' && entry.command === 'check') {
      return {
        status: 503,
        headers: { 'retry-after': '300' },
        json: {
          dispatch: 'not_started',
          provider_calls: 0,
          accounting_complete: true,
          usage: { calls: 0, known_calls: 0, unknown_calls: 0, provider_calls: 0, accounting_complete: true },
          error: { code: 'check-queue-full', details: { retryable: true, retry_after: 300 } },
        },
      };
    }
    if (checkState === 'restarted') {
      const refusal = { code: 'service-restarted', message: 'The interpreter restarted.' };
      return { status: 200, json: fake.job(id, 'check', 'unknown', { refusals: [refusal], report: { refusal } }, 0) };
    }
    return { status: 200, json: fake.check(id, checkState) };
  });
  const env = { HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin };
  const run = async (options, words = ['place-order']) => {
    const p = portsFor(env);
    if (now) p.clock.now = now;
    const code = await runCheck({ cwd: h.repo, words, options }, p.ports);
    now = p.clock.now;
    return { code, out: p.ports.stdout.text, err: p.ports.stderr.text, json: p.ports.stdout.text.startsWith('{') ? JSON.parse(p.ports.stdout.text) : null };
  };
  const simulate = async (options = { '--no-open': true }, words = ['place-order']) => {
    const p = portsFor(env, { openUrl: async () => true });
    const code = await runTry({ cwd: h.repo, words, options }, p.ports);
    return { code, out: p.ports.stdout.text, err: p.ports.stderr.text };
  };
  return {
    h,
    f,
    env,
    run,
    simulate,
    advanceClock: ms => { now = (now ?? Date.parse('2026-10-27T16:27:47Z')) + ms; },
    finishLint: () => { lintDone = true; },
    setShape: next => { currentShape = next; },
    setCheckState: next => { checkState = next; },
  };
}

test('AC1: pdd lint refuses in text and --json when a declared app map is refused, keeping specific code, reason and fix', async t => {
  const s = await setupHarness(t, 'map-refused');
  const textRun = await s.run({ '--lint': true });
  assert.equal(textRun.code, 4, textRun.out + textRun.err);
  assert.match(textRun.out, /template-reference-unprovable\s+app\/maps\/b8\.json\s+initial_world/);
  assert.match(textRun.out, /tests\/place-order\.json\s+refused \(template-reference-unprovable\)/);
  assert.match(textRun.out, /Lint: 0 of 1 tests pass\./);

  const jsonRun = await s.run({ '--lint': true, '--json': true });
  assert.equal(jsonRun.code, 4);
  assert.equal(jsonRun.json.exit_code, 4);
  assert.equal(jsonRun.json.lint_state, 'refused');
  assert.equal(jsonRun.json.state, 'refused');
  assert.equal(jsonRun.json.rows.length, 1);
  assert.equal(jsonRun.json.rows[0].state, 'refused');
  assert.equal(jsonRun.json.rows[0].reason.code, 'template-reference-unprovable');
  assert.equal(jsonRun.json.rows[0].refusals[0].code, 'template-reference-unprovable');
  assert.equal(jsonRun.json.rows[0].refusals[0].path, MAP_PATH);
  assert.equal(jsonRun.json.rows[0].refusals[0].reason, MAP_PROBLEM.reason);
  assert.equal(jsonRun.json.rows[0].refusals[0].fix, MAP_PROBLEM.fix);
  assert.ok(!jsonRun.json.problems.some(item => item.code === 'lint-refused' && item.path === MAP_PATH));
});

test('AC1: declared app map refusal is preserved when an earlier test refusal occupies result.refusals or the worker stops', async t => {
  const behind = await setupHarness(t, 'map-refused-behind-other-test');
  const first = await behind.run({ '--lint': true, '--json': true });
  assert.equal(first.code, 4);
  assert.equal(first.json.rows[0].state, 'refused');
  assert.equal(first.json.rows[0].refusals[0].code, 'template-reference-unprovable');
  assert.equal(first.json.rows[0].refusals[0].path, MAP_PATH);

  const stopped = await setupHarness(t, 'map-worker-stopped');
  const second = await stopped.run({ '--lint': true, '--json': true });
  assert.equal(second.code, 4);
  assert.equal(second.json.rows[0].state, 'refused');
  assert.equal(second.json.rows[0].refusals[0].code, 'lint-worker-stopped');
  assert.equal(second.json.rows[0].refusals[0].path, MAP_PATH);
});

test('AC2: pdd test sends 0 check requests and spends 0 AI calls on a refused declared app map, and --read preserves refused', async t => {
  const s = await setupHarness(t, 'map-refused');
  const lintBatch = await s.run({ '--lint': true, '--json': true });
  assert.equal(lintBatch.code, 4);

  const checkText = await s.run({});
  assert.equal(checkText.code, 4);
  assert.equal(s.f.posts.filter(p => p.command === 'check').length, 0);
  assert.match(checkText.out, /REFUSED before sending \(not sent, 0 AI calls\)/);
  assert.match(checkText.out, /tests\/place-order\.json\s+template-reference-unprovable/);
  assert.match(checkText.out, /Initialize \/state\/attempt\/match_code/);
  assert.doesNotMatch(checkText.out, /^\s+null$/m);

  const checkJson = await s.run({ '--json': true });
  assert.equal(checkJson.code, 4);
  assert.equal(s.f.posts.filter(p => p.command === 'check').length, 0);
  assert.equal(checkJson.json.rows[0].state, 'refused');
  assert.equal(checkJson.json.rows[0].calls, 0);
  assert.equal(checkJson.json.rows[0].refusals[0].code, 'template-reference-unprovable');

  // Even if workspace files change afterward, reading the saved lint or check batch preserves refused (exit 4).
  writeFileSync(join(s.h.repo, MAP_PATH), `${JSON.stringify({ ...MAP_DOC, name: 'Edited Later' }, null, 2)}\n`);
  const readLint = await s.run({ '--read': lintBatch.json.batch, '--json': true }, []);
  assert.equal(readLint.code, 4);
  assert.equal(readLint.json.rows[0].state, 'refused');
  assert.equal(readLint.json.rows[0].refusals[0].code, 'template-reference-unprovable');

  const readCheck = await s.run({ '--read': checkJson.json.batch, '--json': true }, []);
  assert.equal(readCheck.code, 4);
  assert.equal(readCheck.json.rows[0].state, 'refused');
  assert.equal(s.f.posts.filter(p => p.command === 'check').length, 0);
});

test('AC2: pending lint continuation, --retry and restart recovery all enforce the declared app-map lint gate', async t => {
  // 1. Pending standalone lint read later via --read
  const pendingLint = await setupHarness(t, 'map-refused', { pending: true });
  const lintStart = await pendingLint.run({ '--lint': true, '--json': true, '--timeout': 0.01 });
  assert.equal(lintStart.code, 3);
  pendingLint.finishLint();
  const lintResolved = await pendingLint.run({ '--read': lintStart.json.batch, '--json': true }, []);
  assert.equal(lintResolved.code, 4);
  assert.equal(lintResolved.json.rows[0].state, 'refused');
  assert.equal(lintResolved.json.rows[0].refusals[0].code, 'template-reference-unprovable');

  // 2. Pending check batch read later via --read sends 0 checks when declared map refuses,
  // even when reading a legacy batch.json row without saved app_maps (falling back to capture.sources)
  const pendingCheck = await setupHarness(t, 'map-refused', { pending: true });
  const checkStart = await pendingCheck.run({ '--json': true, '--timeout': 0.01 });
  assert.equal(checkStart.code, 3);
  const checkBatchPath = join(pendingCheck.h.state, 'batches', checkStart.json.batch, 'batch.json');
  const legacyBatch = JSON.parse(readFileSync(checkBatchPath, 'utf8'));
  assert.deepEqual(legacyBatch.rows[0].app_maps, [MAP_PATH]);
  delete legacyBatch.rows[0].app_maps;
  writeFileSync(checkBatchPath, JSON.stringify(legacyBatch));
  pendingCheck.finishLint();
  const checkResolved = await pendingCheck.run({ '--read': checkStart.json.batch, '--json': true }, []);
  assert.equal(checkResolved.code, 4);
  assert.equal(checkResolved.json.rows[0].state, 'refused');
  assert.equal(pendingCheck.f.posts.filter(p => p.command === 'check').length, 0);

  // 3. --retry and restart recovery refuse to resend if saved lint has a refused declared map
  const retryHarness = await setupHarness(t, 'map-passed', { checkState: 'busy' });
  const busyRun = await retryHarness.run({ '--json': true, '--timeout': 1 });
  assert.equal(busyRun.code, 5);
  assert.equal(busyRun.json.rows[0].can_retry, true);
  const sentBeforeRetry = retryHarness.f.posts.filter(p => p.command === 'check').length;
  const lintId = JSON.parse(readFileSync(join(retryHarness.h.state, 'batches', busyRun.json.batch, 'batch.json'), 'utf8')).lint.request_ids.at(-1);
  const lintReceiptPath = join(retryHarness.h.state, 'batches', busyRun.json.batch, `${lintId}.json`);
  const refusedLint = applyMapLintShape(JSON.parse(readFileSync(lintReceiptPath, 'utf8')), 'map-refused');
  writeFileSync(lintReceiptPath, JSON.stringify(refusedLint));
  retryHarness.setCheckState('passed');
  retryHarness.advanceClock(400_000);
  const retried = await retryHarness.run({ '--retry': busyRun.json.batch, '--json': true }, []);
  assert.equal(retried.code, 2, retried.err);
  assert.match(retried.err, /saved lint cannot authorize recovery/);
  assert.equal(retryHarness.f.posts.filter(p => p.command === 'check').length, sentBeforeRetry);

  const restartHarness = await setupHarness(t, 'map-passed', { checkState: 'running' });
  const started = await restartHarness.run({ '--json': true, '--timeout': 0.01 });
  assert.equal(started.code, 3);
  assert.equal(restartHarness.f.posts.filter(p => p.command === 'check').length, 1);
  restartHarness.setCheckState('restarted');
  const rLintId = restartHarness.f.posts.find(p => p.command === 'lint').request.requestId;
  const rLintPath = join(restartHarness.h.state, 'batches', started.json.batch, `${rLintId}.json`);
  writeFileSync(rLintPath, JSON.stringify(applyMapLintShape(JSON.parse(readFileSync(rLintPath, 'utf8')), 'map-refused')));
  const recovered = await restartHarness.run({ '--read': started.json.batch, '--json': true }, []);
  assert.equal(restartHarness.f.posts.filter(p => p.command === 'check').length, 1, 'no replacement check posted');
  assert.equal(recovered.code, 3);
  assert.match(recovered.err, /saved lint gives no pass of its own/);
});

test('AC3: pdd simulate stops before /v1/try on refused declared or selected app map, and prints unrelated Lint diagnostic without throwing', async t => {
  // Declared app_maps on the Story's scenario
  const declared = await setupHarness(t, 'map-refused');
  const page = await declared.simulate({ '--no-open': true });
  assert.equal(page.code, 4);
  assert.equal(declared.f.posts.filter(p => p.command === 'try').length, 0);
  assert.match(page.out, /template-reference-unprovable/);

  const cliHarness = await setupHarness(t, 'map-refused', { doorMode: '--cli' });
  const cliDoor = await cliHarness.simulate({ '--cli': true });
  assert.equal(cliDoor.code, 125);
  assert.equal(cliHarness.f.posts.filter(p => p.command === 'try').length, 0);
  assert.match(cliDoor.err, /match_code/);

  const serveHarness = await setupHarness(t, 'map-refused', { doorMode: '--serve' });
  const serveDoor = await serveHarness.simulate({ '--serve': '0' });
  assert.equal(serveDoor.code, 125);
  assert.equal(serveHarness.f.posts.filter(p => p.command === 'try').length, 0);
  assert.match(serveDoor.err, /match_code/);

  // Explicit --app-map on a Story whose scenario does not declare app_maps
  const selectedMap = await setupHarness(t, 'map-refused', { declareOnPlaceOrder: false });
  const explicitPage = await selectedMap.simulate({ '--no-open': true, '--app-map': MAP_PATH }, ['unknown-item']);
  assert.equal(explicitPage.code, 4);
  assert.equal(selectedMap.f.posts.filter(p => p.command === 'try').length, 0);

  const selectedMapCli = await setupHarness(t, 'map-refused', { declareOnPlaceOrder: false, doorMode: '--cli' });
  const explicitCli = await selectedMapCli.simulate({ '--cli': true, '--app-map': MAP_PATH }, ['unknown-item']);
  assert.equal(explicitCli.code, 125);
  assert.equal(selectedMapCli.f.posts.filter(p => p.command === 'try').length, 0);
  assert.match(explicitCli.err, /match_code/);

  // Unrelated scoped-out refusal prints Lint diagnostic on stderr without TypeError and creates the Try
  const unrelated = await setupHarness(t, 'map-refused');
  const okTry = await unrelated.simulate({ '--no-open': true }, ['unknown-item']);
  assert.equal(okTry.code, 0, okTry.out + okTry.err);
  assert.equal(unrelated.f.posts.filter(p => p.command === 'try').length, 1);
  assert.match(okTry.err, /Lint diagnostic: template-reference-unprovable\s+app\/maps\/b8\.json/);
  assert.doesNotMatch(okTry.err, /Lint diagnostic: lint-refused\s+app\/maps\/b8\.json/);
});

test('AC4: not-checked or unlisted map in app_maps is not run (exit 5); legacy answers without app_maps pass; sibling Story stays scoped', async t => {
  for (const [shape, expectedReason] of [
    ['map-not-checked', /lint did not finish/],
    ['map-unlisted', /lint gave no verdict for this app map/],
  ]) {
    const s = await setupHarness(t, shape);
    const lintRes = await s.run({ '--lint': true, '--json': true });
    assert.equal(lintRes.code, 5);
    assert.equal(lintRes.json.rows[0].state, 'not run');
    assert.match(lintRes.json.rows[0].reason.message, expectedReason);

    const checkRes = await s.run({ '--json': true });
    assert.equal(checkRes.code, 5);
    assert.equal(s.f.posts.filter(p => p.command === 'check').length, 0);
    assert.equal(checkRes.json.rows[0].state, 'not run');

    const tryRes = await s.simulate({ '--no-open': true });
    assert.equal(tryRes.code, 5);
    assert.equal(s.f.posts.filter(p => p.command === 'try').length, 0);
    assert.match(tryRes.err, expectedReason);
  }

  // Legacy server reply without result.app_maps or report.lint.app_maps still admits when no refusal/problem names the map
  const legacy = await setupHarness(t, 'legacy-no-map-list');
  const legacyLint = await legacy.run({ '--lint': true, '--json': true });
  assert.equal(legacyLint.code, 0);
  assert.equal(legacyLint.json.rows[0].state, 'passed');

  // Combined batch: place-order (refused map) is refused while unknown-item (no map) passes and dispatches
  const mixed = await setupHarness(t, 'map-refused');
  const mixedLint = await mixed.run({ '--lint': true, '--json': true }, ['place-order', 'unknown-item']);
  assert.equal(mixedLint.code, 4);
  assert.deepEqual(mixedLint.json.rows.map(r => [r.test, r.state]), [
    [TEST_WITH_MAP, 'refused'],
    [TEST_PLAIN, 'passed'],
  ]);

  const mixedCheck = await mixed.run({ '--json': true }, ['place-order', 'unknown-item']);
  assert.equal(mixedCheck.code, 4, mixedCheck.err);
  assert.deepEqual(mixed.f.posts.filter(p => p.command === 'check').map(p => p.request.scenario), [TEST_PLAIN], JSON.stringify(mixedCheck.json));
  assert.deepEqual(mixedCheck.json.rows.map(r => [r.test, r.state]), [
    [TEST_WITH_MAP, 'refused'],
    [TEST_PLAIN, 'passed'],
  ]);
  assert.ok(!mixedCheck.json.warnings.some(w => w.includes('app/maps/b8.json')),
    `refused map already shown on place-order should not repeat as diagnostic: ${mixedCheck.json.warnings.join('; ')}`);
});

test('Formal bounded domain: outcomeFor across testVerdict x mapDeclared x hasMapList x mapVerdict x specificProblem x genericRefusal', () => {
  const scenarioBytes = Buffer.from(JSON.stringify({
    schema_version: 'prompt-runtime.program-scenario.v1',
    steps: [{ step_id: 's1', entry_path: PLACE, operation: 'place_order' }],
  }));
  const promptBytes = Buffer.from('# Place\n');
  const sources = [
    { path: PLACE, bytes: promptBytes },
    { path: TEST_WITH_MAP, bytes: scenarioBytes },
  ];
  const sourceFiles = sources.map(s => ({ path: s.path, sha256: sha(s.bytes) }));
  const caps = ordinaryCapabilities(sources, TEST_WITH_MAP);
  const engine_sha = caps.engine_build;

  let checked = 0;
  for (const testVerdict of ['passed', 'refused', 'not-checked', 'missing']) {
    for (const mapDeclared of [false, true]) {
      for (const hasMapList of [false, true]) {
        for (const mapVerdict of hasMapList ? ['passed', 'refused', 'not-checked', 'missing', 'conflict'] : ['none']) {
          for (const hasSpecificProblem of [false, true]) {
            for (const hasGenericRefusal of [false, true]) {
              for (const complete of [false, true]) {
                checked += 1;
                const tests = testVerdict === 'missing' ? [] : [{ path: TEST_WITH_MAP, verdict: testVerdict }];
                const app_maps = !hasMapList ? undefined
                  : mapVerdict === 'missing' ? []
                  : mapVerdict === 'conflict' ? [{ path: MAP_PATH, verdict: 'passed' }, { path: MAP_PATH, verdict: 'not-checked' }]
                  : [{ path: MAP_PATH, verdict: mapVerdict }];
                const problems = hasSpecificProblem ? [MAP_PROBLEM] : [];
                const refusals = hasGenericRefusal ? [GENERIC_MAP_REFUSAL] : [];
                const anyRefusal = testVerdict === 'refused' || mapVerdict === 'refused' || hasSpecificProblem || hasGenericRefusal;
                const answer = {
                  command: 'lint',
                  state: anyRefusal ? 'refused' : 'passed',
                  engine_sha,
                  result: {
                    tests,
                    ...(hasMapList ? { app_maps } : {}),
                    problems,
                    problems_complete: complete,
                    refusals,
                    capabilities: [{ path: TEST_WITH_MAP, report: caps }],
                    report: {
                      verdict: anyRefusal ? 'refused' : 'passed',
                      lint: { complete, tests, ...(hasMapList ? { app_maps } : {}) },
                      program: { prompts: [{ path: PLACE, state: 'approved', admission_state: 'approved', interface: { calls: [] } }], refused_prompts: [] },
                    },
                  },
                };
                const outcome = outcomeFor(answer, {
                  kind: 'lint',
                  test: TEST_WITH_MAP,
                  steps: [{ step_id: 's1', entry_path: PLACE, operation: 'place_order' }],
                  appMaps: mapDeclared ? [MAP_PATH] : [],
                  sourceFiles,
                });

                const mapRefused = mapDeclared && (mapVerdict === 'refused' || hasSpecificProblem || hasGenericRefusal);
                if (mapRefused) {
                  assert.equal(outcome.state, 'refused', `must refuse when declared map is refused (${JSON.stringify({ testVerdict, mapVerdict, hasSpecificProblem, hasGenericRefusal })})`);
                  if (hasSpecificProblem) assert.equal(outcome.code, MAP_PROBLEM.code, 'specific map problem must win over generic lint-refused');
                  continue;
                }
                if (testVerdict === 'refused') {
                  assert.equal(outcome.state, 'refused');
                  continue;
                }
                if (testVerdict === 'passed') {
                  if (mapDeclared && hasMapList && mapVerdict !== 'passed') {
                    assert.equal(outcome.state, 'not_run', 'unverified map in reported app_maps cannot pass');
                    assert.equal(outcome.reason, !complete || mapVerdict === 'not-checked' ? 'lint did not finish' : 'lint gave no verdict for this app map');
                  } else {
                    assert.equal(outcome.state, 'passed');
                  }
                  continue;
                }
                if (testVerdict === 'missing' && anyRefusal) {
                  assert.equal(outcome.state, 'refused');
                } else {
                  assert.equal(outcome.state, 'not_run');
                }
              }
            }
          }
        }
      }
    }
  }
  assert.equal(checked, 384);
});
