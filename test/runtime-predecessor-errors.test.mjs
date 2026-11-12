import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { projectAnswer, renderJson, renderText, exitCodeFor, summaryLine } from '../src/runtime-output.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, root, sink, TOKEN } from './runtime-fake.mjs';

// Independently authored synthetic inputs. These tests do not replay the private
// original case or call a live interpreter. Only the local CLI projection is tested.
const reference = (step_id = 'load-record', path = '/loaded') => ({ $step_result: { step_id, path } });
const fact = (input_path = '/loaded', extra = {}) => ({ step_id: 'show-record', input_path,
  predecessor_step_id: 'load-record', result_path: '/loaded', error_code: 'record-unavailable', ...extra });
const DEPENDENCY = '  Dependency: step "show-record" input "/loaded" references step "load-record" result "/loaded"; that step reported error code "record-unavailable".';
const RAW_PAYLOAD = 'PRIVATE_APPLICATION_ERROR_BODY';
function fixture() {
  const steps = [
    { step_id: 'load-record', input: {}, checks: [{ criterion_id: 'AC1', target: 'result', path: '/loaded', op: 'equals', value: true }] },
    { step_id: 'show-record', input: { loaded: reference() }, checks: [{ criterion_id: 'AC2', target: 'result', path: '/shown', op: 'equals', value: true }] }
  ];
  const refusal = { code: 'key-error', section: 'samples[0].steps[1]', at: 'steps[1]',
    message: 'The result is unavailable.', reason: 'The referenced result is unavailable.',
    fix: 'Inspect the original report.', where: 'tests/place-order.json samples[0].steps[1]', cause: 'test' };
  const answer = { command: 'check', state: 'refused', usage: { calls: 3, requested_model: 'synthetic-model' },
    result: { refusals: [refusal], why: 'The result is unavailable.', next_step: 'Inspect the original report. Do not resend.',
      report: { samples: [{ steps: [
        { step_id: 'load-record', result: null, error: { code: 'record-unavailable', data: RAW_PAYLOAD }, checks: [
          { criterion_id: 'AC1', target: 'result', path: '/loaded', expected: true, actual: false, passed: false }
        ] }
      ] }], criterion_results: [{ criterion_id: 'AC1', status: 'failed' }, { criterion_id: 'AC2', status: 'not_checked' }] } } };
  return { answer, steps, refusal };
}
function project(f = fixture(), extra = {}) {
  return projectAnswer(f.answer, { steps: f.steps, criterionTexts: { AC1: 'The record loads.', AC2: 'The record appears.' }, ...extra });
}
function asRow(view, steps) {
  return { story: 'example', title: 'Example', test: 'tests/place-order.json', phase: 'server',
    request_ids: ['synthetic-receipt'], steps, ...view };
}
const noFact = f => assert.equal(Object.hasOwn(project(f).refusals[0], 'dependency_errors'), false);

test('PREDECESSOR replay: every approved renderJson scenario check', () => {
  const scenario = JSON.parse(readFileSync(new URL('./runtime/show-predecessor-error.json', import.meta.url), 'utf8'));
  const covered = new Set();
  for (const step of scenario.steps) {
    assert.equal(step.operation, 'renderJson');
    const result = renderJson(step.input);
    for (const check of step.checks) {
      assert.equal(check.target, 'result'); assert.equal(check.op, 'equals');
      const actual = check.path.split('/').slice(1).map(token => token.replaceAll('~1', '/').replaceAll('~0', '~'))
        .reduce((value, key) => value?.[key], result);
      assert.deepEqual(actual, check.value, `PREDECESSOR vector ${step.step_id} ${check.path}`);
      covered.add(check.criterion_id);
    }
  }
  assert.deepEqual([...covered].sort(), scenario.criteria.map(item => item.id).sort());
});

test('PREDECESSOR projection shows a direct reported error in JSON and terminal without changing evidence', () => {
  const f = fixture(), before = structuredClone(f), view = project(f);
  assert.deepEqual(view.refusals[0].dependency_errors, [fact()], 'PREDECESSOR supported fact must survive');
  const row = asRow(view, f.steps), code = exitCodeFor([row]);
  const json = renderJson({ repo: 'example/project', rows: [row], exitCode: code });
  assert.deepEqual(json.rows[0].refusals[0].dependency_errors, [fact()]);
  assert.ok(renderText({ rows: [row], exitCode: code }).split('\n').includes(DEPENDENCY));
  assert.equal(json.rows[0].refusals[0].code, 'key-error');
  assert.equal(json.rows[0].refusals[0].cause, 'test');
  assert.equal(json.rows[0].refusals[0].where, f.refusal.where);
  assert.equal(json.rows[0].refusals[0].reason, f.refusal.reason);
  assert.equal(json.rows[0].refusals[0].fix, f.refusal.fix);
  assert.equal(json.rows[0].next_step, f.answer.result.next_step);
  assert.deepEqual(view.checks, { passed: 0, total: 1 });
  assert.deepEqual(view.criteria, { passed: 0, total: 2 });
  const failed = json.rows[0].failed_checks[0];
  assert.deepEqual(Object.fromEntries(['criterion_id', 'step_id', 'target', 'path', 'expected', 'actual'].map(k => [k, failed[k]])),
    { criterion_id: 'AC1', step_id: 'load-record', target: 'result', path: '/loaded', expected: true, actual: false });
  assert.equal(json.rows[0].calls, 3); assert.equal(json.rows[0].requested_model, 'synthetic-model');
  assert.equal(code, 4); assert.match(summaryLine([row]), /0\/1 checks.*3 AI calls$/);
  assert.doesNotMatch(JSON.stringify(json), new RegExp(RAW_PAYLOAD));
  assert.doesNotMatch(renderText({ rows: [row], exitCode: code }), /not executed|unexecuted/i);
  assert.deepEqual(f, before, 'projection cannot mutate captured inputs or raw receipt');
});

test('PREDECESSOR references keep traversal order and distinct escaped input pointers', () => {
  const f = fixture();
  f.steps[1].input = { rows: [{ 'a/b~c': reference() }, reference()], again: reference(), other: reference('unrelated') };
  assert.deepEqual(project(f).refusals[0].dependency_errors, [fact('/rows/0/a~1b~0c'), fact('/rows/1'), fact('/again')]);
});

// Build and snapshot deep JSON without recursive cloning. These are synthetic
// saved-input shapes; they do not claim current immediate admission accepts them.
function nestedInput(depth, leaf) {
  let input = leaf;
  for (let i = 0; i < depth; i++) input = { a: input };
  return input;
}

test('PREDECESSOR deep traversal without references preserves the existing refusal', () => {
  const f = fixture(); f.steps[1].input = nestedInput(3500, null);
  const before = JSON.stringify(f), baseline = project(f, { steps: [] });
  let view;
  assert.doesNotThrow(() => { view = project(f); }, 'PREDECESSOR deep traversal must preserve the original refusal');
  assert.deepEqual(view, baseline);
  const row = asRow(view, f.steps);
  assert.equal(Object.hasOwn(renderJson({ rows: [row], exitCode: 4 }).rows[0].refusals[0], 'dependency_errors'), false);
  assert.doesNotMatch(renderText({ rows: [row], exitCode: 4 }), /  Dependency:/);
  assert.equal(JSON.stringify(f), before, 'deep inputs and receipts stay unchanged');
});

test('PREDECESSOR deep traversal retains full pointers and sibling reference order', () => {
  const f = fixture(), depth = 3500;
  f.steps[1].input = { before: reference(), deep: nestedInput(depth, { ' loaded/~ ': reference() }), after: [reference()] };
  const before = JSON.stringify(f), expected = [fact('/before'), fact('/deep' + '/a'.repeat(depth) + '/ loaded~1~0 '), fact('/after/0')];
  let view;
  assert.doesNotThrow(() => { view = project(f); }, 'PREDECESSOR deep traversal must retain supported references');
  assert.deepEqual(view.refusals[0].dependency_errors, expected);
  const row = asRow(view, f.steps);
  assert.deepEqual(renderJson({ rows: [row], exitCode: 4 }).rows[0].refusals[0].dependency_errors, expected);
  assert.ok(renderText({ rows: [row], exitCode: 4 }).includes(JSON.stringify(expected[1].input_path)));
  assert.equal(JSON.stringify(f), before, 'deep reference traversal cannot mutate input');
});

test('PREDECESSOR deep traversal through public legacy saved CLI read preserves output without fetching', { timeout: 30000 }, async t => {
  const h = harbor(t), batch = '20261112-030000-dead', id = '22222222-2222-4222-8222-222222222222';
  const folder = join(h.state, 'batches', batch); mkdirSync(folder, { recursive: true });
  for (const hasReference of [false, true]) {
    const steps = [{ step_id: 'load-record', input: {}, checks: [] },
      { step_id: 'show-record', input: nestedInput(3500, hasReference ? reference() : null), checks: [] }];
    const receipt = { id, requestId: id, command: 'check', state: 'refused', usage: { calls: 2 }, result: {
      refusals: [{ code: 'key-error', section: 'samples[0].steps[1]' }],
      report: { samples: [{ steps: [{ step_id: 'load-record', result: null, error: { code: 'record-unavailable' } }] }] }
    } };
    const saved = { version: 1, batch, root: h.repo, origin: 'http://127.0.0.1:1', login: 'octo', user_id: '4242',
      created_at: '2026-11-12T03:00:00.000Z', intent: 'check', files: [], bytes: 0, source_sha256: 'a'.repeat(64),
      contract_snapshots: [], lint: null, warnings: [], rows: [{ test: 'test/example.json', story: 'example', title: 'Example',
        state: 'refused', recovery_state: 'refused', phase: 'server', request_ids: [id], refusals: [], steps, warnings: [] }] };
    const rawReceipt = JSON.stringify(receipt), capturedSteps = JSON.stringify(steps);
    writeFileSync(join(folder, 'batch.json'), JSON.stringify(saved));
    writeFileSync(join(folder, id + '.json'), rawReceipt);
    const stdout = sink(), stderr = sink(); let fetchCalls = 0, code;
    await assert.doesNotReject(async () => {
      code = await runCheck({ cwd: h.repo, words: [batch], options: { '--read': true, '--json': true } }, {
        env: { ...process.env, PDD_STATE_DIR: h.state }, stdout, stderr, interactive: false,
        gh: args => ({ status: 0, stdout: args[0] === 'auth' ? TOKEN : 'octo 4242' }),
        fetch: () => { fetchCalls++; throw new Error('Unexpected network call'); },
        now: () => Date.parse('2026-11-12T04:00:00Z')
      });
    }, 'PREDECESSOR deep traversal must preserve public saved-read output');
    assert.equal(code, 4); assert.equal(stderr.text, ''); assert.equal(fetchCalls, 0);
    const row = JSON.parse(stdout.text).rows[0];
    assert.equal(row.state, 'refused'); assert.equal(row.calls, 2); assert.equal(row.refusals[0].code, 'key-error');
    if (hasReference) assert.deepEqual(row.refusals[0].dependency_errors, [fact('/a'.repeat(3500))]);
    else assert.equal(Object.hasOwn(row.refusals[0], 'dependency_errors'), false);
    assert.equal(readFileSync(join(folder, id + '.json'), 'utf8'), rawReceipt);
    assert.equal(JSON.stringify(JSON.parse(readFileSync(join(folder, 'batch.json'), 'utf8')).rows[0].steps), capturedSteps);
  }
});

test('PREDECESSOR different earlier errors follow input references rather than report order', () => {
  const f = fixture(), first = f.steps[0], dependent = f.steps[1];
  f.steps = [first, { step_id: 'load-second', input: {}, checks: [] }, dependent];
  dependent.input = { second: reference('load-second', '/record'), first: reference() };
  f.answer.result.report.samples[0].steps.push({ step_id: 'load-second', result: null, error: { code: 'second-unavailable' }, checks: [] });
  f.refusal.section = 'samples[0].steps[2]'; f.refusal.at = 'steps[2]';
  f.refusal.where = 'tests/place-order.json samples[0].steps[2]';
  assert.deepEqual(project(f).refusals[0].dependency_errors, [
    fact('/second', { predecessor_step_id: 'load-second', result_path: '/record', error_code: 'second-unavailable' }),
    fact('/first')
  ]);
});

test('PREDECESSOR missing, malformed, conflicting or non-earlier evidence adds no fact', () => {
  const mutations = [
    f => { f.steps = []; },
    f => { delete f.steps[1].input; },
    f => { f.steps[1].input = { loaded: '$step_result load-record /loaded' }; },
    f => { f.steps[1].input.loaded = { ...reference(), extra: true }; },
    f => { f.steps[1].input.loaded.$step_result.extra = true; },
    f => { delete f.steps[1].input.loaded.$step_result.path; },
    f => { f.steps[1].input.loaded.$step_result.path = 1; },
    f => { f.steps[1].input.loaded = reference('not-authored'); },
    f => { f.steps[1].input.loaded = reference('show-record'); },
    f => { f.steps.push({ step_id: 'load-record', input: {} }); },
    f => { f.steps.push({ step_id: 'show-record', input: {} }); },
    f => { f.steps[0].step_id = null; },
    f => { f.steps[0].step_id = '[secret]'; f.steps[1].input.loaded = reference('[secret]'); f.answer.result.report.samples[0].steps[0].step_id = '[secret]'; },
    f => { f.answer.result.report.samples[0].steps[0].step_id = 'other-record'; },
    f => { f.answer.result.report.samples[0].steps[0].step_id = null; },
    f => { f.answer.result.report.samples[0].steps.push({ step_id: 'other-dependent', checks: [] }); },
    f => { f.answer.result.report.samples[0].steps.push({ ...f.answer.result.report.samples[0].steps[0] }); },
    f => { delete f.answer.result.report.samples[0].steps[0].error; },
    f => { delete f.answer.result.report.samples[0].steps[0].error; f.answer.result.report.samples[0].steps[0].result = { loaded: true }; },
    f => { f.answer.result.report.samples[0].steps[0].error.code = ''; },
    f => { f.answer.result.report.samples[0].steps[0].error.code = '   '; },
    f => { f.answer.result.report.samples[0].steps[0].error.code = 7; },
    f => { f.answer.result.report.samples[0].steps[0].error.code = '[secret]'; },
    f => { f.answer.result.report.samples[0].steps[0].result = { loaded: true }; },
    f => { f.answer.result.report.samples[0].steps[0].result = false; },
    f => { f.answer.result.report.samples[0].steps[0].result = 0; },
    f => { f.refusal.section = 'steps[1]'; delete f.refusal.at; },
    f => { delete f.refusal.section; },
    f => { f.refusal.at = 'steps[0]'; },
    f => { f.refusal.where = 'tests/place-order.json samples[0].steps[0]'; },
    f => { f.refusal.section = 'samples[1].steps[1]'; delete f.refusal.at; },
    f => { f.refusal.section = 'samples[0].steps[8]'; delete f.refusal.at; },
    f => { f.refusal.at = 'samples[1].steps[1]'; },
    f => { f.answer.state = 'running'; },
    f => { f.answer.command = 'lint'; }
  ];
  for (const [i, mutate] of mutations.entries()) {
    const f = fixture(); mutate(f);
    assert.equal(Object.hasOwn(project(f).refusals[0], 'dependency_errors'), false, `PREDECESSOR unsupported evidence variant ${i}`);
  }
  const present = fixture(); present.answer.result.report.samples[0].steps.push({ step_id: 'show-record', checks: [] });
  assert.deepEqual(project(present).refusals[0].dependency_errors, [fact()], 'a matching reported dependent row also supports the fact');
  const absent = fixture(); delete absent.answer.result.report.samples[0].steps[0].result;
  assert.deepEqual(project(absent).refusals[0].dependency_errors, [fact()], 'absent and null normal results both support reported error facts');
});

for (const location of ['section', 'at', 'field', 'where']) {
  for (const [kind, value] of [
    ['array', [location === 'section' ? 'samples[0].steps[1]' : 'samples[1].steps[0]']],
    ['object', {}], ['number', 1], ['boolean', false]
  ]) test(`PREDECESSOR location types reject ${kind} ${location} without changing refusal or recovery`, () => {
    const f = fixture(); f.refusal[location] = value;
    const before = structuredClone(f), view = project(f);
    assert.equal(Object.hasOwn(view.refusals[0], 'dependency_errors'), false,
      `PREDECESSOR malformed ${kind} ${location} must not establish or bypass association`);
    assert.deepEqual(view, project(f, { steps: [] }), 'all original refusal, outcome, check, accounting and recovery facts stay unchanged');
    const row = asRow(view, f.steps);
    assert.equal(Object.hasOwn(renderJson({ rows: [row], exitCode: 4 }).rows[0].refusals[0], 'dependency_errors'), false);
    assert.doesNotMatch(renderText({ rows: [row], exitCode: 4 }), /  Dependency:/);
    assert.deepEqual(f, before);
  });
}

test('PREDECESSOR location types allow absent or null optional companions in legacy reports', () => {
  for (const location of ['at', 'field', 'where', 'all']) for (const kind of ['absent', 'null']) {
    const f = fixture();
    for (const field of location === 'all' ? ['at', 'field', 'where'] : [location]) {
      if (kind === 'absent') delete f.refusal[field]; else f.refusal[field] = null;
    }
    assert.deepEqual(project(f).refusals[0].dependency_errors, [fact()], `${kind} ${location} keeps the exact section anchor`);
  }
});

test('PREDECESSOR sample location controls attribution instead of matching IDs in another sample', () => {
  const f = fixture(), selected = f.answer.result.report.samples[0];
  const other = structuredClone(selected); other.steps[0].error.code = 'wrong-sample-code';
  f.answer.result.report.samples.unshift(other);
  f.refusal.section = f.refusal.at = 'samples[1].steps[1]';
  f.refusal.where = 'tests/place-order.json samples[1].steps[1]';
  assert.deepEqual(project(f).refusals[0].dependency_errors, [fact()]);
  delete selected.steps[0].error;
  noFact(f);
});

test('PREDECESSOR diagnostic strings clean secrets, controls and host paths without treating pointers as host paths', () => {
  const f = fixture();
  const id = 'load-record';
  const pointer = `/home/${TOKEN}/value\u0007`;
  f.steps[1].input = { [`/tmp/${TOKEN}/item\u0007`]: reference(id, pointer) };
  const view = project(f, { secrets: [TOKEN] }), added = view.refusals[0].dependency_errors;
  assert.equal(added.length, 1);
  assert.equal(added[0].result_path, '/home/[secret]/value');
  assert.ok(added[0].input_path.startsWith('/~1tmp~1[secret]~1item'));
  // A host path is a separate token here so the existing cleaner recognizes it.
  const host = fixture(); host.answer.result.report.samples[0].steps[0].error.code = 'record-error /srv/private/code';
  const hostFact = project(host).refusals[0].dependency_errors;
  assert.ok(!JSON.stringify(hostFact ?? null).includes('/srv/private/code'));
  const identity = fixture(), rawId = `load-${TOKEN}\u001b[31m /srv/private/record`;
  identity.steps[0].step_id = identity.answer.result.report.samples[0].steps[0].step_id = rawId;
  identity.steps[1].input.loaded = reference(rawId);
  const safeIdentity = JSON.stringify(project(identity, { secrets: [TOKEN] }).refusals[0].dependency_errors ?? null);
  assert.ok(!safeIdentity.includes(TOKEN)); assert.ok(!safeIdentity.includes('/srv/private/record'));

  for (const value of Object.values(added[0])) {
    assert.doesNotMatch(value, new RegExp(TOKEN));
    assert.doesNotMatch(value, /[\u0000-\u001f\u007f-\u009f]/);
  }
  // Credential-shaped strings must be cleaned even without a matching known secret.
  const credential = fixture(); credential.steps[1].input = { value: reference('load-record', '/sk-abcdefghijklmnop/value') };
  const safe = project(credential).refusals[0].dependency_errors;
  assert.equal(safe[0].result_path, '/[secret]/value');
});

test('PREDECESSOR new identities and error codes redact colon-adjacent server paths', () => {
  const f = fixture(), predecessorId = 'load:/srv/private/predecessor', dependentId = 'show:/srv/private/dependent';
  f.steps[0].step_id = f.answer.result.report.samples[0].steps[0].step_id = predecessorId;
  f.steps[1].step_id = dependentId;
  f.steps[1].input.loaded = reference(predecessorId);
  f.answer.result.report.samples[0].steps[0].error.code = 'unavailable:/srv/private/code';
  const view = project(f), expected = fact('/loaded', { step_id: 'show:<server path>',
    predecessor_step_id: 'load:<server path>', error_code: 'unavailable:<server path>' });
  assert.deepEqual(view.refusals[0].dependency_errors, [expected], 'PREDECESSOR new identity/code fields must redact colon-adjacent paths');
  const row = asRow(view, f.steps);
  assert.deepEqual(renderJson({ rows: [row], exitCode: 4 }).rows[0].refusals[0].dependency_errors, [expected]);
  const line = renderText({ rows: [row], exitCode: 4 }).split('\n').find(line => line.startsWith('  Dependency:'));
  assert.doesNotMatch(line, /\/srv\/private\//);
});

test('PREDECESSOR pointer cleaning preserves significant spaces around removed controls', () => {
  const f = fixture();
  f.steps[1].input = { ' loaded \u0007 ': reference('load-record', '/ loaded \u0007 ') };
  const view = project(f), expected = fact('/ loaded  ', { result_path: '/ loaded  ' });
  assert.deepEqual(view.refusals[0].dependency_errors, [expected], 'PREDECESSOR pointer spaces must survive control removal');
  const row = asRow(view, f.steps);
  assert.deepEqual(renderJson({ rows: [row], exitCode: 4 }).rows[0].refusals[0].dependency_errors, [expected]);
  assert.ok(renderText({ rows: [row], exitCode: 4 }).includes('input "/ loaded  " references step "load-record" result "/ loaded  "'));
});

test('PREDECESSOR incomplete usage keeps its known lower bound and cannot change summary or exit', () => {
  const f = fixture(); Object.assign(f.answer.usage, { accounting_complete: false, known_calls: 2, unknown_calls: 1 });
  const row = asRow(project(f), f.steps), without = structuredClone(row);
  delete without.refusals[0].dependency_errors;
  const rendered = renderJson({ repo: 'example/project', rows: [row], exitCode: exitCodeFor([row]) });
  assert.equal(rendered.rows[0].calls, 'unknown');
  assert.equal(rendered.rows[0].known_calls, 2); assert.equal(rendered.rows[0].unknown_calls, 1);
  assert.equal(rendered.rows[0].accounting_complete, false);
  assert.equal(summaryLine([row]), summaryLine([without]));
  assert.match(summaryLine([row]), /2 AI calls \+ 1 unknown$/);
  assert.equal(exitCodeFor([row]), exitCodeFor([without]));
});

const CLI_FACT = fact('/customerName');
const CLI_DEPENDENCY = DEPENDENCY.replace('input "/loaded"', 'input "/customerName"');

async function cliFixture(t) {
  const f = fixture();
  const h = harbor(t, repo => {
    const path = join(repo, 'tests/place-order.json'), doc = JSON.parse(readFileSync(path, 'utf8'));
    const template = doc.steps[0];
    // Keep the fixture's valid schema and all original criterion checks. The
    // report is independently synthetic; the fake engine does not execute it.
    doc.steps = f.steps.map((step, index) => ({ ...template, step_id: step.step_id,
      input: { ...template.input, ...(index ? { customerName: reference() } : {}) } }));
    writeFileSync(path, JSON.stringify(doc));
  });
  const bin = join(h.sandbox, 'bin'); mkdirSync(bin);
  writeFileSync(join(bin, 'gh'), `#!/bin/sh\nif [ "$1" = auth ]; then echo ${TOKEN}; else echo "octo 4242"; fi\n`, { mode: 0o700 });
  const runtime = await fakeRuntime(t, (entry, fake) => {
    if (entry.command === 'lint') return { status: 200, json: fake.lint(entry.request.requestId) };
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    const answer = fake.job(id, 'check', 'refused', structuredClone(f.answer.result), 3);
    fake.jobs.set(id, answer);
    return { status: 200, json: answer };
  });
  async function run(args) {
    const child = spawn(process.execPath, [join(root, 'bin/pdd.mjs'), 'test', ...args], { cwd: h.repo,
      env: { ...process.env, HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: runtime.origin, PATH: bin + ':' + process.env.PATH },
      stdio: ['ignore', 'pipe', 'pipe'] });
    t.after(() => { if (child.exitCode === null) child.kill(); });
    let out = '', err = '';
    child.stdout.on('data', chunk => out += chunk); child.stderr.on('data', chunk => err += chunk);
    const code = await new Promise((resolve, reject) => { child.on('error', reject); child.on('close', resolve); });
    return { code, out, err };
  }
  return { h, runtime, run };
}

test('PREDECESSOR real CLI shows immediate JSON and completed saved JSON/text without another Check POST', { timeout: 30000 }, async t => {
  const c = await cliFixture(t);
  const initial = await c.run(['place-order', '--json']);
  assert.equal(initial.code, 4, initial.err);
  const json = JSON.parse(initial.out);
  assert.deepEqual(json.rows[0].refusals[0].dependency_errors, [CLI_FACT]);
  assert.equal(c.runtime.posts.filter(post => post.command === 'check').length, 1);
  // Change current authored input after dispatch. Attribution must use captured input.
  const path = join(c.h.repo, 'tests/place-order.json'), changed = JSON.parse(readFileSync(path, 'utf8'));
  changed.steps[1].input = {}; writeFileSync(path, JSON.stringify(changed));
  const postCount = c.runtime.posts.length;
  const saved = await c.run(['--read', json.batch, '--json']);
  const savedText = await c.run(['--read', json.batch]);
  assert.equal(saved.code, 4, saved.err); assert.equal(savedText.code, 4, savedText.err);
  const read = JSON.parse(saved.out);
  assert.deepEqual(read.rows[0].refusals, json.rows[0].refusals);
  for (const key of ['state', 'checks', 'criteria', 'failed_checks', 'calls', 'next_step', 'summary_line'])
    assert.deepEqual(read.rows[0][key], json.rows[0][key], `saved read preserves ${key}`);
  assert.ok(savedText.out.split('\n').includes(CLI_DEPENDENCY));
  assert.equal(c.runtime.posts.length, postCount, 'completed saved reads send no POST');
});

test('PREDECESSOR real CLI immediate terminal shows the dependency without retry advice', { timeout: 30000 }, async t => {
  const c = await cliFixture(t), output = await c.run(['place-order']);
  assert.equal(output.code, 4, output.err);
  assert.ok(output.out.split('\n').includes(CLI_DEPENDENCY));
  assert.match(output.out, /Next: Inspect the original report\. Do not resend\./);
  assert.doesNotMatch(output.out, /not executed|unexecuted|Run it again|a new request/i);
  assert.equal(c.runtime.posts.filter(post => post.command === 'check').length, 1);
});

test('PREDECESSOR old completed saved batch and UUID-only reads cannot invent authored references', { timeout: 30000 }, async t => {
  const c = await cliFixture(t), initial = await c.run(['place-order', '--json']);
  assert.equal(initial.code, 4, initial.err);
  const json = JSON.parse(initial.out), path = join(c.h.state, 'batches', json.batch, 'batch.json');
  const old = JSON.parse(readFileSync(path, 'utf8'));
  for (const row of old.rows) {
    delete row.steps;
    for (const refusal of row.refusals ?? []) delete refusal.dependency_errors;
  }
  writeFileSync(path, JSON.stringify(old));
  const posts = c.runtime.posts.length;
  const saved = await c.run(['--read', json.batch, '--json']);
  assert.equal(saved.code, 4, saved.err);
  assert.equal(Object.hasOwn(JSON.parse(saved.out).rows[0].refusals[0], 'dependency_errors'), false);
  const id = c.runtime.posts.find(post => post.command === 'check').request.requestId;
  const uuid = await c.run(['--read', id, '--json']);
  assert.equal(uuid.code, 4, uuid.err);
  assert.equal(Object.hasOwn(JSON.parse(uuid.out).rows[0].refusals[0], 'dependency_errors'), false);
  assert.equal(c.runtime.posts.length, posts, 'reading missing authored references cannot dispatch work');
});
