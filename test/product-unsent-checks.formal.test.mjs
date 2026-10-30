import test from 'node:test';
import assert from 'node:assert/strict';

// Oracle: product-unsent-checks.md, Rules to check. This finite helper-level
// check injects raw saved bytes and source hashes, never desired Story verdicts.
// The alternate module runs the unchanged harness against a private old-code
// control. Product integration and actual runCheck producers have separate tests.
const runtime = await import(process.env.PDD_UNSENT_FORMAL_MODULE
  ?? new URL('../src/runtime-client.mjs', import.meta.url).href);
const A = 'a'.repeat(64), B = 'b'.repeat(64);
const STORY = 'user_stories/one.md', OTHER = 'user_stories/two.md';
const TESTS = ['test/a.json', 'test/b.json'];
const clone = value => structuredClone(value);
const forbidden = name => () => assert.fail(`Forbidden saved-evidence effect: ${name}`);
const uuid = n => `11111111-1111-4111-8111-${String(n).padStart(12, '0')}`;

function authoredRow(story, path) {
  return { story, test: path, request_ids: [], state: 'not_run', max_calls: 18,
    criteria_total: 1, criterion_texts: { AC1: 'Synthetic complete criterion.' },
    steps: [{ step_id: 'observe', entry_path: 'prompts/example.prompt.md', operation: 'observe',
      checks: [{ criterion_id: 'AC1', target: 'result', path: '/ok', op: 'equals', value: true }] }] };
}

function receipt(id, state = 'passed') {
  return { requestId: id, id, command: 'check', state, usage: { calls: 1 }, result: { report: {
    criterion_results: [{ criterion_id: 'AC1', status: state === 'failed' ? 'failed' : 'passed' }],
    samples: [{ sample: 1, steps: [{ step_id: 'observe', result: { ok: true },
      checks: [{ criterion_id: 'AC1', target: 'result', path: '/ok', op: 'equals',
        expected: true, actual: true, passed: state !== 'failed' }] }] }],
  } } };
}

// Each selected row remains in the raw record, including every unsent row.
function world(specs, { intent = 'check', current = true, fullTests = TESTS } = {}) {
  const records = [], files = new Map(), captures = [];
  let sequence = 0, captureCurrent = current;
  for (const [index, spec] of specs.entries()) {
    const batch = { version: 1, batch: `20261030-120000-${String(index).padStart(4, '0')}`,
      root: '/saved', source_sha256: A, created_at: new Date(1000 + index * 2000).toISOString(), rows: [] };
    if (intent !== 'absent') batch.intent = intent;
    for (const input of spec.rows) {
      const row = authoredRow(input.story ?? STORY, input.test);
      row.state = input.savedState ?? input.status;
      if (input.status === 'unsent') {
        if (input.at !== undefined) row.ended_at = input.at;
      } else {
        const id = uuid(++sequence);
        row.request_ids = [id]; row.ended_at = input.at;
        const answer = receipt(id, input.status === 'missingreceipt' ? 'passed' : input.status);
        if (input.priorAttempt) {
          const prior = uuid(++sequence); row.request_ids.unshift(prior);
          files.set(`/state/batches/${batch.batch}/${prior}.json`, JSON.stringify(receipt(prior)));
        }
        input.answer?.(answer);
        if (input.status !== 'missingreceipt') files.set(`/state/batches/${batch.batch}/${id}.json`, JSON.stringify(answer));
      }
      input.edit?.(row);
      batch.rows.push(row);
    }
    const lint = uuid(++sequence);
    batch.lint = { request_ids: [lint], state: 'passed' };
    files.set(`/state/batches/${batch.batch}/${lint}.json`, JSON.stringify({ requestId: lint, id: lint, command: 'lint', state: 'passed', ended_at: 999999 }));
    records.push(batch); files.set(`/state/batches/${batch.batch}/batch.json`, JSON.stringify(batch));
  }
  const before = JSON.stringify([...files]);
  const ports = {
    env: { PDD_STATE_DIR: '/state' }, realpath: path => path,
    readDir: path => { assert.equal(path, '/state/batches'); return records.map(record => record.batch).reverse(); },
    readFile: path => {
      if (!files.has(path)) throw Object.assign(Error('synthetic missing receipt'), { code: 'ENOENT' });
      return files.get(path);
    },
    captureSource: (root, selection) => {
      assert.equal(root, '/saved'); assert.equal(selection.appMap, null); captures.push(clone(selection.tests));
      // A shortened sent-only selection cannot accidentally look current.
      return { sha256: captureCurrent && JSON.stringify(selection.tests) === JSON.stringify(fullTests) ? A : B };
    },
    fetch: forbidden('fetch'), gh: forbidden('gh'), writeFile: forbidden('writeFile'),
    mkdir: forbidden('mkdir'), startRun: forbidden('workflow.start'),
  };
  return { ports, records, captures, setCurrent(value) { captureCurrent = value; },
    unchanged() { assert.equal(JSON.stringify([...files]), before); } };
}

const summary = (pass, current, at, story = STORY) => ({ story, pass, current, result: pass ? '✓' : 'no verdict', at });
const sorted = rows => [...rows].sort((a, b) => JSON.stringify(a).localeCompare(JSON.stringify(b)));
function exact(reply, expected, message, legacyHints = 0) {
  assert.deepEqual(Object.keys(reply).sort(), ['stories', 'warnings'], message);
  assert.deepEqual(sorted(reply.stories), sorted(expected), message);
  assert.ok(Array.isArray(reply.warnings), message);
  assert.equal(new Set(reply.warnings).size, reply.warnings.length, message);
  for (const warning of reply.warnings) assert.ok(typeof warning === 'string' && warning.length > 0 && warning.length < 2000, message);
  const hints = reply.warnings.filter(warning => ['older checks', 'not counted', 'pdd check'].every(text => warning.toLowerCase().includes(text)));
  assert.equal(hints.length, legacyHints, message);
}
async function run(specs, options, expected, message, boundary = 'factory') {
  const w = world(specs, options);
  const read = boundary === 'factory' ? runtime.createSavedStoryEvidenceReader(w.ports)
    : input => runtime.savedStoryEvidence(input, w.ports);
  exact(await read({ root: '/saved' }), expected, message);
  for (const selection of w.captures) assert.deepEqual(selection, options.fullTests ?? TESTS, message);
  if (expected.length) assert.equal(w.captures.length, 1, message);
  w.unchanged();
  return w;
}
const row = (path, status, at, extra = {}) => ({ test: path, status, at, ...extra });
const priorRows = () => TESTS.map((path, i) => row(path, 'passed', 2000 + i * 200));

// The oracle operates on authored domain symbols, not saved row labels or code:
// any sent nonpass is negative; otherwise success needs every selected test sent.
function storyOracle(statuses, current) {
  const sent = statuses.map((status, i) => ({ status, at: 4000 + i * 500 })).filter(item => item.status !== 'unsent');
  if (!sent.length) return [];
  const negative = sent.some(item => item.status !== 'passed');
  if (!negative && sent.length !== TESTS.length) return [];
  return [summary(!negative, current, Math.max(...sent.map(item => item.at)))];
}

test('FORMAL unsent: exhaustive two-test coverage, negative evidence and source identity', async t => {
  const statuses = ['unsent', 'passed', 'failed', 'unknown', 'missingreceipt'];
  let worlds = 0, executions = 0;
  for (const first of statuses) for (const second of statuses) for (const intent of ['check', 'absent'])
    for (const prior of [true, false]) for (const current of [true, false]) {
      const states = [first, second], specs = [];
      if (prior) specs.push({ rows: priorRows() });
      specs.push({ rows: states.map((status, i) => row(TESTS[i], status, status === 'unsent' ? 999999 : 4000 + i * 500, { savedState: status === 'unsent' ? 'passed' : status })) });
      const expected = [...(prior ? [summary(true, current, 2200)] : []), ...storyOracle(states, current)];
      const label = JSON.stringify({ first, second, intent, prior, current });
      for (const boundary of ['factory', 'standalone']) {
        await run(specs, { intent, current }, expected, `${label}/${boundary}`, boundary); executions++;
      }
      worlds++;
    }
  assert.equal(worlds, 200); assert.equal(executions, 400);
  t.diagnostic('Bound: all 5² statuses × 2 intents × 2 prior-pass states × 2 source states = 200 worlds, 400 public helper executions.');
});

test('FORMAL unsent: duplicate order and local timestamps cannot alter sent evidence', async t => {
  let worlds = 0;
  for (const intent of ['check', 'absent']) for (const reverse of [false, true])
    for (const unsentTime of [undefined, 999999]) for (const sent of ['passed', 'failed']) {
      const rows = [row(TESTS[0], sent, 4000), row(TESTS[1], 'passed', 4500),
        row(TESTS[0], 'unsent', unsentTime, { savedState: 'failed' })];
      if (reverse) rows.reverse();
      await run([{ rows }], { intent }, [summary(sent === 'passed', true, 4500)], JSON.stringify({ intent, reverse, unsentTime, sent })); worlds++;
    }
  assert.equal(worlds, 16);
  t.diagnostic('Bound: 16 duplicate/order/time worlds; no unsent row or lint timestamp enters result time.');
});

test('FORMAL unsent: original union retains currentness across another unsent Story and posted negatives', async t => {
  let worlds = 0;
  for (const intent of ['check', 'absent']) for (const sameStory of [true, false]) for (const sent of ['passed', 'failed', 'unknown']) {
    const expected = sameStory && sent === 'passed' ? [] : [summary(sent === 'passed', true, 4000)];
    await run([{ rows: [row(TESTS[0], sent, 4000), row(TESTS[1], 'unsent', 999999, { story: sameStory ? STORY : OTHER })] }],
      { intent }, expected, JSON.stringify({ intent, sameStory, sent })); worlds++;
  }
  assert.equal(worlds, 12);
  t.diagnostic('Bound: 12 full-union worlds, including current failed/unknown summaries plus another unsent test.');
});

test('FORMAL unsent: matching latest receipt remains necessary despite an earlier passed attempt', async t => {
  const defects = [answer => { answer.requestId = uuid(800); }, answer => { answer.id = uuid(801); },
    answer => { answer.command = 'try'; }, answer => { answer.state = 'refused'; },
    answer => { answer.result.report.samples[0].steps[0].checks[0].passed = false; }];
  let worlds = 0;
  for (const intent of ['check', 'absent']) for (const answer of defects) {
    await run([{ rows: priorRows() }, { rows: [row(TESTS[0], 'passed', 4000, { answer, priorAttempt: true }), row(TESTS[1], 'unsent', 999999)] }],
      { intent }, [summary(true, true, 2200), summary(false, true, 4000)], `invalid latest receipt/${intent}/${worlds}`); worlds++;
  }
  for (const intent of ['check', 'absent']) {
    await run([{ rows: priorRows() }, { rows: [row(TESTS[0], 'unknown', 4000, { priorAttempt: true }), row(TESTS[1], 'unsent', 999999)] }],
      { intent }, [summary(true, true, 2200), summary(false, true, 4000)], `unknown latest receipt/${intent}`); worlds++;
  }
  assert.equal(worlds, 12);
  t.diagnostic('Bound: 12 nonempty latest-attempt controls; invalid/missing/unknown receipts never become unsent.');
});

test('FORMAL unsent: shared legacy eligibility still validates every original row', async t => {
  const invalid = [r => { r.max_calls = 0; }, r => { r.max_calls = 1001; }, r => { r.criteria_total = 0; },
    r => { r.steps[0].operation = ''; }, r => { r.steps.push(clone(r.steps[0])); }, r => { r.steps[0].checks = []; }];
  for (const edit of invalid) {
    const w = world([{ rows: [row(TESTS[0], 'passed', 4000), row(TESTS[1], 'unsent', 999999, { edit })] }], { intent: 'absent' });
    exact(await runtime.createSavedStoryEvidenceReader(w.ports)({ root: '/saved' }), [], 'invalid original unsent legacy row', 1);
    assert.deepEqual(w.captures, []); w.unchanged();
  }
  t.diagnostic('Bound: six invalid legacy-row observations; an unsent row does not bypass batch eligibility.');
});

test('FORMAL unsent: capture memo retains the original full union and fresh-reader lifetime', async t => {
  for (const intent of ['check', 'absent']) {
    const w = world([{ rows: priorRows() }, { rows: [row(TESTS[1], 'unsent', 999999), row(TESTS[0], 'failed', 4000)] }], { intent });
    const reader = runtime.createSavedStoryEvidenceReader(w.ports);
    const expected = current => [summary(true, current, 2200), summary(false, current, 4000)];
    for (const reply of await Promise.all([reader({ root: '/saved' }), reader({ root: '/saved' })])) exact(reply, expected(true), intent);
    w.setCurrent(false);
    exact(await reader({ root: '/saved' }), expected(true), intent);
    assert.deepEqual(w.captures, [TESTS]);
    exact(await runtime.createSavedStoryEvidenceReader(w.ports)({ root: '/saved' }), expected(false), intent);
    assert.deepEqual(w.captures, [TESTS, TESTS]); w.unchanged();
  }
  t.diagnostic('Bound: two intent worlds, eight reads; overlap, row order, per-batch comparison and fresh-reader recapture. Total: 248 worlds, 454 helper executions.');
});
