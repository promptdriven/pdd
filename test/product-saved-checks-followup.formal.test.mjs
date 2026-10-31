import test from 'node:test';
import assert from 'node:assert/strict';

// Independent bounded oracle: product-saved-checks-followup.md, Rules to check,
// and runtime-client.prompt.md, Saved Check row validity / local evidence rules.
// Only raw directory/file observations and capture hashes are injected. No
// precomputed evidence, product decision, Runtime, authentication or dispatch.
// An alternate module permits a private semantic control without editing code.
const runtime = await import(process.env.PDD_FOLLOWUP_FORMAL_MODULE
  ?? new URL('../src/runtime-client.mjs', import.meta.url).href);
const A = 'a'.repeat(64), B = 'b'.repeat(64);
const clone = value => structuredClone(value);
const own = (value, key) => Object.prototype.hasOwnProperty.call(value, key);
const canonical = path => ({ '/base-alias': '/base', '/other-alias': '/other' })[path] ?? path;
const forbidden = name => () => assert.fail(`Evidence read caused forbidden effect: ${name}`);
const hint = text => ['older checks', 'not counted', 'pdd test'].every(part => text.toLowerCase().includes(part));

function authoredRow(story, selectedTest, id) {
  return { story, test: selectedTest, request_ids: [id], state: 'passed', ended_at: 2000,
    max_calls: 18, criteria_total: 2, criterion_texts: { AC1: 'Synthetic first.', AC2: 'Synthetic second.' },
    steps: [{ step_id: 'observe', entry_path: 'prompts/example.prompt.md', operation: 'observe',
      checks: ['AC1', 'AC2'].map(criterion_id => ({ criterion_id, target: 'result', path: '/ok', op: 'equals', value: true })) }] };
}

function receipt(id) {
  return { requestId: id, id, command: 'check', state: 'passed', usage: { calls: 1 }, result: { report: {
    criterion_results: ['AC1', 'AC2'].map(criterion_id => ({ criterion_id, status: 'passed' })),
    samples: [{ sample: 1, steps: [{ step_id: 'observe', result: { ok: true },
      checks: ['AC1', 'AC2'].map(criterion_id => ({ criterion_id, target: 'result', path: '/ok', op: 'equals',
        expected: true, actual: true, passed: true })) }] }],
  } } };
}

function world(specs) {
  const records = [], files = new Map(), captures = [];
  let serial = 0, failCapture = false, generation = 0;
  for (const [index, spec] of specs.entries()) {
    const name = `20261030-120000-${index.toString(36).padStart(4, '0')}`;
    const batch = { version: 1, batch: name, root: spec.root ?? '/saved', intent: 'check',
      created_at: '1970-01-01T00:00:01.000Z', source_sha256: spec.sha ?? A, rows: [] };
    if (own(spec, 'intent')) {
      if (spec.intent === undefined) delete batch.intent;
      else batch.intent = spec.intent;
    }
    for (const [rowIndex, selectedTest] of (spec.tests ?? ['test/one.json']).entries()) {
      const id = `11111111-1111-4111-8111-${String(++serial).padStart(12, '0')}`;
      const row = authoredRow(`user_stories/${name}.md`, selectedTest, id), answer = receipt(id);
      spec.row?.(row, rowIndex);
      spec.answer?.(answer, rowIndex);
      batch.rows.push(row);
      files.set(`/state/batches/${name}/${id}.json`, JSON.stringify(answer));
    }
    records.push(batch);
    files.set(`/state/batches/${name}/batch.json`, JSON.stringify(batch));
  }
  const initial = JSON.stringify([...files]);
  const ports = {
    env: { PDD_STATE_DIR: '/state' }, realpath: canonical,
    readDir: path => { assert.equal(path, '/state/batches'); return records.map(record => record.batch).reverse(); },
    readFile: path => { assert.ok(files.has(path), `Unexpected saved-file read: ${path}`); return files.get(path); },
    captureSource: async (root, selection) => {
      captures.push({ root: canonical(root), ...clone(selection) });
      if (failCapture) throw Object.assign(Error('synthetic capture denied'), { code: 'EACCES' });
      const firstGenerationSha = canonical(root) === '/other' ? B : A;
      return { sha256: generation % 2 ? (firstGenerationSha === A ? B : A) : firstGenerationSha };
    },
    fetch: forbidden('fetch'), gh: forbidden('gh'), writeFile: forbidden('writeFile'),
    mkdir: forbidden('mkdir'), startRun: forbidden('workflow.start'),
  };
  return { records, ports, captures,
    factory: () => runtime.createSavedStoryEvidenceReader?.(ports)
      ?? (input => runtime.savedStoryEvidence(input, ports)),
    failure(value) { failCapture = value; }, edit() { generation++; },
    unchanged() { assert.equal(JSON.stringify([...files]), initial); },
  };
}

function expectedStories(w, root, currentSha, pass = true) {
  return w.records.filter(record => record.root === root).map(record => ({
    story: `user_stories/${record.batch}.md`, pass, current: currentSha === record.source_sha256,
    result: pass ? '✓' : 'no verdict', at: 2000,
  }));
}

function exactReply(reply, stories, legacyHints = 0) {
  assert.deepEqual(Object.keys(reply).sort(), ['stories', 'warnings']);
  assert.deepEqual(reply.stories, stories);
  assert.ok(Array.isArray(reply.warnings));
  assert.equal(new Set(reply.warnings).size, reply.warnings.length);
  for (const warning of reply.warnings) assert.ok(typeof warning === 'string' && warning.length > 0 && warning.length < 2000);
  assert.deepEqual(reply.warnings.map(text => hint(text) ? 'legacy' : text), Array(legacyHints).fill('legacy'));
}

// Six symbols deliberately contain equal keys represented by different roots,
// aliases and row order, as well as unequal folder/test-set keys.
const symbols = [
  { root: '/saved-ab', comparisonRoot: '/base', tests: ['test/b.json', 'test/a.json', 'test/a.json'] },
  { root: '/saved-ba', comparisonRoot: '/base-alias', tests: ['test/a.json', 'test/b.json'] },
  { root: '/saved-a', comparisonRoot: '/base', tests: ['test/a.json'] },
  { root: '/saved-b', comparisonRoot: '/base', tests: ['test/b.json'] },
  { root: '/saved-ab', comparisonRoot: '/other', tests: ['test/b.json', 'test/a.json', 'test/a.json'] },
  { root: '/saved-other-ab', comparisonRoot: '/other-alias', tests: ['test/a.json', 'test/b.json'] },
];
const key = symbol => JSON.stringify([canonical(symbol.comparisonRoot), [...new Set(symbol.tests)].sort()]);
const captureObservation = symbol => ({ root: canonical(symbol.comparisonRoot), tests: [...new Set(symbol.tests)].sort(), appMap: null });
function* sequences(prefix = []) {
  if (prefix.length) yield prefix;
  if (prefix.length < 3) for (let next = 0; next < symbols.length; next++) yield* sequences([...prefix, next]);
}
function keyWorld() {
  const roots = [...new Map(symbols.map(symbol => [symbol.root, symbol.tests]))];
  return world(roots.flatMap(([root, tests]) => [A, B].map(sha => ({ root, tests, sha }))));
}

test('FORMAL followup source-key sequences exhaust lengths 1..3 over six symbols', async t => {
  let worlds = 0, reads = 0;
  for (const sequence of sequences()) {
    const w = keyWorld(), reader = w.factory(), seen = new Map();
    for (const index of sequence) {
      const symbol = symbols[index], { root, comparisonRoot } = symbol;
      const reply = await reader({ root, comparisonRoot });
      const sha = canonical(comparisonRoot) === '/other' ? B : A;
      exactReply(reply, expectedStories(w, root, sha));
      if (!seen.has(key(symbol))) seen.set(key(symbol), captureObservation(symbol));
      assert.deepEqual(w.captures, [...seen.values()], `sequence ${sequence}; each key captures once`);
      w.unchanged();
      reads++;
    }
    // Editing the capture input cannot affect a reader's already observed key;
    // a fresh command must recapture even when inputs and saved records match.
    w.edit();
    const symbol = symbols[sequence.at(-1)], { root, comparisonRoot } = symbol;
    exactReply(await reader({ root, comparisonRoot }), expectedStories(w, root, canonical(comparisonRoot) === '/other' ? B : A));
    assert.deepEqual(w.captures, [...seen.values()]);
    exactReply(await w.factory()({ root, comparisonRoot }), expectedStories(w, root, canonical(comparisonRoot) === '/other' ? A : B));
    assert.deepEqual(w.captures, [...seen.values(), captureObservation(symbol)]);
    w.unchanged();
    worlds++;
  }
  assert.equal(worlds, 258); assert.equal(reads, 726);
  t.diagnostic('Bound: all 258 sequences; 726 initial reads + 258 same-scope reads + 258 fresh-scope reads. Two distinct saved SHAs per read.');
});

const ceilings = [
  { name: 'one', value: 1, valid: true }, { name: 'maximum', value: 1000, valid: true },
  { name: 'missing', value: undefined, valid: false }, { name: 'negative', value: -1, valid: false },
  { name: 'zero', value: 0, valid: false }, { name: 'above', value: 1001, valid: false },
  { name: 'fraction', value: 1.5, valid: false }, { name: 'null', value: null, valid: false },
];
const intents = [undefined, 'check', 'lint-only', 'try', 'other', null];
test('FORMAL followup legacy intent, ceiling, text metadata and receipt coverage matrix', async t => {
  let worlds = 0;
  for (const ceiling of ceilings) for (const intent of intents) for (const texts of [true, false]) for (const coverage of [true, false]) {
    const w = world([{ intent, row: row => {
      if (ceiling.value === undefined) delete row.max_calls; else row.max_calls = ceiling.value;
      if (!texts) delete row.criterion_texts;
    }, answer: answer => { if (!coverage) answer.result.report.criterion_results = []; } }]);
    const eligible = intent === 'check' || intent === undefined && ceiling.valid;
    const pass = eligible && coverage && (intent === undefined || texts);
    const hints = intent === undefined && (!ceiling.valid || !coverage) ? 1 : 0;
    exactReply(await w.factory()({ root: '/saved' }), eligible ? expectedStories(w, '/saved', A, pass) : [], hints);
    assert.deepEqual(w.captures, eligible ? [{ root: '/saved', tests: ['test/one.json'], appMap: null }] : []);
    w.unchanged(); worlds++;
  }
  assert.equal(worlds, 192);
  t.diagnostic('Bound: 8 ceilings x 6 intents x 2 text-presence states x 2 receipt-coverage states = 192 worlds.');
});

// Each named mutation has its required validity fixed independently of the
// implementation. Mutate only the second row: legacy eligibility requires ALL
// rows, whereas complete failed receipts remain evidence of failure.
const rowMutations = [
  ['string ceiling', row => { row.max_calls = '18'; }],
  ['missing count', row => { delete row.criteria_total; }],
  ['zero count', row => { row.criteria_total = 0; }],
  ['fraction count', row => { row.criteria_total = 1.5; }],
  ['wrong distinct count', row => { row.criteria_total = 1; }],
  ['missing steps', row => { delete row.steps; }],
  ['empty steps', row => { row.steps = []; }],
  ['null step', row => { row.steps = [null]; }],
  ['missing step id', row => { delete row.steps[0].step_id; }],
  ['blank step id', row => { row.steps[0].step_id = ' '; }],
  ['numeric step id', row => { row.steps[0].step_id = 1; }],
  ['duplicate step id', row => { row.steps.push(clone(row.steps[0])); }],
  ['missing entry', row => { delete row.steps[0].entry_path; }],
  ['blank entry', row => { row.steps[0].entry_path = '\t'; }],
  ['missing operation', row => { delete row.steps[0].operation; }],
  ['blank operation', row => { row.steps[0].operation = ' '; }],
  ['null operation', row => { row.steps[0].operation = null; }],
  ['missing checks', row => { delete row.steps[0].checks; }],
  ['empty checks', row => { row.steps[0].checks = []; }],
  ['null check', row => { row.steps[0].checks = [null]; }],
  ['missing criterion id', row => { delete row.steps[0].checks[0].criterion_id; }],
  ['blank criterion id', row => { row.steps[0].checks[0].criterion_id = ' '; }],
  ['null criterion id', row => { row.steps[0].checks[0].criterion_id = null; }],
  ['duplicate criterion leaves incomplete set', row => { row.steps[0].checks[1].criterion_id = 'AC1'; }],
];
test('FORMAL followup all-row validity and complete terminal receipt guards', async t => {
  for (const [name, mutate] of rowMutations) {
    // Two invalid legacy batches must still produce a single hint.
    const w = world(Array.from({ length: 2 }, () => ({ intent: undefined, tests: ['test/one.json', 'test/two.json'],
      row: (row, index) => { if (index === 1) mutate(row); } })));
    exactReply(await w.factory()({ root: '/saved' }), [], 1);
    assert.deepEqual(w.captures, [], name); w.unchanged();
  }
  const receiptStates = [
    ['complete failed', answer => { answer.state = 'failed'; for (const item of answer.result.report.criterion_results) item.status = 'failed';
      for (const check of answer.result.report.samples[0].steps[0].checks) check.passed = false; }, false, 0],
    ['wrong command', answer => { answer.command = 'try'; }, false, 0],
    ['wrong receipt id', answer => { answer.id = '33333333-3333-4333-8333-333333333333'; }, false, 0],
    ['partial criteria', answer => { answer.result.report.criterion_results.pop(); }, false, 1],
    ['foreign criterion', answer => { answer.result.report.criterion_results[1].criterion_id = 'AC3'; }, false, 1],
    ['one failed selected check', answer => { answer.result.report.samples[0].steps[0].checks[1].passed = false; }, false, 0],
  ];
  for (const [name, mutate, pass, hints] of receiptStates) {
    const w = world([{ intent: undefined, row: row => { delete row.criterion_texts; }, answer: mutate }]);
    exactReply(await w.factory()({ root: '/saved' }), expectedStories(w, '/saved', A, pass), hints);
    assert.equal(w.captures.length, 1, name); w.unchanged();
  }
  t.diagnostic(`Bound: ${rowMutations.length} invalid second-row worlds (two batches each), plus ${receiptStates.length} terminal receipt worlds.`);
});

test('FORMAL followup failed capture scopes and standalone scopes', async t => {
  for (const symbol of symbols) {
    const w = keyWorld(), reader = w.factory(), { root, comparisonRoot } = symbol;
    w.failure(true);
    for (let attempt = 0; attempt < 2; attempt++) {
      const reply = await reader({ root, comparisonRoot });
      assert.deepEqual(Object.keys(reply).sort(), ['stories', 'warnings']);
      assert.deepEqual(reply.stories, expectedStories(w, root, null));
      assert.ok(reply.warnings.length > 0);
      assert.equal(new Set(reply.warnings).size, reply.warnings.length);
      for (const warning of reply.warnings) assert.ok(typeof warning === 'string' && warning.length > 0 && warning.length < 2000);
      assert.deepEqual(w.captures, [captureObservation(symbol)]);
    }
    w.failure(false);
    exactReply(await w.factory()({ root, comparisonRoot }), expectedStories(w, root, canonical(comparisonRoot) === '/other' ? B : A));
    assert.deepEqual(w.captures, [captureObservation(symbol), captureObservation(symbol)]); w.unchanged();
  }
  const w = world([{}]);
  exactReply(await runtime.savedStoryEvidence({ root: '/saved' }, w.ports), expectedStories(w, '/saved', A));
  w.edit();
  exactReply(await runtime.savedStoryEvidence({ root: '/saved' }, w.ports), expectedStories(w, '/saved', B));
  assert.deepEqual(w.captures, Array.from({ length: 2 }, () => ({ root: '/saved', tests: ['test/one.json'], appMap: null })));
  const noComparison = world([{ intent: undefined }]);
  exactReply(await noComparison.factory()({ root: '/saved', comparisonRoot: null }), expectedStories(noComparison, '/saved', null));
  assert.deepEqual(noComparison.captures, []); noComparison.unchanged(); w.unchanged();
  t.diagnostic('Bound: six failed/retried keys, one two-call standalone scope, one null-comparison legacy scope. Total finite worlds in this file: 488.');
});
