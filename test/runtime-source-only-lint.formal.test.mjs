import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { captureSource, sha256 } from '../src/runtime-preflight.mjs';
import { fakeRuntime, portsFor, root, temp } from './runtime-fake.mjs';

// Independent bounded oracle for lint-before-tests.md, Rules to check. The
// fixture supplies authored input bytes only; no expected fixture value or
// production decision helper supplies this oracle. Every invocation executes
// public runCheck, ordinary real capture and canonical fake Runtime receipts.
// Scope: client acceptance of the finite receipt domain below, source-selector
// guards, and saved lint reads. This does not prove real-server source admission,
// arbitrary receipts, capture safety for all paths, or universal privacy.
const fixtures = JSON.parse(readFileSync(new URL('./fixtures/source-only-lint-cases.json', import.meta.url))).fixture_sources;
const promptPath = 'echo.prompt.md';
const accepted = new Set(['approved', 'draft']);
const domain = {
  state: ['passed', 'failed', 'refused', 'unknown'],
  program: [true, false],
  severity: ['none', 'warning', 'error'],
  admission: ['approved', 'draft', 'refused', 'missing'],
};
const sourcePass = facts => facts.unqualified && facts.eligible && facts.matches &&
  facts.state === 'passed' && facts.program && !facts.globalRefusal &&
  facts.severity !== 'error' && facts.admissions.every(value => accepted.has(value));

function fixture(t, name = 'loose-prompt') {
  const sandbox = temp(t), repo = join(sandbox, 'repo'), home = join(sandbox, 'home');
  mkdirSync(repo); mkdirSync(home);
  const write = (path, bytes) => {
    mkdirSync(dirname(join(repo, path)), { recursive: true });
    writeFileSync(join(repo, path), bytes);
  };
  const recipe = fixtures[name];
  for (const path of recipe.include ?? []) write(path, readFileSync(join(root, recipe.copy_public_tree, path)));
  for (const [path, bytes] of Object.entries(recipe.files ?? {})) write(path, bytes);
  for (const args of [['init', '-q'], ['add', '-A']]) {
    const result = spawnSync('git', args, { cwd: repo, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
    assert.equal(result.status, 0, result.stderr);
  }
  return { sandbox, repo, home, write };
}

function receipt(fake, id, facts, paths = [promptPath]) {
  const prompts = facts.admissions.flatMap((admission, index) => admission === 'missing' ? [] : [{
    path: paths[index], state: admission, admission_state: admission, interface: { calls: [] },
  }]);
  const answer = fake.lint(id, prompts);
  answer.state = facts.state;
  if (!facts.program) delete answer.result.report.program;
  if (facts.severity !== 'none') answer.result.problems = [{
    code: 'synthetic-global-diagnostic', file: 'docs/rules.md', section: '/synthetic',
    severity: facts.severity, reason: 'Synthetic receipt evidence.',
  }];
  if (facts.globalRefusal) answer.result.refusals = [{ code: 'synthetic-global-refusal', message: 'Synthetic refusal.' }];
  if (!facts.matches) answer.requestId = answer.id = '00000000-0000-4000-8000-000000000000';
  return answer;
}

const valid = overrides => ({ unqualified: true, eligible: true, matches: true,
  state: 'passed', program: true, severity: 'none', admissions: ['draft'], ...overrides });

async function harness(t, setup) {
  let current, capture, selection, serial = 0;
  const fake = await fakeRuntime(t, (entry, server) => {
    assert.ok(entry.method === 'POST' || entry.method === 'GET');
    if (entry.method === 'POST') {
      assert.equal(entry.command, 'lint', 'source lint never dispatches a Check or Try');
      assert.equal(entry.request.complete, true);
      assert.ok(capture, 'ordinary source capture precedes upload');
      assert.deepEqual(entry.tar, capture.tar);
      assert.equal(entry.request.source_sha256, sha256(capture.tar));
    }
    const id = entry.method === 'POST' ? entry.request.requestId : entry.url.split('/').at(-1);
    return { status: 200, json: receipt(server, id, current, current.paths) };
  });
  async function invoke(facts, { words = [], options = { '--lint': true, '--json': true }, state, ports = {} } = {}) {
    current = facts; capture = undefined; selection = undefined;
    const env = { HOME: setup.home, PDD_STATE_DIR: state ?? join(setup.sandbox, `state-${++serial}`), PDD_RUNTIME_URL: fake.origin };
    const p = portsFor(env, { captureSource(repo, options) {
      selection = options; capture = captureSource(repo, options); return capture;
    }, ...ports });
    const postsBefore = fake.posts.length;
    const code = await runCheck({ cwd: setup.repo, words, options }, p.ports);
    return { code, p, state: env.PDD_STATE_DIR, posts: fake.posts.slice(postsBefore), capture, selection,
      json: p.ports.stdout.text.trim().startsWith('{') ? JSON.parse(p.ports.stdout.text) : null,
      output: p.ports.stdout.text + p.ports.stderr.text };
  }
  return { fake, invoke };
}

function assertSourceJudgment(result, facts, label) {
  // Lead with a semantic exit-code assertion: old No-tests rejection must fail
  // here (2 versus 0), not through a new capture API, JSON parse or missing field.
  if (sourcePass(facts)) assert.equal(result.code, 0, `${label}: confirmed eligible source must pass\n${result.output}`);
  else assert.notEqual(result.code, 0, `${label}: incomplete/refused evidence cannot pass\n${result.output}`);
  assert.ok(result.json, `${label}: source lint publishes JSON`);
  assert.deepEqual(result.json.rows, [], `${label}: source lint has no fabricated Story rows`);
  assert.equal(result.json.exit_code, result.code, label);
  assert.equal(result.json.lint_state === 'passed', sourcePass(facts), label);
  if (sourcePass(facts)) for (const phrase of ['No tests yet', '0 AI calls', 'No checks were sent']) {
    assert.ok(result.json.summary_line.includes(phrase), `${label}: ${phrase}`);
  }
  if (result.capture) {
    assert.deepEqual(result.selection.tests, [], label);
    assert.equal(result.selection.appMap, null, label);
    assert.ok(Array.isArray(result.selection.sourceFiles), label);
  }
}

test('SOURCE-LINT formal positive control: confirmed six-file plan passes through public runCheck', async t => {
  const setup = fixture(t, 'coffee-plan'), { invoke } = await harness(t, setup);
  const facts = valid({ admissions: [] });
  const result = await invoke(facts);
  assertSourceJudgment(result, facts, 'plan-only witness');
  assert.equal(result.posts.length, 1);
  assert.deepEqual(result.capture.files.map(file => file.path).sort(), [...fixtures['coffee-plan'].include].sort());
});

test('SOURCE-LINT bounded proof: all 96 terminal/report/diagnostic/admission combinations', async t => {
  const setup = fixture(t), { invoke } = await harness(t, setup);
  let configurations = 0, successes = 0;
  for (const state of domain.state) for (const program of domain.program)
  for (const severity of domain.severity) for (const admission of domain.admission) {
    const facts = valid({ state, program, severity, admissions: [admission] });
    const result = await invoke(facts);
    assertSourceJudgment(result, facts, `${state}/${program}/${severity}/${admission}`);
    assert.equal(result.posts.length, 1, 'exactly one lint upload');
    configurations++;
    if (sourcePass(facts)) successes++;
  }
  assert.equal(configurations, 96);
  assert.equal(successes, 4, 'both accepted admissions pass with absent or warning-only diagnostics');
  t.diagnostic('96 Cartesian client decisions; 4 positive and 92 nonzero outcomes required');
});

test('SOURCE-LINT bounded controls: identity, global refusal and every selected prompt admission', async t => {
  const setup = fixture(t);
  setup.write('second.prompt.md', fixtures['loose-prompt'].files[promptPath]);
  const { invoke } = await harness(t, setup);
  const paths = [promptPath, 'second.prompt.md'];
  const controls = [
    valid({ paths, admissions: ['approved', 'draft'] }),
    valid({ paths, admissions: ['refused', 'draft'] }),
    valid({ paths, admissions: ['draft', 'refused'] }),
    valid({ paths, admissions: ['draft', 'missing'] }),
    valid({ paths, admissions: ['draft', 'draft'], globalRefusal: true }),
    valid({ paths, admissions: ['draft', 'draft'], matches: false }),
  ];
  for (const [index, facts] of controls.entries()) {
    assertSourceJudgment(await invoke(facts), facts, `control ${index}`);
  }
});

test('SOURCE-LINT bounded selector guards: all four qualification/eligible-source combinations', async t => {
  let configurations = 0;
  for (const unqualified of [true, false]) for (const eligible of [true, false]) {
    const setup = fixture(t, eligible ? 'coffee-plan' : 'unrelated');
    const { invoke } = await harness(t, setup), facts = valid({ unqualified, eligible, admissions: [] });
    const result = await invoke(facts, { words: unqualified ? [] : ['missing-story'] });
    if (sourcePass(facts)) assertSourceJudgment(result, facts, 'eligible unqualified source');
    else {
      assert.equal(result.code, 2, result.output);
      assert.equal(result.posts.length, 0, 'selector rejection precedes upload');
      assert.equal(result.p.clock.gh.length, 0, 'selector rejection precedes authentication');
    }
    configurations++;
  }
  assert.equal(configurations, 4);
});

test('SOURCE-LINT bounded saved reads: queued/running crossed with passed/refused/unknown outcomes', async t => {
  const setup = fixture(t), { fake, invoke } = await harness(t, setup);
  let configurations = 0;
  for (const pending of ['queued', 'running']) for (const state of ['passed', 'refused', 'unknown']) {
    const initialFacts = valid({ state: pending });
    // Give real HTTP time to confirm pending; only then expire the fake wait budget.
    const initial = await invoke(initialFacts, {
      options: { '--lint': true, '--json': true, '--timeout': 1 }, ports: { pollMs: 60_000 },
    });
    assert.equal(initial.code, 3, initial.output);
    assert.deepEqual(initial.json.rows, []);
    assert.equal(initial.json.lint_state, pending);
    assert.ok(initial.output.includes(`pdd check --read ${initial.json.batch}`));
    const getCount = fake.gets.length;
    const facts = valid({ state });
    const result = await invoke(facts, { words: [initial.json.batch],
      options: { '--read': true, '--json': true }, state: initial.state });
    assertSourceJudgment(result, facts, `${pending} saved read to ${state}`);
    assert.equal(result.posts.length, 0, 'saved lint reads never dispatch');
    assert.equal(result.p.clock.uuids, 0, 'saved lint reads allocate no work identity');
    assert.ok(fake.gets.length > getCount, 'saved outcome was obtained');
    assert.ok(fake.gets.slice(getCount).every(entry => entry.url.endsWith(`/${initial.posts[0].request.requestId}`)),
      'all reads retain the original lint identity');
    configurations++;
  }
  assert.equal(configurations, 6);
});
