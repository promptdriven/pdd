import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, writeFileSync, cpSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { captureSource, sha256 } from '../src/runtime-preflight.mjs';
import { fakeRuntime, portsFor, root, temp } from './runtime-fake.mjs';

// Oracle: lint-before-tests-followup.md Rules to check and the owning public
// contracts. No fixture expectations or production predicates supply decisions.
// Exhaustive finite domain: 84 selector +36 recovery +18 warning configurations.
// Additional witnesses cover stat-before-read and ordinary Check/Try isolation.
// These tests establish client behavior against canonical fake HTTP receipts,
// not live Runtime admission, arbitrary transports, or universal filesystem safety.
const schema = 'prompt-runtime.program-scenario.v1';
const candidates = ['none', 'missing-schema', 'malformed', 'wrong-schema', 'suffix', 'interface', 'oversized'];
function setup(t, withTests = false) {
  const sandbox = temp(t), repo = join(sandbox, 'repo'), home = join(sandbox, 'home');
  mkdirSync(repo); mkdirSync(home);
  const write = (path, text) => { mkdirSync(dirname(join(repo, path)), { recursive: true }); writeFileSync(join(repo, path), text); };
  if (withTests) cpSync(join(root, 'test/fixtures/harbor'), repo, { recursive: true });
  else write('user_stories/known.md', '# Known\n\n## Acceptance criteria\n\n1. I can inspect source.\n');
  const track = () => { for (const args of [['init', '-q'], ['add', '-A']]) {
    const r = spawnSync('git', args, { cwd: repo, encoding: 'utf8' }); assert.equal(r.status, 0, r.stderr);
  } };
  return { sandbox, repo, home, write, track };
}
function candidate(s, kind) {
  if (kind === 'missing-schema') s.write('tests/unfinished.json', '{}');
  if (kind === 'malformed') s.write('tests/unfinished.json', '{unfinished');
  if (kind === 'wrong-schema') s.write('tests/unfinished.json', '{"schema_version":"some.other.schema"}');
  if (kind === 'suffix') s.write('unfinished.prompt', '# Unfinished');
  if (kind === 'interface') s.write('unfinished.prompt.md', '# Unfinished');
  if (kind === 'oversized') s.write('tests/unfinished.json', JSON.stringify({ schema_version: schema, padding: 'x'.repeat(1_048_576) }));
}
const busy = () => ({ status: 429, headers: { 'retry-after': '60' }, json: {
  dispatch: 'not_started', error: { code: 'server-full', message: 'Synthetic capacity busy.', details: { retryable: true, retry_after: 60 } },
} });
async function harness(t, s) {
  let outcome = 'passed', problems = [], captures = 0, archive;
  const fake = await fakeRuntime(t, (entry, f) => {
    assert.equal(entry.method === 'POST' ? entry.command : 'lint', 'lint', 'no Check/Try dispatch');
    if (entry.method === 'POST') {
      assert.equal(entry.request.complete, true);
      assert.ok(archive, 'real source capture occurs before upload');
      assert.deepEqual(entry.tar, archive.tar);
      assert.equal(entry.request.source_sha256, sha256(archive.tar));
    }
    if (outcome === 'busy') return busy();
    const id = entry.method === 'POST' ? entry.request.requestId : entry.url.split('/').at(-1);
    const paths = archive.files.filter(file => file.path.endsWith('.prompt.md')).map(file => file.path);
    const answer = f.lint(id, paths.map(path => ({ path, state: 'draft', admission_state: 'draft', interface: { calls: [] } })));
    answer.state = outcome;
    answer.result.problems = problems;
    return { status: 200, json: answer };
  });
  async function invoke({ mode = '--lint', words = [], json = true, state = join(s.sandbox, 'state'), pending = false, forbidCapture = false, ordinary = false, tryMode = false } = {}) {
    const env = { HOME: s.home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: fake.origin };
    const p = portsFor(env, { ...(pending ? { pollMs: 60_000 } : {}), captureSource(repo, opts) {
      captures++; assert.equal(forbidCapture, false, 'saved source lint cannot capture current source');
      archive = captureSource(repo, opts); return archive;
    } });
    const before = { posts: fake.posts.length, gets: fake.gets.length, captures };
    let code, thrown;
    try { code = await (tryMode ? runTry : runCheck)({ cwd: s.repo, words: mode === '--retry' ? [] : words, options: { ...(ordinary || tryMode ? {} : { [mode]: mode === '--retry' ? words[0] : true }), ...(json ? { '--json': true } : {}), '--timeout': 1 } }, p.ports); }
    catch (error) { thrown = error; }
    assert.equal(thrown, undefined, `public invocation must return a semantic result, not throw: ${thrown?.stack}`);
    const output = p.ports.stdout.text + p.ports.stderr.text;
    const lines = p.ports.stdout.text.trim().split('\n').filter(Boolean);
    const result = json && lines.length && lines[0].startsWith('{') ? JSON.parse(lines[0]) : null;
    if (result) assert.equal(lines.length, 1, 'exactly one JSON object');
    return { code, result, output, stdout: p.ports.stdout.text, p, state, posts: fake.posts.slice(before.posts), gets: fake.gets.slice(before.gets), captures: captures - before.captures };
  }
  return { fake, invoke, set(value, diagnostics = []) { outcome = value; problems = diagnostics; } };
}
function sourceResult(r, expectedState, expectedExit) {
  assert.equal(r.code, expectedExit, r.output);
  if (r.result) {
    assert.equal(r.result.exit_code, expectedExit);
    assert.equal(r.result.lint_state, expectedState);
    assert.deepEqual(r.result.rows, []);
  } else assert.match(r.output, new RegExp(expectedState.replace('_', '[ _]'), 'i'));
  for (const phrase of ['No tests yet', '0 AI calls', 'No checks were sent']) assert.ok(r.output.includes(phrase), phrase);
}
test('SOURCE-LINT followup formal: exhaustive 84 candidate/test/operand/plan selections', async t => {
  let count = 0;
  for (const hint of candidates) for (const tests of [false, true]) for (const operand of ['none', 'known', 'missing']) for (const plan of [false, true]) {
    const s = setup(t, tests); if (plan) s.write('product/plan.md', '# Synthetic plan\n'); candidate(s, hint); s.track();
    const h = await harness(t, s);
    const words = operand === 'none' ? [] : [operand === 'known' ? tests ? 'place-order' : 'known' : 'missing-story'];
    const r = await h.invoke({ words });
    const permitted = tests ? operand !== 'missing' : operand === 'none' && hint === 'none' && plan;
    assert.equal(r.code, permitted ? 0 : 2, `${hint}/${tests}/${operand}/${plan}\n${r.output}`);
    if (!permitted) { assert.equal(r.captures, 0); assert.equal(r.p.clock.gh.length, 0); assert.equal(r.posts.length, 0); }
    else { assert.equal(r.posts.length, 1); if (!tests) sourceResult(r, 'passed', 0); }
    count++;
  }
  assert.equal(count, 84);
});

test('SOURCE-LINT followup formal: independent read/retry outcomes over 36 configurations', async t => {
  let count = 0;
  const cases = [
    ['cached-passed', 'passed', 'passed', 0], ['cached-refused', 'refused', 'refused', 4], ['cached-busy', 'busy', 'not_run', 5],
    ['refresh-passed', 'queued', 'passed', 0], ['refresh-refused', 'queued', 'refused', 4], ['refresh-unknown', 'queued', 'unknown', 3],
    ['refresh-queued', 'queued', 'queued', 3], ['refresh-running', 'queued', 'running', 3], ['refresh-busy', 'queued', 'unknown', 3],
  ];
  for (const [name, initial, finalState, exit] of cases) for (const mode of ['--read', '--retry']) for (const json of [false, true]) {
    const s = setup(t); s.write('product/plan.md', '# Synthetic plan\n'); s.track();
    const h = await harness(t, s); h.set(initial);
    const producer = await h.invoke({ pending: true });
    sourceResult(producer, initial === 'busy' ? 'not_run' : initial, initial === 'busy' ? 5 : initial === 'refused' ? 4 : initial === 'passed' ? 0 : 3);
    assert.ok(producer.posts.length > 0, 'producer uses real public lint POST');
    const originalId = producer.posts.at(-1).request.requestId;
    h.set(name === 'refresh-busy' ? 'busy' : finalState);
    const r = await h.invoke({ mode, words: [producer.result.batch], json, state: producer.state, forbidCapture: true });
    sourceResult(r, finalState, exit);
    assert.equal(r.posts.length, 0); assert.equal(r.p.clock.uuids, 0); assert.equal(r.captures, 0);
    assert.ok(r.gets.every(entry => entry.url.endsWith(`/${originalId}`)), 'only original lint ID may be read');
    assert.equal(r.gets.length > 0, name.startsWith('refresh-'), 'refresh only when needed');
    if (mode === '--retry') {
      assert.match(r.output, /nothing to retry/i);
      assert.doesNotMatch(r.output, /warning[^\n]*nothing to retry/i);
      if (r.result) assert.ok(!r.result.warnings.some(w => /nothing to retry/i.test(JSON.stringify(w))));
    }
    count++;
  }
  assert.equal(count, 36);
});

test('SOURCE-LINT followup formal: all 18 warning count and text/JSON combinations', async t => {
  let count = 0;
  for (const context of [0, 1, 2]) for (const server of [0, 1, 2]) for (const json of [false, true]) {
    const s = setup(t); // Remove the helper's unmatched Story from the public file inventory.
    s.write('user_stories/known.md', '# Navigation only\n');
    s.write('product/plan.md', '# Synthetic plan\n');
    for (let n = 0; n < context; n++) s.write(`user_stories/warning-${n}.md`, `# Warning ${n}\n\n## Acceptance criteria\n\n1. I can inspect source.\n`);
    s.track(); const h = await harness(t, s);
    const diagnostics = Array.from({ length: server }, (_, n) => ({ code: `synthetic-warning-${n}`, file: `contracts/warning-${n}.md`, section: '/synthetic', severity: 'warning', reason: `Synthetic warning ${n}.` }));
    h.set('passed', diagnostics); const r = await h.invoke({ json }); sourceResult(r, 'passed', 0);
    const expected = context + server;
    if (expected) assert.ok(r.output.includes(`Source lint passed with ${expected} warning`), r.output);
    if (json) {
      assert.equal(r.result.warnings.length, context);
      assert.equal(r.result.problems.filter(p => p.severity === 'warning').length, server);
    } else {
      for (let n = 0; n < context; n++) assert.ok(r.output.includes(`user_stories/warning-${n}.md`));
      for (let n = 0; n < server; n++) assert.ok(r.output.includes(`synthetic-warning-${n}`));
      const last = r.stdout.trim().split('\n').at(-1);
      assert.ok(last.includes('Source lint passed'), 'summary is final stdout line');
    }
    count++;
  }
  assert.equal(count, 18);
});

test('SOURCE-LINT followup formal: calibrated public oversized hint never reads content', t => {
  const s = setup(t); candidate(s, 'oversized'); s.track();
  const moduleURL = new URL('../src/runtime-preflight.mjs', import.meta.url).href;
  const program = `import fs from 'node:fs'; import {syncBuiltinESMExports} from 'node:module'; import assert from 'node:assert/strict';
const path=${JSON.stringify(join(s.repo, 'tests/unfinished.json'))}; let reads=0; const original=fs.readFileSync;
fs.readFileSync=function(file,...args){if(String(file)===path) reads++; return original.call(this,file,...args)};
syncBuiltinESMExports(); fs.readFileSync(path); assert.equal(reads,1,'spy calibration'); reads=0;
const {whyNoTests}=await import(${JSON.stringify(moduleURL)});
const hints=whyNoTests(${JSON.stringify(s.repo)},new Set(['tests/unfinished.json']));
assert.equal(reads,0,'oversized JSON must be statted and hinted without read');
assert.ok(hints.some(text=>text.includes('tests/unfinished.json') && /limit|MiB|MB|1048576|1,048,576/i.test(text)),'finite oversized hint');
console.log('calibrated oversized no-read witness passed');`;
  const r = spawnSync(process.execPath, ['--input-type=module', '-e', program], { encoding: 'utf8' });
  assert.equal(r.status, 0, r.stdout + r.stderr);
});

test('SOURCE-LINT followup formal: ordinary Check and Try still require tests', async t => {
  for (const tryMode of [false, true]) {
    const s = setup(t); s.write('product/plan.md', '# Synthetic plan\n'); s.track(); const h = await harness(t, s);
    const r = await h.invoke({ ordinary: true, tryMode, json: false });
    assert.equal(r.code, 2, r.output); assert.equal(r.posts.length, 0); assert.equal(r.captures, 0); assert.equal(r.p.clock.gh.length, 0);
  }
});
