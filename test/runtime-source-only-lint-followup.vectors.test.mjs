import test from 'node:test';
import assert from 'node:assert/strict';
import fs, { cpSync, mkdirSync, readFileSync, readdirSync, existsSync, rmSync, writeFileSync } from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
import { spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { captureSource, gitFiles, whyNoTests } from '../src/runtime-preflight.mjs';
import { fakeRuntime, portsFor, root, temp } from './runtime-fake.mjs';

// Synthetic native descriptors are never sent as Runtime protocol fields.
const spec = JSON.parse(readFileSync(new URL('./fixtures/source-only-lint-followup.json', import.meta.url)));
const own = (o, k) => Object.hasOwn(o, k);
const write = (repo, path, bytes) => { mkdirSync(dirname(join(repo, path)), { recursive: true }); writeFileSync(join(repo, path), bytes); };
const contains = (text, fragments) => { for (const f of fragments) assert.ok(text.toLowerCase().includes(f.toLowerCase()), `Missing ${JSON.stringify(f)} in ${text}`); };
function git(repo, ...args) { const r = spawnSync('git', args, { cwd: repo, encoding: 'utf8' }); assert.equal(r.status, 0, r.stderr); return r.stdout; }
function setup(t, input) {
  const dir = temp(t), repo = join(dir, 'repo'), home = join(dir, 'home'), state = join(dir, 'state');
  mkdirSync(repo); mkdirSync(home);
  if (input.control_reference?.fixture === 'test/fixtures/harbor') cpSync(join(root, input.control_reference.fixture), repo, { recursive: true });
  const recipe = spec.fixture_sources[input.fixture] ?? {};
  const files = { ...recipe.files, ...input.files, ...input.extra_files };
  if (!Object.keys(files).length && !input.control_reference && !['empty', 'unrelated-only'].includes(input.fixture)) files['product/plan.md'] = '# Synthetic plan\n';
  if (input.fixture === 'unrelated-only') files['data/notes.json'] = '{}';
  for (const [path, bytes] of Object.entries(files)) write(repo, path, bytes);
  if (input.generated_file) { const g = input.generated_file; write(repo, g.path, g.prefix + g.pad_byte.repeat(g.bytes - Buffer.byteLength(g.prefix + g.suffix)) + g.suffix); }
  git(repo, 'init', '-q'); git(repo, 'add', '-A');
  git(repo, '-c', 'user.name=Native test', '-c', 'user.email=native@example.invalid', 'commit', '--allow-empty', '-qm', 'synthetic');
  return { dir, repo, home, state, recipe };
}
function parse(ports, code) {
  const stdout = ports.stdout.text, stderr = ports.stderr.text;
  let json; try { json = JSON.parse(stdout); } catch { /* Text mode has no JSON result. */ }
  return { code, stdout, stderr, text: stdout + stderr, json };
}
function batchPath(s, batch) { return join(s.state, 'batches', batch, 'batch.json'); }
function readJson(path) { return JSON.parse(readFileSync(path)); }
function setJson(path, value) { writeFileSync(path, JSON.stringify(value)); }
function posts(fake, command) { return fake.posts.filter(p => !command || p.command === command).length; }

async function exercise(t, vector) {
  const input = vector.input, expected = vector.expected, checked = new Set();
  const check = (key, actual) => { if (own(expected, key)) { assert.deepEqual(actual, expected[key], `${vector.id}: ${key}`); checked.add(key); } };
  const fragments = (key, actual) => { if (own(expected, key)) { contains(actual, expected[key]); checked.add(key); } };
  if (input.boundary === 'actual CLI') {
    const result = spawnSync(process.execPath, [join(root, 'bin/pdd.mjs'), ...input.argv], { encoding: 'utf8' });
    assert.equal(result.status, 0, result.stderr);
    const text = result.stdout.toLowerCase();
    for (const fact of expected.semantic_facts) {
      if (fact.includes('selected')) assert.match(text, /selected.*stor|stor.*selected/s);
      else if (fact.includes('existing source')) { assert.match(text, /source/); assert.match(text, /no tests/); assert.match(text, /candidate/); assert.match(text, /story/); }
      else if (fact.includes('AI')) assert.match(text, /(?:0|zero) ai calls/);
      else assert.match(text, /no checks|checks.*(?:not|never).*sent/);
    }
    checked.add('semantic_facts');
  } else {
    const s = setup(t, input); let captured, selection, captureCalls = 0, candidateReads = 0, refreshing = false;
    const generatedPath = input.generated_file && join(s.repo, input.generated_file.path);
    if (generatedPath) {
      const originals = { readFileSync: fs.readFileSync, openSync: fs.openSync };
      for (const name of Object.keys(originals)) fs[name] = (...args) => { if (typeof args[0] === 'string' && resolve(args[0]) === generatedPath) candidateReads++; return originals[name](...args); };
      syncBuiltinESMExports();
      t.after(() => { Object.assign(fs, originals); syncBuiltinESMExports(); });
      // Observe the public diagnostic owner independently of discovery/capture.
      const hints = whyNoTests(s.repo, gitFiles(s.repo));
      contains(hints.join('\n'), expected.diagnostic_contains);
      check('candidate_content_reads', candidateReads);
    }
    const fake = await fakeRuntime(t, (entry, f) => {
      const id = entry.request?.requestId ?? entry.url.split('/').at(-1), command = entry.command ?? 'lint';
      if (command === 'check') return { status: 200, json: f.check(id) };
      if (command === 'try') return { status: 200, json: f.tryJob(id) };
      const outcome = input.saved_fixture ? (refreshing ? input.outcome : input.cache === 'refresh' ? 'queued' : input.outcome === 'busy' ? 'passed' : input.outcome) : 'passed';
      if (outcome === 'busy') return { status: 429, json: { error: { code: 'server-full', message: 'Synthetic capacity busy.', details: { retryable: true, retry_after: 60 } }, dispatch: 'not_started' } };
      if (['unknown', 'queued', 'running'].includes(outcome)) return { status: 200, json: f.job(id, 'lint', outcome) };
      const prompts = input.control_reference?.fixture === 'test/fixtures/harbor' ? undefined : [];
      const answer = f.lint(id, prompts);
      if (outcome === 'refused') { answer.state = 'refused'; answer.result.exitCode = 1; answer.result.refusals = [{ code: 'synthetic-refusal', message: 'Synthetic refusal.' }]; }
      const problems = [...(s.recipe.server_problems ?? [])];
      if (input.server_error_entries) problems.push({ code: 'synthetic-error', file: 'product/plan.md', severity: 'error', message: 'Synthetic error.' });
      if (problems.length) answer.result.problems = problems;
      return { status: 200, json: answer };
    });
    const env = { HOME: s.home, PDD_STATE_DIR: s.state, PDD_RUNTIME_URL: fake.origin };
    const makePorts = () => portsFor(env, {
      captureSource(repo, selected) { captureCalls++; selection = selected; captured = captureSource(repo, selected); if (s.recipe.context_warnings) captured.warnings.push(...s.recipe.context_warnings); if (input.server_error_entries) captured.warnings.push('Warning: synthetic one.', 'Warning: synthetic two.'); return captured; },
    });
    const first = makePorts();
    let options = own(input, 'options') ? { ...input.options } : { ...spec.default_input.options, '--json': input.mode !== 'text' };
    let words = input.words ?? (input.fixture === 'explicit-unknown' ? ['unknown'] : spec.default_input.words);
    if (input.operation === '--retry' && input.control_reference) options = { '--json': true };
    if (input.saved_fixture) options = { '--lint': true, '--json': true, '--timeout': 1 };
    if (input.cache === 'refresh') { first.ports.pollMs = 60_000; }
    const boundary = input.boundary?.endsWith('#runTry') ? runTry : runCheck;
    let result = parse(first.ports, await boundary({ cwd: s.repo, words, options }, first.ports));
    let baseline = { posts: 0, gets: 0 }, baselineWarnings = result.json?.warnings?.length ?? 0, port = first;
    let producer, savedLintId, savedCheckId;
    if (input.operation === '--retry') {
      assert.ok(result.json?.batch, `Producer did not save a batch: ${result.text}`);
      producer = readJson(batchPath(s, result.json.batch)); savedLintId = producer.lint.request_ids.at(-1); savedCheckId = producer.rows[0]?.request_ids.at(-1);
      if (input.saved_fixture && input.outcome === 'busy' && input.cache === 'cached') {
        // Synthetic definitive not-run cache, retaining the actual producer's lint identity.
        producer.lint.state = 'not_run'; producer.lint.note = { message: 'Synthetic definitive not-run capacity advice.' }; producer.lint.pending = false;
        setJson(batchPath(s, result.json.batch), producer);
        rmSync(join(s.state, 'batches', result.json.batch, `${savedLintId}.json`));
      }
      baseline = { posts: posts(fake), gets: fake.gets.length }; captureCalls = 0; refreshing = true; port = makePorts();
      const retryOptions = { '--retry': result.json.batch, ...(input.mode !== 'text' ? { '--json': true } : {}) };
      let thrown;
      try { result = parse(port.ports, await runCheck({ cwd: s.repo, words: [], options: retryOptions }, port.ports)); } catch (error) { thrown = error; }
      assert.equal(thrown, undefined, `Public retry must not throw: ${thrown?.stack}`);
    }
    check('exit_code', result.code);
    const batchNames = existsSync(join(s.state, 'batches')) ? readdirSync(join(s.state, 'batches')).filter(name => existsSync(batchPath(s, name))) : [];
    const batch = result.json?.batch ?? producer?.batch ?? batchNames.at(-1);
    const persisted = batch ? readJson(batchPath(s, batch)) : undefined;
    const summary = batch && existsSync(join(s.state, 'batches', batch, 'summary.json')) ? readJson(join(s.state, 'batches', batch, 'summary.json')) : result.json;
    check('lint_state', result.json?.lint_state ?? persisted?.lint?.state);
    check('rows', result.json?.rows ?? persisted?.rows);
    check('rows_count', result.json?.rows?.length);
    check('capture_calls', captureCalls); check('auth_calls', port.clock.gh.length); check('uuid_calls', port.clock.uuids);
    check('posts', posts(fake) - baseline.posts);
    for (const command of ['lint', 'check', 'try']) check(`${command}_posts`, fake.posts.slice(baseline.posts).filter(p => p.command === command).length);
    check('get_calls', fake.gets.length - baseline.gets);
    if (own(expected, 'get_ids')) { assert.ok(fake.gets.slice(baseline.gets).every(p => p.url.endsWith(`/${savedLintId}`))); checked.add('get_ids'); }
    check('candidate_content_reads', candidateReads);
    fragments('diagnostic_contains', result.text); fragments('summary_contains', result.json?.summary_line ?? result.text);
    fragments('informational_contains', result.text);
    const warningEntries = result.json?.warnings ?? persisted?.warnings ?? [];
    const problems = summary?.problems ?? [];
    check('warning_count', warningEntries.length + problems.filter(p => p.severity === 'warning').length);
    check('context_warnings_visible', result.json ? warningEntries.length : warningEntries.filter(w => result.text.includes(w)).length);
    check('server_warning_diagnostics_visible', result.json ? problems.filter(p => p.severity === 'warning').length : (s.recipe.server_problems ?? []).filter(p => result.text.includes(p.message)).length);
    check('new_warning_entries', warningEntries.length - baselineWarnings);
    check('json_objects', result.json ? 1 : 0); check('extra_result_lines', result.json ? 0 : result.stdout.trim().split('\n').length);
    check('result_summaries', result.json ? Number(typeof result.json.summary_line === 'string') : result.stdout.split('\n').filter(l => /No tests yet.*Source lint/i.test(l)).length);
    if (own(expected, 'summary_is_last_stdout_line')) { const last = result.stdout.trimEnd().split('\n').at(-1); assert.match(last, /No tests yet.*0 AI calls.*No checks were sent/); checked.add('summary_is_last_stdout_line'); }
    if (own(expected, 'story_warning_contains')) { if (expected.story_warning_contains !== null) contains(result.text, [expected.story_warning_contains]); else assert.equal(warningEntries.some(w => /has no test\./.test(w)), false); checked.add('story_warning_contains'); }
    check('source_only', !!persisted?.source_only);
    if (own(expected, 'capture_tests')) { assert.deepEqual(selection.tests, expected.capture_tests); checked.add('capture_tests'); }
    if (expected.captured_paths) { for (const path of expected.captured_paths) assert.ok(captured.files.some(f => f.path === path), path); checked.add('captured_paths'); }
    if (expected.excluded_paths) { for (const path of expected.excluded_paths) assert.equal(captured.files.some(f => f.path === path), false, path); checked.add('excluded_paths'); }
    check('row_states', result.json?.rows?.map(r => r.state)); check('try_setups', posts(fake, 'try'));
    if (own(expected, 'preserved_check_request_id')) { assert.equal(readJson(batchPath(s, producer.batch)).rows[0].request_ids.at(-1), savedCheckId); checked.add('preserved_check_request_id'); }
  }
  assert.deepEqual([...checked].sort(), Object.keys(expected).sort(), `${vector.id}: unmapped frozen fields`);
}
for (const vector of spec.cases) test(`SOURCE-LINT followup: ${vector.id}`, t => exercise(t, vector));
