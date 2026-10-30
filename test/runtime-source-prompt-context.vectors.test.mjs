import test from 'node:test';
import assert from 'node:assert/strict';
import fs, { cpSync, mkdirSync, readFileSync, renameSync, rmSync, writeFileSync } from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
import { spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { captureSource, interfaceBlocks } from '../src/runtime-preflight.mjs';
import { fakeRuntime, portsFor, root, temp } from './runtime-fake.mjs';

const spec = JSON.parse(readFileSync(new URL('./fixtures/source-prompt-context-cases.json', import.meta.url)));
const recipes = JSON.parse(readFileSync(new URL('./fixtures/source-only-lint-cases.json', import.meta.url))).fixture_sources;
const own = (o, k) => Object.hasOwn(o, k);
const write = (repo, path, bytes) => { mkdirSync(dirname(join(repo, path)), { recursive: true }); writeFileSync(join(repo, path), bytes); };
function git(repo, ...args) {
  const r = spawnSync('git', args, { cwd: repo, encoding: 'utf8' }); assert.equal(r.status, 0, r.stderr); return r.stdout;
}
function setup(t, input, variant) {
  const dir = temp(t), repo = join(dir, 'repo'), home = join(dir, 'home'), state = join(dir, 'state');
  mkdirSync(repo); mkdirSync(home);
  if (input.fixture === 'harbor') cpSync(join(root, 'test/fixtures/harbor'), repo, { recursive: true });
  for (const [path, bytes] of Object.entries({ ...recipes[input.fixture]?.files, ...input.files })) write(repo, path, bytes);
  if (input.relocate_test_to) { mkdirSync(dirname(join(repo, input.relocate_test_to)), { recursive: true }); renameSync(join(repo, 'tests/place-order.json'), join(repo, input.relocate_test_to)); rmSync(join(repo, 'tests/unknown-item.json')); }
  if (input.generated_file) { const g = input.generated_file; write(repo, g.path, g.prefix + g.pad_byte.repeat(g.bytes - Buffer.byteLength(g.prefix + g.suffix)) + g.suffix); }
  if (variant) {
    const path = join(repo, 'echo.prompt.md'), text = readFileSync(path, 'utf8'), [block] = interfaceBlocks(text);
    if (variant === 'malformed-json') writeFileSync(path, text.replace(block[1], '{ malformed JSON }'));
    if (variant === 'multiple-blocks') writeFileSync(path, text + text.slice(text.indexOf('<details>')));
    if (variant === 'stale-hash') writeFileSync(path, text.replace('Return the supplied value unchanged.', 'Return a synthetic changed value.'));
    if (variant === 'unapproved') writeFileSync(path, text.replace('"status":"draft"', '"status":"unapproved"'));
    assert.ok(interfaceBlocks(readFileSync(path, 'utf8')).length > 0, 'Runtime-bearing invalid input must retain recognized blocks');
  }
  git(repo, 'init', '-q'); git(repo, 'add', '-A'); git(repo, '-c', 'user.name=Native test', '-c', 'user.email=native@example.invalid', 'commit', '--allow-empty', '-qm', 'synthetic');
  return { repo, home, state };
}
function observeReads(t, repo, onlyPath) {
  let count = 0;
  const originals = { readFileSync: fs.readFileSync, openSync: fs.openSync };
  const source = path => typeof path === 'string' && resolve(path).startsWith(repo + '/') && !resolve(path).startsWith(join(repo, '.git') + '/') && (!onlyPath || resolve(path) === join(repo, onlyPath));
  for (const name of Object.keys(originals)) fs[name] = (...args) => { if (source(args[0])) count++; return originals[name](...args); };
  syncBuiltinESMExports();
  t.after(() => { Object.assign(fs, originals); syncBuiltinESMExports(); });
  return { get count() { return count; }, reset() { count = 0; } };
}
async function exercise(t, vector, variant) {
  const input = vector.input, expected = vector.expected, s = setup(t, input, variant), checked = new Set();
  const check = (key, actual) => { if (own(expected, key)) { assert.deepEqual(actual, expected[key], `${vector.id}: ${key}`); checked.add(key); } };
  let captureCalls = 0, captured, selected, refreshing = false;
  const fake = await fakeRuntime(t, (entry, f) => {
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    const reply = refreshing ? input.refresh_reply ?? input.reply : input.initial_reply ?? input.reply;
    if (reply?.startsWith('running-')) return { status: 200, json: f.job(id, 'lint', 'running') };
    const paths = (captured?.sources ?? []).filter(file => file.path.endsWith('.prompt.md') && interfaceBlocks(file.bytes.toString('utf8')).length).map(file => file.path);
    const admitted = reply === 'passed-selected-test' || reply === 'passed-runtime-admitted-prose-omitted' ? paths.map(path => ({ path, state: 'draft', admission_state: 'draft', interface: { calls: [] } })) : [];
    const answer = f.lint(id, admitted);
    if (reply === 'canonical-runtime-refusal' || reply === 'canonical-refused-prompt') answer.result.report.program.refused_prompts = [{ path: variant ? 'echo.prompt.md' : 'board.prompt.md', code: 'interface-invalid', message: 'Synthetic interface refusal.' }];
    if (reply === 'canonical-explicit-refused-admission') answer.result.report.program.prompts = [{ path: 'board.prompt.md', state: 'refused', admission_state: 'refused' }];
    if (reply === 'canonical-global-failed') answer.state = 'failed';
    if (reply === 'canonical-global-error') answer.result.problems = [{ code: 'synthetic-error', severity: 'error', message: 'Synthetic global error.' }];
    return { status: 200, json: answer };
  });
  const env = { HOME: s.home, PDD_STATE_DIR: s.state, PDD_RUNTIME_URL: fake.origin };
  const makePorts = () => portsFor(env, { captureSource(repo, selection) {
    captureCalls++; selected = selection; captured = captureSource(repo, selection);
    if (input.classification_evidence === 'capture-without-sources') { const legacy = { ...captured }; delete legacy.sources; return legacy; }
    return captured;
  } });
  const first = makePorts(); first.ports.pollMs = 60_000;
  const observer = input.generated_file ? observeReads(t, s.repo, input.generated_file.path) : null;
  let ports = first, options = { ...spec.default_options, ...(input.initial_reply ? { '--timeout': 1 } : {}) };
  let code = await runCheck({ cwd: s.repo, words: [], options }, ports.ports);
  // Assert semantic exit before inspecting derived state: old candidate failures must not become parser crashes.
  if (!input.read_action && !['legacy-missing-metadata', 'unsupported-metadata'].includes(input.classification_evidence)) check('exit_code', code);
  if (input.initial_reply) assert.equal(code, 3, `Expected a genuinely pending producer: ${ports.ports.stdout.text}${ports.ports.stderr.text}`);
  const parse = () => JSON.parse(ports.ports.stdout.text);
  let result = ports.ports.stdout.text.trim().startsWith('{') ? parse() : undefined;
  const batchFile = result?.batch && join(s.state, 'batches', result.batch, 'batch.json');
  const loadBatch = () => batchFile ? JSON.parse(readFileSync(batchFile)) : undefined;
  let saved = loadBatch(), savedHash = saved?.source_sha256, savedLintId = saved?.lint?.request_ids.at(-1);
  let baseline = { posts: 0, gets: 0 }, refreshObserver;
  if (input.read_action || ['legacy-missing-metadata', 'unsupported-metadata'].includes(input.classification_evidence)) {
    assert.ok(result?.batch, 'Actual producer must save a batch before refresh');
    if (input.classification_evidence) {
      assert.equal(code, 0, 'New prose producer must first pass');
      assert.deepEqual(saved.prose_source_paths, ['board.prompt.md']);
      assert.equal(result.warnings.filter(w => w.includes('has no Runtime interface yet')).length, 1);
      if (input.classification_evidence === 'legacy-missing-metadata') delete saved.prose_source_paths;
      else saved.prose_source_paths = { unsupported_version: 99 };
      writeFileSync(batchFile, JSON.stringify(saved));
    }
    for (const [path, bytes] of Object.entries(input.after_save_files ?? {})) write(s.repo, path, bytes.includes('using loose-prompt fixture bytes') ? recipes['loose-prompt'].files['echo.prompt.md'] : bytes);
    if (input.after_save_files) {
      refreshObserver = observeReads(t, s.repo);
      const calibrationPath = Object.keys(input.after_save_files)[0];
      readFileSync(join(s.repo, calibrationPath)); assert.ok(refreshObserver.count > 0, 'Source content spy must detect a real read'); refreshObserver.reset();
    }
    baseline = { posts: fake.posts.length, gets: fake.gets.length }; captureCalls = 0; refreshing = true; ports = makePorts();
    const action = input.read_action ?? '--read';
    code = await runCheck({ cwd: s.repo, words: action === '--read' ? [result.batch] : [],
      options: { [action]: action === '--read' ? true : result.batch, '--json': true } }, ports.ports);
    check('exit_code', code); result = parse(); saved = loadBatch();
  }
  const text = ports.ports.stdout.text + ports.ports.stderr.text;
  check('lint_state', result?.lint_state); check('rows', result?.rows);
  check('capture_calls', captureCalls); check('auth_calls', ports.clock.gh.length); check('posts', fake.posts.length);
  check('candidate_content_reads', observer?.count);
  check('lint_posts', fake.posts.filter(p => p.command === 'lint').length); check('check_posts', fake.posts.filter(p => p.command === 'check').length);
  check('selected_test', selected?.tests?.[0]?.path ?? selected?.tests?.[0]);
  check('prose_source_paths', saved?.prose_source_paths);
  check('prose_warning_count', result?.warnings?.filter(w => w.includes('has no Runtime interface yet')).length ?? 0);
  for (const key of ['diagnostic_contains', 'warning_contains']) if (own(expected, key)) { for (const fragment of expected[key]) assert.ok(text.includes(fragment), `${vector.id}: missing ${fragment}: ${text}`); checked.add(key); }
  if (own(expected, 'problem_code')) { assert.ok(result?.problems?.some(p => p.code === expected.problem_code), text); checked.add('problem_code'); }
  check('refresh_capture_calls', captureCalls); check('refresh_uuid_calls', ports.clock.uuids);
  check('refresh_posts', fake.posts.length - baseline.posts); check('refresh_gets', fake.gets.length - baseline.gets);
  check('json_results', ports.ports.stdout.text.trim().split('\n').filter(line => { try { JSON.parse(line); return true; } catch { return false; } }).length);
  check('saved_source_hash_preserved', saved?.source_sha256 === savedHash);
  check('refresh_source_content_reads', refreshObserver?.count);
  check('refresh_uses_original_lint_id', fake.gets.slice(baseline.gets).length === 1 && fake.gets.slice(baseline.gets).every(g => g.url.endsWith('/' + savedLintId)) && saved?.lint?.request_ids.at(-1) === savedLintId);
  assert.deepEqual([...checked].sort(), Object.keys(expected).sort(), `${vector.id}: unmapped expected fields`);
}
for (const vector of spec.cases) for (const variant of vector.input.runtime_variants ?? [undefined]) test(`SOURCE context: ${vector.id}${variant ? ': ' + variant : ''}`, t => exercise(t, vector, variant));
