import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn, spawnSync } from 'node:child_process';
import fs, { chmodSync, closeSync, cpSync, ftruncateSync, mkdirSync, openSync, readFileSync, readdirSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
import { dirname, join } from 'node:path';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { captureSource, interfaceBlocks, proseSha256, sha256 } from '../src/runtime-preflight.mjs';
import { fakeRuntime, portsFor, root, temp } from './runtime-fake.mjs';

// These are native, synthetic receipt cases, not Runtime program scenarios.
// Expectations are read from the approved Source fixture without rewriting it.
const specification = JSON.parse(readFileSync(new URL('./fixtures/source-only-lint-cases.json', import.meta.url)));
const own = (value, key) => Object.hasOwn(value, key);
const supportedExpectations = new Set([
  'exit_code', 'lint_state', 'rows', 'rows_count', 'lint_posts', 'check_posts', 'try_posts', 'complete', 'calls',
  'archive_paths', 'excluded_paths', 'authored_files_unchanged', 'authored_prompt_unchanged', 'generated_scenarios',
  'summary_contains', 'expanded_prompt_contains', 'expanded_prompt_excludes', 'reference_target', 'problem_code',
  'pointer', 'diagnostic_contains', 'warning_contains', 'auth_lookups', 'read_oversized_file', 'attempts',
  'capture_returned', 'duplicate_paths', 'story_footprints', 'deterministic_sha', 'first_exit_code',
  'first_lint_state', 'first_rows', 'first_read_hint', 'read_exit_code', 'read_lint_state', 'read_rows',
  'same_lint_id', 'read_posts', 'read_gets_minimum', 'read_summary_contains',
]);
const write = (repo, path, bytes) => { mkdirSync(dirname(join(repo, path)), { recursive: true }); writeFileSync(join(repo, path), bytes); };
const git = (repo, ...args) => {
  const answer = spawnSync('git', args, { cwd: repo, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  assert.equal(answer.status, 0, answer.stderr);
  return answer.stdout;
};

function reviseInterface(repo, revise) {
  const path = join(repo, 'echo.prompt.md'), authored = readFileSync(path, 'utf8');
  const [block] = interfaceBlocks(authored), iface = JSON.parse(block[1]);
  revise(iface);
  iface.prose_sha256 = proseSha256(authored);
  writeFileSync(path, authored.slice(0, block.indices[1][0]) + JSON.stringify(iface) + authored.slice(block.indices[1][1]));
}

function makeFixture(t, vector) {
  const sandbox = temp(t), repo = join(sandbox, 'repo'), home = join(sandbox, 'home');
  mkdirSync(repo); mkdirSync(home);
  let replacement;
  const materialize = name => {
    const recipe = specification.fixture_sources[name];
    assert.ok(recipe, `Unknown approved fixture: ${name}`);
    if (recipe.base) materialize(recipe.base);
    if (recipe.copy_public_tree) {
      const source = join(root, recipe.copy_public_tree);
      if (recipe.include) for (const path of recipe.include) write(repo, path, readFileSync(join(source, path)));
      else cpSync(source, repo, { recursive: true });
    }
    for (const [path, bytes] of Object.entries(recipe.files ?? {})) write(repo, path, bytes);
    for (const [path, bytes] of Object.entries(recipe.tracked_before_symlink ?? {})) write(repo, path, bytes);
    if (recipe.outside_files) {
      for (const [path, bytes] of Object.entries(recipe.outside_files)) write(join(sandbox, 'outside-directory'), path, bytes);
    }
    if (recipe.replace_input_schema) reviseInterface(repo, iface => { iface.entries[0].input_schema = recipe.replace_input_schema; });
    replacement = recipe.replace_after_tracking ?? replacement;
  };
  materialize(vector.fixture);
  for (const [path, bytes] of Object.entries(vector.extra_files ?? {})) write(repo, path, bytes);
  if (vector.prompt_limits) reviseInterface(repo, iface => { iface.limits = vector.prompt_limits; });
  for (const path of vector.remove_files ?? []) rmSync(join(repo, path));
  if (vector.sparse_file) {
    const { path, size } = vector.sparse_file;
    mkdirSync(dirname(join(repo, path)), { recursive: true });
    const descriptor = openSync(join(repo, path), 'w');
    try { ftruncateSync(descriptor, size); } finally { closeSync(descriptor); }
  }
  if (vector.generated_files) {
    const recipe = vector.generated_files;
    for (let index = 0; index < recipe.count; index++) {
      const bytes = recipe.size ? Buffer.alloc(recipe.size, ' ').fill(recipe.content_prefix, 0, Buffer.byteLength(recipe.content_prefix)) : recipe.content;
      write(repo, `${recipe.prefix}${index}${recipe.suffix}`, bytes);
    }
  }
  if (vector.symlink) {
    mkdirSync(dirname(join(repo, vector.symlink.path)), { recursive: true });
    symlinkSync(vector.symlink.target, join(repo, vector.symlink.path));
  }
  git(repo, 'init', '-q'); git(repo, 'add', '-A');
  // A tracked child must survive in Git after its ancestor becomes a symlink.
  if (replacement) {
    rmSync(join(repo, replacement.remove_directory), { recursive: true });
    symlinkSync(join(sandbox, replacement.symlink.target), join(repo, replacement.symlink.path));
  }
  return { sandbox, repo, home, state: join(sandbox, 'state') };
}

function archive(tar) {
  const result = new Map();
  let pendingPath;
  for (let offset = 0; offset + 512 <= tar.length;) {
    const header = tar.subarray(offset, offset + 512);
    if (header.every(byte => byte === 0)) break;
    const text = (start, length) => header.subarray(start, start + length).toString().replace(/\0.*$/s, '');
    const size = parseInt(text(124, 12).trim(), 8) || 0;
    const bytes = tar.subarray(offset + 512, offset + 512 + size), type = text(156, 1);
    if (type === 'x') pendingPath = /(?:^|\n)\d+ path=([^\n]*)\n/.exec(bytes.toString())?.[1];
    else {
      assert.ok(type === '0' || type === '', `Unexpected archive type ${type}`);
      const path = pendingPath ?? text(0, 100);
      assert.equal(result.has(path), false, `Duplicate archive entry ${path}`);
      result.set(path, bytes); pendingPath = undefined;
    }
    offset += 512 + Math.ceil(size / 512) * 512;
  }
  return result;
}

function authoredFiles(repo) {
  const result = new Map();
  const visit = (directory, prefix = '') => {
    for (const entry of readdirSync(directory, { withFileTypes: true })) {
      if (entry.name === '.git') continue;
      const path = prefix + entry.name;
      if (entry.isDirectory()) visit(join(directory, entry.name), `${path}/`);
      else if (entry.isFile()) result.set(path, sha256(readFileSync(join(repo, path))));
    }
  };
  visit(repo); return result;
}

function lintReply(fake, id, vector, paths, reading) {
  const recipe = { ...specification.default_reply, ...vector.reply };
  const state = recipe.initial_state ? (reading ? recipe.read_state : recipe.initial_state) : recipe.state;
  if (['queued', 'running', 'unknown'].includes(state)) return fake.job(id, 'lint', state);
  const prompts = paths.filter(path => path.endsWith('.prompt.md')).map(path => ({ path, state: 'draft', admission_state: 'draft', interface: { calls: [] } }));
  const answer = fake.lint(id, prompts, recipe.refused_prompts ?? []);
  answer.state = state;
  answer.result.refusals = recipe.refusals ?? [];
  if (recipe.problems) answer.result.problems = recipe.problems;
  if (!recipe.program) delete answer.result.report.program;
  return answer;
}

function assertContains(actual, fragments, context) {
  for (const fragment of Array.isArray(fragments) ? fragments : [fragments]) assert.ok(actual.includes(fragment), `${context}: missing ${JSON.stringify(fragment)} in ${actual}`);
}

function assertPublic(result, expected, prefix = '') {
  if (own(expected, `${prefix}exit_code`)) assert.equal(result.code, expected[`${prefix}exit_code`], result.output);
  if (own(expected, `${prefix}lint_state`)) assert.equal(result.json?.lint_state, expected[`${prefix}lint_state`], result.output);
  if (own(expected, `${prefix}rows`)) assert.deepEqual(result.json?.rows, expected[`${prefix}rows`], result.output);
  if (own(expected, 'rows_count')) assert.equal(result.json?.rows.length, expected.rows_count, result.output);
  if (own(expected, `${prefix}summary_contains`)) assertContains(result.json?.summary_line ?? result.output, expected[`${prefix}summary_contains`], 'summary');
}

function assertDiagnostics(result, expected) {
  if (expected.problem_code) {
    assert.ok(result.json?.problems?.some(problem => problem.code === expected.problem_code), `Missing diagnostic ${expected.problem_code}: ${result.output}`);
  }
  if (expected.pointer) assert.ok(result.json?.problems?.some(problem => problem.pointer === expected.pointer || problem.section === expected.pointer), result.output);
  if (expected.diagnostic_contains) assertContains(result.output, expected.diagnostic_contains, 'diagnostic');
  if (expected.warning_contains) assertContains(JSON.stringify(result.json?.warnings), expected.warning_contains, 'warning');
}

async function exercise(t, vector) {
  for (const key of Object.keys(vector.expected)) assert.ok(supportedExpectations.has(key), `Not replayed: ${vector.case} has unmapped expectation ${key}`);
  const setup = makeFixture(t, vector), before = authoredFiles(setup.repo);
  let oversizedReads = 0;
  if (vector.sparse_file) {
    const originalRead = fs.readFileSync, originalOpen = fs.openSync;
    const oversizedPath = join(setup.repo, vector.sparse_file.path);
    fs.readFileSync = (...args) => { if (args[0] === oversizedPath) oversizedReads++; return originalRead(...args); };
    fs.openSync = (...args) => { if (args[0] === oversizedPath) oversizedReads++; return originalOpen(...args); };
    syncBuiltinESMExports();
    t.after(() => { fs.readFileSync = originalRead; fs.openSync = originalOpen; syncBuiltinESMExports(); });
  }
  if (vector.boundary?.endsWith('#captureSource')) {
    const originalRead = fs.readFileSync;
    let reads = 0, returned, error;
    if (vector.change_after_each_read) {
      fs.readFileSync = (...args) => {
        const bytes = originalRead(...args);
        if (typeof args[0] === 'number' && bytes.toString().startsWith('# Rules\n')) {
          reads++; write(setup.repo, vector.change_after_each_read, `# Rules\n\nChanged ${reads}.\n`);
        }
        return bytes;
      };
      syncBuiltinESMExports();
      t.after(() => { fs.readFileSync = originalRead; syncBuiltinESMExports(); });
    }
    try { returned = captureSource(setup.repo, vector.selection); } catch (caught) { error = caught; }
    const expected = vector.expected;
    if (own(expected, 'capture_returned')) assert.equal(returned !== undefined, expected.capture_returned);
    if (own(expected, 'exit_code')) assert.equal(error?.exitCode, expected.exit_code, error?.message);
    if (own(expected, 'attempts')) assert.equal(reads, expected.attempts);
    if (returned) {
      const entries = archive(returned.tar);
      assert.deepEqual([...entries.keys()].sort(), expected.archive_paths);
      if (own(expected, 'duplicate_paths')) assert.equal(returned.files.length - new Set(returned.files.map(file => file.path)).size, expected.duplicate_paths);
      if (own(expected, 'story_footprints')) assert.equal(returned.stories.length, expected.story_footprints);
      if (expected.deterministic_sha) {
        assert.equal(returned.sha256, sha256(returned.tar));
        assert.equal(captureSource(setup.repo, vector.selection).sha256, returned.sha256);
      }
    }
    if (expected.authored_files_unchanged) assert.deepEqual(authoredFiles(setup.repo), before);
    return;
  }
  let reading = false, captured, capturedSelection;
  const receipts = [];
  const fake = await fakeRuntime(t, (entry, f) => {
    assert.ok(entry.method === 'GET' || entry.method === 'POST', `Unexpected ${entry.method}`);
    if (entry.method === 'POST') {
      assert.equal(entry.command, 'lint', 'No Check or Try dispatch is permitted by these cases');
      assert.ok(captured, 'Real capture must precede upload');
      assert.deepEqual(entry.tar, captured.tar);
      assert.equal(entry.request.source_sha256, sha256(entry.tar));
      if (vector.reply?.http_status) return { status: vector.reply.http_status, json: { error: vector.reply.error, login: vector.reply.login } };
    }
    const id = entry.method === 'POST' ? entry.request.requestId : entry.url.split('/').at(-1);
    const receipt = lintReply(f, id, vector, captured?.files.map(file => file.path) ?? [], reading);
    receipts.push(receipt);
    return { status: 200, json: receipt };
  });
  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };
  const first = portsFor(env, { captureSource(repo, selection) { capturedSelection = selection; captured = captureSource(repo, selection); return captured; } });
  const input = { cwd: setup.repo, words: vector.words ?? specification.default_input.words,
    options: own(vector, 'options') ? vector.options : specification.default_input.options };
  const invoke = vector.boundary?.endsWith('#runTry') ? runTry : runCheck;
  const call = async (operation, args, ports) => {
    const code = await operation(args, ports), output = ports.stdout.text + ports.stderr.text;
    let json;
    if (ports.stdout.text.trim().startsWith('{')) json = JSON.parse(ports.stdout.text);
    return { code, json, output };
  };
  const initial = await call(invoke, input, first.ports);
  let result = initial, readPosts, readGets;
  if (vector.action === 'lint-then-read-saved-batch') {
    assertPublic(initial, vector.expected, 'first_');
    if (vector.expected.first_read_hint) assertContains(initial.output, `pdd check --read ${initial.json?.batch}`, 'read command');
    const postCount = fake.posts.length, getCount = fake.gets.length;
    reading = true;
    const next = portsFor(env);
    result = await call(runCheck, { cwd: setup.repo, words: [initial.json?.batch], options: { '--read': true, '--json': true } }, next.ports);
    readPosts = fake.posts.length - postCount; readGets = fake.gets.length - getCount;
    assertPublic(result, vector.expected, 'read_');
    assert.equal(next.clock.uuids, 0, 'Saved reads allocate no request');
    if (vector.expected.same_lint_id) assert.ok(fake.gets.slice(getCount).every(entry => entry.url.endsWith(`/${fake.posts[0].request.requestId}`)));
  } else assertPublic(result, vector.expected);
  const expected = vector.expected;
  assert.equal(fake.jsonPosts.length, 0, 'No JSON Check/Try dispatch is permitted');
  assertDiagnostics(result, expected);
  for (const command of ['lint', 'check', 'try']) if (own(expected, `${command}_posts`)) assert.equal(fake.posts.filter(entry => entry.command === command).length, expected[`${command}_posts`], result.output);
  if (own(expected, 'auth_lookups')) assert.equal(first.clock.gh.length, expected.auth_lookups, result.output);
  if (own(expected, 'read_posts')) assert.equal(readPosts, expected.read_posts);
  if (own(expected, 'read_gets_minimum')) assert.ok(readGets >= expected.read_gets_minimum);
  if (own(expected, 'complete')) for (const entry of fake.posts) assert.equal(entry.request.complete, expected.complete);
  if (own(expected, 'calls')) {
    assert.ok(receipts.length || vector.reply?.http_status === 422, 'Known usage needs a fake Runtime receipt or a definite unsent HTTP refusal');
    for (const receipt of receipts) assert.equal(receipt.usage.calls, expected.calls);
    assertContains(result.json?.summary_line ?? result.output, `${expected.calls} AI calls`, 'known zero-call usage');
  }
  if (own(expected, 'read_oversized_file')) assert.equal(oversizedReads > 0, expected.read_oversized_file);
  if (captured) {
    const entries = archive(captured.tar), paths = [...entries.keys()].sort();
    if (expected.archive_paths) assert.deepEqual(paths, expected.archive_paths);
    for (const path of expected.excluded_paths ?? []) assert.equal(entries.has(path), false, path);
    if (expected.generated_scenarios === 0) assert.equal([...entries.values()].filter(bytes => bytes.toString().includes('prompt-runtime.program-scenario.v1')).length, 0);
    if (expected.expanded_prompt_contains) assertContains(entries.get('echo.prompt.md').toString(), expected.expanded_prompt_contains, 'expanded prompt');
    if (expected.expanded_prompt_excludes) assert.equal(entries.get('echo.prompt.md').toString().includes(expected.expanded_prompt_excludes), false);
    if (expected.reference_target) assert.ok(captured.references.some(reference => reference.target === expected.reference_target));
    if (vector.fixture !== 'harbor') {
      assert.deepEqual(capturedSelection.tests, []);
      assert.equal(capturedSelection.appMap, null);
      assert.ok(Array.isArray(capturedSelection.sourceFiles), 'Source-only lint uses the public explicit source selection');
    }
    for (const [path, bytes] of entries) {
      if (!path.endsWith('.prompt.md')) assert.deepEqual(bytes, readFileSync(join(setup.repo, path)), path);
    }
  }
  if (expected.authored_files_unchanged || expected.authored_prompt_unchanged) assert.deepEqual(authoredFiles(setup.repo), before);
}

for (const vector of specification.cases) test(`SOURCE-LINT vector: ${vector.case}`, t => exercise(t, vector));

test('SOURCE-LINT capture preserves omitted selection bytes and accepts prepared source roots through the same closure', t => {
  const setup = makeFixture(t, { fixture: 'harbor' });
  assert.deepEqual(captureSource(setup.repo, { sourceFiles: [] }), captureSource(setup.repo));
  const plan = makeFixture(t, { fixture: 'loose-prompt' });
  const prompt = readFileSync(join(plan.repo, 'echo.prompt.md'));
  const capture = captureSource(plan.repo, { tests: [], sourceFiles: ['generated.prompt.md'],
    prepareSource: () => [{ path: 'generated.prompt.md', bytes: prompt }] });
  assert.deepEqual(capture.files.map(file => file.path), ['docs/rules.md', 'generated.prompt.md']);
  assert.deepEqual(archive(capture.tar).get('generated.prompt.md'), prompt);
  assert.deepEqual(capture.stories, []);
  assert.equal(fs.existsSync(join(plan.repo, 'generated.prompt.md')), false);
  for (const sourceFiles of [null, false, 'echo.prompt.md', [null], ['missing.md'], ['../outside.md']]) {
    assert.throws(() => captureSource(plan.repo, { tests: [], sourceFiles }), error => error.exitCode === 4);
  }
});

test('SOURCE-LINT raw Git candidates retain unsafe ancestors even when their tracked child is absent', async t => {
  const setup = makeFixture(t, { fixture: 'symlink-ancestor' });
  rmSync(join(setup.sandbox, 'outside-directory/record.md'));
  const p = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: 'http://127.0.0.1:9' }, {
    fetch() { assert.fail('Unsafe source must refuse before transport'); },
  });
  const code = await runCheck({ cwd: setup.repo, options: { '--lint': true, '--json': true } }, p.ports);
  assert.equal(code, 4, p.ports.stdout.text + p.ports.stderr.text);
  assert.match(p.ports.stderr.text, /symbolic link ancestor.*contracts/);
  assert.equal(p.clock.gh.length, 0);
});

test('SOURCE-LINT deleted tracked eligible files retain the ordinary skip', async t => {
  const setup = makeFixture(t, { fixture: 'coffee-plan', extra_files: { 'contracts/deleted.md': '# Removed\n' } });
  rmSync(join(setup.repo, 'contracts/deleted.md'));
  const fake = await fakeRuntime(t, (entry, f) => {
    assert.equal(entry.command, 'lint');
    assert.deepEqual([...archive(entry.tar).keys()].sort(), [...specification.fixture_sources['coffee-plan'].include].sort());
    return { status: 200, json: f.lint(entry.request.requestId, []) };
  });
  const p = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--lint': true, '--json': true } }, p.ports), 0, p.ports.stderr.text);
  assert.equal(fake.posts.length, 1);
});

test('SOURCE-LINT regression: actual CLI uploads the six-file coffee plan without manufacturing tests', async t => {
  const vector = specification.cases.find(vector => vector.case === 'coffee-plan-before-features');
  const setup = makeFixture(t, vector), before = authoredFiles(setup.repo), tools = join(setup.sandbox, 'tools');
  mkdirSync(tools);
  writeFileSync(join(tools, 'gh'), '#!/bin/sh\nif [ "$1" = auth ]; then echo synthetic_test_token; else echo "octo 4242"; fi\n');
  chmodSync(join(tools, 'gh'), 0o755);
  const fake = await fakeRuntime(t, (entry, f) => {
    assert.equal(entry.method, 'POST'); assert.equal(entry.command, 'lint'); assert.equal(entry.request.complete, true);
    const entries = archive(entry.tar);
    assert.deepEqual([...entries.keys()].sort(), vector.expected.archive_paths);
    for (const [path, bytes] of entries) assert.deepEqual(bytes, readFileSync(join(setup.repo, path)), path);
    return { status: 200, json: f.lint(entry.request.requestId, []) };
  });
  const child = spawn(process.execPath, [join(root, 'bin/pdd.mjs'), 'check', '--lint', '--json'], {
    cwd: setup.repo, env: { ...process.env, HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin, PATH: `${tools}:${process.env.PATH}` },
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  let stdout = '', stderr = '';
  child.stdout.on('data', chunk => { stdout += chunk; }); child.stderr.on('data', chunk => { stderr += chunk; });
  t.after(() => { if (child.exitCode === null) child.kill('SIGKILL'); });
  const timer = setTimeout(() => child.kill('SIGKILL'), 20_000);
  const code = await new Promise((resolve, reject) => { child.once('error', reject); child.once('close', resolve); });
  clearTimeout(timer);
  assert.equal(code, vector.expected.exit_code, stdout + stderr);
  assertPublic({ code, json: JSON.parse(stdout), output: stdout + stderr }, vector.expected);
  assert.equal(fake.posts.length, vector.expected.lint_posts);
  assert.deepEqual(authoredFiles(setup.repo), before);
});
