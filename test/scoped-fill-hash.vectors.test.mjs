import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { proseSha256, runCheck } from '../src/runtime-seam.mjs';

const vectors = JSON.parse(readFileSync(new URL('./fixtures/fill-hash/scoped-cases.json', import.meta.url)));
const cli = fileURLToPath(new URL('../bin/pdd.mjs', import.meta.url));
const paths = vectors.fixture.paths;
const sink = () => ({ text: '', write(value) { this.text += value; return true; } });
const git = (cwd, ...args) => {
  const result = spawnSync('git', args, { cwd, encoding: 'utf8' });
  assert.equal(result.status, 0, result.stderr);
  return result.stdout;
};
const put = (root, path, text) => {
  mkdirSync(dirname(join(root, path)), { recursive: true });
  writeFileSync(join(root, path), text);
};

function prompt(name, dependencies = [], status = 'draft', resultSchema = { type: 'object', properties: { ok: { type: 'boolean' } }, required: ['ok'], additionalProperties: false }) {
  const interfaceValue = {
    status,
    prose_sha256: '',
    entries: [{
      operation: name,
      input_schema: { type: 'object', properties: {}, additionalProperties: false },
      result_schema: resultSchema,
      errors: [],
    }],
    calls: [],
    resources: [],
    limits: { max_steps: 1, max_model_calls: 0 },
    conventions: [],
  };
  const listed = dependencies.length ? dependencies.map(path => `- [${path}](./${path})`).join('\n') : 'None.';
  return `# ${name}\n\nKeep these prose bytes for ${name}.\n\n## Dependencies\n\n${listed}\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(interfaceValue, null, 2)}\n\`\`\`\n</details>\n`;
}

function story(name) {
  return `# ${name}\n\n## Acceptance criteria\n\n1. ${name} returns an accepted result.\n`;
}

function scenario(name, storyPath, promptPath) {
  return JSON.stringify({
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: storyPath,
    criteria: [{ id: 'AC1', text: `${name} returns an accepted result.` }],
    initial_world: {},
    simulation: {},
    context: [],
    steps: [{
      step_id: `${name}-step`, entry_path: promptPath, operation: name, input: {},
      checks: [{ criterion_id: 'AC1', target: 'result', path: '/ok', op: 'equals', value: true }],
    }],
  }, null, 2) + '\n';
}

function setup(t, vector) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-scoped-fill-hash-'));
  const repo = join(root, 'repo'), home = join(root, 'home');
  t.after(() => rmSync(root, { recursive: true, force: true }));
  mkdirSync(repo); mkdirSync(home);

  const bDependencies = ['shared.prompt.md'];
  if (vector.id === 'unavailable-dependency') bDependencies.push('missing.prompt.md');
  if (vector.id === 'workspace-excluded-dependency') bDependencies.push('excluded.prompt.md');
  if (vector.id === 'contract-ref-and-symlink') {
    put(repo, 'contracts/real-shapes.json', '{"okResult":{"type":"object","properties":{"ok":{"type":"boolean"}},"required":["ok"],"additionalProperties":false}}\n');
    symlinkSync('real-shapes.json', join(repo, 'contracts/shapes.json'));
    put(repo, paths.A, prompt('a', ['shared.prompt.md'], 'draft', { $contract: 'contracts/shapes.json#/okResult' }));
  } else put(repo, paths.A, prompt('a', ['shared.prompt.md']));
  put(repo, paths.B, prompt('b', bDependencies, vector.id === 'partial-refusal' ? 'invalid' : 'draft'));
  put(repo, paths.shared, prompt('shared'));
  put(repo, paths.unrelated, prompt('unrelated'));

  if (vector.id === 'workspace-excluded-dependency') {
    put(repo, 'prompts/excluded.prompt.md', prompt('excluded'));
    put(repo, 'pdd-workspace.json', '{"allowed_paths":["user_stories/","test/","prompts/a.prompt.md","prompts/b.prompt.md","prompts/shared.prompt.md","prompts/unrelated.prompt.md"]}');
  }
  if (!vector.without_tests) {
    put(repo, paths.storyA, story('a'));
    put(repo, paths.storyB, story('b'));
    put(repo, paths.testA, scenario('a', paths.storyA, paths.A));
    put(repo, paths.testB, scenario('b', paths.storyB, paths.B));
  }
  if (['untested-mixed', 'unknown-lists-untested'].includes(vector.id)) put(repo, 'user_stories/untested.md', story('untested'));
  if (vector.id === 'malformed-selected') put(repo, paths.testB, '{');

  git(repo, 'init', '-q');
  git(repo, 'add', '-A');
  git(repo, '-c', 'user.email=test@example.com', '-c', 'user.name=Test', 'commit', '-qm', 'initial');
  const before = new Map();
  for (const path of [paths.A, paths.B, paths.shared, paths.unrelated, 'prompts/excluded.prompt.md', 'contracts/real-shapes.json']) {
    try { before.set(path, readFileSync(join(repo, path), 'utf8')); } catch (error) { if (error.code !== 'ENOENT') throw error; }
  }
  return { repo, home, before };
}

function verifyPromptBytes(state, vector) {
  const expected = new Set(vector.expected_filled ?? []);
  const changed = [];
  for (const [path, original] of state.before) {
    const actual = readFileSync(join(state.repo, path), 'utf8');
    if (expected.has(path)) {
      const filled = original.replace('"prose_sha256": ""', `"prose_sha256": "${proseSha256(original)}"`);
      assert.equal(actual, filled, `${vector.id}: only ${path}'s hash may change`);
      changed.push(path);
    } else assert.equal(actual, original, `${vector.id}: ${path} must be unchanged`);
  }
  assert.deepEqual(new Set(changed), expected, `${vector.id}: filled prompt paths`);
  for (const path of vector.unchanged ?? []) assert.equal(readFileSync(join(state.repo, path), 'utf8'), state.before.get(path), `${vector.id}: fixture unchanged ${path}`);
  if (vector.expected_writes === 0) assert.equal(changed.length, 0, `${vector.id}: no prompt hash writes`);
}

async function replay(vector, state) {
  const calls = { fetch: 0, gh: 0 };
  const stdout = sink(), stderr = sink();
  const cwd = vector.cwd ? join(state.repo, vector.cwd) : state.repo;
  const code = await runCheck({
    cwd,
    words: vector.words,
    options: { '--fill-hash': true, ...(vector.options ?? {}) },
  }, {
    env: { HOME: state.home, PDD_RUNTIME_URL: 'http://127.0.0.1:9' }, stdout, stderr,
    fetch: async () => { calls.fetch += 1; throw Error('fill hash must not use the network'); },
    gh: () => { calls.gh += 1; throw Error('fill hash must not use authentication'); },
  });
  return { code, stdout: stdout.text, stderr: stderr.text, calls };
}

// Story: user_stories/scoped-fill-hash.md. Replays the accepted matrix at the
// public check boundary. Each row gets a new tracked repository and no Runtime.
test('2935: scoped fill-hash replays its native cases without network or authentication', async t => {
  for (const vector of vectors.cases) {
    const state = setup(t, vector);
    const result = await replay(vector, state);
    assert.equal(result.code, vector.exit_code, `${vector.id}: ${result.stdout}${result.stderr}`);
    assert.deepEqual(result.calls, { fetch: 0, gh: 0 }, `${vector.id}: local only`);
    if (vector.exit_code !== 0) assert.ok(result.stdout || result.stderr, `${vector.id}: refusal is reported`);
    if (vector.stderr_includes) assert.ok(result.stderr.includes(vector.stderr_includes), `${vector.id}: stderr includes ${vector.stderr_includes} (got: ${result.stderr})`);
    if (vector.stdout_each) for (const path of vector.expected_filled) {
      assert.ok(result.stdout.includes(vector.stdout_each.replace('PATH', path)), `${vector.id}: reports ${path}`);
    }
    verifyPromptBytes(state, vector);
  }
});

// Exercise the installed command path too, using its actual Git discovery in a
// repository with no Story or test. The PATH has Git only, so no gh command can run.
test('2935: CLI fills an explicit prompt and its dependency without tests', t => {
  const vector = vectors.cases.find(item => item.id === 'explicit-prompt');
  const state = setup(t, vector), bin = join(dirname(state.repo), 'bin');
  mkdirSync(bin);
  const found = spawnSync('which', ['git'], { encoding: 'utf8' });
  assert.equal(found.status, 0, found.stderr);
  symlinkSync(found.stdout.trim(), join(bin, 'git'));
  const result = spawnSync(process.execPath, [cli, 'test', '--fill-hash', ...vector.words], {
    cwd: state.repo,
    encoding: 'utf8',
    input: '',
    timeout: 30000,
    env: { HOME: state.home, PATH: bin, PDD_RUNTIME_URL: 'http://127.0.0.1:9' },
  });
  assert.equal(result.error, undefined);
  assert.equal(result.signal, null);
  assert.equal(result.status, vector.exit_code, `${result.stdout}${result.stderr}`);
  assert.equal(result.stderr, '');
  verifyPromptBytes(state, vector);
});
