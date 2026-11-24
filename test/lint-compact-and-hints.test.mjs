import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { runLocalLint } from '../src/core/lint/run-local-lint.mjs';
import { formatDiagnosticLine } from '../src/core/lint/diagnostics.mjs';
import { compileScenario } from '../src/scenario-compile.mjs';
import { lintSvgLayouts } from '../src/svg-layout.mjs';

const PDD_BIN = resolve(fileURLToPath(new URL('../bin/pdd.mjs', import.meta.url)));

function makeRepo(t, files) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-lint-compact-hints-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  for (const [rel, content] of Object.entries(files)) {
    const abs = join(root, rel);
    mkdirSync(join(abs, '..'), { recursive: true });
    writeFileSync(abs, content, 'utf8');
  }
  execFileSync('git', ['init', '-q'], { cwd: root });
  execFileSync('git', ['add', '-A'], { cwd: root });
  return root;
}

test('default pdd lint surfaces compact scenario compile errors (exit 1) and patch-null warnings offline', t => {
  const brokenRepo = makeRepo(t, {
    'prompts/app.prompt.md': '# App\n\nReturn `{ ok: true }` from `run()`.\n\n## Dependencies\n\nNone.\n',
    'user_stories/app.md': '# Run app\n\nAs a developer, I want to run the app, so that I see ok.\n\n## Acceptance criteria\n\n1. Running returns ok true.\n',
    'tests/app.json': JSON.stringify({
      entry_path: 'prompts/app.prompt.md',
      steps: [{ id: 's1', op: 'run', input: {}, checks: { '1': [['result', '/ok', 'bogus_op', true]] } }],
    }, null, 2),
  });
  const out1 = { text: '', write(s) { this.text += s; } };
  const err1 = { text: '', write(s) { this.text += s; } };
  const code1 = runLocalLint({ cwd: brokenRepo, json: true }, { stdout: out1, stderr: err1 });
  assert.equal(code1, 1);
  const parsed1 = JSON.parse(out1.text);
  assert.equal(parsed1.ok, false);
  assert.ok(parsed1.problems.some(p => p.includes('tests/app.json') && p.includes('compact scenario compile failed') && p.includes('bogus_op')), out1.text);

  const warnRepo = makeRepo(t, {
    'prompts/app.prompt.md': '# App\n\nReturn `{ ok: true }` from `run()`.\n\n## Dependencies\n\nNone.\n',
    'user_stories/app.md': '# Run app\n\nAs a developer, I want to run the app, so that I see ok.\n\n## Acceptance criteria\n\n1. Running returns ok true.\n',
    'tests/app.json': JSON.stringify({
      entry_path: 'prompts/app.prompt.md',
      seeds: { base: { note: 'hi' } },
      steps: [{ id: 's1', op: 'run', from: 'base', patch: { note: null }, checks: { '1': [['result', '/ok', '=', true]] } }],
    }, null, 2),
  });
  const out2 = { text: '', write(s) { this.text += s; } };
  const err2 = { text: '', write(s) { this.text += s; } };
  const code2 = runLocalLint({ cwd: warnRepo, json: true }, { stdout: out2, stderr: err2 });
  assert.equal(code2, 0);
  const parsed2 = JSON.parse(out2.text);
  assert.ok(parsed2.warnings.some(w => w.includes('tests/app.json') && w.includes('"patch" sets "note" to null')), out2.text);
});

test('diagnostics and scenario-compile error messages avoid fake repo-relative skill paths and list all valid operators', () => {
  const line = formatDiagnosticLine({
    category: 'Story hygiene',
    filePath: 'user_stories/demo.md',
    line: 5,
    code: 'story-missing-criteria',
    detail: 'Missing acceptance criteria.',
  }, 'error');
  assert.doesNotMatch(line, /skills\/pdd\/references\//);
  assert.match(line, /stories\.md/);

  const compiled = compileScenario({
    entry_path: 'prompts/app.prompt.md',
    steps: [{ id: 's1', op: 'run', input: {}, checks: { '1': [['result', '/n', 'bad_op', 1]] } }],
  });
  assert.ok(compiled.refusal);
  for (const op of ['==', '<', '>', 'lt', 'lte', 'gt', 'gte', 'length_at_least', 'length_at_most', 'integer_relation', 'includes_all']) {
    assert.ok(compiled.refusal.message.includes(op), `missing ${op} in ${compiled.refusal.message}`);
  }
});

test('scoped pdd lint catches Story/test compact errors, isolates sibling Stories on a shared prompt, ignores non-PDD test JSON, and avoids duplicate --local refusals', t => {
  const repo = makeRepo(t, {
    'prompts/shared.prompt.md': '# Shared\n\nReturn `{ ok: true }` from `run()`.\n\n## Dependencies\n\nNone.\n',
    'user_stories/clean-story.md': '# Clean\n\nAs a developer, I want clean checks, so that clean passes.\n\n## Acceptance criteria\n\n1. Running returns ok true.\n',
    'tests/clean-story.json': JSON.stringify({
      entry_path: 'prompts/shared.prompt.md',
      steps: [{ id: 's1', op: 'run', input: {}, checks: { '1': [['result', '/ok', '=', true]] } }],
    }, null, 2),
    'user_stories/broken-story.md': '# Broken\n\nAs a developer, I want errors caught, so that typos fail fast.\n\n## Acceptance criteria\n\n1. Running returns ok true.\n',
    'tests/broken-story.json': JSON.stringify({
      entry_paths: ['prompts/shared.prompt.md'],
      steps: [{ id: 's1', op: 'run', input: {}, checks: { '1': [['result', '/ok', 'bogus_op', true]] } }],
    }, null, 2),
    'user_stories/warn-story.md': '# Warn\n\nAs a developer, I want patch-null warnings, so that null deletion is visible.\n\n## Acceptance criteria\n\n1. Running returns ok true.\n',
    'tests/warn-story.json': JSON.stringify({
      entry_path: 'prompts/shared.prompt.md',
      seeds: { base: { note: 'hi' } },
      steps: [{ id: 's1', op: 'run', from: 'base', patch: { note: null }, checks: { '1': [['result', '/ok', '=', true]] } }],
    }, null, 2),
    'tests/pipeline.json': JSON.stringify({ steps: ['build', 'test'] }, null, 2),
  });

  // 1. Scoped `pdd lint broken-story` and `pdd lint tests/broken-story.json` exit 1 with 4-part error.
  for (const target of ['broken-story', 'tests/broken-story.json']) {
    const out = { text: '', write(s) { this.text += s; } };
    const err = { text: '', write(s) { this.text += s; } };
    const code = runLocalLint({ cwd: repo, words: [target], json: true }, { stdout: out, stderr: err });
    assert.equal(code, 1, `expected exit 1 for ${target}: ${out.text}`);
    const parsed = JSON.parse(out.text);
    assert.ok(parsed.problems.some(p => p.includes('tests/broken-story.json') && p.includes('compact-scenario-compile') && p.includes('Fix:') && p.includes('Rerun: pdd lint')), out.text);
  }

  // 2. Scoped `pdd lint clean-story` does NOT leak sibling broken-story error or warn-story warning on the shared prompt.
  const outClean = { text: '', write(s) { this.text += s; } };
  const errClean = { text: '', write(s) { this.text += s; } };
  const codeClean = runLocalLint({ cwd: repo, words: ['clean-story'], json: true }, { stdout: outClean, stderr: errClean });
  assert.equal(codeClean, 0, outClean.text);
  const parsedClean = JSON.parse(outClean.text);
  assert.deepEqual(parsedClean.problems, []);
  assert.equal(parsedClean.warnings.some(w => w.includes('warn-story') || w.includes('broken-story')), false, outClean.text);

  // 3. Non-PDD test data JSON (tests/pipeline.json) never causes a false-positive compile error.
  const nonPddRepo = makeRepo(t, {
    'prompts/app.prompt.md': '# App\n\nReturn `{ ok: true }` from `run()`.\n\n## Dependencies\n\nNone.\n',
    'tests/pipeline.json': JSON.stringify({ steps: ['build', 'test'] }, null, 2),
  });
  const outNonPdd = { text: '', write(s) { this.text += s; } };
  const errNonPdd = { text: '', write(s) { this.text += s; } };
  const codeNonPdd = runLocalLint({ cwd: nonPddRepo, json: true }, { stdout: outNonPdd, stderr: errNonPdd });
  assert.equal(codeNonPdd, 0, outNonPdd.text);
  assert.deepEqual(JSON.parse(outNonPdd.text).problems, []);

  // 4. `pdd lint --local` on clean-story isolates sibling warnings AND on broken-story emits only one refusal (no duplicate).
  const stateDir = mkdtempSync(join(tmpdir(), 'pdd-lint-state-'));
  const homeDir = mkdtempSync(join(tmpdir(), 'pdd-lint-home-'));
  t.after(() => {
    rmSync(stateDir, { recursive: true, force: true });
    rmSync(homeDir, { recursive: true, force: true });
  });
  const env = { ...process.env, HOME: homeDir, PDD_STATE_DIR: stateDir };
  const cleanLocal = spawnSync(process.execPath, [PDD_BIN, 'lint', '--local', '--json', 'clean-story'], { cwd: repo, encoding: 'utf8', env });
  assert.equal(cleanLocal.status, 0, cleanLocal.stderr);
  const cleanLocalJson = JSON.parse(cleanLocal.stdout);
  assert.equal(cleanLocalJson.warnings.some(w => w.includes('warn-story') || w.includes('broken-story')), false, cleanLocal.stdout);

  const brokenLocal = spawnSync(process.execPath, [PDD_BIN, 'lint', '--local', '--json', 'broken-story'], { cwd: repo, encoding: 'utf8', env });
  const brokenLocalJson = JSON.parse(brokenLocal.stdout);
  const brokenWarnings = (brokenLocalJson.warnings ?? []).filter(w => String(w).includes('bogus_op'));
  assert.equal(brokenWarnings.length, 1, `expected single warning without duplication, got: ${JSON.stringify(brokenWarnings)}`);
  assert.equal(brokenWarnings.some(w => w.includes('compact scenario compile failed')), false, `duplicate svg-layout refusal leaked into lint --local warnings: ${JSON.stringify(brokenWarnings)}`);

  // 5. Invalid app-map JSON hint mentions compact app-map.json.
  const badMapRepo = makeRepo(t, {
    'prompts/ui.prompt.md': '# UI\n\nRender screen.\n\n## Dependencies\n\nNone.\n',
    'app-map.json': '{ bad json',
  });
  const mapWarnings = lintSvgLayouts({ root: badMapRepo, files: ['prompts/ui.prompt.md', 'app-map.json'] });
  assert.ok(mapWarnings.some(w => w.includes('app-map.json') && w.includes('compact')), JSON.stringify(mapWarnings));
});
