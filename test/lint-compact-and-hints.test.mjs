import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { runLocalLint } from '../src/core/lint/run-local-lint.mjs';
import { formatDiagnosticLine } from '../src/core/lint/diagnostics.mjs';
import { compileScenario } from '../src/scenario-compile.mjs';

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
  for (const op of ['==', '<', '>', 'lt', 'lte', 'gt', 'gte', 'integer_relation', 'includes_all']) {
    assert.ok(compiled.refusal.message.includes(op), `missing ${op} in ${compiled.refusal.message}`);
  }
});
