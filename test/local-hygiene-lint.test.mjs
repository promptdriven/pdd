import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { proseSha256 } from '../src/runtime-preflight.mjs';
import { promptHeaderHash } from '../src/file-owner.mjs';
import { harbor, sink } from './runtime-fake.mjs';

const write = (repo, path, text) => {
  mkdirSync(dirname(join(repo, path)), { recursive: true });
  writeFileSync(join(repo, path), text);
};

function withApprovedInterface(prose, operation = 'calculate') {
  const hash = proseSha256(prose);
  const iface = {
    status: 'approved',
    prose_sha256: hash,
    limits: { max_steps: 2, max_model_calls: 2 },
    entries: [{
      operation,
      input_schema: { type: 'object', required: ['x'], additionalProperties: false, properties: { x: { type: 'integer' } } },
      result_schema: { type: 'object', required: ['y'], additionalProperties: false, properties: { y: { type: 'integer' } } },
    }],
  };
  return `${prose}<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(iface, null, 2)}\n\`\`\`\n</details>\n`;
}

function makeSteps(count) {
  return Array.from({ length: count }, (_, idx) => ({
    step_id: `s${idx + 1}`,
    entry_path: 'prompts/calc.prompt.md',
    operation: 'calculate',
    input: { x: idx + 1 },
    checks: [{ criterion_id: 'AC1', target: 'result', path: '/y', op: 'equals', value: (idx + 1) * 2 }],
  }));
}

test('local lint emits non-blocking warnings for all 4 hygiene traps and clears to 0 warnings once fixed', async t => {
  const setup = harbor(t, repo => {
    // 1 + 3. Bloated ~3,500-byte prompt owning a ~400-byte src/calc.mjs that contains a TODO excuse comment
    // plus normal domain comments and string/regex literals that must NOT trigger false warnings.
    const filler = Array.from({ length: 48 }, (_, idx) =>
      `- Rule detail ${idx + 1}: double the supplied whole-number input deterministically without hidden side effects.`).join('\n');
    const bloatedProse = `# Calculator\n\nOwns \`src/calc.mjs\` and reads \`pdd.json\`.\n\n${filler}\n\n`;
    const calcPrompt = withApprovedInterface(bloatedProse);
    const calcHash = promptHeaderHash(calcPrompt);
    write(repo, 'pdd.json', '{"strict_approvals":false}\n');
    write(repo, 'prompts/calc.prompt.md', calcPrompt);
    write(repo, 'src/calc.mjs', [
      `// Generated from prompts/calc.prompt.md (sha256: ${calcHash}).`,
      '// Domain invariant: integer doubling preserves exact sign and zero.',
      '// A skipped or todo test in TAP output is not an arithmetic input.',
      'const LITERAL = "// TODO: inside a string literal, not a comment";',
      'const PATTERN = /TODO|FIXME/;',
      '// TODO: handle edge case later',
      'export function calculate({ x }) { return { y: x * 2, tag: LITERAL.slice(0, 0), ok: !PATTERN.test("") }; }',
      '',
    ].join('\n'));

    // 2. Misplaced prompt claiming ownership of test/calc.test.mjs (plus config/CI claims).
    const testPrompt = withApprovedInterface('# Calculator tests\n\nOwns `test/calc.test.mjs`, `.github/workflows/ci.yml` and `tsconfig.json`.\n\n', 'verifyCalc');
    write(repo, 'prompts/test/calc-test.prompt.md', testPrompt);
    write(repo, 'test/calc.test.mjs', '// Generated from prompts/test/calc-test.prompt.md.\nexport {};\n');

    // 4. Bloated 22-step Story in user_stories/calc.md + tests/calc.json.
    write(repo, 'user_stories/calc.md', '# Calculator\n\n## Acceptance criteria\n\n1. Doubling x returns 2x.\n');
    write(repo, 'tests/calc.json', JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/calc.md',
      criteria: [{ id: 'AC1', text: 'Doubling x returns 2x.' }],
      initial_world: {},
      steps: makeSteps(22),
    }, null, 2));
  });

  const env = { HOME: setup.home, PDD_RUNTIME_URL: 'invalid', PDD_STATE_DIR: setup.state };
  const runLint = async (extra = []) => {
    const stdout = sink(), stderr = sink();
    const code = await runPdd(['lint', '--local', ...extra], { cwd: setup.repo, env, stdout, stderr });
    return { code, out: stdout.text, err: stderr.text };
  };

  const trapped = await runLint(['--json']);
  assert.equal(trapped.code, 0, `warnings must never block exit 0: ${trapped.err}`);
  const parsed = JSON.parse(trapped.out);
  assert.equal(parsed.exit_code, 0);
  assert.equal(parsed.warnings.length, 4, JSON.stringify(parsed.warnings, null, 2));
  assert.match(parsed.warnings[0], /Warning: oversized prompt: prompts\/calc\.prompt\.md has \d+ prose bytes vs \d+ code bytes \(src\/calc\.mjs\)\./);
  assert.match(parsed.warnings[1], /Warning: misplaced prompt owner: prompts\/test\/calc-test\.prompt\.md claims \.github\/workflows\/ci\.yml, test\/calc\.test\.mjs, tsconfig\.json\./);
  assert.match(parsed.warnings[2], /Warning: oversized Story: user_stories\/calc\.md \(tests\/calc\.json\) has 22 scenario steps \(limit: 15\)\./);
  assert.match(parsed.warnings[3], /Warning: excuse comment in src\/calc\.mjs:6 \(owned by prompts\/calc\.prompt\.md\): \/\/ TODO: handle edge case later/);

  // Scoped Story local lint catches the selected Story's warnings and omits unrelated misplaced prompts.
  const scoped = await runLint(['calc', '--json']);
  assert.equal(scoped.code, 0);
  const scopedJson = JSON.parse(scoped.out);
  assert.equal(scopedJson.warnings.length, 3);
  assert.ok(!scopedJson.warnings.some(line => line.includes('calc-test.prompt.md')));

  // Fix all 4 traps: remove the test-owning prompt, shrink prose below code size, trim Story to 3 steps, remove TODO.
  const conciseProse = '# Calculator\n\nOwns `src/calc.mjs` and reads `pdd.json`: return `{ y: x * 2 }`.\n\n';
  const cleanPrompt = withApprovedInterface(conciseProse);
  const cleanHash = promptHeaderHash(cleanPrompt);
  write(setup.repo, 'prompts/calc.prompt.md', cleanPrompt);
  write(setup.repo, 'src/calc.mjs', [
    `// Generated from prompts/calc.prompt.md (sha256: ${cleanHash}).`,
    '// Domain invariant: integer doubling preserves exact sign and zero across negative, zero and positive inputs.',
    'export function calculate({ x }) {',
    '  if (!Number.isSafeInteger(x)) throw new RangeError("x must be a safe integer");',
    '  return { y: x * 2 };',
    '}',
    '',
  ].join('\n'));
  const { execFileSync } = await import('node:child_process');
  execFileSync('git', ['rm', '-rf', '-q', 'prompts/test'], { cwd: setup.repo });
  write(setup.repo, 'test/calc.test.mjs', '// Plain native test without prompt ownership.\nexport {};\n');
  const trimmedDoc = JSON.parse(readFileSync(join(setup.repo, 'tests/calc.json'), 'utf8'));
  trimmedDoc.steps = makeSteps(3);
  write(setup.repo, 'tests/calc.json', JSON.stringify(trimmedDoc, null, 2));

  const clean = await runLint(['--json']);
  assert.equal(clean.code, 0, clean.err);
  const cleanJson = JSON.parse(clean.out);
  assert.deepEqual(cleanJson.warnings, []);
});

test('excuse comment scanner handles block comments, Python hash comments, and workspace path limits', async t => {
  const { lintLocalHygiene } = await import('../src/runtime-preflight.mjs');
  const setup = harbor(t, repo => {
    write(repo, 'prompts/worker.prompt.md', withApprovedInterface('# Worker\n\nOwns `src/worker.mjs` and `src/helper.py`.\n\n', 'work'));
    write(repo, 'src/worker.mjs', [
      '// Generated from prompts/worker.prompt.md.',
      '/* Normal block header explaining retry backoff math. */',
      '/*',
      ' * FIXME: replace busy spin with timer',
      ' */',
      'export const run = () => "// XXX not a comment"; // XXX: temporary fallback',
      '',
    ].join('\n'));
    write(repo, 'src/helper.py', [
      '#!/usr/bin/env python3',
      '# Generated from prompts/worker.prompt.md.',
      '"""# TODO: inside Python docstring literal"""',
      '# Ordinary note: values are normalized in UTC.',
      '# HACK: bypass locale parsing on older builds',
      'def normalize(x): return x',
      '',
    ].join('\n'));
    write(repo, 'private/secret.prompt.md', '# Secret\n\nOwns `private/secret.mjs`.\n');
    write(repo, 'private/secret.mjs', '// Generated from private/secret.prompt.md.\n// TODO: PRIVATE-SECRET-MARKER\n');
  });

  const warnings = lintLocalHygiene({
    root: setup.repo,
    workspace: { configured: true, allowed_paths: ['prompts/', 'src/', 'user_stories/', 'tests/'] },
  });
  assert.equal(JSON.stringify(warnings).includes('PRIVATE-SECRET-MARKER'), false);
  const excuseWarnings = warnings.filter(line => line.startsWith('Warning: excuse comment'));
  assert.deepEqual(excuseWarnings, [
    'Warning: excuse comment in src/helper.py:5 (owned by prompts/worker.prompt.md): # HACK: bypass locale parsing on older builds',
    'Warning: excuse comment in src/worker.mjs:4 (owned by prompts/worker.prompt.md): * FIXME: replace busy spin with timer',
    'Warning: excuse comment in src/worker.mjs:6 (owned by prompts/worker.prompt.md): // XXX: temporary fallback',
  ]);
});

