import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { proseSha256 } from '../src/runtime-preflight.mjs';
import { promptHeaderHash } from '../src/file-owner.mjs';
import { fakeRuntime, harbor, portsFor, sink } from './runtime-fake.mjs';

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
    // 1 + 4. Bloated 505-prose-line prompt owning a tiny src/calc.mjs that contains a TODO excuse comment
    // plus normal domain comments and string/regex literals that must NOT trigger false warnings.
    const filler = Array.from({ length: 500 }, (_, idx) =>
      `- Rule detail ${idx + 1}: double the supplied whole-number input deterministically without hidden side effects.`).join('\n');
    const bloatedProse = `# Calculator\n\nOwns \`src/calc.mjs\` and reads \`pdd.json\`.\n\n${filler}\n`;
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

    // 3. Bloated 22-step Story in user_stories/calc.md + tests/calc.json.
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
  assert.match(parsed.warnings[0], /Warning: oversized prompt: prompts\/calc\.prompt\.md has 504 prose lines \(limit: 500\)\./);
  assert.match(parsed.warnings[1], /Warning: misplaced prompt owner: prompts\/test\/calc-test\.prompt\.md claims \.github\/workflows\/ci\.yml, test\/calc\.test\.mjs, tsconfig\.json\./);
  assert.match(parsed.warnings[2], /Warning: oversized Story: user_stories\/calc\.md \(tests\/calc\.json\) has 22 scenario steps \(limit: 15\)\. Keep prompt scenarios focused on policy and authority boundaries and move multi-step state-machine or wire-protocol sequences to native tests \(RUNBOOK\.md §17, §18\)\./);
  assert.match(parsed.warnings[3], /Warning: excuse comment in src\/calc\.mjs:6 \(owned by prompts\/calc\.prompt\.md\): \/\/ TODO: handle edge case later/);

  // Scoped Story local lint catches the selected Story's warnings and omits unrelated misplaced prompts.
  const scoped = await runLint(['calc', '--json']);
  assert.equal(scoped.code, 0);
  const scopedJson = JSON.parse(scoped.out);
  assert.equal(scopedJson.warnings.length, 3);
  assert.ok(!scopedJson.warnings.some(line => line.includes('calc-test.prompt.md')));

  // Fix all 4 traps: remove the test-owning prompt, keep a normal 35-line prompt (even when prose bytes exceed tiny code bytes
  // and even when <details>Runtime interface</details> adds 520 schema lines!), trim Story to 3 steps, and remove TODO.
  const domainLines = Array.from({ length: 30 }, (_, idx) => `- Domain note ${idx + 1}: preserve exact signed integer doubling.`).join('\n');
  const conciseProse = `# Calculator\n\nOwns \`src/calc.mjs\` and reads \`pdd.json\`.\n\n## Domain decisions\n\n${domainLines}\n\n`;
  const bigSchemaProps = Object.fromEntries(Array.from({ length: 185 }, (_, idx) => [`f${idx}`, { type: 'integer' }]));
  const bigIface = {
    status: 'approved',
    prose_sha256: proseSha256(conciseProse),
    limits: { max_steps: 2, max_model_calls: 2 },
    entries: [{
      operation: 'calculate',
      input_schema: { type: 'object', required: ['x'], additionalProperties: false, properties: { x: { type: 'integer' }, ...bigSchemaProps } },
      result_schema: { type: 'object', required: ['y'], additionalProperties: false, properties: { y: { type: 'integer' } } },
    }],
  };
  const cleanPrompt = `${conciseProse}<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(bigIface, null, 2)}\n\`\`\`\n</details>\n`;
  assert.ok(cleanPrompt.split('\n').length > 550, 'total prompt file lines exceed 500 due to Runtime interface JSON');
  const cleanHash = promptHeaderHash(cleanPrompt);
  write(setup.repo, 'prompts/calc.prompt.md', cleanPrompt);
  write(setup.repo, 'src/calc.mjs', [
    `// Generated from prompts/calc.prompt.md (sha256: ${cleanHash}).`,
    'export const calculate = ({ x }) => ({ y: x * 2 });',
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

test('3295 elevated >1000-line prompt warning, >1000-line Story warning, preflight(), and pdd lint parity', async t => {
  const { findTests, preflight } = await import('../src/runtime-preflight.mjs');
  const { runCheck } = await import('../src/runtime-client.mjs');
  const setup = harbor(t, repo => {
    const elevatedBody = Array.from({ length: 1002 }, (_, idx) => `- Subsystem rule ${idx + 1}: enforce explicit authority checks.`).join('\n');
    const elevatedProse = `# Giant subsystem\n\nOwns \`src/giant.mjs\`.\n\n${elevatedBody}\n`;
    const giantPrompt = withApprovedInterface(elevatedProse, 'runGiant');
    write(repo, 'prompts/giant.prompt.md', giantPrompt);
    write(repo, 'src/giant.mjs', `// Generated from prompts/giant.prompt.md (sha256: ${promptHeaderHash(giantPrompt)}).\nexport const runGiant = ({ x }) => ({ y: x });\n`);
    write(repo, 'user_stories/giant.md', '# Giant\n\n## Acceptance criteria\n\n1. Returns x.\n');
    // Only 2 scenario steps, but > 1,000 lines of large fixture world JSON!
    const largeWorld = Object.fromEntries(Array.from({ length: 990 }, (_, idx) => [`record_${idx}`, `value_${idx}`]));
    write(repo, 'tests/giant.json', `${JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/giant.md',
      criteria: [{ id: 'AC1', text: 'Returns x.' }],
      initial_world: largeWorld,
      steps: [
        {
          step_id: 's1',
          entry_path: 'prompts/giant.prompt.md',
          operation: 'runGiant',
          input: { x: 1 },
          checks: [{ criterion_id: 'AC1', target: 'result', path: '/y', op: 'equals', value: 1 }],
        },
        {
          step_id: 's2',
          entry_path: 'prompts/giant.prompt.md',
          operation: 'runGiant',
          input: { x: 2 },
          checks: [{ criterion_id: 'AC1', target: 'result', path: '/y', op: 'equals', value: 2 }],
        },
      ],
    }, null, 2)}\n`);
  });

  // 1. preflight() emits both the elevated >1000-line prompt warning and the >1000-line Story warning.
  const found = findTests({ root: setup.repo });
  const pre = preflight({ root: setup.repo, found, selected: found.tests.filter(item => item.storyPath === 'user_stories/giant.md') });
  assert.ok(pre.warnings.some(line => /Warning: oversized prompt \(elevated\): prompts\/giant\.prompt\.md has 1006 prose lines \(limit: 500; elevated above 1000\)\./.test(line)), JSON.stringify(pre.warnings));
  assert.ok(pre.warnings.some(line => /Warning: oversized Story: user_stories\/giant\.md \(tests\/giant\.json\) has 1038 lines \(limit: 1000\)\./.test(line)), JSON.stringify(pre.warnings));

  // 2. Ordinary hosted `pdd lint` (not `--local`) surfaces the exact same non-blocking warnings with exit 0.
  const fake = await fakeRuntime(t, (entry, f) => ({
    status: 200,
    json: f.lint(entry.request.requestId, [{ path: 'prompts/giant.prompt.md', state: 'approved', admission_state: 'approved', interface: { calls: [] } }]),
  }));
  const jsonPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }).ports;
  assert.equal(await runCheck({ cwd: setup.repo, words: ['giant'], options: { '--lint': true, '--json': true } }, jsonPorts), 0, jsonPorts.stderr.text);
  const lintJson = JSON.parse(jsonPorts.stdout.text);
  assert.ok(lintJson.warnings.some(line => line.includes('Warning: oversized prompt (elevated): prompts/giant.prompt.md has 1006 prose lines')));
  assert.ok(lintJson.warnings.some(line => line.includes('Warning: oversized Story: user_stories/giant.md (tests/giant.json) has 1038 lines')));
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

test('strict boundary skips symlinks, ancestor symlinks, secret paths, and non-visible extra claims', async t => {
  const { symlinkSync } = await import('node:fs');
  const { mkdtempSync } = await import('node:fs');
  const { tmpdir } = await import('node:os');
  const { lintLocalHygiene } = await import('../src/runtime-preflight.mjs');

  const outside = mkdtempSync(join(tmpdir(), 'pdd-hygiene-outside-'));
  writeFileSync(join(outside, 'leak.mjs'), '// Generated from prompts/app.prompt.md.\n// TODO: OUTSIDE-SYMLINK-LEAK\n');
  mkdirSync(join(outside, 'nested'), { recursive: true });
  writeFileSync(join(outside, 'nested', 'mod.mjs'), '// Generated from prompts/app.prompt.md.\n// TODO: ANCESTOR-SYMLINK-LEAK\n');
  writeFileSync(join(outside, 'bindings.json'), JSON.stringify({
    schema_version: 'pdd.bindings.v1',
    modules: [{ module: 'test/bound-via-symlink.test.mjs', prompt: 'prompts/app.prompt.md' }],
  }));

  const setup = harbor(t, repo => {
    write(repo, 'prompts/app.prompt.md', withApprovedInterface(
      '# App\n\nOwns `src/app.mjs`, `src/unlisted.mjs`, `src/direct-link.mjs`, `src/ancestor-link/mod.mjs`, `secrets/key.mjs` and `test/unlisted.test.mjs`.\n\n',
      'runApp',
    ));
    write(repo, 'src/app.mjs', [
      '// Generated from prompts/app.prompt.md.',
      'export function runApp({ x }) { return { y: x }; }',
      '// padding so owned code exceeds prompt prose bytes cleanly without oversized warning: 01234567890123456789012345678901234567890123456789',
      '',
    ].join('\n'));
    write(repo, 'src/unlisted.mjs', '// Generated from prompts/app.prompt.md.\n// TODO: UNLISTED-DISK-LEAK\n');
    write(repo, 'secrets/key.mjs', '// Generated from prompts/app.prompt.md.\n// TODO: SECRET-PATH-LEAK\n');
    write(repo, '.env', '# TODO: DOTENV-SECRET-LEAK\n');
    symlinkSync(join(outside, 'leak.mjs'), join(repo, 'src/direct-link.mjs'));
    symlinkSync(join(outside, 'nested'), join(repo, 'src/ancestor-link'));
    symlinkSync(join(outside, 'bindings.json'), join(repo, 'pdd-bindings.json'));
  });

  // Pass explicit visible files list that omits src/unlisted.mjs while including secret and symlinked entries.
  const warnings = lintLocalHygiene({
    root: setup.repo,
    files: [
      '.env',
      'pdd-bindings.json',
      'prompts/app.prompt.md',
      'secrets/key.mjs',
      'src/ancestor-link/mod.mjs',
      'src/app.mjs',
      'src/direct-link.mjs',
    ],
  });

  const combined = warnings.join('\n');
  assert.equal(combined.includes('OUTSIDE-SYMLINK-LEAK'), false);
  assert.equal(combined.includes('ANCESTOR-SYMLINK-LEAK'), false);
  assert.equal(combined.includes('UNLISTED-DISK-LEAK'), false);
  assert.equal(combined.includes('SECRET-PATH-LEAK'), false);
  assert.equal(combined.includes('DOTENV-SECRET-LEAK'), false);
  assert.equal(combined.includes('bound-via-symlink'), false);
  // Name-only misplaced test claim is still reported without opening test/unlisted.test.mjs.
  assert.deepEqual(warnings, [
    'Warning: misplaced prompt owner: prompts/app.prompt.md claims test/unlisted.test.mjs. Prompts own production modules, not test suites, CI workflows or repository config files.',
  ]);
});

test('PR 1 prompt-before-code and opening-sentence config mentions avoid false positives while catching owned configs', async t => {
  const { lintLocalHygiene } = await import('../src/runtime-preflight.mjs');
  const setup = harbor(t, repo => {
    write(repo, 'pdd.json', '{"strict_approvals":false}\n');
    write(repo, 'package.json', '{"name":"demo"}\n');
    // PR 1: src/future.mjs does not exist on disk yet; long participle phrase reads pdd.json and package.json.
    write(repo, 'prompts/pr1.prompt.md', withApprovedInterface(
      '# Future module\n\nOwns `src/future.mjs`, reading repository strict approval flags, workspace ceiling settings and package metadata from `pdd.json` and `package.json`.\n\n',
      'futureOp',
    ));
    // Participle verbs loading / parsing / inspecting without tight character limit.
    write(repo, 'prompts/loader.prompt.md', withApprovedInterface(
      '# Loader\n\nOwns `src/loader.mjs` while loading default compiler flags and module resolution paths defined inside `tsconfig.json`.\n\n',
      'loadOp',
    ));
    write(repo, 'src/loader.mjs', '// Generated from prompts/loader.prompt.md.\nexport const loadOp = () => ({ y: 1 }); // padding 0123456789012345678901234567890123456789012345678901234567890123456789\n');
    // Sentence 1 claims ownership of tsconfig.json; Sentence 2 says "reads tsconfig.json" — must STILL warn!
    write(repo, 'prompts/sneaky.prompt.md', withApprovedInterface(
      '# Sneaky\n\nOwns `src/sneaky.mjs` and `tsconfig.json`. Later at runtime it reads `tsconfig.json`.\n\n',
      'sneakOp',
    ));
    write(repo, 'src/sneaky.mjs', '// Generated from prompts/sneaky.prompt.md.\nexport const sneakOp = () => ({ y: 2 }); // padding 012345678901234567890123456789012345678901234567890123456789\n');
    // Mixed clause: reads pdd.json, then owns src/mixed.mjs and jsconfig.json — must warn ONLY on jsconfig.json!
    write(repo, 'prompts/mixed.prompt.md', withApprovedInterface(
      '# Mixed\n\nReads `pdd.json` and owns `src/mixed.mjs` and `jsconfig.json`.\n\n',
      'mixOp',
    ));
    write(repo, 'src/mixed.mjs', '// Generated from prompts/mixed.prompt.md.\nexport const mixOp = () => ({ y: 3 }); // padding 012345678901234567890123456789012345678901234567890123456789\n');
  });

  const warnings = lintLocalHygiene({ root: setup.repo });
  assert.deepEqual(warnings, [
    'Warning: misplaced prompt owner: prompts/mixed.prompt.md claims jsconfig.json. Prompts own production modules, not test suites, CI workflows or repository config files.',
    'Warning: misplaced prompt owner: prompts/sneaky.prompt.md claims tsconfig.json. Prompts own production modules, not test suites, CI workflows or repository config files.',
  ]);
});

test('excuse comment lexer handles postfix ++/--/! before division, Rust lifetimes, and Go raw strings', async t => {
  const { lintLocalHygiene } = await import('../src/runtime-preflight.mjs');
  const setup = harbor(t, repo => {
    write(repo, 'prompts/polyglot.prompt.md', withApprovedInterface(
      '# Polyglot\n\nOwns `src/math.ts`, `src/slice.rs` and `src/path.go`.\n\n',
      'polyOp',
    ));
    write(repo, 'src/math.ts', [
      '// Generated from prompts/polyglot.prompt.md.',
      'export function compute(count: number, value: number | null, box: { return: number }) {',
      '  const ok = !/TODO/.test(String(count));',
      '  const tpl = `${count + 1} // TODO: inside template`;',
      '  const half = count++ / 2; // TODO: check overflow after increment',
      '  const quarter = count-- / 4; // FIXME: check underflow after decrement',
      '  const asserted = value! / 2; // HACK: remove non-null assertion',
      '  const prop = box.return / 2; // XXX: rename reserved property',
      '  return { ok, tpl, half, quarter, asserted, prop };',
      '}',
      '',
    ].join('\n'));
    write(repo, 'src/slice.rs', [
      '// Generated from prompts/polyglot.prompt.md.',
      'pub fn borrow<\'a>(input: &\'a str, fallback: &\'static str) -> char {',
      '    let raw = r#"// TODO: inside rust raw string"#;',
      '    let _ = (input, fallback, raw, \'\\\'\');',
      '    \'/\' // TODO: handle empty slice',
      '}',
      '',
    ].join('\n'));
    write(repo, 'src/path.go', [
      '// Generated from prompts/polyglot.prompt.md.',
      'package pathutil',
      'const winPrefix = `C:\\temp\\${not_js} // TODO: inside go raw string\\`',
      'func Normalize(n int) int { return n / 2 } // FIXME: normalize volume root',
      '',
    ].join('\n'));
  });

  const warnings = lintLocalHygiene({ root: setup.repo }).filter(line => line.startsWith('Warning: excuse comment'));
  assert.deepEqual(warnings, [
    'Warning: excuse comment in src/math.ts:5 (owned by prompts/polyglot.prompt.md): // TODO: check overflow after increment',
    'Warning: excuse comment in src/math.ts:6 (owned by prompts/polyglot.prompt.md): // FIXME: check underflow after decrement',
    'Warning: excuse comment in src/math.ts:7 (owned by prompts/polyglot.prompt.md): // HACK: remove non-null assertion',
    'Warning: excuse comment in src/math.ts:8 (owned by prompts/polyglot.prompt.md): // XXX: rename reserved property',
    'Warning: excuse comment in src/path.go:4 (owned by prompts/polyglot.prompt.md): // FIXME: normalize volume root',
    'Warning: excuse comment in src/slice.rs:5 (owned by prompts/polyglot.prompt.md): // TODO: handle empty slice',
  ]);
});

test('scoped local lint excludes unselected nested fixtures, preserves filename-matched storyPath, and ignores non-scenario JSON', async t => {
  const setup = harbor(t, repo => {
    const prompt = withApprovedInterface('# Draft calc\n\nOwns `src/calc.mjs`.\n\n');
    write(repo, 'prompts/calc.prompt.md', prompt);
    write(repo, 'src/calc.mjs', '// Generated from prompts/calc.prompt.md.\nexport const calculate = ({ x }) => ({ y: x * 2 }); // padding 0123456789012345678901234567890123456789\n');
    write(repo, 'user_stories/calc.md', '# Calculator\n\n## Acceptance criteria\n\n1. Doubling x returns 2x.\n');
    // Draft scenario test omits both schema_version and story_path; matched to user_stories/calc.md by filename!
    write(repo, 'tests/calc.json', JSON.stringify({
      criteria: [{ id: 'AC1', text: 'Doubling x returns 2x.' }],
      initial_world: {},
      steps: makeSteps(18),
    }, null, 2));
    // Non-scenario vector JSON matching calc.<variant>.json with a 25-item steps array — must NOT trigger oversized Story!
    write(repo, 'tests/calc.vectors.json', JSON.stringify({
      schema_version: 'custom.vectors.v1',
      steps: Array.from({ length: 25 }, (_, i) => ({ case: i })),
    }, null, 2));

    // Nested fixture project under test/fixtures/nested-app with traps (including claiming root src/calc.mjs!).
    write(repo, 'test/fixtures/nested-app/prompts/nested.prompt.md', withApprovedInterface(
      '# Nested fixture\n\nOwns `test/fixtures/nested-app/src/nested.mjs` and `test/nested.test.mjs`.\n\n',
      'nestedOp',
    ));
    write(repo, 'test/fixtures/nested-app/src/nested.mjs', '// TODO: inside nested fixture project\nexport {};\n');
    write(repo, 'test/fixtures/nested-app/user_stories/nested.md', '# Nested\n\n## Acceptance criteria\n\n1. Nested rule.\n');
    write(repo, 'test/fixtures/nested-app/tests/nested.json', JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'test/fixtures/nested-app/user_stories/nested.md',
      criteria: [{ id: 'AC1', text: 'Nested rule.' }],
      initial_world: {},
      steps: Array.from({ length: 20 }, (_, idx) => ({
        step_id: `n${idx + 1}`,
        entry_path: 'test/fixtures/nested-app/prompts/nested.prompt.md',
        operation: 'nestedOp',
        input: { x: 1 },
        checks: [{ criterion_id: 'AC1', target: 'result', path: '/y', op: 'equals', value: 2 }],
      })),
    }, null, 2));
  });

  const env = { HOME: setup.home, PDD_RUNTIME_URL: 'invalid', PDD_STATE_DIR: setup.state };
  const runLint = async (extra = []) => {
    const stdout = sink(), stderr = sink();
    const code = await runPdd(['lint', '--local', ...extra], { cwd: setup.repo, env, stdout, stderr });
    return { code, out: stdout.text, err: stderr.text };
  };

  // Unscoped local lint: excludes nested-app, ignores calc.vectors.json, and names user_stories/calc.md for calc.json.
  const unscoped = await runLint(['--json']);
  assert.equal(unscoped.code, 0, unscoped.err);
  const unscopedJson = JSON.parse(unscoped.out);
  assert.equal(unscopedJson.reason.code, 'local-only');
  assert.equal(unscopedJson.reason.message, 'checked SVG layout only; prompts not checked');
  assert.deepEqual(unscopedJson.warnings, [
    'Warning: oversized Story: user_stories/calc.md (tests/calc.json) has 18 scenario steps (limit: 15). Keep prompt scenarios focused on policy and authority boundaries and move multi-step state-machine or wire-protocol sequences to native tests (RUNBOOK.md §17, §18).',
  ]);

  // Scoped local lint on root Story calc: still excludes nested-app and preserves user_stories/calc.md!
  const scopedRoot = await runLint(['calc', '--json']);
  assert.equal(scopedRoot.code, 0, scopedRoot.err);
  const scopedRootJson = JSON.parse(scopedRoot.out);
  assert.deepEqual(scopedRootJson.warnings, [
    'Warning: oversized Story: user_stories/calc.md (tests/calc.json) has 18 scenario steps (limit: 15). Keep prompt scenarios focused on policy and authority boundaries and move multi-step state-machine or wire-protocol sequences to native tests (RUNBOOK.md §17, §18).',
  ]);

  // Explicitly selecting the nested fixture Story inspects that nested fixture root.
  const scopedFixture = await runLint(['test/fixtures/nested-app/user_stories/nested.md', '--json']);
  assert.equal(scopedFixture.code, 0, scopedFixture.err);
  const scopedFixtureJson = JSON.parse(scopedFixture.out);
  assert.ok(scopedFixtureJson.warnings.some(line => line.includes('test/fixtures/nested-app/user_stories/nested.md')));
  assert.ok(scopedFixtureJson.warnings.some(line => line.includes('test/fixtures/nested-app/src/nested.mjs:1')));
});


