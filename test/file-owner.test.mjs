import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { execFileSync } from 'node:child_process';
import {
  headerPrompts,
  headerEntries,
  headerHashState,
  promptHeaderHash,
  moduleContentHash,
  updateHeaderHash,
  promptClaims,
  isTestOwnedPath,
  isTestPromptPath,
  resolveOwners,
  findOwners,
  findTestPromptViolations,
  runOwner,
} from '../src/file-owner.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

const HEX = 'a'.repeat(64), CUT = '// Generated from prompts/cut.prompt.md';
const capture = () => ({ text: '', write(value) { this.text += value; } });
function repo(t, files) {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-owner-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q'], { cwd: root });
  for (const [path, text] of Object.entries(files)) {
    mkdirSync(dirname(join(root, path)), { recursive: true });
    writeFileSync(join(root, path), text);
  }
  return root;
}
const row = (path, owners, source, certain, note = '') => ({ path, owner: owners[0] ?? null, owners, source, certain, note });
const plain = files => files.map(({ headers, ...rest }) => rest);
const sha = text => createHash('sha256').update(text).digest('hex');
const asDraft = text => text.replace('"status": "approved"', '"status": "draft"').replace(/("prose_sha256": )"[a-f0-9]{64}"/, '$1""');

test('3200/S2 headerPrompts reads every strict header form (including MDX and YAML frontmatter) in the first 4 KiB', () => {
  const late = `#!/usr/bin/env node\n${'// line\n'.repeat(10)}// Generated from prompts/cli/late.prompt.md (sha256: ${HEX}).\n`;
  assert.deepEqual(headerPrompts(late), ['prompts/cli/late.prompt.md']);
  assert.deepEqual(headerPrompts(Buffer.from(late)), ['prompts/cli/late.prompt.md'], 'bytes and strings read the same');
  const forms = [
    '# Generated from prompts/a.prompt.md.',
    '"""Generated from prompts/b.prompt.md."""',
    '<!-- Generated from prompts/c.prompt.md -->',
    ' * Generated from prompts/d.prompt.md',
    '// Prompt: prompts/e.prompt.md',
    `# Prompt: prompts/f.prompt.md sha256=${HEX}`,
    '{/* Prompt: prompts/g.prompt.md */}',
    `{/* Generated from prompts/h.prompt.md (sha256: ${HEX}) */}`,
    '// Generated from prompts/a.prompt.md.',
  ].join('\n');
  assert.deepEqual(headerPrompts(forms), [
    'prompts/a.prompt.md', 'prompts/b.prompt.md', 'prompts/c.prompt.md', 'prompts/d.prompt.md',
    'prompts/e.prompt.md', 'prompts/f.prompt.md', 'prompts/g.prompt.md', 'prompts/h.prompt.md',
  ], 'line order, no duplicates');
  assert.deepEqual(headerPrompts('---\ntitle: Docs\nprompt: prompts/page.prompt.md\n---\n# Hello\n'), ['prompts/page.prompt.md']);
  assert.deepEqual(headerPrompts(`${' '.repeat(4100)}\n// Generated from prompts/far.prompt.md.\n`), [], 'a header after 4 KiB is not read');
  assert.deepEqual(headerPrompts(`${' '.repeat(4096 - CUT.length - 1)}\n${CUT} (sha256: ${HEX}).\n`), [], 'a line cut by the window is not read');
  assert.deepEqual(headerPrompts([
    'Generated from the canonical m1_policy prompt.',
    'Prompt: prompts/not-a-comment.prompt.md',
    'const x = "Generated from prompts/s.prompt.md.";',
    '// see Generated from prompts/t.prompt.md for details',
    '// Generated from ../outside.prompt.md.',
    '// Generated from /abs/x.prompt.md.',
    '// Generated from prompts/.git/x.prompt.md.',
    `// Generated from prompts/${'y'.repeat(1100)}.prompt.md.`,
    '// Generated from prompts/x.md.',
  ].join('\n')), []);
  assert.deepEqual(headerPrompts(null), []);
  assert.deepEqual(headerPrompts(undefined), []);
});

test('3200 promptClaims reads only the first sentence of the opening paragraph', () => {
  const prompt = '# Queue\n\nOwn `src/queue.mjs` and the entry\n`scripts/run.sh`, and the adapter src/adapter.mjs. It reads `pdd.json`.\n\n## Rules\n\nOwn `src/later.mjs`.\n';
  assert.deepEqual(promptClaims('prompts/cli/queue.prompt.md', prompt), ['scripts/run.sh', 'src/adapter.mjs', 'src/queue.mjs']);
  assert.deepEqual(
    promptClaims('prompts/cli/x.prompt.md', '# X\n\n`src/x.mjs` exports `run(input, ports)` for the [Y rules](y.prompt.md), see [doc](../../docs/x.md#top). More.\n'),
    ['docs/x.md', 'src/x.mjs'],
    'links resolve against the prompt folder; prompts are not claims',
  );
  assert.deepEqual(promptClaims('prompts/a.prompt.md', '# A\n\n## Purpose\n\nOwn `src/a.mjs`.\n'), [], 'no opening paragraph');
  assert.deepEqual(promptClaims('prompts/a.prompt.md', '# A\n\nOwn `src/a.mjs` with `x. y` notes and `src/c.mjs`. Own `src/b.mjs`.\n'), ['src/a.mjs', 'src/c.mjs']);
  assert.deepEqual(promptClaims('prompts/a.prompt.md', null), []);
});

test('S2 honest resolveOwners: only binding and header claim ownership; prose/path become advisory notes', () => {
  const prompts = ['a', 'b', 'c'].map(name => ({ path: `prompts/${name}.prompt.md`, content: `# ${name}\n\nOwn \`src/${name}.mjs\` and \`src/shared.mjs\`.\n` }));
  const bindings = JSON.stringify({
    schema_version: 'pdd.bindings.v1',
    modules: [
      { module: 'src/bound.mjs', stories: ['user_stories/s.md'], prompt: 'prompts/a.prompt.md' },
      { module: 'src/both.mjs', stories: ['user_stories/s.md'], prompt: 'prompts/a.prompt.md' },
      { module: 'src/unbound.mjs', stories: ['user_stories/s.md'], reason: 'device', port_attempt: 'tried' },
      { module: 'src/gone.mjs', stories: ['user_stories/s.md'], prompt: 'prompts/gone.prompt.md' },
      'junk',
    ],
  });
  const heads = [
    { path: 'src/b.mjs', content: '// Generated from prompts/b.prompt.md.\n' },
    { path: 'src/both.mjs', content: '// Generated from prompts/b.prompt.md.\n// Generated from prompts/a.prompt.md.\n' },
    { path: 'src/two.mjs', content: '// Generated from prompts/c.prompt.md.\n# Generated from prompts/b.prompt.md.\n' },
    { path: 'src/dangling.mjs', content: '// Generated from prompts/none.prompt.md.\n' },
    { path: 'src/c.mjs', content: false },
  ];
  const paths = [
    'src/bound.mjs', 'src/b.mjs', 'src/both.mjs', 'src/two.mjs', 'src/a.mjs', 'src/shared.mjs',
    'src/dangling.mjs', 'src/gone.mjs', 'src/unbound.mjs', 'src/c.mjs', 'docs/x.md', 'src/b.mjs',
  ];
  const result = resolveOwners({ paths, bindings, heads, prompts });
  assert.equal(result.schema_version, 'pdd.owner.v1');
  const proseNote = names => `named only in the opening sentence of ${names}; add a // Prompt: header or a pdd-bindings.json entry`;
  assert.deepEqual(plain(result.files), [
    row('src/bound.mjs', ['prompts/a.prompt.md'], 'binding', true),
    row('src/b.mjs', ['prompts/b.prompt.md'], 'header', true),
    row('src/both.mjs', ['prompts/a.prompt.md', 'prompts/b.prompt.md'], 'binding', true),
    row('src/two.mjs', ['prompts/c.prompt.md', 'prompts/b.prompt.md'], 'header', true),
    row('src/a.mjs', [], null, true, proseNote('prompts/a.prompt.md')),
    row('src/shared.mjs', [], null, true, proseNote('prompts/a.prompt.md, prompts/b.prompt.md, prompts/c.prompt.md')),
    row('src/dangling.mjs', ['prompts/none.prompt.md'], 'header', false, 'names prompts/none.prompt.md, which is not a Git-visible prompt'),
    row('src/gone.mjs', ['prompts/gone.prompt.md'], 'binding', false, 'names prompts/gone.prompt.md, which is not a Git-visible prompt'),
    row('src/unbound.mjs', [], 'binding', true, 'pdd-bindings.json declares it with no prompt'),
    row('src/c.mjs', [], null, false, 'the file could not be read, so a header may be missing'),
    row('docs/x.md', [], null, true),
  ]);
  for (const bad of ['{', JSON.stringify({ schema_version: 'pdd.bindings.v2', modules: [] }), JSON.stringify({ schema_version: 'pdd.bindings.v1' }), false]) {
    const [unowned, headed] = plain(resolveOwners({ paths: ['docs/x.md', 'src/b.mjs'], bindings: bad, heads, prompts }).files);
    assert.deepEqual(unowned, row('docs/x.md', [], null, false, 'pdd-bindings.json could not be read, so a binding may be missing'), String(bad));
    assert.deepEqual(headed, row('src/b.mjs', ['prompts/b.prompt.md'], 'header', true), 'a header owner stays certain');
  }
  assert.deepEqual(
    plain(resolveOwners({ paths: ['src/c.mjs'], bindings: null, heads: [{ path: 'src/c.mjs', content: false }], prompts: [] }).files),
    [row('src/c.mjs', [], null, false, 'the file could not be read, so a header may be missing')],
  );
});

test('3200/S2 findOwners reads the working tree, enforces Git visibility on pdd-bindings.json, and detects >64 KiB truncation', t => {
  const cutHeader = '// Generated from prompts/cut-header.prompt.md';
  const root = repo(t, {
    'pdd-bindings.json': JSON.stringify({ schema_version: 'pdd.bindings.v1', modules: [{ module: 'src/bound.mjs', stories: ['user_stories/s.md'], prompt: 'prompts/bound.prompt.md' }] }),
    'prompts/bound.prompt.md': '# Bound\n',
    'prompts/new.prompt.md': '# New\n\nOwn `src/new.mjs`.\n',
    'prompts/late.prompt.md': '# Late\n',
    'src/late.mjs': `${'// license\n'.repeat(11)}// Generated from prompts/late.prompt.md (sha256: ${HEX}).\nexport const x = 1;\n`,
    'src/bound.mjs': 'export {};\n',
    'prompts/cut-header.prompt.md': '# Cut\n',
    'src/cut.mjs': `${' '.repeat(4096 - cutHeader.length - 1)}\n${cutHeader} (sha256: ${HEX}).\n`,
  });
  const result = findOwners({ root, paths: ['src/late.mjs', 'src/bound.mjs', 'src/new.mjs', 'README.md', 'src/cut.mjs'] });
  assert.deepEqual(result.files.map(({ path, owner, source, certain }) => [path, owner, source, certain]), [
    ['src/late.mjs', 'prompts/late.prompt.md', 'header', true],
    ['src/bound.mjs', 'prompts/bound.prompt.md', 'binding', true],
    ['src/new.mjs', null, null, true],
    ['README.md', null, null, true],
    ['src/cut.mjs', null, null, true],
  ]);
  assert.match(result.files[2].note, /add a \/\/ Prompt: header/);

  // Bug 3 fix: bindings read requests PROMPT + 1 = 65537 bytes so >64 KiB files trigger truncation failure.
  const reads = [];
  findOwners(
    { root, paths: ['src/late.mjs'] },
    {
      files: () => ['prompts/late.prompt.md', 'src/late.mjs', 'pdd-bindings.json'],
      read: (path, limit) => { reads.push([path, limit]); return null; },
    },
  );
  assert.deepEqual(reads.sort(), [['pdd-bindings.json', 65537], ['prompts/late.prompt.md', 10 * 1024 * 1024 + 1], ['src/late.mjs', 4097]]);

  const bigBindings = Buffer.alloc(65537, ' ');
  const truncated = findOwners(
    { root, paths: ['README.md'] },
    {
      files: () => ['pdd-bindings.json', 'README.md'],
      read: path => (path === 'pdd-bindings.json' ? bigBindings : null),
    },
  );
  assert.equal(truncated.files[0].certain, false);
  assert.match(truncated.files[0].note, /pdd-bindings\.json could not be read/);

  // Bug 2 fix: gitignored pdd-bindings.json is ignored consistently across findOwners.
  const ignoredRoot = repo(t, {
    '.gitignore': 'pdd-bindings.json\n',
    'pdd-bindings.json': JSON.stringify({ schema_version: 'pdd.bindings.v1', modules: [{ module: 'src/a.mjs', stories: [], prompt: 'prompts/a.prompt.md' }] }),
    'prompts/a.prompt.md': '# A\n',
    'src/a.mjs': 'export {};\n',
  });
  assert.equal(findOwners({ root: ignoredRoot, paths: ['src/a.mjs'] }).files[0].owner, null);
});

test('3200/S2 pdd owner prints honest text and JSON answers and refuses paths outside the repository', async t => {
  const root = repo(t, {
    'prompts/a.prompt.md': '# A\n\nOwn `src/a.mjs`.\n',
    'prompts/b.prompt.md': '# B\n',
    'src/b.mjs': '#!/usr/bin/env node\n// Generated from prompts/b.prompt.md.\n',
    'src/a.mjs': 'export {};\n',
  });
  const run = async (argv, cwd = root) => {
    const stdout = capture(), stderr = capture();
    const code = await runPdd(argv, { stdout, stderr, cwd });
    return { code, out: stdout.text, err: stderr.text };
  };
  const text = await run(['owner', 'src/b.mjs', 'src/a.mjs', 'docs/none.md']);
  assert.equal(text.code, 0, text.err);
  assert.equal(text.out, [
    'src/b.mjs: prompts/b.prompt.md (header)',
    'src/a.mjs: no owner',
    '  named only in the opening sentence of prompts/a.prompt.md; add a // Prompt: header or a pdd-bindings.json entry',
    'docs/none.md: no owner',
    '',
  ].join('\n'));
  const json = await run(['owner', 'b.mjs', '--json'], join(root, 'src'));
  assert.equal(json.code, 0, json.err);
  const answer = JSON.parse(json.out);
  assert.equal(answer.schema_version, 'pdd.owner.v1');
  assert.deepEqual(plain(answer.files), [row('src/b.mjs', ['prompts/b.prompt.md'], 'header', true)]);
  assert.deepEqual(answer.files[0].headers, [{ prompt: 'prompts/b.prompt.md', sha256: null, expected: promptHeaderHash('# B\n'), state: 'none', legacy: false }]);
  for (const argv of [['owner', '../outside.mjs'], ['owner', '.'], ['owner', join(tmpdir(), 'x.mjs')]]) {
    const refused = await run(argv);
    assert.equal(refused.code, 2, argv.join(' '));
    assert.equal(refused.out, '');
    assert.equal(refused.err, `${argv[1]} is not a file path inside this repository.\n`);
  }
  assert.equal((await run(['owner'])).code, 2, 'PATH is required');
  const outside = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-owner-none-')));
  t.after(() => rmSync(outside, { recursive: true, force: true }));
  const none = await run(['owner', 'x.mjs'], outside);
  assert.deepEqual([none.code, none.out, none.err], [2, '', 'pdd owner works inside a Git repository.\n']);
});

test('3200 header hash: approval metadata and JSON spacing do not count; prose and interface declarations do', () => {
  const approved = readFileSync(new URL('./fixtures/harbor/prompts/place_order.prompt.md', import.meta.url), 'utf8'), draft = asDraft(approved);
  assert.notEqual(draft, approved);
  const hash = promptHeaderHash(draft);
  assert.match(hash, /^[a-f0-9]{64}$/);
  assert.equal(promptHeaderHash(approved), hash, 'status and prose_sha256 are approval metadata');
  assert.equal(promptHeaderHash(Buffer.from(approved)), hash, 'bytes and strings hash the same');
  const block = /```json\n([\s\S]*?)\n```/.exec(approved)[1];
  assert.equal(promptHeaderHash(approved.replace(block, JSON.stringify(JSON.parse(block)))), hash, 'interface JSON white space does not count');
  assert.notEqual(promptHeaderHash(approved.replace('in whole cents.', 'in cents.')), hash, 'a prose change counts');
  assert.notEqual(promptHeaderHash(approved.replace('"maximum": 20', '"maximum": 30')), hash, 'an interface entry change counts');
  assert.notEqual(promptHeaderHash(approved.replace('"status": "approved",', '"status": "approved", "kind": "partial",')), hash, 'other interface fields count');
  assert.equal(promptHeaderHash('# No interface\n\nOwn `src/x.mjs`.\n'), sha('# No interface\n\nOwn `src/x.mjs`.\n'));
  assert.deepEqual(headerHashState(hash, approved), { expected: hash, state: 'current', legacy: false });
  assert.deepEqual(headerHashState(sha(approved), approved), { expected: hash, state: 'current', legacy: true });
  assert.deepEqual(headerHashState(sha(draft), approved), { expected: hash, state: 'stale', legacy: false });
  assert.deepEqual(headerHashState(null, approved), { expected: hash, state: 'none', legacy: false });
  assert.deepEqual(headerHashState(hash, null), { expected: null, state: 'unknown', legacy: false });
  assert.deepEqual(
    headerEntries(`// Generated from prompts/a.prompt.md (sha256: ${HEX}).\n// Prompt: prompts/b.prompt.md\n# Prompt: prompts/c.prompt.md sha256=${HEX}\n// Generated from prompts/a.prompt.md.\n`),
    [{ prompt: 'prompts/a.prompt.md', sha256: HEX }, { prompt: 'prompts/b.prompt.md', sha256: null }, { prompt: 'prompts/c.prompt.md', sha256: HEX }],
  );
});

test('3200 pdd owner shows each header hash that is not current', async t => {
  const prompt = '# A\n\nOwn `src/a.mjs`.\n', hash = promptHeaderHash(prompt);
  const root = repo(t, {
    'prompts/a.prompt.md': prompt,
    'src/ok.mjs': `// Prompt: prompts/a.prompt.md sha256=${hash}\n`,
    'src/stale.mjs': `// Generated from prompts/a.prompt.md (sha256: ${HEX}).\n`,
    'src/bare.mjs': '// Prompt: prompts/a.prompt.md\n',
    'src/gone.mjs': `// Generated from prompts/gone.prompt.md (sha256: ${HEX}).\n`,
  });
  const stdout = capture(), stderr = capture();
  assert.equal(await runPdd(['owner', 'src/ok.mjs', 'src/stale.mjs', 'src/bare.mjs', 'src/gone.mjs'], { stdout, stderr, cwd: root }), 0, stderr.text);
  assert.equal(stdout.text, [
    'src/ok.mjs: prompts/a.prompt.md (header)',
    'src/stale.mjs: prompts/a.prompt.md (header)',
    `  prompts/a.prompt.md header hash is stale (${HEX}); current is ${hash}`,
    'src/bare.mjs: prompts/a.prompt.md (header)',
    'src/gone.mjs: prompts/gone.prompt.md (header, not certain: treat as owned)',
    '  names prompts/gone.prompt.md, which is not a Git-visible prompt',
    '',
  ].join('\n'));
  const json = capture();
  await runPdd(['owner', 'src/stale.mjs', '--json'], { stdout: json, stderr, cwd: root });
  assert.deepEqual(JSON.parse(json.text).files[0].headers, [{ prompt: 'prompts/a.prompt.md', sha256: HEX, expected: hash, state: 'stale', legacy: false }]);
});

test('3295/S2 test-prompt detection, mixed-owner bug fix, and non-blocking warnings on stderr', async t => {
  assert.equal(isTestPromptPath('prompts/tests/foo.prompt.md'), true);
  assert.equal(isTestPromptPath('prompts/foo.test.prompt.md'), true);
  assert.equal(isTestPromptPath('test/foo.prompt.md'), true);
  assert.equal(isTestPromptPath('test/fixtures/foo.prompt.md'), false);
  assert.equal(isTestPromptPath('prompts/cli/foo.prompt.md'), false);

  const root = repo(t, {
    'pdd-bindings.json': JSON.stringify({
      schema_version: 'pdd.bindings.v1',
      modules: [
        { module: 'test/bound.e2e.mjs', stories: ['user_stories/s.md'], prompt: 'prompts/bound.prompt.md' },
        { module: 'test/mixed.test.mjs', stories: ['user_stories/s.md'], prompt: 'prompts/tests/bad.prompt.md' },
      ],
    }),
    'prompts/prod.prompt.md': '# Prod\n\nOwn `src/prod.mjs`.\n',
    'prompts/clean.prompt.md': '# Clean\n\nOwn `src/clean.mjs`.\n',
    'prompts/bound.prompt.md': '# Bound test\n\nVerify suite.\n',
    'prompts/header.prompt.md': '# Header test\n\nVerify suite.\n',
    'prompts/prose.prompt.md': '# Prose test\n\nOwn `src/unit.test.mjs`.\n',
    'prompts/tests/bad.prompt.md': '# Bad test prompt\n',
    'src/prod.mjs': '// Prompt: prompts/prod.prompt.md\n',
    'test/bound.e2e.mjs': 'export {};\n',
    'tests/header.mjs': '// Prompt: prompts/header.prompt.md\n',
    'test/mixed.test.mjs': '// Prompt: prompts/prod.prompt.md\n',
    'src/unit.test.mjs': 'export {};\n',
  });
  const run = async argv => {
    const stdout = capture(), stderr = capture();
    const code = await runPdd(argv, { stdout, stderr, cwd: root });
    return { code, out: stdout.text, err: stderr.text };
  };

  // Production modules stay silent on stderr.
  const prod = await run(['owner', 'src/prod.mjs']);
  assert.equal(prod.code, 0);
  assert.equal(prod.err, '');

  // Explicit binding/header ownership of test files warns on stderr with exit 0.
  const text = await run(['owner', 'test/bound.e2e.mjs', 'tests/header.mjs']);
  assert.equal(text.code, 0);
  assert.match(text.err, /Warning: misplaced prompt owner: test\/bound\.e2e\.mjs is claimed by prompts\/bound\.prompt\.md \(binding\)/);
  assert.match(text.err, /Warning: misplaced prompt owner: tests\/header\.mjs is claimed by prompts\/header\.prompt\.md \(header\)/);

  // Querying a test prompt directly fails with exit 1.
  const badPrompt = await run(['owner', 'prompts/tests/bad.prompt.md']);
  assert.equal(badPrompt.code, 1);
  assert.match(badPrompt.err, /Error: misplaced test prompt: prompts\/tests\/bad\.prompt\.md/);

  // Bug 1 fix: mixed owners on a test file emit BOTH test-prompt-path and ordinary misplaced-owner diagnostics!
  const violations = findTestPromptViolations({ root, checkPaths: ['test/mixed.test.mjs'] });
  assert.equal(violations.ok, false);
  assert.equal(violations.violations.length, 2);
  assert.ok(violations.violations.some(v => v.message.includes('prompts/tests/bad.prompt.md')));
  assert.ok(violations.violations.some(v => v.message.includes('prompts/prod.prompt.md')));

  // Querying a prompt path that mentions test files in prose warns on stderr; a clean prompt stays silent.
  const byPrompt = await run(['owner', 'prompts/prose.prompt.md', 'prompts/clean.prompt.md']);
  assert.equal(byPrompt.code, 0);
  assert.equal(byPrompt.err, 'Warning: misplaced prompt owner: prompts/prose.prompt.md claims src/unit.test.mjs. Prompts own production modules, not test files.\n');
});

test('3295 isTestOwnedPath requires canonicalPath and runOwner never opens non-visible or symlinked test claims', async t => {
  for (const bad of ['../outside.test.mjs', '/tmp/secret.test.mjs', 'test/../../outside.mjs', '.git/hooks/pre-commit.test.sh', 'prompts/foo.prompt.md', '']) {
    assert.equal(isTestOwnedPath(bad), false, `must reject non-canonical or prompt path: ${bad}`);
  }
  assert.equal(isTestOwnedPath('test/ok.test.mjs'), true);

  const outside = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-owner-outside-')));
  t.after(() => rmSync(outside, { recursive: true, force: true }));
  writeFileSync(join(outside, 'outside.test.mjs'), '// Generated from prompts/leak.prompt.md.\n');

  const root = repo(t, {
    '.gitignore': 'test/ignored.test.mjs\n',
    'pdd-bindings.json': JSON.stringify({
      schema_version: 'pdd.bindings.v1',
      modules: [
        { module: '../outside.test.mjs', stories: ['user_stories/s.md'], prompt: 'prompts/bound.prompt.md' },
        { module: 'test/ignored.test.mjs', stories: ['user_stories/s.md'], prompt: 'prompts/bound.prompt.md' },
        { module: 'test/link.test.mjs', stories: ['user_stories/s.md'], prompt: 'prompts/bound.prompt.md' },
      ],
    }),
    'prompts/bound.prompt.md': '# Bound\n\nOwn `test/prose-absent.test.mjs`.\n',
    'prompts/leak.prompt.md': '# Leak\n\nVerify nothing.\n',
    'test/ignored.test.mjs': '// Generated from prompts/leak.prompt.md.\n',
  });
  symlinkSync(join(outside, 'outside.test.mjs'), join(root, 'test/link.test.mjs'));

  const stdout = capture(), stderr = capture();
  const code = await runPdd(['owner', 'prompts/bound.prompt.md', 'prompts/leak.prompt.md'], { stdout, stderr, cwd: root });
  assert.equal(code, 0);
  assert.equal(stderr.text, 'Warning: misplaced prompt owner: prompts/bound.prompt.md claims test/ignored.test.mjs, test/link.test.mjs, test/prose-absent.test.mjs. Prompts own production modules, not test files.\n');
});

test('S2 mirrored path/stem matches produce advisory notes without claiming ownership', t => {
  const root = repo(t, {
    'prompts/cli/verify-token.prompt.md': '# Verify token\n\nChecks bearer tokens.\n',
    'src/verify-token.mjs': 'export const verifyToken = () => true;\n',
    'prompts/index.prompt.md': '# Index\n',
    'src/a/index.mjs': 'export const a = 1;\n',
    'src/b/index.mjs': 'export const b = 2;\n',
  });
  const res = findOwners({ root, paths: ['src/verify-token.mjs', 'src/a/index.mjs'] });
  assert.deepEqual(plain(res.files), [
    row('src/verify-token.mjs', [], null, true, 'matched by file name to prompts/cli/verify-token.prompt.md; add a // Prompt: header or a pdd-bindings.json entry'),
    row('src/a/index.mjs', [], null, true),
  ]);
});

test('3447/3203 per-module derived hashes, header refresh, and linear-time header regex', () => {
  const promptBase = '# Widget\n\nOwn `src/a.mjs`.\n';
  const baseHash = promptHeaderHash(promptBase);

  const bare = '// Generated from prompts/widget.prompt.md.\nexport const x = 1;\n';
  const hashed1 = `// Generated from prompts/widget.prompt.md (sha256: ${HEX}).\nexport const x = 1;\n`;
  const hashed2 = `\uFEFF// Generated from prompts/widget.prompt.md (sha256: ${baseHash}).\r\nexport const x = 1;\r\n`;
  assert.equal(moduleContentHash(bare), moduleContentHash(hashed1));
  assert.equal(moduleContentHash(bare), moduleContentHash(hashed2));
  assert.notEqual(moduleContentHash(bare), moduleContentHash(bare.replace('1', '2')));

  const upd1 = updateHeaderHash(bare, 'prompts/widget.prompt.md', baseHash);
  assert.equal(upd1.changed, true);
  assert.equal(upd1.content, `// Generated from prompts/widget.prompt.md (sha256: ${baseHash}).\nexport const x = 1;\n`);
  assert.equal(updateHeaderHash(upd1.content, 'prompts/widget.prompt.md', baseHash).changed, false);

  const eqStyle = `# Prompt: prompts/widget.prompt.md sha256=${HEX}\nx = 1\n`;
  const updEq = updateHeaderHash(eqStyle, 'prompts/widget.prompt.md', baseHash);
  assert.equal(updEq.content, `# Prompt: prompts/widget.prompt.md sha256=${baseHash}\nx = 1\n`);

  const headerless = 'export const y = 2;\n';
  assert.deepEqual(updateHeaderHash(headerless, 'prompts/widget.prompt.md', baseHash), { content: headerless, changed: false });

  const leadingSpaces = `${' '.repeat(1050)}!`;
  const trailingSpaces = `// Generated from prompts/widget.prompt.md${' '.repeat(1000)}!`;
  const t0 = Date.now();
  assert.deepEqual(headerEntries(`${leadingSpaces}\n${trailingSpaces}\n`), []);
  assert.equal(updateHeaderHash(`${leadingSpaces}\n${trailingSpaces}\n`, 'prompts/widget.prompt.md', baseHash).changed, false);
  assert.ok(Date.now() - t0 < 200, 'header matching must stay linear time');
});
