import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { Readable } from 'node:stream';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { headerPrompts, headerEntries, headerHashState, promptHeaderHash, promptClaims, resolveOwners, findOwners } from '../src/file-owner.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { runApprove } from '../src/prompt-approve.mjs';
import { PLACE, harbor, sink } from './runtime-fake.mjs';

const HEX = 'a'.repeat(64), CUT = '// Generated from prompts/cut.prompt.md';
const capture = () => ({ text: '', write(value) { this.text += value; } });
function repo(t, files) {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-owner-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q'], { cwd: root });
  for (const [path, text] of Object.entries(files)) { mkdirSync(dirname(join(root, path)), { recursive: true }); writeFileSync(join(root, path), text); }
  return root;
}
const row = (path, owners, source, certain, note = '') => ({ path, owner: owners[0] ?? null, owners, source, certain, note });
const plain = files => files.map(({ headers, ...rest }) => rest);
const sha = text => createHash('sha256').update(text).digest('hex');
const asDraft = text => text.replace('"status": "approved"', '"status": "draft"').replace(/("prose_sha256": )"[a-f0-9]{64}"/, '$1""');
const headerRows = (root, path) => findOwners({ root, paths: [path] }).files[0].headers;

// Wrong: the reader stops after 10 lines, so a header after a license or imports names no owner.
test('3200 headerPrompts reads every strict header line in the first 4 KiB', () => {
  const late = `#!/usr/bin/env node\n${'// line\n'.repeat(10)}// Generated from prompts/cli/late.prompt.md (sha256: ${HEX}).\n`;
  assert.deepEqual(headerPrompts(late), ['prompts/cli/late.prompt.md']);
  assert.deepEqual(headerPrompts(Buffer.from(late)), ['prompts/cli/late.prompt.md'], 'bytes and strings read the same');
  const forms = ['# Generated from prompts/a.prompt.md.', '"""Generated from prompts/b.prompt.md."""', '<!-- Generated from prompts/c.prompt.md -->',
    ' * Generated from prompts/d.prompt.md', '// Generated from prompts/a.prompt.md.'].join('\n');
  assert.deepEqual(headerPrompts(forms), ['prompts/a.prompt.md', 'prompts/b.prompt.md', 'prompts/c.prompt.md', 'prompts/d.prompt.md'], 'line order, no duplicates');
  assert.deepEqual(headerPrompts(`${' '.repeat(4100)}\n// Generated from prompts/far.prompt.md.\n`), [], 'a header after 4 KiB is not read');
  assert.deepEqual(headerPrompts(`${' '.repeat(4096 - CUT.length - 1)}\n${CUT} (sha256: ${HEX}).\n`), [], 'a line cut by the window is not read');
  assert.deepEqual(headerPrompts([
    'Generated from the canonical m1_policy prompt.', 'const x = "Generated from prompts/s.prompt.md.";',
    '// see Generated from prompts/t.prompt.md for details', '// Generated from ../outside.prompt.md.', '// Generated from /abs/x.prompt.md.',
    '// Generated from prompts/.git/x.prompt.md.', `// Generated from prompts/${'y'.repeat(1100)}.prompt.md.`, '// Generated from prompts/x.md.'].join('\n')), []);
  assert.deepEqual(headerPrompts(null), []);
  assert.deepEqual(headerPrompts(undefined), []);
});

// Wrong: a claim in a later sentence (a file that the module only reads) makes that file owned.
test('3200 promptClaims reads only the first sentence of the opening paragraph', () => {
  const prompt = '# Queue\n\nOwn `src/queue.mjs` and the entry\n`scripts/run.sh`, and the adapter src/adapter.mjs. It reads `pdd.json`.\n\n## Rules\n\nOwn `src/later.mjs`.\n';
  assert.deepEqual(promptClaims('prompts/cli/queue.prompt.md', prompt), ['scripts/run.sh', 'src/adapter.mjs', 'src/queue.mjs']);
  assert.deepEqual(promptClaims('prompts/cli/x.prompt.md', '# X\n\n`src/x.mjs` exports `run(input, ports)` for the [Y rules](y.prompt.md), see [doc](../../docs/x.md#top). More.\n'),
    ['docs/x.md', 'src/x.mjs'], 'links resolve against the prompt folder; prompts are not claims');
  assert.deepEqual(promptClaims('prompts/a.prompt.md', '# A\n\n## Purpose\n\nOwn `src/a.mjs`.\n'), [], 'no opening paragraph');
  assert.deepEqual(promptClaims('prompts/a.prompt.md', '# A\n\nOwn `src/a.mjs` with `x. y` notes and `src/c.mjs`. Own `src/b.mjs`.\n'), ['src/a.mjs', 'src/c.mjs'],
    'a period inside backticks does not end the sentence');
  assert.deepEqual(promptClaims('prompts/a.prompt.md', null), []);
});

// Wrong: a prose-only claim is reported as unowned, or a binding/header answer is reported as uncertain.
test('3200 resolveOwners: binding, header, prose, and the uncertain cases', () => {
  const prompts = ['a', 'b', 'c'].map(name => ({ path: `prompts/${name}.prompt.md`, content: `# ${name}\n\nOwn \`src/${name}.mjs\` and \`src/shared.mjs\`.\n` }));
  const bindings = JSON.stringify({ schema_version: 'pdd.bindings.v1', modules: [
    { module: 'src/bound.mjs', stories: ['user_stories/s.md'], prompt: 'prompts/a.prompt.md' },
    { module: 'src/both.mjs', stories: ['user_stories/s.md'], prompt: 'prompts/a.prompt.md' },
    { module: 'src/unbound.mjs', stories: ['user_stories/s.md'], reason: 'device', port_attempt: 'tried' },
    { module: 'src/gone.mjs', stories: ['user_stories/s.md'], prompt: 'prompts/gone.prompt.md' }, 'junk'] });
  const heads = [
    { path: 'src/b.mjs', content: '// Generated from prompts/b.prompt.md.\n' },
    { path: 'src/both.mjs', content: '// Generated from prompts/b.prompt.md.\n// Generated from prompts/a.prompt.md.\n' },
    { path: 'src/two.mjs', content: '// Generated from prompts/c.prompt.md.\n# Generated from prompts/b.prompt.md.\n' },
    { path: 'src/dangling.mjs', content: '// Generated from prompts/none.prompt.md.\n' },
    { path: 'src/c.mjs', content: false }];
  const paths = ['src/bound.mjs', 'src/b.mjs', 'src/both.mjs', 'src/two.mjs', 'src/a.mjs', 'src/shared.mjs', 'src/dangling.mjs', 'src/gone.mjs',
    'src/unbound.mjs', 'src/c.mjs', 'docs/x.md', 'src/b.mjs'];
  const result = resolveOwners({ paths, bindings, heads, prompts });
  assert.equal(result.schema_version, 'pdd.owner.v1');
  const prose = names => `named only in the opening sentence of ${names}; add a Generated from header or a pdd-bindings.json entry`;
  assert.deepEqual(plain(result.files), [
    row('src/bound.mjs', ['prompts/a.prompt.md'], 'binding', true),
    row('src/b.mjs', ['prompts/b.prompt.md'], 'header', true),
    row('src/both.mjs', ['prompts/a.prompt.md', 'prompts/b.prompt.md'], 'binding', true),
    row('src/two.mjs', ['prompts/c.prompt.md', 'prompts/b.prompt.md'], 'header', true),
    row('src/a.mjs', ['prompts/a.prompt.md'], 'prose', false, prose('prompts/a.prompt.md')),
    row('src/shared.mjs', ['prompts/a.prompt.md', 'prompts/b.prompt.md', 'prompts/c.prompt.md'], 'prose', false,
      prose('prompts/a.prompt.md, prompts/b.prompt.md, prompts/c.prompt.md')),
    row('src/dangling.mjs', ['prompts/none.prompt.md'], 'header', false, 'names prompts/none.prompt.md, which is not a Git-visible prompt'),
    row('src/gone.mjs', ['prompts/gone.prompt.md'], 'binding', false, 'names prompts/gone.prompt.md, which is not a Git-visible prompt'),
    row('src/unbound.mjs', [], 'binding', true, 'pdd-bindings.json declares it with no prompt'),
    row('src/c.mjs', ['prompts/c.prompt.md'], 'prose', false, `${prose('prompts/c.prompt.md')}; the file could not be read, so a header may be missing`),
    row('docs/x.md', [], null, true)]);
  for (const bad of ['{', JSON.stringify({ schema_version: 'pdd.bindings.v2', modules: [] }), JSON.stringify({ schema_version: 'pdd.bindings.v1' }), false]) {
    const [unowned, headed] = plain(resolveOwners({ paths: ['docs/x.md', 'src/b.mjs'], bindings: bad, heads, prompts }).files);
    assert.deepEqual(unowned, row('docs/x.md', [], null, false, 'pdd-bindings.json could not be read, so a binding may be missing'), String(bad));
    assert.deepEqual(headed, row('src/b.mjs', ['prompts/b.prompt.md'], 'header', true), 'a header owner stays certain');
  }
  assert.deepEqual(plain(resolveOwners({ paths: ['src/c.mjs'], bindings: null, heads: [{ path: 'src/c.mjs', content: false }], prompts: [] }).files),
    [row('src/c.mjs', [], null, false, 'the file could not be read, so a header may be missing')]);
});

// Wrong: findOwners reads other files, misses an untracked prompt or fails on a path that does not exist yet.
test('3200 findOwners reads the working tree of a real repository', t => {
  const root = repo(t, {
    'pdd-bindings.json': JSON.stringify({ schema_version: 'pdd.bindings.v1', modules: [{ module: 'src/bound.mjs', stories: ['user_stories/s.md'], prompt: 'prompts/bound.prompt.md' }] }),
    'prompts/bound.prompt.md': '# Bound\n', 'prompts/new.prompt.md': '# New\n\nOwn `src/new.mjs`.\n', 'prompts/late.prompt.md': '# Late\n',
    'src/late.mjs': `${'// license\n'.repeat(11)}// Generated from prompts/late.prompt.md (sha256: ${HEX}).\nexport const x = 1;\n`, 'src/bound.mjs': 'export {};\n',
    'prompts/cut.prompt.md': '# Cut\n', 'src/cut.mjs': `${' '.repeat(4096 - CUT.length - 1)}\n${CUT} (sha256: ${HEX}).\n` });
  const result = findOwners({ root, paths: ['src/late.mjs', 'src/bound.mjs', 'src/new.mjs', 'README.md', 'src/cut.mjs'] });
  assert.deepEqual(result.files.map(({ path, owner, source, certain }) => [path, owner, source, certain]), [
    ['src/late.mjs', 'prompts/late.prompt.md', 'header', true], ['src/bound.mjs', 'prompts/bound.prompt.md', 'binding', true],
    ['src/new.mjs', 'prompts/new.prompt.md', 'prose', false], ['README.md', null, null, true],
    ['src/cut.mjs', null, null, true]], 'a header cut by the 4 KiB window names no owner, as in replay');
  const reads = [];
  findOwners({ root, paths: ['src/late.mjs'] }, { files: () => ['prompts/late.prompt.md', 'src/late.mjs', 'pdd-bindings.json'], read: (path, limit) => { reads.push([path, limit]); return null; } });
  assert.deepEqual(reads.sort(), [['pdd-bindings.json', 65536], ['prompts/late.prompt.md', 10 * 1024 * 1024 + 1], ['src/late.mjs', 4097]]);
});

// Wrong: the command is missing from the catalog, prints a different shape or accepts a path outside the repository.
test('3200 pdd owner prints text and JSON answers and refuses paths outside the repository', async t => {
  const root = repo(t, { 'prompts/a.prompt.md': '# A\n\nOwn `src/a.mjs`.\n', 'prompts/b.prompt.md': '# B\n',
    'src/b.mjs': '#!/usr/bin/env node\n// Generated from prompts/b.prompt.md.\n', 'src/a.mjs': 'export {};\n' });
  const run = async (argv, cwd = root) => { const stdout = capture(), stderr = capture(); const code = await runPdd(argv, { stdout, stderr, cwd }); return { code, out: stdout.text, err: stderr.text }; };
  const text = await run(['owner', 'src/b.mjs', 'src/a.mjs', 'docs/none.md']);
  assert.equal(text.code, 0, text.err);
  assert.equal(text.out, ['src/b.mjs: prompts/b.prompt.md (header)', `  prompts/b.prompt.md header has no hash; current is ${promptHeaderHash('# B\n')}`,
    'src/a.mjs: prompts/a.prompt.md (prose, not certain: treat as owned)',
    '  named only in the opening sentence of prompts/a.prompt.md; add a Generated from header or a pdd-bindings.json entry',
    'docs/none.md: no owner', ''].join('\n'));
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

// Wrong: the header hash covers the approval metadata, so approving a prompt makes every header of it stale.
test('3200 header hash: approval metadata and JSON spacing do not count; prose and interface declarations do', t => {
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
  assert.equal(promptHeaderHash('# No interface\n\nOwn `src/x.mjs`.\n'), sha('# No interface\n\nOwn `src/x.mjs`.\n'), 'without an interface the behavior text is the file');
  assert.deepEqual(headerHashState(hash, approved), { expected: hash, state: 'current', legacy: false });
  assert.deepEqual(headerHashState(sha(approved), approved), { expected: hash, state: 'current', legacy: true }, 'the whole-file form still reads as current');
  assert.deepEqual(headerHashState(sha(draft), approved), { expected: hash, state: 'stale', legacy: false });
  assert.deepEqual(headerHashState(null, approved), { expected: hash, state: 'none', legacy: false });
  assert.deepEqual(headerHashState(hash, null), { expected: null, state: 'unknown', legacy: false });
  assert.deepEqual(headerEntries(`// Generated from prompts/a.prompt.md (sha256: ${HEX}).\n# Generated from prompts/b.prompt.md.\n// Generated from prompts/a.prompt.md.\n`),
    [{ prompt: 'prompts/a.prompt.md', sha256: HEX }, { prompt: 'prompts/b.prompt.md', sha256: null }]);
});

// Wrong: pdd approve makes the code header stale, or a prose change keeps it current.
test('3200 header hash: pdd approve leaves headers current; a prose change makes them stale', async t => {
  const setup = harbor(t, repo => {
    const file = join(repo, PLACE), draft = asDraft(readFileSync(file, 'utf8'));
    writeFileSync(file, draft);
    mkdirSync(join(repo, 'src'));
    writeFileSync(join(repo, 'src/order.mjs'), `// Generated from ${PLACE} (sha256: ${promptHeaderHash(draft)}).\nexport {};\n`);
    writeFileSync(join(repo, 'src/legacy.mjs'), `// Generated from ${PLACE} (sha256: ${sha(draft)}).\nexport {};\n`);
  });
  const state = path => headerRows(setup.repo, path).map(({ state, legacy }) => [state, legacy]);
  assert.deepEqual(state('src/order.mjs'), [['current', false]]);
  assert.deepEqual(state('src/legacy.mjs'), [['current', true]], 'an old whole-file header reads as current');
  const ports = { stdout: sink(), stderr: sink(), stdin: Readable.from(['y\n']), interactive: true };
  assert.equal(await runApprove({ words: [PLACE], cwd: setup.repo }, ports), 0, ports.stdout.text + ports.stderr.text);
  assert.match(readFileSync(join(setup.repo, PLACE), 'utf8'), /"status": "approved"/);
  assert.deepEqual(state('src/order.mjs'), [['current', false]], 'approval leaves the header current');
  assert.deepEqual(state('src/legacy.mjs'), [['stale', false]], 'the whole-file form changes with each approval');
  const file = join(setup.repo, PLACE);
  writeFileSync(file, readFileSync(file, 'utf8').replace('in whole cents.', 'in cents.'));
  assert.deepEqual(state('src/order.mjs'), [['stale', false]], 'a prose change makes it stale');
});

// Wrong: the owner command hides a stale or missing header hash, or prints no current hash to write.
test('3200 pdd owner shows each header hash that is not current', async t => {
  const prompt = '# A\n\nOwn `src/a.mjs`.\n', hash = promptHeaderHash(prompt);
  const root = repo(t, { 'prompts/a.prompt.md': prompt,
    'src/ok.mjs': `// Generated from prompts/a.prompt.md (sha256: ${hash}).\n`, 'src/stale.mjs': `// Generated from prompts/a.prompt.md (sha256: ${HEX}).\n`,
    'src/bare.mjs': '// Generated from prompts/a.prompt.md.\n', 'src/gone.mjs': `// Generated from prompts/gone.prompt.md (sha256: ${HEX}).\n` });
  const stdout = capture(), stderr = capture();
  assert.equal(await runPdd(['owner', 'src/ok.mjs', 'src/stale.mjs', 'src/bare.mjs', 'src/gone.mjs'], { stdout, stderr, cwd: root }), 0, stderr.text);
  assert.equal(stdout.text, ['src/ok.mjs: prompts/a.prompt.md (header)',
    'src/stale.mjs: prompts/a.prompt.md (header)', `  prompts/a.prompt.md header hash is stale (${HEX}); current is ${hash}`,
    'src/bare.mjs: prompts/a.prompt.md (header)', `  prompts/a.prompt.md header has no hash; current is ${hash}`,
    'src/gone.mjs: prompts/gone.prompt.md (header, not certain: treat as owned)', '  names prompts/gone.prompt.md, which is not a Git-visible prompt', ''].join('\n'));
  const json = capture();
  await runPdd(['owner', 'src/stale.mjs', '--json'], { stdout: json, stderr, cwd: root });
  assert.deepEqual(JSON.parse(json.text).files[0].headers, [{ prompt: 'prompts/a.prompt.md', sha256: HEX, expected: hash, state: 'stale', legacy: false }]);
});

test('3295 pdd owner warns on stderr without blocking exit 0 or changing stdout when prompts claim test files', async t => {
  const prodPrompt = '# Prod\n\nOwn `src/prod.mjs`.\n';
  const boundPrompt = '# Bound test\n\nVerify suite.\n';
  const headerPrompt = '# Header test\n\nVerify suite.\n';
  const prosePrompt = '# Prose test\n\nOwn `src/unit.test.mjs`, `src/unit_test.go` and `src/test_unit.py`.\n';
  const root = repo(t, {
    'pdd-bindings.json': JSON.stringify({
      schema_version: 'pdd.bindings.v1',
      modules: [{ module: 'test/bound.e2e.mjs', stories: ['user_stories/s.md'], prompt: 'prompts/bound.prompt.md' }],
    }),
    'prompts/prod.prompt.md': prodPrompt,
    'prompts/bound.prompt.md': boundPrompt,
    'prompts/header.prompt.md': headerPrompt,
    'prompts/prose.prompt.md': prosePrompt,
    'src/prod.mjs': `// Generated from prompts/prod.prompt.md (sha256: ${promptHeaderHash(prodPrompt)}).\n`,
    'test/bound.e2e.mjs': 'export {};\n',
    'tests/header.mjs': `// Generated from prompts/header.prompt.md (sha256: ${promptHeaderHash(headerPrompt)}).\n`,
    'src/unit.test.mjs': 'export {};\n',
    'src/unit_test.go': 'package unit\n',
    'src/test_unit.py': 'x = 1\n',
  });
  const run = async argv => {
    const stdout = capture(), stderr = capture();
    const code = await runPdd(argv, { stdout, stderr, cwd: root });
    return { code, out: stdout.text, err: stderr.text };
  };

  // Production modules stay completely silent on stderr.
  const prod = await run(['owner', 'src/prod.mjs']);
  assert.equal(prod.code, 0);
  assert.equal(prod.err, '');
  assert.equal(prod.out, 'src/prod.mjs: prompts/prod.prompt.md (header)\n');

  // Test paths claimed via binding, header, or prose emit non-blocking stderr warnings while keeping exit 0 and stdout intact.
  const text = await run(['owner', 'test/bound.e2e.mjs', 'tests/header.mjs', 'src/unit.test.mjs', 'src/unit_test.go', 'src/test_unit.py']);
  assert.equal(text.code, 0);
  assert.equal(text.out, [
    'test/bound.e2e.mjs: prompts/bound.prompt.md (binding)',
    'tests/header.mjs: prompts/header.prompt.md (header)',
    'src/unit.test.mjs: prompts/prose.prompt.md (prose, not certain: treat as owned)',
    '  named only in the opening sentence of prompts/prose.prompt.md; add a Generated from header or a pdd-bindings.json entry',
    'src/unit_test.go: prompts/prose.prompt.md (prose, not certain: treat as owned)',
    '  named only in the opening sentence of prompts/prose.prompt.md; add a Generated from header or a pdd-bindings.json entry',
    'src/test_unit.py: prompts/prose.prompt.md (prose, not certain: treat as owned)',
    '  named only in the opening sentence of prompts/prose.prompt.md; add a Generated from header or a pdd-bindings.json entry',
    '',
  ].join('\n'));
  assert.equal(text.err, [
    'Warning: misplaced prompt owner: test/bound.e2e.mjs is claimed by prompts/bound.prompt.md (binding). Prompts own production modules, not test files.',
    'Warning: misplaced prompt owner: tests/header.mjs is claimed by prompts/header.prompt.md (header). Prompts own production modules, not test files.',
    'Warning: misplaced prompt owner: src/unit.test.mjs is claimed by prompts/prose.prompt.md (prose). Prompts own production modules, not test files.',
    'Warning: misplaced prompt owner: src/unit_test.go is claimed by prompts/prose.prompt.md (prose). Prompts own production modules, not test files.',
    'Warning: misplaced prompt owner: src/test_unit.py is claimed by prompts/prose.prompt.md (prose). Prompts own production modules, not test files.',
    '',
  ].join('\n'));

  // --json keeps stdout pure valid pdd.owner.v1 JSON and writes the warning to stderr.
  const json = await run(['owner', 'test/bound.e2e.mjs', '--json']);
  assert.equal(json.code, 0);
  assert.equal(JSON.parse(json.out).schema_version, 'pdd.owner.v1');
  assert.equal(JSON.parse(json.out).files[0].owner, 'prompts/bound.prompt.md');
  assert.match(json.err, /Warning: misplaced prompt owner: test\/bound\.e2e\.mjs is claimed by prompts\/bound\.prompt\.md \(binding\)\./);

  // Querying a prompt path directly also warns on stderr when that prompt claims test files.
  const byPrompt = await run(['owner', 'prompts/prose.prompt.md', 'prompts/prod.prompt.md']);
  assert.equal(byPrompt.code, 0);
  assert.equal(byPrompt.out, 'prompts/prose.prompt.md: no owner\nprompts/prod.prompt.md: no owner\n');
  assert.equal(byPrompt.err, 'Warning: misplaced prompt owner: prompts/prose.prompt.md claims src/test_unit.py, src/unit.test.mjs, src/unit_test.go. Prompts own production modules, not test files.\n');
});
