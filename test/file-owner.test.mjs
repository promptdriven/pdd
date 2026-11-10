import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, mkdtempSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { headerPrompts, promptClaims, resolveOwners, findOwners } from '../src/file-owner.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

const HEX = 'a'.repeat(64);
const capture = () => ({ text: '', write(value) { this.text += value; } });
function repo(t, files) {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-owner-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q'], { cwd: root });
  for (const [path, text] of Object.entries(files)) { mkdirSync(dirname(join(root, path)), { recursive: true }); writeFileSync(join(root, path), text); }
  return root;
}
const row = (path, owners, source, certain, note = '') => ({ path, owner: owners[0] ?? null, owners, source, certain, note });

// Wrong: the reader stops after 10 lines, so a header after a license or imports names no owner.
test('3200 headerPrompts reads every strict header line in the first 4 KiB', () => {
  const late = `#!/usr/bin/env node\n${'// line\n'.repeat(10)}// Generated from prompts/cli/late.prompt.md (sha256: ${HEX}).\n`;
  assert.deepEqual(headerPrompts(late), ['prompts/cli/late.prompt.md']);
  assert.deepEqual(headerPrompts(Buffer.from(late)), ['prompts/cli/late.prompt.md'], 'bytes and strings read the same');
  const forms = ['# Generated from prompts/a.prompt.md.', '"""Generated from prompts/b.prompt.md."""', '<!-- Generated from prompts/c.prompt.md -->',
    ' * Generated from prompts/d.prompt.md', '// Generated from prompts/a.prompt.md.'].join('\n');
  assert.deepEqual(headerPrompts(forms), ['prompts/a.prompt.md', 'prompts/b.prompt.md', 'prompts/c.prompt.md', 'prompts/d.prompt.md'], 'line order, no duplicates');
  assert.deepEqual(headerPrompts(`${' '.repeat(4100)}\n// Generated from prompts/far.prompt.md.\n`), [], 'a header after 4 KiB is not read');
  const cut = '// Generated from prompts/cut.prompt.md';
  assert.deepEqual(headerPrompts(`${' '.repeat(4096 - cut.length - 1)}\n${cut} (sha256: ${HEX}).\n`), [], 'a line cut by the window is not read');
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
  assert.deepEqual(result.files, [
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
    const [plain, headed] = resolveOwners({ paths: ['docs/x.md', 'src/b.mjs'], bindings: bad, heads, prompts }).files;
    assert.deepEqual(plain, row('docs/x.md', [], null, false, 'pdd-bindings.json could not be read, so a binding may be missing'), String(bad));
    assert.deepEqual(headed, row('src/b.mjs', ['prompts/b.prompt.md'], 'header', true), 'a header owner stays certain');
  }
  assert.deepEqual(resolveOwners({ paths: ['src/c.mjs'], bindings: null, heads: [{ path: 'src/c.mjs', content: false }], prompts: [] }).files,
    [row('src/c.mjs', [], null, false, 'the file could not be read, so a header may be missing')]);
});

// Wrong: findOwners reads other files, misses an untracked prompt or fails on a path that does not exist yet.
test('3200 findOwners reads the working tree of a real repository', t => {
  const root = repo(t, {
    'pdd-bindings.json': JSON.stringify({ schema_version: 'pdd.bindings.v1', modules: [{ module: 'src/bound.mjs', stories: ['user_stories/s.md'], prompt: 'prompts/bound.prompt.md' }] }),
    'prompts/bound.prompt.md': '# Bound\n', 'prompts/new.prompt.md': '# New\n\nOwn `src/new.mjs`.\n', 'prompts/late.prompt.md': '# Late\n',
    'src/late.mjs': `${'// license\n'.repeat(11)}// Generated from prompts/late.prompt.md (sha256: ${HEX}).\nexport const x = 1;\n`, 'src/bound.mjs': 'export {};\n' });
  const result = findOwners({ root, paths: ['src/late.mjs', 'src/bound.mjs', 'src/new.mjs', 'README.md'] });
  assert.deepEqual(result.files.map(({ path, owner, source, certain }) => [path, owner, source, certain]), [
    ['src/late.mjs', 'prompts/late.prompt.md', 'header', true], ['src/bound.mjs', 'prompts/bound.prompt.md', 'binding', true],
    ['src/new.mjs', 'prompts/new.prompt.md', 'prose', false], ['README.md', null, null, true]]);
  const reads = [];
  findOwners({ root, paths: ['src/late.mjs'] }, { files: () => ['prompts/late.prompt.md', 'src/late.mjs', 'pdd-bindings.json'], read: (path, limit) => { reads.push([path, limit]); return null; } });
  assert.deepEqual(reads.sort(), [['pdd-bindings.json', 65536], ['prompts/late.prompt.md', 65536], ['src/late.mjs', 4096]]);
});

// Wrong: the command is missing from the catalog, prints a different shape or accepts a path outside the repository.
test('3200 pdd owner prints text and JSON answers and refuses paths outside the repository', async t => {
  const root = repo(t, { 'prompts/a.prompt.md': '# A\n\nOwn `src/a.mjs`.\n', 'prompts/b.prompt.md': '# B\n',
    'src/b.mjs': '#!/usr/bin/env node\n// Generated from prompts/b.prompt.md.\n', 'src/a.mjs': 'export {};\n' });
  const run = async (argv, cwd = root) => { const stdout = capture(), stderr = capture(); const code = await runPdd(argv, { stdout, stderr, cwd }); return { code, out: stdout.text, err: stderr.text }; };
  const text = await run(['owner', 'src/b.mjs', 'src/a.mjs', 'docs/none.md']);
  assert.equal(text.code, 0, text.err);
  assert.equal(text.out, ['src/b.mjs: prompts/b.prompt.md (header)',
    'src/a.mjs: prompts/a.prompt.md (prose, not certain: treat as owned)',
    '  named only in the opening sentence of prompts/a.prompt.md; add a Generated from header or a pdd-bindings.json entry',
    'docs/none.md: no owner', ''].join('\n'));
  const json = await run(['owner', 'b.mjs', '--json'], join(root, 'src'));
  assert.equal(json.code, 0, json.err);
  assert.deepEqual(JSON.parse(json.out), { schema_version: 'pdd.owner.v1', files: [row('src/b.mjs', ['prompts/b.prompt.md'], 'header', true)] });
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
