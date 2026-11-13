import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, symlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { captureSource } from '../../src/runtime-seam.mjs';
import { PLACE, harbor, root } from './runtime-fake.mjs';

const DOCUMENT = 'docs/example.md', ORDER = 'tests/place-order.json';
const FIXTURE_PATHS = ['README.md', PLACE, ORDER, 'tests/unknown-item.json',
  'user_stories/place-order.md', 'user_stories/unknown-item.md'];
const BASE = [DOCUMENT, PLACE, ORDER, 'user_stories/place-order.md'];
const rows = [];
const add = (id, markdown, files = [], refusal = null) => rows.push({ id, markdown, files, refusal });

// The three issue documents are reproduced byte for byte. Their expectations
// come from the approved Story, not from observed parser output.
add('author four-space example', '# Example\n\n    ![a](miss5.svg)\n');
add('author escaped image marker outside Dependencies', '# Example\n\n\\![a](x)\n');
add('author escaped bracket inside Dependencies', '# Example\n\n## Dependencies\n\n!\\[a](x)\n');

for (const [id, example] of [
  ['tab', '\t![example](missing.svg)'],
  ['mixed tab', ' \t![example](missing.svg)'],
  ['quote', '> Quote\n>\n>     ![example](missing.svg)'],
  ['list', '- Item\n\n      ![example](missing.svg)'],
  ['code does not start a quote', '    > ![example](missing.svg)'],
  ['code does not start a list', '    - ![example](missing.svg)'],
  ['code does not start a fence', '    ```\n    ![example](missing.svg)'],
  ['code does not start a comment', '    <!--\n    ![example](missing.svg)'],
]) add(`${id} code preserves following real image`, '# Example\r\n\r\n' + example
  + '\r\n\r\n![real](real.svg)\r\n', ['real.svg']);

add('indented paragraph continuation remains real', '# Example\n\nParagraph\n    ![real](real.svg)\n', ['real.svg']);
add('indented definition cannot override prose definition', '# Example\n\n    [chosen]: missing.svg\n\n'
  + '![real][chosen]\n[chosen]: real.svg\n', ['real.svg']);

for (const [kind, use] of [
  ['inline', path => `[a](${path})`],
  ['full reference', path => `[a][chosen]\n\n[chosen]: ${path}`],
  ['collapsed reference', path => `[a][]\n\n[a]: ${path}`],
  ['shortcut reference', path => `[a]\n\n[a]: ${path}`],
]) {
  // Escaping the first bracket leaves a later unescaped [chosen] eligible as
  // its own shortcut. Use an unresolved suffix when testing no-use behavior.
  const escapedUse = kind === 'full reference' ? path => `[a][unresolved]\n\n[chosen]: ${path}` : use;
  add(`${kind} escaped image marker becomes navigation only`, '# Example\n\n\\!' + use('missing.svg') + '\n');
  add(`${kind} escaped image bracket declares nothing`, '# Example\n\n## Dependencies\n\n!\\' + escapedUse('missing.svg') + '\n');
  add(`${kind} escaped ordinary bracket declares nothing`, '# Example\n\n## Dependencies\n\n\\' + escapedUse('missing.md') + '\n');
  add(`${kind} escaped image marker remains a dependency link`, '# Example\n\n## Dependencies\n\n\\!' + use('real.svg') + '\n', ['real.svg']);
  add(`${kind} even backslashes retain real image`, '# Example\n\n\\\\!' + use('real.svg') + '\n', ['real.svg']);
}

add('escaped image bracket leaves a genuine missing shortcut suffix',
  '# Example\n\n## Dependencies\n\n!\\[a][chosen]\n\n[chosen]: missing.svg\n', [], 'missing.svg');
add('escaped ordinary bracket leaves a genuine missing shortcut suffix',
  '# Example\n\n## Dependencies\n\n\\[a][chosen]\n\n[chosen]: missing.md\n', [], 'missing.md');
add('navigation outside Dependencies remains excluded', '# Example\n\n[ordinary](missing.md)\n');
add('real image is included with exact UTF-8 and CRLF bytes', '# café\r\n\r\n![real](real.svg)\r\n', ['real.svg']);
add('real dependency link is included', '# Example\n\n## Dependencies\n\n[real](real.txt)\n', ['real.txt']);
add('real missing image still refuses', '# Example\n\n![real](missing.svg)\n', [], 'missing.svg');
add('real missing dependency link still refuses', '# Example\n\n## Dependencies\n\n[real](missing.md)\n', [], 'missing.md');
add('real outside-target image still refuses', '# Example\n\n![real](unsafe.svg)\n', [], 'unsafe.svg');
add('real outside-target dependency link still refuses', '# Example\n\n## Dependencies\n\n[real](unsafe.svg)\n', [], 'unsafe.svg');

for (const row of rows) test(`SOURCE-DEPENDENCIES CLI: ${row.id}`, t => {
  const { repo, home, sandbox } = harbor(t);
  const fixtureBytes = new Map(FIXTURE_PATHS.map(path => [path, readFileSync(join(repo, path))]));
  mkdirSync(join(repo, 'docs'));
  writeFileSync(join(repo, 'pdd-source.json'), JSON.stringify({ include: [DOCUMENT] }));
  const bytes = Buffer.from(row.markdown);
  writeFileSync(join(repo, DOCUMENT), bytes);
  writeFileSync(join(repo, 'docs/real.svg'), '<svg><!-- café -->\r\n</svg>\r\n');
  writeFileSync(join(repo, 'docs/real.txt'), 'Real context\r\n');
  writeFileSync(join(sandbox, 'outside.svg'), '<svg/>\n');
  symlinkSync(join(sandbox, 'outside.svg'), join(repo, 'docs/unsafe.svg'));
  const cli = spawnSync(process.execPath, [join(root, 'bin/pdd.mjs'), 'test', '--files', 'place-order', '--json'], {
    cwd: repo, env: { ...process.env, HOME: home, USERPROFILE: home, PDD_RUNTIME_URL: 'http://127.0.0.1:9' },
    encoding: 'utf8', timeout: 30_000, maxBuffer: 1024 * 1024,
  });
  assert.ifError(cli.error);
  assert.equal(cli.signal, null, 'CLI must finish normally');
  const manifest = JSON.parse(cli.stdout);
  const expectedExit = row.refusal ? 4 : 0;
  assert.equal(cli.status, expectedExit, `Markdown dependency semantics: ${cli.stdout}\n${cli.stderr}`);
  assert.equal(manifest.exit_code, expectedExit);
  if (row.refusal) {
    assert.ok(JSON.stringify(manifest.rows).includes(`docs/${row.refusal}`), 'refusal must name the real destination');
    assert.throws(() => captureSource(repo, { tests: [ORDER] }), error =>
      error.exitCode === 4 && error.message.includes(`docs/${row.refusal}`));
  } else {
    const expected = [...BASE, ...row.files.map(path => `docs/${path}`)].sort();
    assert.deepEqual(manifest.files.map(file => file.path), expected, 'CLI upload membership follows authored Markdown');
    const capture = captureSource(repo, { tests: [ORDER] });
    assert.deepEqual(capture.files.map(file => file.path), expected);
    for (const path of expected) {
      const authored = readFileSync(join(repo, path));
      assert.equal(manifest.files.find(file => file.path === path).size, authored.length, `${path}: manifest byte count`);
      const archived = spawnSync('tar', ['-xOf', '-', path], { input: capture.tar });
      assert.equal(archived.status, 0, archived.stderr.toString());
      assert.deepEqual(archived.stdout, authored, `${path}: archive retains authored bytes`);
      assert.deepEqual(capture.sources.find(file => file.path === path).bytes, authored, `${path}: source retains authored bytes`);
    }
  }
  assert.deepEqual(readFileSync(join(repo, DOCUMENT)), bytes, 'discovery preserves documentation bytes');
  for (const [path, before] of fixtureBytes) assert.deepEqual(readFileSync(join(repo, path)), before, `Harbor stays unchanged: ${path}`);
});
