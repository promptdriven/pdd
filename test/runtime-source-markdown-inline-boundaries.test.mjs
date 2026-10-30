import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, symlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { captureSource } from '../src/runtime-preflight.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { PLACE, harbor, portsFor } from './runtime-fake.mjs';

// Root approved these literal Markdown expectations before either old-code or
// repaired-code execution. CommonMark 0.31.2 §§2.4, 3, 6.1 supply escape/block
// meaning; the module contract supplies dependency scope and safety outcomes.
const DOCUMENT = 'docs/inline.md', ORDER = 'tests/place-order.json';
const cases = [];
const add = (id, markdown, exitCode = 0, target = null) => cases.push({ id, markdown, exitCode, target });
const uses = [['link', path => `[required](${path})`], ['image', path => `![required](${path})`],
  ['reference link', path => `[required][chosen]\n\n[chosen]: ${path}`],
  ['reference image', path => `![required][chosen]\n\n[chosen]: ${path}`]];

for (const [name, use] of uses.slice(0, 2)) {
  for (let slashes = 0; slashes <= 3; slashes++) {
    const escape = '\\'.repeat(slashes), outside = slashes % 2 === 1;
    add(`${name}: ${slashes} backslashes before tick`, `${escape}\` ${use('credentials.json')} \\` + '`', outside ? 4 : 0,
      outside ? 'credentials.json' : null);
    add(`${name}: ${slashes} backslashes before comment`, `${escape}<!-- ${use('credentials.json')} -->`, outside ? 4 : 0,
      outside ? 'credentials.json' : null);
  }
  for (const width of [2, 3]) {
    add(`${name}: escaped first of ${width} ticks leaves a code opener`, '\\' + '`'.repeat(width)
      + ' ' + use('credentials.json') + ' ' + '`'.repeat(width - 1));
    add(`${name}: escaped first of ${width} ticks does not keep original width`, '\\' + '`'.repeat(width)
      + ' ' + use('credentials.json') + ' ' + '`'.repeat(width), 4, 'credentials.json');
  }
  add(`${name}: backslash inside code does not escape closer`, '`example \\` ' + use('credentials.json') + ' `', 4, 'credentials.json');
}

const boundaries = [
  ['blank paragraph', '\n\n'], ['ATX heading', '\n### Next\n'],
  ['setext heading', '\n===\n'], ['thematic break', '\n***\n'],
  ['tilde fence', '\n~~~\nexample\n~~~\n'], ['backtick fence', '\n```\nexample\n```\n'],
  ['new list', '\n- next item\n'], ['new quote', '\n> next quote\n'],
];
for (const [name, use] of uses) {
  for (const [boundary, between] of boundaries) {
    add(`${name}: ${boundary} ends unmatched span`, 'before `' + between + use('credentials.json') + '\n\nend `', 4, 'credentials.json');
  }
  add(`${name}: sibling list item ends unmatched span`, '- before `\n- ' + use('credentials.json') + '\n\nend `', 4, 'credentials.json');
  add(`${name}: quote ends unmatched span`, '> before `\n\n' + use('credentials.json') + '\n\nend `', 4, 'credentials.json');
}

for (const [name, use] of uses.slice(0, 2)) {
  for (const path of ['real.txt', 'missing.txt', 'unsafe.svg']) {
    const exit = path === 'real.txt' ? 0 : 4;
    add(`${name}: escaped tick preserves ${path}`, '\\` ' + use(path) + ' \\`', exit, path);
    add(`${name}: paragraph boundary preserves ${path}`, 'before `\n\n' + use(path) + '\n\nend `', exit, path);
    add(`${name}: escaped comment preserves ${path}`, '\\<!-- ' + use(path) + ' -->', exit, path);
  }
  add(`${name}: soft line stays in span`, '`before\n' + use('credentials.json') + '\nend`');
  add(`${name}: lazy quote continuation stays in span`, '> before `\n' + use('credentials.json') + '\nend`');
  add(`${name}: lazy list continuation stays in span`, '- before `\n' + use('credentials.json') + '\nend`');
  add(`${name}: comment crosses blank lines and block markers`, '<!--\n\n### example\n~~~\n'
    + use('credentials.json') + '\n\n-->');
  add(`${name}: inline comment cannot cross paragraph boundary`, 'Lead <!--\n\n'
    + use('credentials.json') + '\n\n--> tail', 4, 'credentials.json');
  add(`${name}: quote comment ends with its container`, '> <!--\n> example\n'
    + use('credentials.json') + '\n--> tail', 4, 'credentials.json');
  add(`${name}: list comment ends with its container`, '- <!--\n  example\n'
    + use('credentials.json') + '\n--> tail', 4, 'credentials.json');
}
add('outside definition survives code example', '`before\n[chosen]: credentials.json\nend`\n\n[required][chosen]\n[chosen]: real.txt');
add('escaped tick leaves genuine reference definition', '\\` before\n\n[chosen]: credentials.json\n\nend \\`\n![required][chosen]', 4, 'credentials.json');
add('unclosed comment protects remainder', '<!--\n\n![example](credentials.json)\n### ignored');
add('ordered marker 2 cannot interrupt a span paragraph', 'before `\n2. ![example](credentials.json)\nend`');
add('incomplete ordinary angle prose cannot interrupt a span paragraph', 'before `\n<ordinary prose\n![example](credentials.json)\nend`');

const TAIL = '\n\n[real](real.txt) ![real](real.svg)\n- `bare.json`\n';
for (const row of cases) test(`SOURCE-INLINE: ${row.id}`, async t => {
  const { repo, home } = harbor(t);
  mkdirSync(join(repo, 'docs'));
  writeFileSync(join(repo, 'pdd-source.json'), JSON.stringify({ include: [DOCUMENT] }));
  const bytes = Buffer.from('# UTF-8: café\r\n## Dependencies\r\n' + row.markdown + TAIL);
  writeFileSync(join(repo, DOCUMENT), bytes);
  for (const path of ['real.txt', 'real.svg', 'bare.json', 'credentials.json']) writeFileSync(join(repo, 'docs', path), 'synthetic\n');
  symlinkSync('real.svg', join(repo, 'docs/unsafe.svg'));
  const calls = { gh: 0, fetch: 0 };
  const { ports } = portsFor({ HOME: home, PDD_RUNTIME_URL: 'http://127.0.0.1:9' }, {
    gh: () => { calls.gh++; assert.fail('file discovery must not authenticate'); },
    fetch: () => { calls.fetch++; assert.fail('file discovery must not use the network'); },
  });
  let capture, failure;
  try { capture = captureSource(repo, { tests: [ORDER] }); }
  catch (error) { failure = error; }
  assert.equal(failure?.exitCode ?? 0, row.exitCode, failure?.message ?? 'genuine dependency was hidden');
  if (row.exitCode) assert.ok(failure.message.includes(`docs/${row.target}`), failure.message);
  else {
    const expected = [PLACE, ORDER, 'user_stories/place-order.md', DOCUMENT];
    if (row.id !== 'unclosed comment protects remainder') expected.push('docs/real.txt', 'docs/real.svg', 'docs/bare.json');
    assert.deepEqual(capture.files.map(file => file.path), expected.sort());
    const archived = spawnSync('tar', ['-xOf', '-', DOCUMENT], { input: capture.tar });
    assert.equal(archived.status, 0, archived.stderr.toString());
    assert.deepEqual(archived.stdout, bytes, 'captured bytes retain CRLF and UTF-8');
  }
  assert.equal(await runCheck({ cwd: repo, words: [ORDER], options: { '--files': true } }, ports), row.exitCode, ports.stderr.text);
  assert.deepEqual(readFileSync(join(repo, DOCUMENT)), bytes, 'discovery leaves authored bytes unchanged');
  assert.deepEqual(calls, { gh: 0, fetch: 0 });
});
