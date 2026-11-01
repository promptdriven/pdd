import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { captureSource } from '../src/runtime-preflight.mjs';

// Literal container examples approved against the existing Code examples rule.
// These ordinary regressions supplement the frozen prompt-space vectors.
const DOCUMENT = 'docs/example.md';
const BODY = ['![Example](missing.svg)', '[Example](missing.txt)', '[chosen]: hidden.svg',
  '## Example heading', '- `missing.json`'];
const OUTSIDE = '[real](real.txt) ![real](real.svg) ![reference][chosen]\n[chosen]: real.svg';
const container = (prefix, fence, body = BODY) => [prefix + fence, ...body.map(line => prefix + line), prefix + fence].join('\n');
const examples = [
  ['quote', fence => container('> ', fence)],
  ['list', fence => '- ' + container('  ', fence).slice(2)],
  ['continued list', fence => '- Example:\n\n' + container('    ', fence)],
  ['lazy list paragraph before fence', fence => '- Example\nlazy continuation\n' + container('  ', fence)],
  ['ordered list', fence => '1. ' + container('   ', fence).slice(3)],
  ['quote then list', fence => '> - ' + container('>   ', fence).slice(4)],
  ['list then quote', fence => '- > ' + container('  > ', fence).slice(4)],
  ['empty quote line', fence => container('> ', fence, ['', ...BODY])],
  ['empty list marker', fence => '-\n' + container('  ', fence)],
  ['short and different closers', fence => container('> ', fence + fence[0],
    [fence, fence[0] === '~' ? '```' : '~~~', ...BODY])],
];
const exits = [
  ['quote ends', fence => `> ${fence}\n> ![Example](missing.svg)\n`],
  ['quote ends at blank line', fence => `> ${fence}\n> ![Example](missing.svg)\n\n`],
  ['new quote after blank line', fence => `> ${fence}\n> ![Example](missing.svg)\n\n> `],
  ['list dedents', fence => `- ${fence}\n  ![Example](missing.svg)\n`],
  ['lazy list unclosed fence dedents', fence => '- Example\nlazy continuation\n'
    + [fence, ...BODY].map(line => '  ' + line).join('\n') + '\n\n'],
  ['list sibling', fence => `- ${fence}\n  ![Example](missing.svg)\n- `],
  ['nested quote ends', fence => `> - ${fence}\n>   ![Example](missing.svg)\n`],
];

function fixture(t, text) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-markdown-containers-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const init = spawnSync('git', ['init', '-q'], { cwd: root, encoding: 'utf8' });
  assert.equal(init.status, 0, init.stderr);
  mkdirSync(join(root, 'docs'));
  writeFileSync(join(root, 'pdd-source.json'), JSON.stringify({ include: [DOCUMENT] }));
  writeFileSync(join(root, DOCUMENT), text);
  writeFileSync(join(root, 'docs/real.txt'), 'Real context\n');
  writeFileSync(join(root, 'docs/real.svg'), '<svg/>\n');
  symlinkSync('missing-link-target.svg', join(root, 'docs/unsafe.svg'));
  return root;
}
function outcome(root) {
  try { return { exitCode: 0, capture: captureSource(root, { tests: [] }) }; }
  catch (error) { return { exitCode: error.exitCode, message: error.message }; }
}
function selected(t, example) {
  const text = `# Synthetic example\r\n## Dependencies\r\n${example}\n${OUTSIDE}\n`;
  const root = fixture(t, text), before = readFileSync(join(root, DOCUMENT));
  const got = outcome(root);
  assert.equal(got.exitCode, 0, `container example must not declare files: ${got.message}`);
  assert.deepEqual(got.capture.files.map(file => file.path), [DOCUMENT, 'docs/real.svg', 'docs/real.txt']);
  const extracted = spawnSync('tar', ['-xOf', '-', DOCUMENT], { input: got.capture.tar });
  assert.equal(extracted.status, 0, String(extracted.stderr));
  assert.deepEqual(extracted.stdout, before, 'archive preserves authored Markdown bytes');
  assert.deepEqual(readFileSync(join(root, DOCUMENT)), before, 'discovery does not edit Markdown');
}

for (const fence of ['~~~', '```']) {
  for (const [label, example] of examples) test(`SOURCE-CONTAINER: ${label} ${fence}`, t => selected(t, example(fence)));
  for (const [label, example] of exits) {
    test(`SOURCE-CONTAINER: ${label} ${fence} preserves genuine context`, t => selected(t, example(fence)));
    for (const path of ['missing-outside.svg', 'unsafe.svg']) {
      test(`SOURCE-CONTAINER: ${label} ${fence} refuses outside ${path}`, t => {
        const text = `## Dependencies\n${example(fence)}![outside](${path})\n`;
        const root = fixture(t, text), got = outcome(root);
        assert.equal(got.exitCode, 4, 'genuine outside dependency must refuse');
        assert.ok(got.message.includes(`docs/${path}`), got.message);
      });
    }
  }
}
