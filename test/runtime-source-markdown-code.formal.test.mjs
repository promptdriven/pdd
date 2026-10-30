import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { captureSource } from '../src/runtime-preflight.mjs';

// Bounded rule from runtime-preflight's Code examples contract and lead12:22:
// code examples add no Markdown dependencies; genuine declarations still do.
// Every input in the finite wrapper grammar below is checked. This is not a
// claim about arbitrary Markdown. The oracle uses literal delimiter choices,
// not parser output or production parsing helpers.
const DOCUMENT = 'docs/case.md';
const BODY_FILES = ['inline.txt', 'inline.svg', 'reference.txt', 'reference.svg'];
const PAYLOAD = '[inline](inline.txt) ![inline](inline.svg) [reference][text] ![reference][image]';
const DEFINITIONS = '[text]: reference.txt\n[image]: reference.svg';

function fixture(t) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-markdown-formal-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const init = spawnSync('git', ['init', '-q'], { cwd: root, encoding: 'utf8' });
  assert.equal(init.status, 0, init.stderr);
  mkdirSync(join(root, 'docs'));
  writeFileSync(join(root, 'pdd-source.json'), JSON.stringify({ include: [DOCUMENT] }));
  for (const path of [...BODY_FILES, 'before.txt', 'after.txt', 'actual.svg', 'hidden.svg', 'bare.txt']) {
    writeFileSync(join(root, 'docs', path), `Synthetic fixture ${path}\n`);
  }
  return root;
}

function outcome(root) {
  try {
    const captured = captureSource(root, { tests: [] });
    return { exitCode: 0, paths: captured.files.map(file => file.path), tar: captured.tar };
  } catch (error) {
    return { exitCode: error.exitCode, message: error.message };
  }
}

function checkSelection(root, text, selected, label) {
  writeFileSync(join(root, DOCUMENT), text);
  const got = outcome(root);
  assert.equal(got.exitCode, 0, `${label}: ${got.message ?? 'capture succeeded'}`);
  assert.deepEqual(got.paths, [DOCUMENT, ...selected.map(path => `docs/${path}`)].sort(), label);
  const extracted = spawnSync('tar', ['-xOf', '-', DOCUMENT], { input: got.tar });
  assert.equal(extracted.status, 0, String(extracted.stderr));
  assert.deepEqual(extracted.stdout, Buffer.from(text), `${label}: preserve original Markdown bytes`);
}

function checkMissing(root, text, label) {
  writeFileSync(join(root, DOCUMENT), text);
  const got = outcome(root);
  assert.equal(got.exitCode, 4, `${label}: missing genuine dependency must refuse`);
  assert.ok(got.message.includes(DOCUMENT), `${label}: refusal identifies owner`);
  assert.ok(got.message.includes('docs/before.txt'), `${label}: refusal identifies missing dependency`);
}

// Six spans: both opening lengths crossed with every stated closer kind.
const SPAN_LENGTHS = [1, 2];
const SPAN_CLOSERS = ['equal', 'longer', 'absent'];
const FENCE_CHARS = ['`', '~'];
const FENCE_LENGTHS = [3, 4];
const FENCE_CLOSERS = ['equal', 'longer', 'shorter', 'different', 'absent'];

test('formal: every bounded span and fence wrapper selects exactly genuine Markdown dependencies', t => {
  const root = fixture(t);
  const configurations = [];
  for (const length of SPAN_LENGTHS) for (const closer of SPAN_CLOSERS) {
    const close = closer === 'absent' ? '' : '`'.repeat(length + (closer === 'longer' ? 1 : 0));
    configurations.push({
      label: `span length=${length} closer=${closer}`,
      example: '`'.repeat(length) + PAYLOAD + close,
      bodyIsCode: closer === 'equal', afterIsCode: false,
    });
  }
  // Twenty fences: both characters and lengths crossed with all closer kinds.
  for (const char of FENCE_CHARS) for (const length of FENCE_LENGTHS) for (const closer of FENCE_CLOSERS) {
    const close = closer === 'absent' ? '' : (closer === 'different' ? (char === '`' ? '~' : '`') : char)
      .repeat(length + (closer === 'longer' ? 1 : closer === 'shorter' ? -1 : 0));
    configurations.push({
      label: `fence char=${char} length=${length} closer=${closer}`,
      example: `${char.repeat(length)}text\n${PAYLOAD}\n${close}`,
      bodyIsCode: true, afterIsCode: !['equal', 'longer'].includes(closer),
    });
  }
  assert.equal(configurations.length, 26);
  for (const item of configurations) {
    const text = `# Synthetic case\n${DEFINITIONS}\n## Dependencies\n[before](before.txt)\n${item.example}\n[after](after.txt)\n`;
    const selected = ['before.txt', ...(!item.bodyIsCode ? BODY_FILES : []), ...(!item.afterIsCode ? ['after.txt'] : [])];
    checkSelection(root, text, selected, item.label);
    rmSync(join(root, 'docs/before.txt'));
    checkMissing(root, text, item.label);
    writeFileSync(join(root, 'docs/before.txt'), 'Synthetic genuine dependency\n');
  }
});

// Eight literal definition controls. The six reference forms cross ordinary
// links/images with full/collapsed/shortcut references. Two more use spans.
const REFERENCES = [
  ['full link', '[label][chosen]', '```\n[chosen]: hidden.svg\n```'],
  ['collapsed link', '[chosen][]', '```\n[chosen]: hidden.svg\n```'],
  ['shortcut link', '[chosen]', '```\n[chosen]: hidden.svg\n```'],
  ['full image', '![label][chosen]', '~~~\n[chosen]: hidden.svg\n~~~'],
  ['collapsed image', '![chosen][]', '~~~\n[chosen]: hidden.svg\n~~~'],
  ['shortcut image', '![chosen]', '~~~\n[chosen]: hidden.svg\n~~~'],
  ['span definition link', '[label][chosen]', '`\n[chosen]: hidden.svg\n`'],
  ['span definition image', '![label][chosen]', '``\n[chosen]: hidden.svg\n``'],
];

test('formal: code reference definitions cannot shadow genuine outside definitions', t => {
  const root = fixture(t);
  for (const [label, reference, example] of REFERENCES) {
    const text = `# Synthetic references\n## Dependencies\n${example}\n${reference}\n`;
    checkSelection(root, text, [], `${label}: code definition alone supplies no dependency`);
    checkSelection(root, `${text}[chosen]: actual.svg\n`, ['actual.svg'], `${label}: outside definition wins`);
  }
});

test('formal: bare dependency-list declarations survive masking and the exact guide example adds no file', t => {
  const root = fixture(t);
  checkSelection(root, '# Synthetic bare declaration\n## Dependencies\n```\n- `hidden.svg`: example\n```\n- `bare.txt`: required context\n',
    ['bare.txt'], 'bare declaration exception');
  const example = 'Embed each primary SVG using Markdown image syntax\n(`![Descriptive alt text](relative/path.svg)`) beside the requirement it\nillustrates so GitHub displays the preview. Additional views may be disclosed,\n';
  checkSelection(root, example, [], 'exact guide example');
});
