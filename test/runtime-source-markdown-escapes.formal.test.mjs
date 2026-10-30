import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { captureSource } from '../src/runtime-preflight.mjs';

// Root-reviewed oracle from the owner's code-example rule and CommonMark 0.31.2
// sections 2.4, 3.1, 4.6, 4.8 and 6.1: actual code/comments suppress examples;
// escaped delimiters and delimiters in different inline blocks do not.
// Exhaustive only over the 170 literal inputs below, not arbitrary Markdown.
// Expected values were fixed before execution; no production parser is reused.
const DOCUMENT = 'docs/case.md';
const SEPARATORS = [' ', '\n', '\n\n'];
const TARGETS = ['present.txt', 'missing.txt', 'credentials.json'];
const FORMS = ['link', 'image'];
const BASE_FILES = [DOCUMENT, 'docs/after.txt', 'docs/before.txt'];
const payload = (form, target) => `${form === 'image' ? '!' : ''}[required](${target})`;

function fixture(t) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-markdown-escapes-formal-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const init = spawnSync('git', ['init', '-q'], { cwd: root, encoding: 'utf8' });
  assert.equal(init.status, 0, init.stderr);
  mkdirSync(join(root, 'docs'));
  writeFileSync(join(root, 'pdd-source.json'), JSON.stringify({ include: [DOCUMENT] }));
  for (const path of ['present.txt', 'before.txt', 'after.txt', 'credentials.json']) {
    writeFileSync(join(root, 'docs', path), `Synthetic fixture ${path}\n`);
  }
  return root;
}

function check(root, example, target, masked, label) {
  const markdown = `# Synthetic delimiter case\n## Dependencies\n[before](before.txt)\n\n${example}\n\n[after](after.txt)\n`;
  writeFileSync(join(root, DOCUMENT), markdown);
  let captured, failure;
  try { captured = captureSource(root, { tests: [] }); }
  catch (error) { failure = { exitCode: error.exitCode, message: error.message }; }
  const refuses = !masked && target !== 'present.txt';
  assert.equal(failure?.exitCode ?? (captured ? 0 : undefined), refuses ? 4 : 0,
    `${label}: genuine dependency selection/refusal; ${JSON.stringify(failure)}`);
  if (refuses) {
    assert.ok(failure.message.includes(DOCUMENT), `${label}: refusal identifies owner`);
    assert.ok(failure.message.includes(`docs/${target}`), `${label}: refusal identifies target`);
    assert.ok(failure.message.includes(target === 'missing.txt' ? 'not a Git-visible file' : 'name looks like a secret'),
      `${label}: correct missing/privacy refusal`);
  } else {
    assert.deepEqual(captured.files.map(file => file.path),
      [...BASE_FILES, ...(!masked ? [`docs/${target}`] : [])].sort(), `${label}: exact genuine membership`);
    const archive = spawnSync('tar', ['-xOf', '-', DOCUMENT], { input: captured.tar });
    assert.equal(archive.status, 0, String(archive.stderr));
    assert.deepEqual(archive.stdout, Buffer.from(markdown), `${label}: archive preserves authored bytes`);
  }
  assert.deepEqual(readFileSync(join(root, DOCUMENT)), Buffer.from(markdown), `${label}: source is unchanged`);
}

// 4 slash counts x 2 families x 2 forms x 3 separators x 3 targets = 144.
// A bare line-start <!-- is an HTML block. With two preceding backslashes it
// is an inline comment after a literal backslash, confined to its paragraph.
for (const family of ['backtick', 'comment']) for (const slashes of [0, 1, 2, 3]) {
  test(`formal: ${family} opener with ${slashes} backslashes over every bounded payload and paragraph`, t => {
    const root = fixture(t);
    let count = 0;
    for (const form of FORMS) for (const separator of SEPARATORS) for (const target of TARGETS) {
      const prefix = '\\'.repeat(slashes);
      const example = family === 'backtick'
        ? `Lead ${prefix}\`${separator}${payload(form, target)}${separator}\` tail`
        : `${prefix}<!--${separator}${payload(form, target)}${separator}--> tail`;
      const masked = family === 'backtick'
        ? slashes % 2 === 0 && separator !== '\n\n'
        : slashes === 0 || (slashes === 2 && separator !== '\n\n');
      check(root, example, target, masked, `${family} slashes=${slashes} ${form} separator=${JSON.stringify(separator)} ${target}`);
      count++;
    }
    assert.equal(count, 18);
  });
}

test('formal: every bounded matching code run closes even after a backslash inside code', t => {
  const root = fixture(t);
  let count = 0;
  for (const width of [1, 2, 3]) for (const closerSlashes of [0, 1]) for (const form of FORMS) {
    const marker = '`'.repeat(width);
    const example = `Lead ${marker} ${payload(form, 'missing.txt')} ${'\\'.repeat(closerSlashes)}${marker} tail`;
    check(root, example, 'missing.txt', true, `valid run width=${width} closer slashes=${closerSlashes} ${form}`);
    count++;
  }
  assert.equal(count, 12);
});

test('formal: every bounded unmatched or mismatched code run retains the genuine dependency', t => {
  const root = fixture(t);
  let count = 0;
  for (const width of [1, 2]) for (const closer of ['absent', 'longer']) for (const form of FORMS) {
    const close = closer === 'absent' ? '' : '`'.repeat(width + 1);
    const example = `Lead ${'`'.repeat(width)} ${payload(form, 'missing.txt')} ${close} tail`;
    check(root, example, 'missing.txt', false, `unmatched width=${width} closer=${closer} ${form}`);
    count++;
  }
  assert.equal(count, 8);
});

test('formal: every bounded inline comment stays within its paragraph', t => {
  const root = fixture(t);
  let count = 0;
  for (const form of FORMS) for (const separator of SEPARATORS) {
    const example = `Lead <!--${separator}${payload(form, 'missing.txt')}${separator}--> tail`;
    check(root, example, 'missing.txt', separator !== '\n\n', `inline comment ${form} separator=${JSON.stringify(separator)}`);
    count++;
  }
  assert.equal(count, 6);
});
