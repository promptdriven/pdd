import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { captureSource } from '../src/runtime-preflight.mjs';

// Approved source: lead12:22 and runtime-preflight's Code examples contract.
// Exhaustive only over this literal finite grammar, not arbitrary CommonMark:
// 2 fence families x 4 containers x 3 endings = 24 documents, each captured
// successfully and with missing/secret genuine-after controls = 72 captures.
// Expected membership is stated independently of production parser helpers.
const DOCUMENT = 'docs/case.md';
const CONTAINERS = [
  { name: 'quote', first: '> ', rest: '> ' },
  { name: 'list', first: '- ', rest: '  ' },
  { name: 'quote-list', first: '> - ', rest: '>   ' },
  { name: 'list-quote', first: '- > ', rest: '  > ' },
];
const ENDINGS = ['matching-close', 'container-end-unclosed', 'decoys-before-longer-close'];
const SELECTED = ['after.svg', 'after.txt', 'bare.json', 'before.txt', 'chosen.svg'];
const DEFINITIONS = [
  '[full]: missing-full.txt', '[full-image]: missing-full.svg',
  '[collapsed]: missing-collapsed.txt', '[collapsed-image]: missing-collapsed.svg',
  '[shortcut]: missing-shortcut.txt', '[shortcut-image]: missing-shortcut.svg',
];
const EXAMPLE = [
  '[inline](missing-inline.txt) ![inline image](missing-inline.svg)',
  '[label][full] ![label][full-image] [collapsed][] ![collapsed-image][] [shortcut] ![shortcut-image]',
  '[chosen]: missing-shadow.svg',
  '[only-in-code]: missing-code-definition.svg',
  '- `missing-bare.json`: illustrative declaration',
  '## Fictional example heading',
  '[example after heading](missing-after-heading.txt)',
];

function documentFor(marker, container, ending, after = 'after.txt') {
  const length = ending === 'decoys-before-longer-close' ? 4 : 3;
  const lines = [`${container.first}${marker.repeat(length)}markdown`];
  const append = line => lines.push(container.rest + line);
  for (const line of EXAMPLE) append(line);
  if (ending === 'matching-close') append(marker.repeat(length));
  if (ending === 'decoys-before-longer-close') {
    append(marker.repeat(3));
    append('![after short marker](missing-short.svg)');
    append((marker === '`' ? '~' : '`').repeat(4));
    append('![after different marker](missing-other.svg)');
    append(marker.repeat(5));
  }
  // A blank and an unindented line end every stated container. An unclosed
  // contained fence cannot consume the genuine declarations after this point.
  return [
    '# Synthetic container example', ...DEFINITIONS, '## Dependencies',
    '[before](before.txt)', '', ...lines, '',
    `[after](${after})`, '![after image](after.svg)',
    '[outside][chosen]', '[chosen]: chosen.svg',
    '[unresolved outside][only-in-code] ![unresolved outside][only-in-code]',
    '- `bare.json`: required context', '',
  ].join('\n');
}

function fixture(t) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-container-formal-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const init = spawnSync('git', ['init', '-q'], { cwd: root, encoding: 'utf8' });
  assert.equal(init.status, 0, init.stderr);
  mkdirSync(join(root, 'docs'));
  writeFileSync(join(root, 'pdd-source.json'), JSON.stringify({ include: [DOCUMENT] }));
  for (const file of [...SELECTED, 'credentials.json']) {
    writeFileSync(join(root, 'docs', file), `Synthetic fixture ${file}\n`);
  }
  return root;
}

function outcome(root, markdown) {
  writeFileSync(join(root, DOCUMENT), markdown);
  try {
    return { capture: captureSource(root, { tests: [] }) };
  } catch (error) {
    return { failure: { exitCode: error.exitCode, message: error.message } };
  }
}

test('formal: every bounded container fence excludes examples and retains genuine dependencies', t => {
  const root = fixture(t);
  let configurations = 0, captures = 0;
  for (const marker of ['`', '~']) for (const container of CONTAINERS) for (const ending of ENDINGS) {
    configurations++;
    const label = `${marker} ${container.name} ${ending}`;
    const markdown = documentFor(marker, container, ending);
    const good = outcome(root, markdown); captures++;
    assert.equal(good.failure, undefined, `${label}: ${JSON.stringify(good.failure)}`);
    assert.deepEqual(good.capture.files.map(file => file.path),
      [DOCUMENT, ...SELECTED.map(file => `docs/${file}`)].sort(), `${label}: exact genuine membership`);
    const archived = spawnSync('tar', ['-xOf', '-', DOCUMENT], { input: good.capture.tar });
    assert.equal(archived.status, 0, String(archived.stderr));
    assert.deepEqual(archived.stdout, Buffer.from(markdown), `${label}: archive preserves authored bytes`);
    assert.deepEqual(readFileSync(join(root, DOCUMENT)), Buffer.from(markdown), `${label}: discovery does not edit source`);

    rmSync(join(root, 'docs/after.txt'));
    const missing = outcome(root, markdown); captures++;
    assert.equal(missing.failure?.exitCode, 4, `${label}: missing genuine after dependency refuses`);
    assert.ok(missing.failure.message.includes(DOCUMENT), `${label}: missing refusal identifies owner`);
    assert.ok(missing.failure.message.includes('docs/after.txt'), `${label}: missing refusal identifies genuine target`);
    assert.ok(missing.failure.message.includes('not a Git-visible file'), `${label}: missing-file refusal`);
    writeFileSync(join(root, 'docs/after.txt'), 'Synthetic restored genuine dependency\n');

    const unsafe = outcome(root, documentFor(marker, container, ending, 'credentials.json')); captures++;
    assert.equal(unsafe.failure?.exitCode, 4, `${label}: secret genuine after dependency refuses`);
    assert.ok(unsafe.failure.message.includes(DOCUMENT), `${label}: privacy refusal identifies owner`);
    assert.ok(unsafe.failure.message.includes('docs/credentials.json'), `${label}: privacy refusal identifies genuine target`);
    assert.ok(unsafe.failure.message.includes('name looks like a secret'), `${label}: privacy refusal`);
  }
  assert.equal(configurations, 24);
  assert.equal(captures, 72);
});
