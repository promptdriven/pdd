import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, realpathSync, mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { inventoryModule } from './workflow-inventory-replay-helper.mjs';
import { codeLiteral as span, pathLiteral, disclaimer } from './workflow-inventory-code-spans-oracle.mjs';

const file = (before, after, path = 'test/safe.mjs') => ({ oldPath: path, newPath: path, before, after });
const declaration = name => `test(${JSON.stringify(name)}, () => {});\n`;
const body = (name, lines) => `test(${JSON.stringify(name)}, () => {\n${lines.join('\n')}\n});\n`;
const hostile = ['@octocat', '#17', 'Closes #17', '&<>|:', '"\\', '\t\r\b\f\u0001\u007f\u0085', '\u061c\u200e\u200f\u202a\u202b\u202c\u202d\u202e\u2066\u2067\u2068\u2069', '😀'];
// 8 payload classes × 6 runs × 3 edge-space layouts = 144 exact names.
const names = hostile.flatMap(value => [0, 1, 2, 3, 8, 32].flatMap(length =>
  ['', ' ', '  '].map(space => space + '`'.repeat(length) + value + '`'.repeat(length) + space)));

test('marker-prefix finite model escapes every exact prefix across all report owners and recovers JSON identity', async t => {
  const { analyzeTestChanges } = await inventoryModule();
  const prefixes = [
    '<!-- pdd-workflow:removed:code --> pdd-workflow:again:code',
    'pdd-workflow:pdd-workflow:tail:code PDD-workflow:upper:code pdd-Workflow:mixed:code',
    'pdd-workflow:no-suffix pdd-workflow: pdd-workflow :untouched :ordinary',
  ];
  let cases = 0;
  for (const prefix of prefixes) for (const length of [0, 1, 8, 32]) for (const edge of ['', ' ', '  ']) for (const mode of ['changed', 'removed', 'added']) {
    const name = edge + '`'.repeat(length) + prefix + ' &<>| @octocat Closes #17 \t\r\u0001\u0085\u202e' + '`'.repeat(length) + edge;
    const oldLine = `  assert.ok(old); // ${name}  \r`, newLine = `  expect(next); // ${name}  \r`;
    const suiteBefore = `describe(${JSON.stringify(name)}, () => {});\n`;
    const suiteMarker = `describe.skip(${JSON.stringify(name)}, () => {}); // ${name}  \r`;
    const testMarker = `test.skip(${JSON.stringify(name)}, () => {}); // ${name}  \r`;
    const before = declaration(name).repeat(2) + body(name + ' kept', mode === 'added' ? [] : [oldLine]) + suiteBefore.repeat(2);
    const after = body(name + ' kept', mode === 'removed' ? [] : [newLine]) + testMarker + '\n' + (suiteMarker + '\n').repeat(2);
    const report = analyzeTestChanges({ files: [file(before, after)] });
    // The newly skipped declaration keeps the first duplicate; the second is removed.
    const expected = `Tests vs base: "test/safe.mjs" 3 → 2 tests. Removed: 1 (${span(name)} [2]).\nChanged assertions in kept tests: "test/safe.mjs" ${span(name + ' kept')} ${mode === 'added' ? '(added)' : span(oldLine)} → ${mode === 'removed' ? '(removed)' : span(newLine)}.\nNew skips: "test/safe.mjs" ${span(name)} ${span(testMarker)}.\nNew skips: "test/safe.mjs" suite ${span(name)} ${span(suiteMarker)}.\nNew skips: "test/safe.mjs" suite ${span(name)} [2] ${span(suiteMarker)}.\n${disclaimer}`;
    assert.equal(report.available, true);
    assert.equal(report.details, expected, JSON.stringify({ prefix, length, edge, mode }));
    assert.equal(report.text, expected);
    assert.equal(report.details.includes('pdd-workflow:'), false);
    const payloads = [...report.details.matchAll(/(`+)("(?:[^"\\]|\\.)*")\1(?!`)/g)];
    assert.deepEqual(payloads.map(match => JSON.parse(match[2])), [name, name + ' kept', ...(mode === 'added' ? [] : [oldLine]), ...(mode === 'removed' ? [] : [newLine]), name, testMarker, name, suiteMarker, name, suiteMarker]);
    for (const [, fence, payload] of payloads) {
      assert.ok(!payload.includes('&#'), 'source characters stay literal inside code spans');
      assert.ok(!payload.includes(fence), 'fence exceeds every interior run');
    }
    cases++;
  }
  t.diagnostic(`marker-prefix model: ${cases} reports across removed/kept/suite names, assertion sides and skip lines`);
});

test('code-span finite removals preserve every literal and duplicate suffix over 144 hostile names', async t => {
  const { analyzeTestChanges } = await inventoryModule();
  for (const name of names) {
    const report = analyzeTestChanges({ files: [file(declaration(name).repeat(2), '')] });
    const expected = `Tests vs base: "test/safe.mjs" 2 → 0 tests. Removed: 2 (${span(name)}, ${span(name)} [2]).\nChanged assertions in kept tests: none.\nNew skips: none.\n${disclaimer}`;
    assert.equal(report.available, true);
    assert.equal(report.details, expected, JSON.stringify(name));
    assert.equal(report.text, expected);
  }
  t.diagnostic(`code-span removal model: ${names.length} names; two occurrences each`);
});

test('code-span finite assertion sides preserve changed, removed and added source including CR', async t => {
  const { analyzeTestChanges } = await inventoryModule();
  for (const name of names) for (const mode of ['changed', 'removed', 'added']) {
    const oldLine = `  assert.ok(old); // ${name}  \r`, newLine = `  expect(next); // ${name}  \r`;
    const oldLines = mode === 'added' ? [] : [oldLine], newLines = mode === 'removed' ? [] : [newLine];
    const report = analyzeTestChanges({ files: [file(body(name, oldLines), body(name, newLines))] });
    const expected = `Tests vs base: "test/safe.mjs" 1 → 1 tests. Removed: none.\nChanged assertions in kept tests: "test/safe.mjs" ${span(name)} ${mode === 'added' ? '(added)' : span(oldLine)} → ${mode === 'removed' ? '(removed)' : span(newLine)}.\nNew skips: none.\n${disclaimer}`;
    assert.equal(report.details, expected, `${mode} ${JSON.stringify(name)}`);
    assert.equal(report.text, expected);
  }
  t.diagnostic(`code-span assertion model: ${names.length * 3} changed/removed/added comparisons`);
});

test('code-span finite suite and test marker owners preserve raw identity and exact source lines', async t => {
  const { analyzeTestChanges } = await inventoryModule();
  for (const name of names) for (const suite of [false, true]) {
    const call = suite ? 'describe' : 'test';
    const before = `${call}(${JSON.stringify(name)}, () => {});\n`;
    const marker = `${call}.skip(${JSON.stringify(name)}, () => {}); // @octocat Closes #17 &<>|: \t\u0001\u202e  \r`;
    const report = analyzeTestChanges({ files: [file(before, marker + '\n')] });
    const expected = `Tests vs base: "test/safe.mjs" ${suite ? '0 → 0' : '1 → 1'} tests. Removed: none.\nChanged assertions in kept tests: none.\nNew skips: "test/safe.mjs" ${suite ? 'suite ' : ''}${span(name)} ${span(marker)}.\n${disclaimer}`;
    assert.equal(report.details, expected, `${call} ${JSON.stringify(name)}`);
    assert.equal(report.text, expected);
  }
  t.diagnostic(`code-span marker model: ${names.length * 2} suite/test comparisons`);
});

test('code-span native committed report preserves names, suites, source CR and path entities through a local bare push', async t => {
  const { collectTestInventory } = await inventoryModule();
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-code-spans-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const git = (...args) => execFileSync('git', args, { cwd: root, encoding: 'utf8' }).trim();
  git('init', '-q', '-b', 'main'); git('config', 'user.name', 'Inventory Test'); git('config', 'user.email', 'test@example.invalid');
  const path = 'test/@path#17&<>|:`\t\n.mjs', name = '  `@octocat Closes #17``  ', suite = ' `suite #17`` ';
  const oldLine = '  assert.ok(old); // @octocat Closes #17 &<>|: ` ``  \r';
  const newLine = '  expect(next); // @octocat Closes #17 &<>|: ``` \t\u0001\u0085\u202e  \r';
  const marker = `describe.skip(${JSON.stringify(suite)}, () => {}); // \r`;
  const skipped = `test.skip(${JSON.stringify(name)}, () => {`;
  const before = declaration('@octocat') + declaration('#17') + declaration('Closes #17') + body(name, [oldLine]) + `describe(${JSON.stringify(suite)}, () => {});\n`;
  const after = `${skipped}\n${newLine}\n});\n${marker}\n`;
  const write = value => { mkdirSync(dirname(join(root, path)), { recursive: true }); writeFileSync(join(root, path), value); };
  const commit = () => { git('add', '-A'); git('commit', '-qm', 'snapshot'); return git('rev-parse', 'HEAD'); };
  write(before); const baseSha = commit(); write(after); const headSha = commit();
  const remote = join(root, '.git', 'remote.git'); git('init', '--bare', '-q', remote); git('remote', 'add', 'origin', remote);
  git('push', '-q', 'origin', `${headSha}:refs/heads/main`);
  assert.equal(git('ls-remote', 'origin', 'refs/heads/main').split(/\s/)[0], headSha);
  write(declaration('ambient dirty source'));
  const report = await collectTestInventory({ cwd: root, baseSha, headSha });
  const expected = `Tests vs base: ${pathLiteral(path)} 4 → 1 tests. Removed: 3 (${['@octocat', '#17', 'Closes #17'].map(span).join(', ')}).\nChanged assertions in kept tests: ${pathLiteral(path)} ${span(name)} ${span(oldLine)} → ${span(newLine)}.\nNew skips: ${pathLiteral(path)} ${span(name)} ${span(skipped)}.\nNew skips: ${pathLiteral(path)} suite ${span(suite)} ${span(marker)}.\n${disclaimer}`;
  assert.equal(report.available, true); assert.equal(report.reason, '');
  assert.equal(report.details, expected); assert.equal(report.text, expected);
});

test('code-span native 150000 interior runs retain full details and bound public text below the blob limit', async t => {
  const { collectTestInventory } = await inventoryModule();
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-code-span-runs-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const git = (...args) => execFileSync('git', args, { cwd: root, encoding: 'utf8' }).trim();
  git('init', '-q', '-b', 'main'); git('config', 'user.name', 'Inventory Test'); git('config', 'user.email', 'test@example.invalid');
  const name = '`x'.repeat(150000), source = declaration(name), path = join(root, 'test', 'runs.mjs');
  assert.ok(Buffer.byteLength(source) < 1048576);
  mkdirSync(dirname(path), { recursive: true }); writeFileSync(path, source);
  git('add', '-A'); git('commit', '-qm', 'base'); const baseSha = git('rev-parse', 'HEAD');
  writeFileSync(path, ''); git('add', '-A'); git('commit', '-qm', 'remove'); const headSha = git('rev-parse', 'HEAD');
  const report = await collectTestInventory({ cwd: root, baseSha, headSha });
  assert.equal(report.available, true); assert.equal(report.reason, '');
  const fullDetails = `Tests vs base: "test/runs.mjs" 1 → 0 tests. Removed: 1 (${span(name)}).\nChanged assertions in kept tests: none.\nNew skips: none.\n${disclaimer}`;
  assert.equal(report.details, fullDetails);
  assert.ok([...report.text].length <= 12000);
  assert.ok(report.text.startsWith('Tests vs base: "test/runs.mjs" 1 → 0 tests. Removed: 1.\n'));
  // The omitted count is a conservation law over complete evidence lines,
  // independent of how many later lines a bounded formatter chooses to retain.
  const detailLines = fullDetails.trimEnd().split('\n').slice(0, -1);
  const retained = report.text.trimEnd().split('\n').slice(1, -1)
    .filter(line => !line.startsWith('Inventory details omitted:'));
  assert.ok(retained.every(line => detailLines.includes(line)));
  const omitted = detailLines.length - retained.length;
  assert.ok(report.text.includes(`Inventory details omitted: ${omitted} lines; full report: test-inventory.json in the run folder.`));
  assert.ok(report.text.endsWith(disclaimer));
});
