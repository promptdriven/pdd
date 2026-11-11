// #3239: the core path rules take the changed files from Git and each owner from the `pdd owner` reader, in three
// states (owned on the base, unowned on the base, new in this PR). The cases are the rows of the Nov 11 report, with
// the real Path lines of those PRs (long lines cut after their files field) and small trees with the same file states.
import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname } from 'node:path';
import { execFileSync } from 'node:child_process';
import { ownerRead, ownerTable, pathRules } from '../src/autopilot-core.mjs';
import { listReportDrafts } from '../src/autopilot-reports.mjs';
import { runOwner } from '../src/file-owner.mjs';
import { coreWorld } from './helpers/core-world.mjs';

const bindings = modules => `${JSON.stringify({ schema_version: 'pdd.bindings.v1', modules: modules.map(([module, prompt]) => ({ module, stories: ['user_stories/s.md'], prompt })) }, null, 2)}\n`;
function tree(t, files) {
  const dir = fs.mkdtempSync(join(tmpdir(), 'pdd-paths-'));
  t.after(() => fs.rmSync(dir, { recursive: true, force: true }));
  for (const [path, text] of Object.entries(files)) { fs.mkdirSync(dirname(join(dir, path)), { recursive: true }); fs.writeFileSync(join(dir, path), text); }
  return { dir, files: Object.keys(files).sort() };
}
// The changed files of two trees as Git names them (A, M, D); a test gives a rename itself.
const diff = (base, head) => [...new Set([...Object.keys(base), ...Object.keys(head)])].sort()
  .flatMap(path => !(path in base) ? [{ status: 'A', path }] : !(path in head) ? [{ status: 'D', path }] : base[path] === head[path] ? [] : [{ status: 'M', path }]);
function check(t, { base, head, body, changed = diff(base, head), adopting = false }) {
  const b = tree(t, base), h = tree(t, head);
  return pathRules({ changed, baseFiles: b.files, before: ownerRead(fs, b.dir, b.files), after: ownerRead(fs, h.dir, h.files), body, adopting });
}
const MIN = 60 * 1000;
const endComments = (w, n) => w.comments(n).filter(body => body.includes('<!-- pdd:autopilot-core:end:'));
const jobFile = (w, n) => { const file = join(w.root, 'jobs', `${n}.json`); return fs.existsSync(file) ? JSON.parse(fs.readFileSync(file, 'utf8')) : null; };
const writeIn = (cwd, path, text) => { fs.mkdirSync(dirname(join(cwd, path)), { recursive: true }); fs.writeFileSync(join(cwd, path), text); };
const rule = red => red.startsWith('The PR body has no Path line') ? 'R6' : red.startsWith('pdd-bindings.json cannot be read at this head') ? 'R8' : / is new in this PR .* cannot take path e/.test(red) ? 'R7'
  : / is a new prompt that owns no new code file/.test(red) ? 'R3' : / exists on the base with no owner/.test(red) ? 'R4' : / is owned by /.test(red) ? 'R1' : red;
const R7_TEXT = 'is new in this PR (not on the base), so it cannot take path e (existing code that no prompt owns): a new code file takes path c, with its prompt and a binding or a Generated from header; any other new file takes path d.';
const R3_TEXT = 'is a new prompt that owns no new code file of this PR by a binding or header (its opening sentence alone is not enough): give the new code file a binding or a Generated from header (path c); a non-code change takes path d, with no new prompt.';

// ---- The recorded cases (report rows 1-10) ---------------------------------------------------------------------
const SPLIT = '# split\n\nThis module divides a whole-cent amount as evenly as possible. Its public binding is the module function `splitCents(cents, parts)` in `src/split.js`, exported at `tiny-format/split`.\n\n## Dependencies\n\nNone.\n';
const COUNT = '# count\n\nThis module formats a count and its supplied noun for display.\n\nPublic binding: module function `formatCount(count, singular, plural)` in `src/count.js`, exported at `tiny-format/count`.\n';
const ORDINAL = '# ordinal\n\nThis module owns `src/ordinal.js` and formats leaderboard positions as English ordinal text. Its public binding is the named module function `formatOrdinal(number)`.\n';
const SANDBOX = { 'pdd-bindings.json': bindings([['src/money.js', 'prompts/money.prompt.md']]), 'prompts/money.prompt.md': '# money\n\nThis module formats cents.\n', 'src/money.js': 'export const money = 1;\n',
  'README.md': '# tiny-format\n', 'docs/verification.md': '# Verification\n', 'package.json': '{"name":"tiny-format"}\n' };
// A new module of the sandbox: its prompt, code (with or without a header), binding (or none), Story and tests.
function module(name, prompt, { header = false, binding = false } = {}) {
  return { ...SANDBOX, 'README.md': `# tiny-format\n\n${name}\n`, 'docs/verification.md': `# Verification\n\n${name}\n`, 'package.json': `{"name":"tiny-format","exports":{"./${name}":"./src/${name}.js"}}\n`,
    ...(binding ? { 'pdd-bindings.json': bindings([['src/money.js', 'prompts/money.prompt.md'], [`src/${name}.js`, `prompts/${name}.prompt.md`]]) } : {}),
    [`prompts/${name}.prompt.md`]: prompt, [`src/${name}.js`]: `${header ? `// Generated from prompts/${name}.prompt.md\n` : ''}export const ${name} = 1;\n`,
    [`user_stories/${name}.md`]: `# ${name}\n`, [`test/${name}.test.js`]: 'test\n', [`test/${name}.formal.test.mjs`]: 'test\n' };
}
const ERRORS = { 'pdd-bindings.json': bindings([['docs/errors.md', 'prompts/errors.prompt.md']]), 'prompts/errors.prompt.md': '# Errors\n\nThe error table.\n', 'docs/errors.md': '# Errors\n',
  'test/errors-doc.test.js': 'test\n', 'user_stories/error-helper-links.md': '# Links\n' };
const ERRORS_HEAD = { ...ERRORS, 'prompts/errors.prompt.md': '# Errors\n\nThe error table, with links.\n', 'docs/errors.md': '# Errors\n\nLinks.\n', 'test/errors-doc.test.js': 'test 2\n', 'user_stories/error-helper-links.md': '# Links\n\nMore.\n' };
const PDD = { 'bin/pdd.mjs': '#!/usr/bin/env node\n// Generated from prompts/cli/bin-entry.prompt.md\n', 'prompts/cli/bin-entry.prompt.md': '# Bin entry\n\nOwn `bin/pdd.mjs`.\n',
  'src/workflow-replay.mjs': '// Generated from prompts/cli/workflow-replay.prompt.md\n', 'prompts/cli/workflow-replay.prompt.md': '# Workflow replay\n\nOwn `src/workflow-replay.mjs`.\n',
  'RUNBOOK.md': '# Runbook\n', 'skills/pdd-prompting/RUNBOOK.md': '# Runbook\n', 'user_stories/adopt-approved-corpus.md': '# Corpus\n', 'test/adopt-approved-corpus.test.mjs': 'test\n', 'test/runtime/adopt-approved-corpus.json': '{}\n' };
const PDD_3218 = { ...PDD, 'prompts/cli/workflow-replay.prompt.md': '# Workflow replay\n\nOwn `src/workflow-replay.mjs`.\n\nMore cases.\n', 'user_stories/adopt-approved-corpus.md': '# Corpus\n\nMore.\n',
  'test/adopt-approved-corpus.test.mjs': 'test 2\n', 'test/runtime/adopt-approved-corpus.json': '{"cases":[]}\n', 'test/adopt-approved-corpus.declaration-formal.test.mjs': 'test\n' };
const PDD_3223 = { ...PDD, 'RUNBOOK.md': '# Runbook\n\nprose_sha256.\n', 'skills/pdd-prompting/RUNBOOK.md': '# Runbook\n\nprose_sha256.\n' };
const NEW_MODULE_D = name => `Path: d — package.json, README.md, docs/verification.md, user_stories/${name}.md, test/${name}.test.js, test/${name}.formal.test.mjs — unowned — no contract change — Test: test/${name}.test.js`;
const CASES = [
  // [report row, PR and version, base, head, Path lines, expected rules]
  ['row 1: pdd #3218 v1 (built before the path rules)', PDD, PDD_3218, '', ['R6']],
  ['row 1: pdd #3218 v2 (after its repair)', PDD, PDD_3218, [
    'Path: a — prompts/cli/workflow-replay.prompt.md — prompts/cli/workflow-replay.prompt.md (owns src/workflow-replay.mjs; native code unchanged) — prompt changed — Test: test/adopt-approved-corpus.test.mjs',
    'Path: d — user_stories/adopt-approved-corpus.md, test/runtime/adopt-approved-corpus.json, test/adopt-approved-corpus.test.mjs, test/adopt-approved-corpus.declaration-formal.test.mjs — unowned — quote prompts/cli/workflow-replay.prompt.md:167 — Test: test/adopt-approved-corpus.test.mjs'], []],
  ['row 2: pdd #3223 v1 (bin/pdd.mjs only in the Test text; the false R1)', PDD, PDD_3223, [
    'Path: d — RUNBOOK.md, skills/pdd-prompting/RUNBOOK.md — unowned documentation — quote prompts/cli/runtime-preflight.prompt.md:184: “a missing key is refused (`add "prose_sha256": ""`)” — Test: done check: isolated Echo draft through `node bin/pdd.mjs test --fill-hash`; existing SKILLS2 copy-sync test.'], []],
  ['row 3: sandbox #75 v1 (a new file with a binding and a header on path c)', SANDBOX, module('split', SPLIT, { header: true, binding: true }), [
    'Path: c — prompts/split.prompt.md, src/split.js — prompts/split.prompt.md (new binding and Generated from header) — new prompt — Test: test/split.test.js',
    'Path: d — pdd-bindings.json, package.json, README.md, docs/verification.md, user_stories/split.md, test/split.test.js, test/split.formal.test.mjs — unowned — quote prompts/split.prompt.md:3 — Test: test/split.test.js'], []],
  ['row 4: sandbox #75 v3 (the missed red: new code on path e, the new prompt on path d)', SANDBOX, module('split', SPLIT), [
    'Path: e — src/split.js — unowned on the supplied base owner table; adopt: src/split.js — no contract change (ownership metadata repair) — Test: test/split.test.js',
    'Path: d — prompts/split.prompt.md — unowned — new prompt (unchanged by this repair; does not establish ownership on the base) — Test: test/runtime/split-cents.json',
    NEW_MODULE_D('split')], ['R7', 'R3']],
  ['row 5: sandbox #79 v1 (a new file with a header on path c)', SANDBOX, module('count', COUNT, { header: true }), [
    'Path: c — prompts/count.prompt.md, src/count.js — prompts/count.prompt.md (Generated from header) — new prompt — Test: test/count.test.js', NEW_MODULE_D('count')], []],
  ['row 6: sandbox #79 v2 (header removed, path e; the true R3)', SANDBOX, module('count', COUNT), [
    'Path: e — src/count.js — unowned (supplied base owner table) — no contract change — Test: test/count.test.js',
    'Path: d — prompts/count.prompt.md — unowned — new prompt — Test: test/runtime/format-count.json', NEW_MODULE_D('count')], ['R7', 'R3']],
  ['row 6: sandbox #79 v3 (a binding, path c)', SANDBOX, module('count', COUNT, { binding: true }), [
    'Path: c — src/count.js, prompts/count.prompt.md — prompts/count.prompt.md (pdd-bindings.json) — new prompt — Test: test/count.test.js',
    NEW_MODULE_D('count'), 'Path: d — pdd-bindings.json — unowned — quote prompts/count.prompt.md:5 (module src/count.js and formatCount) — Test: binding assertions'], []],
  ['row 7: sandbox #80 v1 (the owned doc on path d; the true R1)', ERRORS, ERRORS_HEAD, [
    'Path: d — docs/errors.md — owner prompts/errors.prompt.md (pdd-bindings.json) — prompt changed — Test: test/errors-doc.test.js',
    'Path: d — prompts/errors.prompt.md — owning prompt for docs/errors.md — prompt changed — Test: test/errors-doc.test.js',
    'Path: d — user_stories/error-helper-links.md, test/errors-doc.test.js — unowned (Story associated through pdd-bindings.json; no owning prompt names either artifact) — no contract change outside the owning prompt above — Test: test/errors-doc.test.js'], ['R1']],
  ['row 8: sandbox #80 v2 (docs/errors.md only in the owner text; the false R1 that ended #69)', ERRORS, ERRORS_HEAD, [
    'Path: a — docs/errors.md — owner prompts/errors.prompt.md (pdd-bindings.json) — prompt changed — Test: test/errors-doc.test.js',
    'Path: d — prompts/errors.prompt.md — owning prompt for docs/errors.md — prompt changed — Test: test/errors-doc.test.js',
    'Path: d — user_stories/error-helper-links.md, test/errors-doc.test.js — unowned (Story associated through pdd-bindings.json; no owning prompt names either artifact) — no contract change — Test: test/errors-doc.test.js'], []],
  ['row 9: sandbox #103 v1 (a new file with a binding on path c)', SANDBOX, module('ordinal', ORDINAL, { binding: true }), [
    'Path: c — prompts/ordinal.prompt.md, src/ordinal.js — prompts/ordinal.prompt.md (new owner) — new prompt — Test: test/ordinal.test.js',
    'Path: d — user_stories/ordinal.md, test/ordinal.test.js, test/ordinal.formal.test.mjs, package.json, pdd-bindings.json, README.md, docs/verification.md — unowned — prompt changed — Test: test/ordinal.test.js'], []],
  ['row 10: sandbox #103 v2 (the missed red: binding removed, path e; the prompt only names the file in prose)', SANDBOX, module('ordinal', ORDINAL), [
    'Path: e — src/ordinal.js — unowned — no contract change in this repair; ordinal behavior added by this PR — Test: test/ordinal.test.js',
    'Path: d — prompts/ordinal.prompt.md, user_stories/ordinal.md, test/ordinal.test.js, test/ordinal.formal.test.mjs, package.json, README.md, docs/verification.md — unowned — prompt changed — Test: test/ordinal.test.js'], ['R7', 'R3']],
];

test('P13 the recorded cases of the report: 3 true reds stay, 2 false reds go, 2 missed reds are caught, no other red', async t => {
  for (const [name, base, head, lines, expected] of CASES) {
    const body = `Fixes #1.\n\nRuntime: PASS\n${Array.isArray(lines) ? lines.join('\n') : lines}\n`;
    assert.deepEqual(check(t, { base, head, body }).reds.map(rule).sort(), [...expected].sort(), name);
  }
});

test('P1 (#80) an owned file is red on path d and passes on path a; a name in the owner text is not on that path', async t => {
  const [, , , before] = CASES.find(c => c[0].startsWith('row 7')), [, , , after] = CASES.find(c => c[0].startsWith('row 8'));
  assert.deepEqual(check(t, { base: ERRORS, head: ERRORS_HEAD, body: before.join('\n') }).reds,
    ['docs/errors.md is owned by prompts/errors.prompt.md (binding), so it cannot take path d: use path a or b.']);
  assert.deepEqual(check(t, { base: ERRORS, head: ERRORS_HEAD, body: after.join('\n') }).reds, []);
});

test('P2 (#3223) a header-owned file that the PR does not change is no red, wherever the body names it', async t => {
  const body = 'Path: d — RUNBOOK.md, skills/pdd-prompting/RUNBOOK.md, bin/pdd.mjs — unowned — no contract change — Test: done check: node bin/pdd.mjs test --fill-hash';
  assert.deepEqual(check(t, { base: PDD, head: PDD_3223, body }).reds, [], 'bin/pdd.mjs is not a changed file, even in the files field');
});

test('P3 an owned file that changes must be on a Path line; on a path a or b line it passes', async t => {
  const base = { 'pdd-bindings.json': bindings([['src/words.js', 'prompts/words.prompt.md']]), 'prompts/words.prompt.md': '# Words\n\nCount words.\n', 'src/words.js': 'export const words = 1;\n', 'README.md': '# R\n' };
  const head = { ...base, 'src/words.js': 'export const words = 2;\n', 'README.md': '# R\n\nWords.\n' };
  assert.deepEqual(check(t, { base, head, body: 'Path: d — README.md — unowned — no contract change — Test: done check' }).reds,
    ['src/words.js is owned by prompts/words.prompt.md (binding) and this PR changes it, but no Path line names it in its files field: put it on a path a or b line.']);
  assert.deepEqual(check(t, { base, head, body: 'Path: b — src/words.js — prompts/words.prompt.md — no contract change — Test: done check\nPath: d — README.md — unowned — no contract change — Test: done check' }).reds, []);
});

test('P4 only changed files count: a name in parentheses, in the owner field or after a reordered field', async t => {
  const base = { 'pdd-bindings.json': bindings([['docs/errors.md', 'prompts/errors.prompt.md']]), 'prompts/errors.prompt.md': '# Errors\n\nThe error table.\n', 'docs/errors.md': '# Errors\n', 'docs/b.md': '# B\n' };
  const onlyB = { ...base, 'docs/b.md': '# B\n\nMore.\n' }, both = { ...onlyB, 'docs/errors.md': '# Errors\n\nMore.\n' };
  const paren = 'Path: d — docs/b.md (owner prompts/x.prompt.md; for docs/errors.md) — unowned — no contract change — Test: done check';
  assert.deepEqual(check(t, { base, head: onlyB, body: paren }).reds, [], 'docs/errors.md is not changed: its name is ignored');
  assert.deepEqual(check(t, { base, head: both, body: paren }).reds.map(rule), ['R1'], 'a changed owned file in the files field is on that path');
  assert.match(check(t, { base, head: both, body: paren }).reds[0], /^docs\/errors\.md is owned by prompts\/errors\.prompt\.md \(binding\), so it cannot take path d/);
  for (const body of ['Path: d — docs/b.md — owning prompt for docs/errors.md — no contract change — Test: done check',
    'Path: d — unowned — docs/errors.md, docs/b.md — no contract change — Test: done check']) {
    assert.deepEqual(check(t, { base, head: both, body }).reds,
      ['docs/errors.md is owned by prompts/errors.prompt.md (binding) and this PR changes it, but no Path line names it in its files field: put it on a path a or b line.'], body);
  }
});

test('P5 (#75, #103) a new file on path e is red with the path c hint; a new test file on path d is not', async t => {
  const head = module('split', SPLIT, { header: true });
  const body = `Path: e — src/split.js — unowned — no contract change — Test: test/split.test.js\nPath: c — prompts/split.prompt.md — prompts/split.prompt.md — new prompt — Test: test/split.test.js\n${NEW_MODULE_D('split')}`;
  assert.deepEqual(check(t, { base: SANDBOX, head, body }).reds, [`src/split.js ${R7_TEXT}`], 'the header owns the file, so only R7 is red');
  const good = body.replace('Path: e — src/split.js', 'Path: c — src/split.js');
  assert.deepEqual(check(t, { base: SANDBOX, head, body: good }).reds, []);
});

test('P6 (#103) a new prompt whose opening sentence names the new file, with no binding and no header, is red (R3)', async t => {
  const head = module('ordinal', ORDINAL), h = tree(t, head);
  const owner = ownerTable(fs, h.dir, h.files).get('src/ordinal.js');
  assert.equal(owner.prompt, 'prompts/ordinal.prompt.md'); assert.equal(owner.how, 'prose'); assert.equal(owner.certain, false);
  const body = `Path: c — prompts/ordinal.prompt.md, src/ordinal.js — prompts/ordinal.prompt.md — new prompt — Test: test/ordinal.test.js\n${NEW_MODULE_D('ordinal')}`;
  assert.deepEqual(check(t, { base: SANDBOX, head, body }).reds, [`prompts/ordinal.prompt.md ${R3_TEXT}`]);
  assert.deepEqual(check(t, { base: SANDBOX, head: module('ordinal', ORDINAL, { header: true }), body }).reds, [], 'a header is enough');
});

test('P7 R4, R6 and adopt: ownership for an existing unowned file is red unless the issue adopts PDD; no Path line is one red', async t => {
  const base = { 'src/util.js': 'export const util = 0;\n', 'src/words.js': 'export const words = 0;\n', 'pdd-bindings.json': bindings([['src/words.js', 'prompts/words.prompt.md']]), 'prompts/words.prompt.md': '# Words\n\nCount.\n' };
  const head = { ...base, 'src/util.js': '// Generated from prompts/util.prompt.md\nexport const util = 1;\n', 'prompts/util.prompt.md': '# Util\n\nOwn `src/util.js`.\n' };
  const body = 'Path: c — src/util.js, prompts/util.prompt.md — prompts/util.prompt.md — new prompt — Test: done check';
  assert.deepEqual(check(t, { base, head, body }).reds.map(rule), ['R3', 'R4'], 'the new prompt owns no new file, and the existing file gets a header');
  assert.deepEqual(check(t, { base, head, body, adopting: true }).reds, [], 'adopting PDD may give an existing file its first owner');
  const words = { ...base, 'src/words.js': 'export const words = 1;\n' };
  assert.deepEqual(check(t, { base, head: words, body: 'No path here.' }).reds.map(rule), ['R6'], 'no Path line: R6 only, no per-file red');
});

test('P8 a renamed file keeps the state of its source; a header added on a moved unowned file is R4', async t => {
  const base = { 'pdd-bindings.json': bindings([['src/a.js', 'prompts/a.prompt.md']]), 'prompts/a.prompt.md': '# A\n\nCount.\n', 'src/a.js': 'export const a = 1;\n', 'src/u.js': 'export const u = 1;\n' };
  const owned = { ...base, 'pdd-bindings.json': bindings([['src/b.js', 'prompts/a.prompt.md']]), 'src/b.js': base['src/a.js'] }; delete owned['src/a.js'];
  const moved = [{ status: 'R100', path: 'src/b.js', from: 'src/a.js' }, { status: 'M', path: 'pdd-bindings.json' }];
  const result = check(t, { base, head: owned, changed: moved, body: 'Path: e — src/b.js — unowned — no contract change — Test: done check\nPath: d — pdd-bindings.json — unowned — no contract change — Test: done check' });
  assert.deepEqual(result.reds, ['src/b.js (moved from src/a.js) is owned by prompts/a.prompt.md (binding), so it cannot take path e: use path a or b.']);
  assert.match(result.owners, /^- src\/b\.js \(moved from src\/a\.js\): owned on the base by prompts\/a\.prompt\.md \(binding\)$/m);
  const unowned = { ...base, 'src/v.js': base['src/u.js'] }; delete unowned['src/u.js'];
  const rename = [{ status: 'R100', path: 'src/v.js', from: 'src/u.js' }];
  assert.deepEqual(check(t, { base, head: unowned, changed: rename, body: 'Path: e — src/v.js — unowned — no contract change — Test: done check' }).reds, [], 'moved unowned code may take path e');
  const headed = { ...unowned, 'src/v.js': `// Generated from prompts/a.prompt.md\n${base['src/u.js']}` };
  assert.deepEqual(check(t, { base, head: headed, changed: [{ status: 'R090', path: 'src/v.js', from: 'src/u.js' }], body: 'Path: e — src/v.js — unowned — no contract change — Test: done check' }).reds.map(rule), ['R4']);
});

const UNREADABLE = '{"modules":[{"module":"docs/errors.md","prompt":"prompts/errors.prompt.md"}]}\n';   // no schema_version
test('P9 decision 1: a pdd-bindings.json that the head broke is red (R8); one that main cannot read is no red, and its files are not checked', async t => {
  const base = { 'pdd-bindings.json': bindings([['docs/errors.md', 'prompts/errors.prompt.md']]), 'prompts/errors.prompt.md': '# Errors\n\nThe table.\n', 'docs/errors.md': '# Errors\n', 'src/h.js': '// Generated from prompts/errors.prompt.md\n' };
  const broke = check(t, { base, head: { ...base, 'pdd-bindings.json': UNREADABLE }, body: 'Path: d — pdd-bindings.json — unowned — no contract change — Test: done check' });
  assert.deepEqual(broke.reds, ['pdd-bindings.json cannot be read at this head: fix it (pdd owner needs valid JSON with schema_version pdd.bindings.v1 and a modules array, at most 64 KiB).']);
  const behind = check(t, { base, head: { ...base, 'pdd-bindings.json': UNREADABLE, 'README.md': '# R\n' }, changed: [{ status: 'A', path: 'README.md' }], body: 'Path: d — README.md — unowned — no contract change — Test: done check' });
  assert.deepEqual(behind.reds, [], 'a head that only lacks main\'s fix of pdd-bindings.json (the PR does not change it) gets it at the refresh: no R8');
  const main = { ...base, 'pdd-bindings.json': UNREADABLE }, b = tree(t, main);
  const read = ownerRead(fs, b.dir, b.files);
  assert.equal(read.bindings, false); assert.equal(read.owners.has('docs/errors.md'), false, 'never owned by an unknown prompt');
  assert.equal(read.unchecked.get('docs/errors.md'), 'pdd-bindings.json unreadable'); assert.equal(read.owners.get('src/h.js')?.how, 'header', 'a header still owns its file');
  const head = { ...main, 'docs/errors.md': '# Errors\n\nMore.\n', 'src/h.js': '// Generated from prompts/errors.prompt.md\nexport const h = 1;\n', 'src/new.js': 'export const n = 1;\n' };
  const result = check(t, { base: main, head, body: 'Path: d — docs/errors.md — unowned — no contract change — Test: done check\nPath: e — src/new.js — unowned — no contract change — Test: done check\nPath: b — src/h.js — prompts/errors.prompt.md — no contract change — Test: done check' });
  assert.deepEqual(result.reds.map(rule), ['R7'], 'main is broken, not this PR: no red for docs/errors.md; a new file is still checked');
  assert.deepEqual(result.unchecked, ['docs/errors.md']);
  assert.equal(result.wait, 'pdd-bindings.json cannot be read on main, so the owners of docs/errors.md are not checked');
  assert.match(result.owners, /^- docs\/errors\.md: not checked \(pdd-bindings\.json unreadable on main\)$/m);
  assert.doesNotMatch(result.owners, /unknown prompt/);
  assert.deepEqual(check(t, { base: { ...base }, head: { ...base, 'README.md': '# R\n' }, body: 'Path: d — README.md — unowned — no contract change — Test: done check' }).reds, [], 'a readable or missing file is no red');
});

test('P11 the reviewer gets the three states, and no ownership must-fix that the engine checks', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.baseCommit('pdd-bindings.json', bindings([['src/words.js', 'prompts/words.prompt.md']]));
  w.baseCommit('prompts/words.prompt.md', '# Words\n\nCount the words.\n');
  w.baseCommit('src/words.js', 'export const words = 0;\n');
  w.baseCommit('src/util.js', 'export const util = 0;\n');
  w.issue(17); await w.tick();
  const cwd = w.job(17, 'build').cwd;
  for (const [path, text] of [['src/words.js', 'export const words = 1;\n'], ['src/util.js', 'export const util = 1;\n'], ['test/util.test.js', 'test\n']]) { fs.mkdirSync(dirname(join(cwd, path)), { recursive: true }); fs.writeFileSync(join(cwd, path), text); }
  w.build(17, { body: 'Fixes #17\n\nRuntime: not run (no prompt changed)\nPath: b — src/words.js — prompts/words.prompt.md — no contract change — Test: done check\nPath: e — src/util.js — unowned — no contract change — Test: test/util.test.js\nPath: d — test/util.test.js, change-17.txt — unowned — no contract change — Test: test/util.test.js', result: { promptChanged: false } });
  await w.tick();
  assert.equal(w.job(17, 'repair'), undefined, 'no red');
  const review = w.job(17, 'review').input;
  assert.match(review, /^- src\/words\.js: owned on the base by prompts\/words\.prompt\.md \(binding\)$/m);
  assert.match(review, /^- src\/util\.js: unowned on the base$/m);
  assert.match(review, /^- test\/util\.test\.js: new in this PR \(not on the base\)$/m);
  assert.match(review, /A new code file with new behavior takes path c, with its prompt and a binding or header: that binding or header is required, so never ask to remove it\./);
  assert.match(review, /These are must-fixes: a new prompt for a non-code file; owned code that disagrees with its prompt\./);
  assert.doesNotMatch(review, /a binding or header added for an unowned file on the base;/, 'that must-fix left the reviewer rules: R4 checks it');
  assert.match(review, /Autopilot checks the ownership rules itself \(an owned file on path d or e or on no Path line, a new file on path e, a new prompt with no binding or header, a binding or header added for a file that is unowned on the base, no Path line\): do not report them\./);
});

test('P12 one owner reader: the engine table and `pdd owner` give the same answer for every file (#75 and #103 heads)', async t => {
  const repo = tree(t, { ...module('split', SPLIT), ...module('ordinal', ORDINAL), 'src/money.js': '// Generated from prompts/money.prompt.md\nexport const money = 1;\n' });
  execFileSync('git', ['init', '-q'], { cwd: repo.dir }); execFileSync('git', ['add', '.'], { cwd: repo.dir });
  let out = '';
  assert.equal(runOwner({ cwd: repo.dir, paths: repo.files, json: true }, { stdout: { write: text => { out += text; } }, stderr: { write: () => {} } }), 0);
  const cli = new Map(JSON.parse(out).files.map(row => [row.path, row])), engine = ownerTable(fs, repo.dir, repo.files);
  for (const path of repo.files) {
    const row = cli.get(path), mine = engine.get(path);
    assert.deepEqual(mine ? [mine.prompt, mine.owners, mine.certain] : [null, [], true], [row.owner, row.owners, row.certain], path);
    if (mine?.prompt) assert.equal(mine.how, row.source, path);
  }
  assert.equal(engine.get('src/split.js'), undefined, 'src/split.js: no owner (its prompt names it after the opening sentence)');
  assert.equal(engine.get('src/ordinal.js')?.how, 'prose');
  assert.equal(engine.get('src/money.js')?.how, 'binding', 'the binding comes first');
});

test('P14 main cannot read pdd-bindings.json: the merge waits, a quiet period ends the job with one PDD report; a fixed main merges', async t => {
  const waiting = async () => {
    const w = await coreWorld(t, { settings: { runs: 1 } });
    w.baseCommit('pdd-bindings.json', UNREADABLE); w.baseCommit('docs/x.md', '# X\n');
    w.issue(17); await w.tick();
    writeIn(w.job(17, 'build').cwd, 'docs/x.md', '# X\n\nMore.\n');
    const { pr } = w.build(17, { body: 'Fixes #17\n\nRuntime: not run (no prompt changed)\nPath: d — docs/x.md, change-17.txt — unowned — no contract change — Test: done check', result: { promptChanged: false } });
    await w.tick();
    assert.equal(w.job(17, 'repair'), undefined, 'no red for the PR');
    const review = w.job(17, 'review').input;
    assert.match(review, /^- docs\/x\.md: not checked \(pdd-bindings\.json unreadable on main\)$/m); assert.doesNotMatch(review, /unknown prompt/);
    w.review(17, 'PASS'); w.suite(17, 0); await w.tick(); await w.tick();
    assert.deepEqual(w.github.merges, [], 'the merge waits');
    assert.match(jobFile(w, 17).lastError, /^the merge waits: pdd-bindings\.json cannot be read on main, so the owners of docs\/x\.md are not checked$/);
    return { w, pr };
  };
  const { w } = await waiting();
  for (let i = 0; i < 4 && !endComments(w, 17).length; i++) { w.advance(20 * MIN); await w.tick(); }   // ticks, not one long gap (a gap is sleep)
  const end = endComments(w, 17);
  assert.equal(end.length, 1); assert.match(end[0], /the merge waits: pdd-bindings\.json cannot be read on main/); assert.match(end[0], /Cause: pdd \/ bindings-unreadable/);
  const drafts = listReportDrafts({ root: w.reportRoot }).filter(d => d.fingerprint.startsWith('pdd.autopilot-core.'));
  assert.equal(drafts.length, 1, 'one PDD report for the cause'); assert.match(drafts[0].detail, /pdd-bindings\.json cannot be read on main/);
  // Main is fixed while the PR waits: the path checks read the new base tip, and the PR merges after the base refresh.
  const { w: v, pr } = await waiting();
  v.baseCommit('pdd-bindings.json', bindings([])); await v.tick();
  const job = jobFile(v, 17);
  assert.deepEqual(job.paths.unchecked, [], 'read again at the new base tip'); assert.notEqual(job.head, pr.head);
  await v.tick(); v.github.setChecks(job.head); v.suite(17, 0); await v.tick();
  assert.deepEqual(v.github.merges, [pr.number]);
  assert.equal(listReportDrafts({ root: v.reportRoot }).filter(d => d.fingerprint.startsWith('pdd.autopilot-core.')).length, 0);
});

test('P15 the adopt report waits for the final head: a new file on path e never makes a draft; an existing unowned file does at the merge', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.baseCommit('src/old.js', 'export const old = 0;\n');
  w.issue(17); await w.tick();
  const cwd = w.job(17, 'build').cwd;
  writeIn(cwd, 'src/old.js', 'export const old = 1;\n'); writeIn(cwd, 'src/new.js', 'export const n = 1;\n');
  w.build(17, { body: 'Fixes #17\n\nRuntime: not run (no prompt changed)\nPath: e — src/old.js, src/new.js — unowned — no contract change — Test: done check\nPath: d — change-17.txt — unowned — no contract change — Test: done check', result: { promptChanged: false, adopt: ['src/old.js', 'src/new.js'] } });
  await w.tick();
  assert.match(w.job(17, 'repair')?.input ?? '', /src\/new\.js is new in this PR \(not on the base\), so it cannot take path e/);
  const adoptDrafts = () => listReportDrafts({ root: w.reportRoot }).filter(d => d.fingerprint.startsWith('pdd.autopilot-core.adopt-pdd'));
  assert.equal(adoptDrafts().length, 0, 'no draft before the final head');
  w.build(17, { role: 'repair', body: 'Fixes #17\n\nRuntime: not run (no prompt changed)\nPath: e — src/old.js — unowned — no contract change — Test: done check\nPath: d — src/new.js, change-17.txt — unowned — no contract change — Test: done check', result: { promptChanged: false, adopt: [] } });
  await w.tick();
  assert.equal(adoptDrafts().length, 0);
  w.review(17, 'PASS'); w.suite(17, 0); await w.tick(); await w.tick();
  assert.equal(w.github.merges.length, 1);
  const drafts = adoptDrafts();
  assert.equal(drafts.length, 1); assert.match(drafts[0].detail, /src\/old\.js/); assert.doesNotMatch(drafts[0].detail, /src\/new\.js/, 'a new file is never adopted');
});

test('P16 item 7: when the same path red comes back, the END text quotes the line and the field that the check read', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.baseCommit('pdd-bindings.json', bindings([['src/words.js', 'prompts/words.prompt.md']]));
  w.baseCommit('prompts/words.prompt.md', '# Words\n\nCount the words.\n'); w.baseCommit('src/words.js', 'export const words = 0;\n');
  w.issue(17); await w.tick();
  writeIn(w.job(17, 'build').cwd, 'src/words.js', 'export const words = 1;\n');
  const body = 'Fixes #17\n\nRuntime: not run (no prompt changed)\nPath: d — src/words.js, change-17.txt — unowned — no contract change — Test: done check';
  w.build(17, { body, result: { promptChanged: false } }); await w.tick();
  assert.ok(w.job(17, 'repair'), 'R1');
  assert.doesNotMatch(w.job(17, 'repair').input, /What the path checks read/, 'the repair gets the red as it is');
  w.build(17, { role: 'repair', body, result: { promptChanged: false } }); await w.tick();
  const end = endComments(w, 17);
  assert.equal(end.length, 1); assert.match(end[0], /a finding of the last round is still there/);
  assert.match(end[0], /What the path checks read: read "src\/words\.js, change-17\.txt" in the files field of the line "Path: d — src\/words\.js, change-17\.txt — unowned — no contract change — Test: done check"/);
});
