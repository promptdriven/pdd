import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import {
  applyPreExistingDiffGuard,
  extractFindingLocation,
  guardPreExistingFindings,
  parseReviewOutput,
  parseUnifiedDiffHunks,
} from '../src/autopilot-core.mjs';
import { coreWorld } from './helpers/core-world.mjs';

function seedBaseFiles(w, files) {
  for (const [rel, content] of Object.entries(files)) {
    w.baseCommit(rel, content);
  }
  w.git(w.cwd, 'fetch', '-q', 'origin', 'main');
  w.git(w.cwd, 'reset', '-q', '--hard', 'origin/main');
}

test('#3559 (1): parseUnifiedDiffHunks parses modified, added, deleted, renamed, binary, and pure-deletion hunks linearly', () => {
  const diff = [
    'diff --git a/src/auth.mjs b/src/auth.mjs',
    'index 1111111..2222222 100644',
    '--- a/src/auth.mjs',
    '+++ b/src/auth.mjs',
    '@@ -10,2 +10,3 @@ export function check() {',
    '+  return true;',
    '@@ -40,4 +41,0 @@ export function legacy() {',
    '-  old();',
    'diff --git a/src/new-feature.mjs b/src/new-feature.mjs',
    'new file mode 100644',
    'index 0000000..3333333',
    '--- /dev/null',
    '+++ b/src/new-feature.mjs',
    '@@ -0,0 +1,20 @@',
    '+export const x = 1;',
    'diff --git a/src/old-name.mjs b/src/new-name.mjs',
    'similarity index 80%',
    'rename from src/old-name.mjs',
    'rename to src/new-name.mjs',
    '--- a/src/old-name.mjs',
    '+++ b/src/new-name.mjs',
    '@@ -5,1 +5,2 @@',
    '+const y = 2;',
    'diff --git a/src/removed.mjs b/src/removed.mjs',
    'deleted file mode 100644',
    '--- a/src/removed.mjs',
    '+++ /dev/null',
    '@@ -1,5 +0,0 @@',
    '-gone();',
    'diff --git a/src/emptied.mjs b/src/emptied.mjs',
    '--- a/src/emptied.mjs',
    '+++ b/src/emptied.mjs',
    '@@ -1,3 +0,0 @@',
    '-a();',
    'diff --git a/assets/icon.png b/assets/icon.png',
    'Binary files a/assets/icon.png and b/assets/icon.png differ',
  ].join('\n');

  const scope = parseUnifiedDiffHunks(diff);
  assert.deepEqual(scope.files.get('src/auth.mjs'), {
    added: false,
    deleted: false,
    binary: false,
    modeChanged: false,
    ranges: [[10, 12], [41, 42]],
  });
  assert.equal(scope.files.get('src/new-feature.mjs').added, true);
  assert.equal(scope.renamedFrom.get('src/old-name.mjs'), 'src/new-name.mjs');
  assert.deepEqual(scope.files.get('src/new-name.mjs').ranges, [[5, 6]]);
  assert.equal(scope.files.get('src/removed.mjs').deleted, true);
  assert.deepEqual(scope.files.get('src/emptied.mjs').ranges, [[1, 4]]);
  assert.equal(scope.files.get('assets/icon.png').binary, true);
});

test('#3559 (2): extractFindingLocation parses standard prefixes, ranges, #L syntax, markdown links, and rejects traversal/URLs', () => {
  assert.deepEqual(extractFindingLocation('P1 src/auth.mjs:42 missing check'), {
    path: 'src/auth.mjs', startLine: 42, endLine: 42, range: [42, 42],
  });
  assert.deepEqual(extractFindingLocation('P2 `./src/auth.mjs:10-15` range overlap'), {
    path: 'src/auth.mjs', startLine: 10, endLine: 15, range: [10, 15],
  });
  assert.deepEqual(extractFindingLocation('P2 [src/auth.mjs#L20-L25](https://example.com) markdown link'), {
    path: 'src/auth.mjs', startLine: 20, endLine: 25, range: [20, 25],
  });
  assert.deepEqual(extractFindingLocation('P1 src\\win\\mod.mjs:8:12 windows separator with col'), {
    path: 'src/win/mod.mjs', startLine: 8, endLine: 8, range: [8, 8],
  });
  assert.deepEqual(extractFindingLocation('P2 Makefile (line 14) extensionless file'), {
    path: 'Makefile', startLine: 14, endLine: 14, range: [14, 14],
  });
  assert.equal(extractFindingLocation('P1 ../outside.mjs:10 path traversal'), null);
  assert.equal(extractFindingLocation('P1 https://example.com:443/foo not a repo file'), null);
  assert.equal(extractFindingLocation('P1 missing file and line completely'), null);
  assert.equal(extractFindingLocation('P2 src/auth.mjs missing line number'), null);
});

test('#3559 (3): guardPreExistingFindings fails closed on diff overlap, added/deleted/binary/renamed files, missing location, multi-location evasion, >20-item padding, and null diffScope', () => {
  const diff = [
    'diff --git a/src/auth.mjs b/src/auth.mjs',
    '--- a/src/auth.mjs',
    '+++ b/src/auth.mjs',
    '@@ -20,5 +20,5 @@',
    '+change();',
    '@@ -50,2 +50,0 @@',
    '-deleted();',
    'diff --git a/src/added.mjs b/src/added.mjs',
    'new file mode 100644',
    '--- /dev/null',
    '+++ b/src/added.mjs',
    '@@ -0,0 +1,5 @@',
    '+export const a = 1;',
    'diff --git a/src/old-util.mjs b/src/new-util.mjs',
    'rename from src/old-util.mjs',
    'rename to src/new-util.mjs',
    '--- a/src/old-util.mjs',
    '+++ b/src/new-util.mjs',
    '@@ -8,1 +8,2 @@',
    '+export const b = 2;',
    'diff --git a/src/deleted.mjs b/src/deleted.mjs',
    'deleted file mode 100644',
    '--- a/src/deleted.mjs',
    '+++ /dev/null',
    '@@ -1,2 +0,0 @@',
    '-x();',
  ].join('\n');
  const scope = parseUnifiedDiffHunks(diff);

  // Outside-diff items stay in preExisting
  const cleanRes = guardPreExistingFindings([
    'P2 src/untouched.mjs:12 legacy bug in untouched file',
    'P2 src/auth.mjs:5 bug strictly before changed hunk',
    'P2 src/auth.mjs:35 bug strictly after changed hunk',
  ], scope);
  assert.deepEqual(cleanRes.promoted, []);
  assert.equal(cleanRes.preExisting.length, 3);

  // Every evasion vector is deterministically promoted
  const evasionItems = [
    'P1 src/auth.mjs:22 directly inside changed hunk',
    'P2 src/auth.mjs:18-21 range partially overlapping hunk start',
    'P2 src/auth.mjs:24-30 range partially overlapping hunk end',
    'P2 src/auth.mjs:50 pure deletion boundary',
    'P1 src/added.mjs:999 newly added file at any line',
    'P2 src/old-util.mjs:8 renamed file citing old path',
    'P2 src/deleted.mjs:2 deleted file',
    'P1 broken auth without file or line',
    'P2 src/auth.mjs file without line number',
    'P1 src/untouched.mjs:1 and src/auth.mjs:22 multi-location hiding changed hunk second',
  ];
  const evasionRes = guardPreExistingFindings(evasionItems, scope);
  assert.equal(evasionRes.promoted.length, evasionItems.length);
  assert.deepEqual(evasionRes.preExisting, []);

  // Padding >20 outside-diff items before a changed-hunk bug cannot hide item #22
  const padded = [];
  for (let i = 1; i <= 22; i++) padded.push(`P2 src/untouched.mjs:${i} padding item ${i}`);
  padded.push('P1 src/auth.mjs:21 real regression hidden past index 20');
  const paddedRes = guardPreExistingFindings(padded, scope);
  assert.deepEqual(paddedRes.promoted, ['P1 src/auth.mjs:21 real regression hidden past index 20']);
  assert.equal(paddedRes.preExisting.length, 20);

  // Unavailable diffScope (null) fails closed and promotes everything
  const failClosed = guardPreExistingFindings(['P2 src/untouched.mjs:12 outside diff when diff unavailable'], null);
  assert.deepEqual(failClosed.promoted, ['P2 src/untouched.mjs:12 outside diff when diff unavailable']);
  assert.deepEqual(failClosed.preExisting, []);

  // Scalar non-array coercion
  const scalar = guardPreExistingFindings('P2 src/auth.mjs:22 scalar string', scope);
  assert.deepEqual(scalar.promoted, ['P2 src/auth.mjs:22 scalar string']);
});

test('#3559 (4): parseReviewOutput and applyPreExistingDiffGuard flip PASS->FAIL on promoted P1/P2, route promoted P3 to followUps, and keep outside-diff preExisting non-blocking', () => {
  const diffText = [
    'diff --git a/src/app.mjs b/src/app.mjs',
    '--- a/src/app.mjs',
    '+++ b/src/app.mjs',
    '@@ -10,2 +10,3 @@',
    '+  return bad();',
  ].join('\n');

  // 1. PASS with outside-diff preExisting remains PASS
  const passRaw = JSON.stringify({
    verdict: 'PASS',
    head: 'abc123',
    summary: 'Clean PR.\nRead: src/app.mjs',
    mustFix: [],
    preExisting: ['P2 src/legacy.mjs:88 unrelated pre-existing bug'],
  });
  const passParsed = parseReviewOutput(passRaw, { fromResultFile: true, diffText });
  assert.equal(passParsed.verdict, 'PASS');
  assert.deepEqual(passParsed.mustFix, []);
  assert.deepEqual(passParsed.preExisting, ['P2 src/legacy.mjs:88 unrelated pre-existing bug']);

  // 2. PASS trying to excuse a changed-hunk P1 as preExisting flips to FAIL
  const sneakRaw = JSON.stringify({
    verdict: 'PASS',
    head: 'abc123',
    summary: 'Tried to wave through.\nRead: src/app.mjs',
    mustFix: [],
    preExisting: [
      'P1 src/app.mjs:11 introduced regression disguised as pre-existing',
      'P2 src/legacy.mjs:88 genuinely outside diff',
    ],
  });
  const sneakParsed = parseReviewOutput(sneakRaw, { fromResultFile: true, diffText });
  assert.equal(sneakParsed.verdict, 'FAIL');
  assert.deepEqual(sneakParsed.mustFix, ['P1 src/app.mjs:11 introduced regression disguised as pre-existing']);
  assert.deepEqual(sneakParsed.preExisting, ['P2 src/legacy.mjs:88 genuinely outside diff']);

  // 3. Promoted P3 inside changed hunk becomes non-blocking followUp (not mustFix)
  const p3Promoted = applyPreExistingDiffGuard({
    verdict: 'PASS',
    head: 'abc123',
    summary: 'Nit only.',
    mustFix: [],
    preExisting: ['P3 src/app.mjs:11 minor naming nit'],
  }, diffText);
  assert.equal(p3Promoted.verdict, 'PASS');
  assert.deepEqual(p3Promoted.mustFix, []);
  assert.deepEqual(p3Promoted.followUps, ['P3 src/app.mjs:11 minor naming nit']);
  assert.deepEqual(p3Promoted.preExisting, []);

  // 4. FAIL with empty mustFix and only outside-diff preExisting stays FAIL (fail-closed)
  const failEmpty = applyPreExistingDiffGuard({
    verdict: 'FAIL',
    head: 'abc123',
    summary: 'Reviewer marked FAIL without mustFix.',
    mustFix: [],
    preExisting: ['P2 src/legacy.mjs:88 outside diff'],
  }, diffText);
  assert.equal(failEmpty.verdict, 'FAIL');
  assert.deepEqual(failEmpty.preExisting, ['P2 src/legacy.mjs:88 outside diff']);
});

test('#3559 (5): end-to-end reviewState with real git diff -U0 keeps outside-diff preExisting non-blocking and promotes overlapping preExisting to FAIL/repair', async t => {
  // Scenario A: Outside-diff preExisting in untouched file + modified file outside hunk -> PASS & merges, logged in PR review comment
  const wPass = await coreWorld(t, { settings: { runs: 1 } });
  const baseLines = Array.from({ length: 40 }, (_, i) => `export const line${i + 1} = ${i + 1};`).join('\n') + '\n';
  seedBaseFiles(wPass, {
    'src/target.mjs': baseLines,
    'src/unrelated.mjs': 'export const oldBug = 1;\n',
  });
  wPass.state.agent = { kind: 'codex', command: 'codex' };
  wPass.issue(31);
  await wPass.tick();
  const buildA = wPass.job(31, 'build');
  const editedLines = baseLines.replace('export const line30 = 30;', 'export const line30 = 300;');
  mkdirSync(dirname(join(buildA.cwd, 'src/target.mjs')), { recursive: true });
  writeFileSync(join(buildA.cwd, 'src/target.mjs'), editedLines);
  const { pr: prA, head: headA } = wPass.build(31);
  await wPass.tick();

  const revA = wPass.job(31, 'review');
  assert.match(revA.input, /"preExisting"/, 'reviewPrompt documents optional preExisting field');
  assert.match(revA.input, /automatically promoted back to "mustFix"/, 'reviewPrompt states anti-sycophancy promotion rule');

  writeFileSync(
    revA.result,
    JSON.stringify({
      verdict: 'PASS',
      head: headA,
      summary: 'Target change looks clean.\nRead: src/target.mjs',
      mustFix: [],
      preExisting: [
        'P2 src/unrelated.mjs:1 unrelated pre-existing defect',
        'P2 src/target.mjs:3 old issue far from changed line 30',
      ],
    }),
  );
  wPass.finish(31, 'review', { code: 0 });
  wPass.suite(31, 0);
  await wPass.tick();
  assert.deepEqual(wPass.github.merges, [prA.number], 'verified outside-diff preExisting findings do not block merge');
  const prAComments = wPass.github.prs.get(prA.number).comments.map(c => c.body).join('\n');
  assert.match(prAComments, /Review: PASS for head/);
  assert.match(prAComments, /Pre-existing \(outside diff, non-blocking\):/);
  assert.match(prAComments, /P2 src\/unrelated\.mjs:1 unrelated pre-existing defect/);
  assert.match(prAComments, /P2 src\/target\.mjs:3 old issue far from changed line 30/);

  // Scenario B: Reviewer marks PASS but tries to hide a bug at changed line 30 in preExisting -> deterministically promoted to mustFix, blocks merge, triggers repair!
  const wFail = await coreWorld(t, { settings: { runs: 1 } });
  seedBaseFiles(wFail, {
    'src/target.mjs': baseLines,
    'src/unrelated.mjs': 'export const oldBug = 1;\n',
  });
  wFail.state.agent = { kind: 'codex', command: 'codex' };
  wFail.issue(32);
  await wFail.tick();
  const buildB = wFail.job(32, 'build');
  writeFileSync(join(buildB.cwd, 'src/target.mjs'), editedLines);
  const { pr: prB, head: headB } = wFail.build(32);
  await wFail.tick();

  const revB = wFail.job(32, 'review');
  writeFileSync(
    revB.result,
    JSON.stringify({
      verdict: 'PASS',
      head: headB,
      summary: 'Waving through changed line.\nRead: src/target.mjs',
      mustFix: [],
      preExisting: [
        'P1 src/target.mjs:30 line30 regression disguised as pre-existing',
        'P2 src/unrelated.mjs:1 real outside-diff bug',
      ],
    }),
  );
  wFail.finish(32, 'review', { code: 0 });
  wFail.suite(32, 0);
  await wFail.tick();
  assert.deepEqual(wFail.github.merges, [], 'promoted changed-hunk preExisting blocks merge');
  const prBComments = wFail.github.prs.get(prB.number).comments.map(c => c.body).join('\n');
  assert.match(prBComments, /Review: FAIL for head/);
  assert.match(prBComments, /Must fix:\n- P1 src\/target\.mjs:30 line30 regression disguised as pre-existing/);
  assert.match(prBComments, /Pre-existing \(outside diff, non-blocking\):\n- P2 src\/unrelated\.mjs:1 real outside-diff bug/);
  const repairB = wFail.job(32, 'repair');
  assert.ok(repairB, 'promoted preExisting triggers a repair job');
  assert.match(repairB.input, /P1 src\/target\.mjs:30 line30 regression disguised as pre-existing/);
});

test('#3559 (6): Round-1 adversarial diff-parser and verdict regressions (FAIL->PASS lock, hunk hijack, C-quoting, copy, mode, line-1 delete, rename+re-add)', () => {
  // P1 #1: Explicit FAIL with empty mustFix + promoted P3 (diffScope=null or overlapping) MUST NEVER flip to PASS
  const failNullP3 = applyPreExistingDiffGuard({
    verdict: 'FAIL',
    head: 'abc123',
    summary: 'Explicit FAIL with only preExisting P3 and unavailable diff.',
    mustFix: [],
    preExisting: ['P3 src/unrelated.mjs:5 minor nit'],
  }, null);
  assert.equal(failNullP3.verdict, 'FAIL');
  assert.deepEqual(failNullP3.followUps, ['P3 src/unrelated.mjs:5 minor nit']);

  const overlapDiff = 'diff --git a/src/a.mjs b/src/a.mjs\n--- a/src/a.mjs\n+++ b/src/a.mjs\n@@ -5,1 +5,1 @@\n-old\n+new\n';
  const failOverlapP3 = applyPreExistingDiffGuard({
    verdict: 'FAIL',
    head: 'abc123',
    summary: 'Explicit FAIL with overlapping P3 in preExisting.',
    mustFix: [],
    preExisting: ['P3 src/a.mjs:5 minor nit on changed line'],
  }, overlapDiff);
  assert.equal(failOverlapP3.verdict, 'FAIL');

  // Existing behavior preserved: FAIL with raw mustFix containing only P3 still downgrades to PASS
  const failRawP3 = applyPreExistingDiffGuard({
    verdict: 'FAIL',
    head: 'abc123',
    summary: 'Only P3 in mustFix.',
    mustFix: ['P3 src/a.mjs:5 minor nit'],
    preExisting: [],
  }, overlapDiff);
  assert.equal(failRawP3.verdict, 'PASS');

  // P1 #5: Hunk-body `+++ b/fake.mjs` and `--- a/fake.mjs` CANNOT spoof file headers
  const spoofDiff = [
    'diff --git a/src/auth.mjs b/src/auth.mjs',
    '--- a/src/auth.mjs',
    '+++ b/src/auth.mjs',
    '@@ -5,1 +5,2 @@',
    '-old();',
    '+++ b/fake.mjs',
    '+real();',
    '@@ -30,1 +31,1 @@',
    '--- a/fake.mjs',
    '+patched();',
  ].join('\n');
  const spoofScope = parseUnifiedDiffHunks(spoofDiff);
  assert.equal(spoofScope.files.has('fake.mjs'), false);
  assert.equal(spoofScope.renamedFrom.size, 0);
  assert.deepEqual(spoofScope.files.get('src/auth.mjs').ranges, [[5, 6], [31, 31]]);
  assert.equal(guardPreExistingFindings(['P1 src/auth.mjs:5 spoofed hunk 1', 'P1 src/auth.mjs:31 spoofed hunk 2'], spoofScope).promoted.length, 2);

  // P1 #5: C-quoted paths (UTF-8 octal + tab) unquote cleanly
  const quotedDiff = [
    'diff --git "a/src/f\\303\\251.mjs" "b/src/f\\303\\251.mjs"',
    '--- "a/src/f\\303\\251.mjs"',
    '+++ "b/src/f\\303\\251.mjs"',
    '@@ -10,1 +10,2 @@',
    '+const x = 1;',
  ].join('\n');
  const quotedScope = parseUnifiedDiffHunks(quotedDiff);
  assert.deepEqual(quotedScope.files.get('src/fé.mjs')?.ranges, [[10, 11]]);

  // P2 #8: Paths containing ` b/` and binary lines + copy from/to (destination added, source NOT aliased)
  const trickyDiff = [
    'diff --git a/dir b/file.png b/dir b/file.png',
    'Binary files a/dir b/file.png and b/dir b/file.png differ',
    'diff --git a/src/base.mjs b/src/copied.mjs',
    'similarity index 100%',
    'copy from src/base.mjs',
    'copy to src/copied.mjs',
    'diff --git a/scripts/run.sh b/scripts/run.sh',
    'old mode 100644',
    'new mode 100755',
    'diff --git a/src/long.mjs b/src/long.mjs',
    '--- a/src/long.mjs',
    '+++ b/src/long.mjs',
    '@@ -1 +0,0 @@',
    '-import unused from "./x.mjs";',
  ].join('\n');
  const trickyScope = parseUnifiedDiffHunks(trickyDiff);
  assert.equal(trickyScope.files.get('dir b/file.png')?.binary, true);
  assert.equal(trickyScope.files.get('src/copied.mjs')?.added, true);
  assert.equal(trickyScope.renamedFrom.has('src/base.mjs'), false);
  assert.equal(trickyScope.files.get('scripts/run.sh')?.modeChanged, true);
  // Deleting line 1 covers [1, 2] without falsely marking line 900 changed (P2 #9)
  assert.deepEqual(trickyScope.files.get('src/long.mjs')?.ranges, [[1, 2]]);
  const longCheck = guardPreExistingFindings([
    'P1 src/long.mjs:1 deleted import regression',
    'P2 src/long.mjs:900 distant pre-existing bug',
    'P2 scripts/run.sh:10 mode changed file',
    'P2 src/copied.mjs:1 copied new file',
    'P2 src/base.mjs:10 untouched copy source',
  ], trickyScope);
  assert.deepEqual(longCheck.promoted, [
    'P1 src/long.mjs:1 deleted import regression',
    'P2 scripts/run.sh:10 mode changed file',
    'P2 src/copied.mjs:1 copied new file',
  ]);
  assert.deepEqual(longCheck.preExisting, [
    'P2 src/long.mjs:900 distant pre-existing bug',
    'P2 src/base.mjs:10 untouched copy source',
  ]);

  // P1 #6: Rename + re-add of the same path checks BOTH paths
  const renameReaddDiff = [
    'diff --git a/src/a.mjs b/src/a-impl.mjs',
    'similarity index 90%',
    'rename from src/a.mjs',
    'rename to src/a-impl.mjs',
    '--- a/src/a.mjs',
    '+++ b/src/a-impl.mjs',
    '@@ -10,1 +10,2 @@',
    '+change();',
    'diff --git a/src/a.mjs b/src/a.mjs',
    'new file mode 100644',
    '--- /dev/null',
    '+++ b/src/a.mjs',
    '@@ -0,0 +1,5 @@',
    '+export * from "./a-impl.mjs";',
  ].join('\n');
  const rrRes = guardPreExistingFindings(['P1 src/a.mjs:5 bug in newly added wrapper'], parseUnifiedDiffHunks(renameReaddDiff));
  assert.equal(rrRes.promoted.length, 1);
  assert.deepEqual(rrRes.preExisting, []);
});

test('#3559 (7): Round-1 adversarial bypass vectors (wrappers, markdown links, git/abs prefixes, spaces, >500-char, bare mentions, ANSI, comma lines, repoFiles, omitted preExisting)', () => {
  const diff = [
    'diff --git a/src/auth.mjs b/src/auth.mjs',
    '--- a/src/auth.mjs',
    '+++ b/src/auth.mjs',
    '@@ -20,5 +20,5 @@',
    '+change();',
    'diff --git a/src/added.mjs b/src/added.mjs',
    'new file mode 100644',
    '--- /dev/null',
    '+++ b/src/added.mjs',
    '@@ -0,0 +1,5 @@',
    '+export const a = 1;',
    'diff --git a/src/my file.mjs b/src/my file.mjs',
    '--- a/src/my file.mjs',
    '+++ b/src/my file.mjs',
    '@@ -10,1 +10,2 @@',
    '+changedSpace();',
  ].join('\n');
  const scope = {
    ...parseUnifiedDiffHunks(diff),
    repoFiles: new Set(['src/auth.mjs', 'src/added.mjs', 'src/my file.mjs', 'src/untouched.mjs', 'other/src/auth.mjs']),
  };

  const bypasses = [
    'P1 `src/auth.mjs`:22 backtick around path only',
    'P1 **src/auth.mjs**:22 bold around path only',
    'P1 [broken check](src/auth.mjs#L22) multi-word markdown link',
    'P1 [src/untouched.mjs:1](src/auth.mjs#L22) dual-location markdown link',
    'P1 b/src/auth.mjs:22 git dst prefix',
    'P1 a/src/auth.mjs:22 git src prefix',
    'P1 /Users/dev/repo/src/auth.mjs:22 absolute POSIX path',
    'P1 C:\\repo\\src\\auth.mjs:22 absolute Windows path',
    'P1 src/my file.mjs:10 changed file with spaces',
    `P1 src/untouched.mjs:1 ${'x'.repeat(550)} and breaks src/auth.mjs:22`,
    'P1 src/auth.mjs breaks login (see src/untouched.mjs:1)',
    'P1 src/added.mjs has SQLi (compare src/untouched.mjs:1)',
    'P1 src/untouched.mjs:1:src/auth.mjs:22 unvalidated col suffix bypass',
    'P1 src/untouched.mjs:1 \x1b[31msrc/auth.mjs:22\x1b[0m ANSI escape bypass',
    'P1 src/untouched.mjs:1 (see:src/auth.mjs:22) attached prefix bypass',
    'P1 src/untouched.mjs:1 and src/auth.mjs:19,22 comma line list bypass',
    'P2 src/hallucinated.mjs:10 nonexistent path fails closed via repoFiles',
    'P2 SRC/AUTH.MJS:22 case-variant path fails closed via repoFiles',
  ];
  const res = guardPreExistingFindings(bypasses, scope);
  assert.equal(res.promoted.length, bypasses.length, `all ${bypasses.length} bypasses must be promoted; kept=${JSON.stringify(res.preExisting)}`);
  assert.deepEqual(res.preExisting, []);

  // Legitimate outside-diff findings (including spaces and distinct repo path sharing suffix) still stay non-blocking
  const validOutside = [
    'P2 src/my file.mjs:2 unrelated pre-existing bug in file with spaces',
    'P2 other/src/auth.mjs:5 distinct repo file sharing suffix',
    'P2 src/untouched.mjs:10 clean outside-diff bug',
  ];
  const validRes = guardPreExistingFindings(validOutside, scope);
  assert.deepEqual(validRes.promoted, []);
  assert.deepEqual(validRes.preExisting, validOutside);

  // >500-char preExisting evasion via two-step parseReviewOutput (NDJSON stdout) -> applyPreExistingDiffGuard
  const longPayload = JSON.stringify({
    verdict: 'PASS',
    head: 'abc123',
    summary: 'Clean.\nRead: src/auth.mjs',
    mustFix: [],
    preExisting: [`P1 src/untouched.mjs:1 ${'z'.repeat(600)} breaks src/auth.mjs:22`],
  });
  const ndjson = JSON.stringify({ type: 'result', result: longPayload }) + '\n';
  const step1 = parseReviewOutput(ndjson, { fromResultFile: false });
  const step2 = applyPreExistingDiffGuard(step1, scope);
  assert.equal(step2.verdict, 'FAIL', 'NDJSON parseReviewOutput must not truncate preExisting before diff guard runs');
  assert.equal(step2.mustFix.length, 1);

  // Backwards compatibility when preExisting is omitted (both result file and NDJSON)
  const legacyObj = { verdict: 'PASS', head: 'abc123', summary: 'Clean.', mustFix: [] };
  const fromFile = parseReviewOutput(JSON.stringify(legacyObj), { fromResultFile: true });
  assert.equal(fromFile.verdict, 'PASS');
  assert.equal(fromFile.preExisting, undefined);
  const fromNdjson = parseReviewOutput(JSON.stringify({ type: 'result', result: JSON.stringify(legacyObj) }) + '\n', { fromResultFile: false });
  assert.equal(fromNdjson.verdict, 'PASS');
  assert.equal(fromNdjson.preExisting, undefined);
});

test('#3559 (8): end-to-end reviewState resists diff.noprefix=true and rejects hallucinated preExisting paths via git ls-tree', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  const baseLines = Array.from({ length: 40 }, (_, i) => `export const line${i + 1} = ${i + 1};`).join('\n') + '\n';
  seedBaseFiles(w, {
    'src/target.mjs': baseLines,
    'src/unrelated.mjs': 'export const oldBug = 1;\n',
  });
  // Enable diff.noprefix=true in the repo config to prove reviewState overrides it explicitly
  w.git(w.cwd, 'config', 'diff.noprefix', 'true');
  w.state.agent = { kind: 'codex', command: 'codex' };
  w.issue(33);
  await w.tick();
  const build = w.job(33, 'build');
  w.git(build.cwd, 'config', 'diff.noprefix', 'true');
  writeFileSync(join(build.cwd, 'src/target.mjs'), baseLines.replace('export const line30 = 30;', 'export const line30 = 300;'));
  const { pr, head } = w.build(33);
  await w.tick();

  const rev = w.job(33, 'review');
  writeFileSync(
    rev.result,
    JSON.stringify({
      verdict: 'PASS',
      head,
      summary: 'Sneaking changed line under diff.noprefix=true.\nRead: src/target.mjs',
      mustFix: [],
      preExisting: [
        'P1 src/target.mjs:30 changed line under diff.noprefix=true',
        'P2 src/does-not-exist.mjs:4 hallucinated path not in git ls-tree',
        'P2 src/unrelated.mjs:1 real outside-diff bug',
      ],
    }),
  );
  w.finish(33, 'review', { code: 0 });
  w.suite(33, 0);
  await w.tick();

  assert.deepEqual(w.github.merges, [], 'changed line under diff.noprefix=true and hallucinated path both block merge');
  const comments = w.github.prs.get(pr.number).comments.map(c => c.body).join('\n');
  assert.match(comments, /Review: FAIL for head/);
  assert.match(comments, /P1 src\/target\.mjs:30 changed line under diff\.noprefix=true/);
  assert.match(comments, /P2 src\/does-not-exist\.mjs:4 hallucinated path not in git ls-tree/);
  assert.match(comments, /Pre-existing \(outside diff, non-blocking\):\n- P2 src\/unrelated\.mjs:1 real outside-diff bug/);
});

test('#3559 (9): Round-2 adversarial regressions (redundant segments, URLs/tilde/parent/colon prefixes, emoji UTF-16 mask alignment, zero-width/unterminated OSC, %20/comma/#L, C-quoted surrogate pairs, non-git reset, verdict guard)', () => {
  const diff = [
    'diff --git a/src/auth.mjs b/src/auth.mjs',
    '--- a/src/auth.mjs',
    '+++ b/src/auth.mjs',
    '@@ -20,5 +20,5 @@',
    '+change();',
    'diff --git a/src/added.mjs b/src/added.mjs',
    'new file mode 100644',
    '--- /dev/null',
    '+++ b/src/added.mjs',
    '@@ -0,0 +1,5 @@',
    '+export const a = 1;',
    'diff --git a/src/my file.mjs b/src/my file.mjs',
    '--- a/src/my file.mjs',
    '+++ b/src/my file.mjs',
    '@@ -10,1 +10,2 @@',
    '+changedSpace();',
  ].join('\n');
  const baseScope = parseUnifiedDiffHunks(diff);
  const scopeWithRepo = {
    ...baseScope,
    repoFiles: new Set(['src/auth.mjs', 'src/added.mjs', 'src/my file.mjs', 'src/untouched.mjs', 'other/src/auth.mjs']),
  };

  // P1-1, P1-2, P2-1, P2-2: ALL bypasses must be promoted BOTH with and without repoFiles
  const r2Bypasses = [
    'P1 src/./auth.mjs breaks login (see src/untouched.mjs:1)',
    'P1 src//added.mjs has SQLi (see src/untouched.mjs:1)',
    'P1 ././src/auth.mjs breaks login (see src/untouched.mjs:1)',
    'P1 src/untouched.mjs:1 and src/./auth.mjs at line 22',
    'P1 src/untouched.mjs:1 and `src/./auth.mjs`:`22`',
    'P1 src/untouched.mjs:1 and /Users/dev/repo/src/./auth.mjs:22',
    'P1 src/untouched.mjs:1 and C:\\repo\\src\\.\\auth.mjs:22',
    'P1 src/untouched.mjs:1 and src/my\\ file.mjs breaks auth',
    'P1 src/untouched.mjs:1 and https://github.com/org/repo/blob/HEAD/src/auth.mjs#L22',
    'P1 src/untouched.mjs:1 and file:///Users/dev/repo/src/auth.mjs:22',
    'P1 src/untouched.mjs:1 (see:/Users/dev/repo/src/auth.mjs:22)',
    'P1 src/untouched.mjs:1 and ../repo/src/auth.mjs:22',
    'P1 src/untouched.mjs:1 and ~/repo/src/auth.mjs breaks login',
    'P1 src/untouched.mjs:1 [regression](src/./auth.mjs:22 "broken")',
    'P1 src/untouched.mjs:1 [x](note src/./auth.mjs:22 tail)',
    `P1 ${'🐛'.repeat(20)} src/my file.mjs:2 src/./auth.mjs:22`,
    'P1 src/untouched.mjs:1 and src/\u200bauth.mjs breaks login',
    'P1 src/untouched.mjs:1 \x1b]0;hidden src/auth.mjs:22',
    'P1 [bug](src/my%20file.mjs#L10)',
    'P1 (see:src/./auth.mjs#L22) and src/untouched.mjs:1',
    'P1 src/untouched.mjs:1,src/./auth.mjs:22',
  ];
  for (const [label, sc] of [['with repoFiles', scopeWithRepo], ['without repoFiles', baseScope]]) {
    const res = guardPreExistingFindings(r2Bypasses, sc);
    assert.equal(res.promoted.length, r2Bypasses.length, `all ${r2Bypasses.length} R2 bypasses must promote (${label}); kept=${JSON.stringify(res.preExisting)}`);
    assert.deepEqual(res.preExisting, []);
  }

  // Legitimate outside-diff findings with emojis, %20 markdown links, and (see:file#L) MUST stay non-blocking with repoFiles
  const r2Valid = [
    `P2 ${'🐛'.repeat(20)} src/my file.mjs:2 unrelated outside-diff bug`,
    'P2 [bug](src/my%20file.mjs#L2) outside diff in space-path markdown link',
    'P2 (see:src/untouched.mjs#L5) attached prefix on untouched file',
    'P2 other/src/auth.mjs:5 unrelated repo-relative sibling path',
  ];
  const validRes = guardPreExistingFindings(r2Valid, scopeWithRepo);
  assert.deepEqual(validRes.promoted, [], `valid outside-diff findings must not promote: ${JSON.stringify(validRes.promoted)}`);
  assert.equal(validRes.preExisting.length, r2Valid.length);

  // P2-3: Surrogate pairs in C-quoted paths, non-git multi-file pendingFlags reset, unquoted+quoted binary, ambiguous ` b/` rename
  const r2Diff = [
    'diff --git "a/src/🚀\\tfile.mjs" "b/src/🚀\\tfile.mjs"',
    '--- "a/src/🚀\\tfile.mjs"',
    '+++ "b/src/🚀\\tfile.mjs"',
    '@@ -3,1 +3,2 @@',
    '+ok();',
    'diff --git a/plain.png "b/f\\303\\251.png"',
    'Binary files a/plain.png and "b/f\\303\\251.png" differ',
    'diff --git a/dir b/old.mjs b/dir b/new.mjs',
    'similarity index 90%',
    'rename from dir b/old.mjs',
    'rename to dir b/new.mjs',
    '--- a/dir b/old.mjs',
    '+++ b/dir b/new.mjs',
    '@@ -4,1 +4,1 @@',
    '+patched();',
  ].join('\n');
  const r2Scope = parseUnifiedDiffHunks(r2Diff);
  assert.deepEqual(r2Scope.files.get('src/🚀\tfile.mjs')?.ranges, [[3, 4]]);
  assert.equal(r2Scope.files.get('plain.png')?.binary, true);
  assert.equal(r2Scope.files.get('fé.png')?.binary, true);
  assert.equal(r2Scope.files.has('old.mjs b/dir b/new.mjs'), false, 'ambiguous ` b/` rename must not leave bogus key');
  assert.equal(r2Scope.renamedFrom.get('dir b/old.mjs'), 'dir b/new.mjs');
  assert.deepEqual(r2Scope.files.get('dir b/new.mjs')?.ranges, [[4, 4]]);

  // Non-git multi-file unified diff must reset pendingFlags between files
  const nonGitDiff = [
    '--- /dev/null',
    '+++ b/src/first-new.mjs',
    '@@ -0,0 +1,2 @@',
    '+const a = 1;',
    '+const b = 2;',
    '--- a/src/second-mod.mjs',
    '+++ b/src/second-mod.mjs',
    '@@ -10,1 +10,1 @@',
    '-old();',
    '+new();',
  ].join('\n');
  const nonGitScope = parseUnifiedDiffHunks(nonGitDiff);
  assert.equal(nonGitScope.files.get('src/first-new.mjs')?.added, true);
  assert.equal(nonGitScope.files.get('src/second-mod.mjs')?.added, false, 'non-git diff must not leak added flag to file 2');

  // P3-1 & P3-2: Invalid verdict fails closed even with P3 mustFix, and extractFindingLocation preserves primary location order
  const maybeVerdict = applyPreExistingDiffGuard({
    verdict: 'MAYBE',
    head: 'abc123',
    summary: 'Invalid verdict.',
    mustFix: ['P3 src/untouched.mjs:1 minor nit'],
    preExisting: [],
  }, baseScope);
  assert.equal(maybeVerdict.verdict, 'FAIL');

  const orderedLoc = extractFindingLocation('P1 src/primary.mjs:10 (see [doc](src/secondary.mjs#L5))');
  assert.equal(orderedLoc?.path, 'src/primary.mjs');
  assert.equal(orderedLoc?.startLine, 10);
});
