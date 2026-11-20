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
    ranges: [[10, 12], [41, 42]],
  });
  assert.equal(scope.files.get('src/new-feature.mjs').added, true);
  assert.equal(scope.renamedFrom.get('src/old-name.mjs'), 'src/new-name.mjs');
  assert.deepEqual(scope.files.get('src/new-name.mjs').ranges, [[5, 6]]);
  assert.equal(scope.files.get('src/removed.mjs').deleted, true);
  assert.deepEqual(scope.files.get('src/emptied.mjs').ranges, [[1, Number.MAX_SAFE_INTEGER]]);
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
