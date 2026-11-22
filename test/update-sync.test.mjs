import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import {
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  realpathSync,
  rmSync,
  symlinkSync,
  unlinkSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { promptHeaderHash } from '../src/file-owner.mjs';
import {
  analyzeChangedMap,
  extractDiffSummary,
  formatChangedMapJson,
  formatChangedMapText,
} from '../src/core/changed-map.mjs';
import { analyzeUpdate, runUpdate } from '../src/update-sync.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

const GIT_BIN = execFileSync('which', ['git'], { encoding: 'utf8' }).trim() || '/usr/bin/git';
const capture = () => ({ text: '', write(value) { this.text += value; return true; } });

function git(cwd, args) {
  return execFileSync(GIT_BIN, args, {
    cwd,
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
    env: {
      PATH: `${dirname(GIT_BIN)}:/usr/bin:/bin`,
      HOME: cwd,
      GIT_CONFIG_NOSYSTEM: '1',
      GIT_CONFIG_GLOBAL: '/dev/null',
      GIT_AUTHOR_NAME: 'Test',
      GIT_AUTHOR_EMAIL: 'test@example.invalid',
      GIT_COMMITTER_NAME: 'Test',
      GIT_COMMITTER_EMAIL: 'test@example.invalid',
    },
  }).trim();
}

function makeRepo(t, files = {}) {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-changed-map-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  git(root, ['init', '-q', '-b', 'main']);
  for (const [rel, content] of Object.entries(files)) {
    const full = join(root, rel);
    mkdirSync(dirname(full), { recursive: true });
    writeFileSync(full, content);
  }
  if (Object.keys(files).length) {
    git(root, ['add', '.']);
    git(root, ['commit', '-qm', 'init']);
  }
  return root;
}

async function cli(argv, cwd) {
  const stdout = capture(), stderr = capture();
  const code = await runPdd(argv, {
    stdout,
    stderr,
    cwd,
    env: {
      PATH: dirname(GIT_BIN),
      HOME: cwd,
      PDD_STATE_DIR: join(cwd, '.local', 'state', 'pdd'),
      PDD_RUNTIME_URL: 'invalid',
    },
  });
  return { code, out: stdout.text, err: stderr.text };
}

test('extractDiffSummary counts lines and classifies polyglot symbols deterministically', () => {
  const diff = [
    'diff --git a/src/math.mjs b/src/math.mjs',
    '--- a/src/math.mjs',
    '+++ b/src/math.mjs',
    '@@ -1,4 +1,5 @@',
    '-export function oldHelper(a) { return a; }',
    '-export function computeTotal(items) { return items.length; }',
    '+export function computeTotal(items, tax) { return items.length + tax; }',
    '+export const MAX_TOTAL = 1000;',
    '+export async function syncTotals() {}',
  ].join('\n');
  assert.deepEqual(extractDiffSummary(diff), {
    added: 3,
    removed: 2,
    changed_symbols: [
      { kind: 'added', symbol: 'MAX_TOTAL' },
      { kind: 'updated', symbol: 'computeTotal' },
      { kind: 'removed', symbol: 'oldHelper' },
      { kind: 'added', symbol: 'syncTotals' },
    ],
  });

  const polyglot = [
    '+def calc_fee(amount):',
    '-class LegacyFee:',
    '+func ParseHeader(raw string) error {',
    '+pub async fn verify_pin() -> bool {',
  ].join('\n');
  assert.deepEqual(extractDiffSummary(polyglot), {
    added: 3,
    removed: 1,
    changed_symbols: [
      { kind: 'removed', symbol: 'LegacyFee' },
      { kind: 'added', symbol: 'ParseHeader' },
      { kind: 'added', symbol: 'calc_fee' },
      { kind: 'added', symbol: 'verify_pin' },
    ],
  });
});

test('analyzeChangedMap maps working-tree, --from range, and explicit files to owning prompts and changed symbols', t => {
  const billingPrompt = '# Billing\n\nOwn `src/billing.mjs`.\n\n## Domain decisions\n\n- Amounts use integer cents.\n';
  const billingHash = promptHeaderHash(billingPrompt);
  const root = makeRepo(t, {
    'prompts/billing.prompt.md': billingPrompt,
    'src/billing.mjs': `// Generated from prompts/billing.prompt.md (sha256: ${billingHash}).\nexport function totalCents(items) { return items.length * 100; }\n`,
    'README.md': '# Demo\n',
  });

  // Clean working tree -> empty report
  const clean = analyzeChangedMap({ cwd: root });
  assert.equal(clean.ok, true);
  assert.equal(clean.report.schema_version, 'pdd.changed-map.v1');
  assert.deepEqual(clean.report.prompts, []);
  assert.deepEqual(clean.report.modules, []);
  assert.match(formatChangedMapText(clean.report), /no touched files in scope/);

  // Modify owned code + unowned file -> working-tree changed-map
  writeFileSync(
    join(root, 'src/billing.mjs'),
    `// Generated from prompts/billing.prompt.md (sha256: ${billingHash}).\nexport function totalCents(items) { return items.length * 100; }\nexport function applyCap(cents, max) { return Math.min(cents, max); }\n`,
  );
  writeFileSync(join(root, 'README.md'), '# Demo updated\n');

  const dirty = analyzeChangedMap({ cwd: root });
  assert.equal(dirty.ok, true, dirty.error);
  assert.equal(dirty.report.scope.kind, 'working-tree');
  assert.equal(dirty.report.prompts.length, 1);
  assert.equal(dirty.report.prompts[0].prompt, 'prompts/billing.prompt.md');
  assert.equal(dirty.report.prompts[0].status, 'changed');
  assert.equal(dirty.report.modules[0].diff_stats.added, 1);
  assert.deepEqual(dirty.report.modules[0].changed_symbols, [{ kind: 'added', symbol: 'applyCap' }]);
  assert.deepEqual(dirty.report.unowned, [{ path: 'README.md', reason: 'no owning prompt' }]);
  assert.match(formatChangedMapText(dirty.report), /prompts\/billing\.prompt\.md \[changed\]/);
  assert.match(formatChangedMapJson(dirty.report), /"schema_version":"pdd\.changed-map\.v1"/);

  // Commit and inspect via --from HEAD~1..HEAD
  git(root, ['add', '.']);
  git(root, ['commit', '-qm', 'add applyCap']);
  const ranged = analyzeChangedMap({ cwd: root, from: 'HEAD~1' });
  assert.equal(ranged.ok, true, ranged.error);
  assert.equal(ranged.report.scope.kind, 'from');
  assert.equal(ranged.report.scope.range, 'HEAD~1..HEAD');
  assert.equal(ranged.report.modules[0].path, 'src/billing.mjs');
  assert.deepEqual(ranged.report.modules[0].changed_symbols, [{ kind: 'added', symbol: 'applyCap' }]);

  // Edit prompt prose -> prompt-stale detected via header hash without sidecars
  writeFileSync(join(root, 'prompts/billing.prompt.md'), billingPrompt.replace('integer cents.', 'integer cents with cap.'));
  const stale = analyzeChangedMap({ cwd: root });
  assert.equal(stale.ok, true, stale.error);
  assert.equal(stale.report.modules[0].path, 'src/billing.mjs');
  assert.equal(stale.report.modules[0].status, 'prompt-stale');
  assert.equal(existsSync(join(root, '.pdd/sync')), false, 'read-only changed-map must never create .pdd/sync');
});

test('read-only pdd update wrapper delegates to changed-map, refuses --write with 4-part diagnostic, and writes zero files', async t => {
  const promptText = '# App\n\nOwn `src/app.mjs`.\n';
  const hash = promptHeaderHash(promptText);
  const root = makeRepo(t, {
    'prompts/app.prompt.md': promptText,
    'src/app.mjs': `// Generated from prompts/app.prompt.md (sha256: ${hash}).\nexport function run() { return 1; }\n`,
    'README.md': '# App\n',
  });

  // Unchanged explicit file -> current, --check exits 0
  const plan = await cli(['update', 'src/app.mjs', 'README.md', '--json'], root);
  assert.equal(plan.code, 0, plan.err);
  const planJson = JSON.parse(plan.out);
  assert.equal(planJson.schema_version, 'pdd.update-sync.v1');
  assert.equal(planJson.modules[0].status, 'current');
  assert.deepEqual(planJson.unowned, [{ path: 'README.md', reason: 'no owning prompt' }]);
  assert.deepEqual(planJson.updated, []);
  assert.equal((await cli(['update', 'src/app.mjs', '--check', '--json'], root)).code, 0);

  // Changed code -> --check exits 1
  writeFileSync(join(root, 'src/app.mjs'), `// Generated from prompts/app.prompt.md (sha256: ${hash}).\nexport function run() { return 2; }\n`);
  const checkChanged = await cli(['update', '--check', '--json'], root);
  assert.equal(checkChanged.code, 1);
  assert.equal(JSON.parse(checkChanged.out).drifted[0].status, 'changed');

  // --write is refused with exit 2 and 4-part agent-teaching diagnostic (zero writes!)
  const writeRefusal = await cli(['update', 'src/app.mjs', '--write'], root);
  assert.equal(writeRefusal.code, 2);
  assert.match(writeRefusal.err, /Location: pdd update --write/);
  assert.match(writeRefusal.err, /Invariant:/);
  assert.match(writeRefusal.err, /Fix:/);
  assert.match(writeRefusal.err, /Rerun:/);
  assert.equal(existsSync(join(root, '.pdd/sync')), false);
  assert.equal(readFileSync(join(root, 'prompts/app.prompt.md'), 'utf8'), promptText);

  // --check + --write refused with exit 2
  const bothFlags = analyzeUpdate({ cwd: root, check: true, write: true });
  assert.equal(bothFlags.exitCode, 2);
});

test('security and edge guards: secrets, symlinks, option injection, traversal, binary files, malformed bindings, deletions, and misplaced test prompts', t => {
  const promptText = '# Core\n\nOwn `src/core.mjs`.\n';
  const root = makeRepo(t, {
    'prompts/core.prompt.md': promptText,
    'src/core.mjs': 'export const ok = true;\n',
  });

  // Invalid --from option injection & triple-dot
  assert.equal(analyzeChangedMap({ cwd: root, from: '--exec=sh' }).exitCode, 2);
  assert.equal(analyzeChangedMap({ cwd: root, from: 'a...b' }).exitCode, 2);
  assert.equal(analyzeChangedMap({ cwd: root, files: ['src/core.mjs'], from: 'HEAD~1' }).exitCode, 2);
  assert.equal(analyzeChangedMap({ cwd: root, files: ['-evil'] }).exitCode, 2);
  assert.equal(analyzeChangedMap({ cwd: root, files: ['../escape.mjs'] }).exitCode, 2);

  // Secret file refused before read
  writeFileSync(join(root, '.env'), 'API_KEY=secret\n');
  assert.equal(analyzeChangedMap({ cwd: root, files: ['.env'] }).exitCode, 2);
  unlinkSync(join(root, '.env'));

  // Symlink refused
  symlinkSync(join(root, 'src/core.mjs'), join(root, 'src/link.mjs'));
  assert.equal(analyzeChangedMap({ cwd: root, files: ['src/link.mjs'] }).exitCode, 2);
  unlinkSync(join(root, 'src/link.mjs'));

  // Binary explicit file refused; unowned binary in working-tree skipped under unowned
  writeFileSync(join(root, 'logo.bin'), Buffer.from([0x89, 0x50, 0x00, 0x47]));
  assert.equal(analyzeChangedMap({ cwd: root, files: ['logo.bin'] }).exitCode, 2);
  const binWork = analyzeChangedMap({ cwd: root });
  assert.equal(binWork.ok, true, binWork.error);
  assert.deepEqual(binWork.report.unowned, [{ path: 'logo.bin', reason: 'binary file (skipped)' }]);
  unlinkSync(join(root, 'logo.bin'));

  // Malformed pdd-bindings.json fails closed (exit 2)
  writeFileSync(join(root, 'pdd-bindings.json'), '{not-json');
  assert.equal(analyzeChangedMap({ cwd: root, files: ['src/core.mjs'] }).exitCode, 2);
  unlinkSync(join(root, 'pdd-bindings.json'));

  // Misplaced test prompt refused (exit 1)
  writeFileSync(join(root, 'prompts/core.test.prompt.md'), '# Bad test prompt\n');
  assert.equal(analyzeChangedMap({ cwd: root, files: ['prompts/core.test.prompt.md'] }).exitCode, 1);
  unlinkSync(join(root, 'prompts/core.test.prompt.md'));

  // Outside a Git repo -> exit 2
  const nonGit = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-nongit-')));
  t.after(() => rmSync(nonGit, { recursive: true, force: true }));
  const out = capture(), err = capture();
  assert.equal(runUpdate({ cwd: nonGit }, { stdout: out, stderr: err }), 2);
  assert.match(err.text, /works inside a Git repository/);
});
