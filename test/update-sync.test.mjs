import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
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
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { promptHeaderHash } from '../src/file-owner.mjs';
import {
  analyzeChangedMap,
  extractDiffSummary,
  formatChangedMapJson,
  formatChangedMapText,
} from '../src/core/changed-map.mjs';
import { analyzeUpdate, runUpdate } from '../src/update-sync.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

const HERE = dirname(fileURLToPath(import.meta.url));
const BIN_PDD = resolve(HERE, '../bin/pdd.mjs');
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

function cliSpawn(argv, cwd) {
  const res = spawnSync(process.execPath, [BIN_PDD, ...argv], {
    cwd,
    encoding: 'utf8',
    env: {
      PATH: `${dirname(process.execPath)}:${dirname(GIT_BIN)}:/usr/bin:/bin`,
      HOME: cwd,
      PDD_STATE_DIR: join(cwd, '.local', 'state', 'pdd'),
      PDD_RUNTIME_URL: 'invalid',
    },
  });
  return { code: res.status ?? 1, out: res.stdout ?? '', err: res.stderr ?? '' };
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

  // Modify owned code + unowned product file + doc file -> working-tree changed-map
  writeFileSync(
    join(root, 'src/billing.mjs'),
    `// Generated from prompts/billing.prompt.md (sha256: ${billingHash}).\nexport function totalCents(items) { return items.length * 100; }\nexport function applyCap(cents, max) { return Math.min(cents, max); }\n`,
  );
  writeFileSync(join(root, 'src/legacy.py'), 'def legacy_helper():\n    return 1\n');
  writeFileSync(join(root, 'README.md'), '# Demo updated\n');

  const dirty = analyzeChangedMap({ cwd: root });
  assert.equal(dirty.ok, true, dirty.error);
  assert.equal(dirty.report.scope.kind, 'working-tree');
  assert.equal(dirty.report.prompts.length, 1);
  assert.equal(dirty.report.prompts[0].prompt, 'prompts/billing.prompt.md');
  assert.equal(dirty.report.prompts[0].status, 'changed');
  assert.equal(dirty.report.modules[0].diff_stats.added, 1);
  assert.deepEqual(dirty.report.modules[0].changed_symbols, [{ kind: 'added', symbol: 'applyCap' }]);
  assert.deepEqual(dirty.report.unowned, [{ path: 'src/legacy.py', reason: 'no owning prompt' }]);
  const dirtyText = formatChangedMapText(dirty.report);
  assert.match(dirtyText, /prompts\/billing\.prompt\.md \[changed\]/);
  assert.match(dirtyText, /reminder: Verify prompts\/billing\.prompt\.md still matches src\/billing\.mjs/);
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

  // Edit prompt prose -> prompt-stale detected via legacy header hash without sidecars
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

  // Unchanged explicit file -> current, --check exits 0 (explicit non-code query still reported in unowned)
  const plan = await cli(['update', 'src/app.mjs', 'README.md', '--json'], root);
  assert.equal(plan.code, 0, plan.err);
  const planJson = JSON.parse(plan.out);
  assert.equal(planJson.schema_version, 'pdd.update-sync.v1');
  assert.equal(planJson.modules[0].status, 'current');
  assert.deepEqual(planJson.unowned, [{ path: 'README.md', reason: 'no owning prompt' }]);
  assert.deepEqual(planJson.updated, []);
  assert.equal((await cli(['update', 'src/app.mjs', '--check', '--json'], root)).code, 0);

  // Pure code-only edit on valid owned file -> --check exits 0 with advisory reminder (NOT hard failure)
  writeFileSync(join(root, 'src/app.mjs'), `// Generated from prompts/app.prompt.md (sha256: ${hash}).\nexport function run() { return 2; }\n`);
  const checkChanged = await cli(['update', '--check', '--json'], root);
  assert.equal(checkChanged.code, 0, checkChanged.err || checkChanged.out);
  const checkChangedJson = JSON.parse(checkChanged.out);
  assert.equal(checkChangedJson.ok, true);
  assert.deepEqual(checkChangedJson.drifted, []);
  assert.equal(checkChangedJson.modules[0].status, 'changed');
  assert.equal(checkChangedJson.reminders.length, 1);
  assert.match(checkChangedJson.reminders[0].message, /Verify prompts\/app\.prompt\.md still matches src\/app\.mjs/);

  // Stale legacy (sha256: ...) hash -> --check exits 1
  writeFileSync(join(root, 'prompts/app.prompt.md'), '# App\n\nOwn `src/app.mjs`.\n\nUpdated rule.\n');
  const checkStale = await cli(['update', '--check', '--json'], root);
  assert.equal(checkStale.code, 1, checkStale.out);
  const checkStaleJson = JSON.parse(checkStale.out);
  assert.equal(checkStaleJson.ok, false);
  assert.equal(checkStaleJson.drifted[0].status, 'prompt-stale');
  writeFileSync(join(root, 'prompts/app.prompt.md'), promptText);

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

  // Symlinked pdd.json and pdd-workspace.json refused (exit 2)
  symlinkSync(join(root, 'prompts/core.prompt.md'), join(root, 'pdd.json'));
  assert.equal(analyzeChangedMap({ cwd: root, files: ['src/core.mjs'] }).exitCode, 2);
  unlinkSync(join(root, 'pdd.json'));
  symlinkSync(join(root, 'prompts/core.prompt.md'), join(root, 'pdd-workspace.json'));
  assert.equal(analyzeChangedMap({ cwd: root, files: ['src/core.mjs'] }).exitCode, 2);
  unlinkSync(join(root, 'pdd-workspace.json'));

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

test('Test A (#3657): live --all --check on 0.1.50 hashless + pdd-bindings.json repo exits 0 with unowned: []', t => {
  const root = makeRepo(t, {
    'prompts/app.prompt.md': '# App\n\nOwn `src/app.mjs`.\n\n## Domain decisions\n- Return version string.\n',
    'prompts/rules.prompt.md': '# Rules\n\nOwn `config/rules.json`.\n\n## Domain decisions\n- Store integer limits.\n',
    'src/app.mjs': '// Prompt: prompts/app.prompt.md\n\nexport function version() { return "0.1.50"; }\n',
    'config/rules.json': '{\n  "maxItems": 25\n}\n',
    'pdd-bindings.json': `${JSON.stringify({
      schema_version: 'pdd.bindings.v1',
      modules: [{ module: 'config/rules.json', prompt: 'prompts/rules.prompt.md' }],
    }, null, 2)}\n`,
    'tests/app.test.mjs': 'export const ok = true;\n',
    'docs/guide.md': '# User Guide\n',
    'user_stories/app.md': '# Story\n',
    'package.json': '{"name":"demo","private":true}\n',
    '.github/workflows/ci.yml': 'name: CI\n',
  });
  // Add an untracked local config file inside a dot-directory.
  mkdirSync(join(root, '.local'), { recursive: true });
  writeFileSync(join(root, '.local/config'), 'theme=dark\n');

  const res = cliSpawn(['update', '--all', '--check', '--json'], root);
  assert.equal(res.code, 0, `expected exit 0, got ${res.code}\nstdout: ${res.out}\nstderr: ${res.err}`);
  const report = JSON.parse(res.out);
  assert.equal(report.ok, true);
  assert.equal(report.scope.kind, 'all');
  assert.deepEqual(report.drifted, []);
  assert.deepEqual(report.reminders, []);
  assert.deepEqual(report.unowned, []);
  const byPath = Object.fromEntries(report.modules.map(m => [m.path, m]));
  assert.equal(byPath['src/app.mjs'].status, 'current');
  assert.equal(byPath['src/app.mjs'].header_state, 'none');
  assert.equal(byPath['config/rules.json'].status, 'current');
  assert.equal(byPath['config/rules.json'].source, 'binding');
  assert.ok(!report.modules.some(m => m.status === 'unpinned'), 'must never emit failing unpinned status');
});

test('Test B (#3657): live --from base..HEAD --check with co-changed code + prompt exits 0 as reconciled', async t => {
  const { inspectStatus } = await import('../src/core/status.mjs');
  const root = makeRepo(t, {
    'prompts/ledger.prompt.md': '# Ledger\n\nOwn `src/ledger.mjs`.\n\n## Domain decisions\n- Append entries.\n',
    'prompts/rules.prompt.md': '# Rules\n\nOwn `config/rules.json`.\n\n## Domain decisions\n- Limit is 10.\n',
    'src/ledger.mjs': '// Prompt: prompts/ledger.prompt.md\n\nexport function append(list, x) { return [...list, x]; }\n',
    'config/rules.json': '{"limit": 10}\n',
    'pdd-bindings.json': `${JSON.stringify({
      schema_version: 'pdd.bindings.v1',
      modules: [{ module: 'config/rules.json', prompt: 'prompts/rules.prompt.md' }],
    }, null, 2)}\n`,
  });

  const baseSha = git(root, ['rev-parse', 'HEAD']);
  git(root, ['checkout', '-q', '-b', 'feat/co-change']);
  writeFileSync(
    join(root, 'prompts/ledger.prompt.md'),
    '# Ledger\n\nOwn `src/ledger.mjs`.\n\n## Domain decisions\n- Append non-null entries.\n',
  );
  writeFileSync(
    join(root, 'src/ledger.mjs'),
    '// Prompt: prompts/ledger.prompt.md\n\nexport function append(list, x) { return x == null ? list : [...list, x]; }\n',
  );
  writeFileSync(
    join(root, 'prompts/rules.prompt.md'),
    '# Rules\n\nOwn `config/rules.json`.\n\n## Domain decisions\n- Limit is 20.\n',
  );
  writeFileSync(join(root, 'config/rules.json'), '{"limit": 20}\n');
  git(root, ['add', '.']);
  git(root, ['commit', '-qm', 'update code and prompts together']);

  const res = cliSpawn(['update', '--from', `${baseSha}..HEAD`, '--check', '--json'], root);
  assert.equal(res.code, 0, res.err || res.out);
  const report = JSON.parse(res.out);
  assert.equal(report.ok, true);
  assert.deepEqual(report.drifted, []);
  assert.deepEqual(report.reminders, []);
  const byPath = Object.fromEntries(report.modules.map(m => [m.path, m]));
  assert.equal(byPath['src/ledger.mjs'].status, 'reconciled');
  assert.equal(byPath['config/rules.json'].status, 'reconciled');
  assert.ok(report.prompts.every(p => p.status === 'reconciled' && p.prompt_changed === true));

  // Bare `pdd update --check` on this clean committed branch widens to branch and exits 0.
  const branchCheck = cliSpawn(['update', '--check', '--json'], root);
  assert.equal(branchCheck.code, 0, branchCheck.err || branchCheck.out);
  const branchJson = JSON.parse(branchCheck.out);
  assert.equal(branchJson.scope.kind, 'branch');
  assert.equal(branchJson.scope.widened_from, 'working-tree');
  assert.equal(branchJson.ok, true);

  // pdd status --changed stays compatible on the clean committed branch.
  const statusView = await inspectStatus({ cwd: root, changed: true });
  assert.ok(statusView.changed.includes('src/ledger.mjs'));
  assert.ok(statusView.changed.includes('prompts/ledger.prompt.md'));
});

test('Test C (#3657): live pure code bugfix & 2-PR workflow exits 0 with clear reminder naming owning prompt', t => {
  const root = makeRepo(t, {
    'prompts/calc.prompt.md': '# Calc\n\nOwn `src/calc.mjs`.\n\n## Domain decisions\n- Return sum of finite numbers.\n',
    'src/calc.mjs': '// Prompt: prompts/calc.prompt.md\n\nexport function sum(a, b) { return a + b; }\n',
    'prompts/flags.prompt.md': '# Flags\n\nOwn `config/flags.json`.\n',
    'config/flags.json': '{"strict": false}\n',
    'pdd-bindings.json': `${JSON.stringify({
      schema_version: 'pdd.bindings.v1',
      modules: [{ module: 'config/flags.json', prompt: 'prompts/flags.prompt.md' }],
    }, null, 2)}\n`,
  });

  // Code-only edits (pure bugfix / PR 2 without touching prompts)
  writeFileSync(
    join(root, 'src/calc.mjs'),
    '// Prompt: prompts/calc.prompt.md\n\nexport function sum(a, b) { return Number(a) + Number(b); }\n',
  );
  writeFileSync(join(root, 'config/flags.json'), '{"strict": true}\n');

  const jsonRes = cliSpawn(['update', '--check', '--json'], root);
  assert.equal(jsonRes.code, 0, jsonRes.err || jsonRes.out);
  const report = JSON.parse(jsonRes.out);
  assert.equal(report.ok, true);
  assert.deepEqual(report.drifted, []);
  assert.equal(report.reminders.length, 2);
  const remByPath = Object.fromEntries(report.reminders.map(r => [r.path, r]));
  assert.equal(remByPath['src/calc.mjs'].owner, 'prompts/calc.prompt.md');
  assert.match(remByPath['src/calc.mjs'].message, /Verify prompts\/calc\.prompt\.md still matches src\/calc\.mjs/);
  assert.equal(remByPath['config/flags.json'].owner, 'prompts/flags.prompt.md');
  assert.match(remByPath['config/flags.json'].message, /Verify prompts\/flags\.prompt\.md still matches config\/flags\.json/);

  // Human-readable output also shows clear reminder naming the owning prompt and exits 0.
  const textRes = cliSpawn(['update', '--check'], root);
  assert.equal(textRes.code, 0, textRes.err || textRes.out);
  assert.match(textRes.out, /prompts\/calc\.prompt\.md \[changed\]/);
  assert.match(textRes.out, /reminder: Verify prompts\/calc\.prompt\.md still matches src\/calc\.mjs/);
  assert.match(textRes.out, /reminder: Verify prompts\/flags\.prompt\.md still matches config\/flags\.json/);

  // `--all --check` with dirty code-only edit MUST still classify as `changed` (not falsely `reconciled`).
  const allRes = cliSpawn(['update', '--all', '--check', '--json'], root);
  assert.equal(allRes.code, 0, allRes.err || allRes.out);
  const allJson = JSON.parse(allRes.out);
  assert.equal(allJson.modules.find(m => m.path === 'src/calc.mjs').status, 'changed');
});

test('Test D (#3657): broken links (missing prompt, dangling binding) and stale legacy sha256 MUST fail with exit 1', t => {
  // 1. Code file header pointing to a deleted/missing .prompt.md -> exit 1
  const missingHeaderRepo = makeRepo(t, {
    'prompts/auth.prompt.md': '# Auth\n\nOwn `src/auth.mjs`.\n',
    'src/auth.mjs': '// Prompt: prompts/auth.prompt.md\n\nexport const check = () => true;\n',
  });
  unlinkSync(join(missingHeaderRepo, 'prompts/auth.prompt.md'));
  const deletedPromptRes = cliSpawn(['update', '--check'], missingHeaderRepo);
  assert.equal(deletedPromptRes.code, 1, `expected exit 1 on deleted owning prompt\nstdout: ${deletedPromptRes.out}\nstderr: ${deletedPromptRes.err}`);
  assert.match(deletedPromptRes.err, /Owning prompt is missing or unreadable: prompts\/auth\.prompt\.md/);

  // Also fails on a committed repo where the prompt never existed (via widening to --all).
  const neverExistedRepo = makeRepo(t, {
    'src/orphan.mjs': '// Prompt: prompts/ghost.prompt.md\n\nexport const x = 1;\n',
  });
  const ghostRes = cliSpawn(['update', '--check'], neverExistedRepo);
  assert.equal(ghostRes.code, 1, `expected exit 1 on missing prompt after widening\nstdout: ${ghostRes.out}\nstderr: ${ghostRes.err}`);
  assert.match(ghostRes.err, /Owning prompt is missing or unreadable: prompts\/ghost\.prompt\.md/);

  // 2. pdd-bindings.json pointing to a missing .prompt.md -> exit 1
  const missingBindingPromptRepo = makeRepo(t, {
    'config/policy.json': '{"allow": true}\n',
    'pdd-bindings.json': `${JSON.stringify({
      schema_version: 'pdd.bindings.v1',
      modules: [{ module: 'config/policy.json', prompt: 'prompts/missing-policy.prompt.md' }],
    }, null, 2)}\n`,
  });
  const missingBindingRes = cliSpawn(['update', '--check'], missingBindingPromptRepo);
  assert.equal(missingBindingRes.code, 1, missingBindingRes.out);
  assert.match(missingBindingRes.err, /Owning prompt is missing or unreadable: prompts\/missing-policy\.prompt\.md/);

  // 3. Code file with mismatched legacy (sha256: ...) header -> exit 1
  const oldPrompt = '# Tax\n\nOwn `src/tax.mjs`.\n\n## Domain decisions\n- Rate is 10%.\n';
  const oldHash = promptHeaderHash(oldPrompt);
  const staleRepo = makeRepo(t, {
    'prompts/tax.prompt.md': '# Tax\n\nOwn `src/tax.mjs`.\n\n## Domain decisions\n- Rate is 15%.\n',
    'src/tax.mjs': `// Generated from prompts/tax.prompt.md (sha256: ${oldHash}).\n\nexport const tax = n => Math.round(n * 0.15);\n`,
  });
  const staleRes = cliSpawn(['update', '--check', '--json'], staleRepo);
  assert.equal(staleRes.code, 1, `expected exit 1 on mismatched legacy sha256\nstdout: ${staleRes.out}\nstderr: ${staleRes.err}`);
  const staleJson = JSON.parse(staleRes.out);
  assert.equal(staleJson.ok, false);
  assert.equal(staleJson.drifted.length, 1);
  assert.equal(staleJson.drifted[0].path, 'src/tax.mjs');
  assert.equal(staleJson.drifted[0].status, 'prompt-stale');

  // 4. Dangling pdd-bindings.json entry whose bound file was deleted (both uncommitted AND committed!) -> exit 1
  const danglingBindingRepo = makeRepo(t, {
    'prompts/data.prompt.md': '# Data\n\nOwn `config/data.json`.\n',
    'config/data.json': '{"v": 1}\n',
    'pdd-bindings.json': `${JSON.stringify({
      schema_version: 'pdd.bindings.v1',
      modules: [{ module: 'config/data.json', prompt: 'prompts/data.prompt.md' }],
    }, null, 2)}\n`,
  });
  unlinkSync(join(danglingBindingRepo, 'config/data.json'));
  const danglingRes = cliSpawn(['update', '--check', '--json'], danglingBindingRepo);
  assert.equal(danglingRes.code, 1, danglingRes.out);
  const danglingJson = JSON.parse(danglingRes.out);
  assert.equal(danglingJson.ok, false);
  assert.equal(danglingJson.drifted[0].path, 'config/data.json');
  assert.equal(danglingJson.drifted[0].status, 'deleted');

  // Commit the deletion of config/data.json while leaving pdd-bindings.json dangling -> bare --check and --all --check MUST still exit 1!
  git(danglingBindingRepo, ['rm', '-q', 'config/data.json']);
  git(danglingBindingRepo, ['commit', '-qm', 'delete bound file without cleaning pdd-bindings.json']);
  const committedDanglingAll = cliSpawn(['update', '--all', '--check', '--json'], danglingBindingRepo);
  assert.equal(committedDanglingAll.code, 1, committedDanglingAll.out);
  assert.equal(JSON.parse(committedDanglingAll.out).drifted[0].status, 'deleted');
  const committedDanglingBare = cliSpawn(['update', '--check', '--json'], danglingBindingRepo);
  assert.equal(committedDanglingBare.code, 1, committedDanglingBare.out);
  assert.equal(JSON.parse(committedDanglingBare.out).drifted[0].status, 'deleted');

  // 5. pdd-bindings.json pointing to an existing non-.prompt.md file -> exit 1 (including when modified alongside a dirty valid module!)
  const nonPromptBindingRepo = makeRepo(t, {
    'prompts/app.prompt.md': '# App\n\nOwn `src/app.mjs`.\n',
    'src/app.mjs': '// Prompt: prompts/app.prompt.md\n\nexport const ok = 1;\n',
    'config/rules.json': '{"a": 1}\n',
    'README.md': '# Readme\n',
    'pdd-bindings.json': `${JSON.stringify({ schema_version: 'pdd.bindings.v1', modules: [] }, null, 2)}\n`,
  });
  writeFileSync(join(nonPromptBindingRepo, 'src/app.mjs'), '// Prompt: prompts/app.prompt.md\n\nexport const ok = 2;\n');
  writeFileSync(
    join(nonPromptBindingRepo, 'pdd-bindings.json'),
    `${JSON.stringify({
      schema_version: 'pdd.bindings.v1',
      modules: [{ module: 'config/rules.json', prompt: 'README.md' }],
    }, null, 2)}\n`,
  );
  const nonPromptRes = cliSpawn(['update', '--check'], nonPromptBindingRepo);
  assert.equal(nonPromptRes.code, 1, `binding to non-.prompt.md must exit 1\nstdout: ${nonPromptRes.out}\nstderr: ${nonPromptRes.err}`);
  assert.match(nonPromptRes.err, /Owning prompt path is invalid: README\.md/);

  // 6. Symlinked bound module in --all --check MUST fail closed with exit 2 (never silently skipped!)
  const symlinkBoundRepo = makeRepo(t, {
    'prompts/rules.prompt.md': '# Rules\n\nOwn `config/rules.json`.\n',
    'config/real.json': '{"ok": true}\n',
    'pdd-bindings.json': `${JSON.stringify({
      schema_version: 'pdd.bindings.v1',
      modules: [{ module: 'config/rules.json', prompt: 'prompts/rules.prompt.md' }],
    }, null, 2)}\n`,
  });
  symlinkSync(join(symlinkBoundRepo, 'config/real.json'), join(symlinkBoundRepo, 'config/rules.json'));
  git(symlinkBoundRepo, ['add', 'config/rules.json']);
  git(symlinkBoundRepo, ['commit', '-qm', 'commit symlinked bound module']);
  const symlinkBoundRes = cliSpawn(['update', '--all', '--check'], symlinkBoundRepo);
  assert.equal(symlinkBoundRes.code, 2, `symlinked bound module must fail closed with exit 2\nstdout: ${symlinkBoundRes.out}\nstderr: ${symlinkBoundRes.err}`);
  assert.match(symlinkBoundRes.err, /Symlinks are not allowed: config\/rules\.json/);
});

test('Test E (#3630): 1 untracked .local/config never hides a broken or stale module during bare pdd update --check', t => {
  const oldPrompt = '# Billing\n\nOwn `src/billing.mjs`.\n\n## Domain decisions\n- Integer cents.\n';
  const oldHash = promptHeaderHash(oldPrompt);

  // Case 1: Clean committed feature branch with stale legacy sha256 + 1 untracked .local/config -> widens to --all and exits 1!
  const staleBranchRepo = makeRepo(t, {
    'prompts/billing.prompt.md': oldPrompt,
    'src/billing.mjs': `// Generated from prompts/billing.prompt.md (sha256: ${oldHash}).\n\nexport const cents = n => n * 100;\n`,
  });
  git(staleBranchRepo, ['checkout', '-q', '-b', 'feat/stale-with-untracked']);
  writeFileSync(
    join(staleBranchRepo, 'prompts/billing.prompt.md'),
    '# Billing\n\nOwn `src/billing.mjs`.\n\n## Domain decisions\n- Integer cents with rounding.\n',
  );
  git(staleBranchRepo, ['add', '.']);
  git(staleBranchRepo, ['commit', '-qm', 'update prompt without updating legacy hash']);

  // Drop 1 untracked non-module local config file.
  mkdirSync(join(staleBranchRepo, '.local'), { recursive: true });
  writeFileSync(join(staleBranchRepo, '.local/config'), 'debug=1\n');

  const staleWidened = cliSpawn(['update', '--check', '--json'], staleBranchRepo);
  assert.equal(staleWidened.code, 1, `1 untracked .local/config must NOT bypass --check widening\nstdout: ${staleWidened.out}\nstderr: ${staleWidened.err}`);
  const staleJson = JSON.parse(staleWidened.out);
  assert.equal(staleJson.ok, false);
  assert.equal(staleJson.scope.kind, 'all');
  assert.equal(staleJson.scope.widened_from, 'working-tree');
  assert.equal(staleJson.drifted[0].path, 'src/billing.mjs');
  assert.equal(staleJson.drifted[0].status, 'prompt-stale');
  assert.deepEqual(staleJson.unowned, []);

  // Case 2: 1 untracked unowned product file (src/legacy.py) also widens to --all, exits 1, and preserves src/legacy.py in unowned!
  unlinkSync(join(staleBranchRepo, '.local/config'));
  writeFileSync(join(staleBranchRepo, 'src/legacy.py'), 'def legacy():\n    return 1\n');
  const unownedProductWidened = cliSpawn(['update', '--check', '--json'], staleBranchRepo);
  assert.equal(unownedProductWidened.code, 1, unownedProductWidened.out);
  const unownedProductJson = JSON.parse(unownedProductWidened.out);
  assert.equal(unownedProductJson.scope.kind, 'all');
  assert.equal(unownedProductJson.drifted[0].path, 'src/billing.mjs');
  assert.deepEqual(unownedProductJson.unowned, [{ path: 'src/legacy.py', reason: 'no owning prompt' }]);
  unlinkSync(join(staleBranchRepo, 'src/legacy.py'));

  // Case 3: Untracked .env or symlink in working tree fails closed with exit 2 BEFORE widening.
  writeFileSync(join(staleBranchRepo, '.env'), 'SECRET=1\n');
  assert.equal(cliSpawn(['update', '--check'], staleBranchRepo).code, 2);
  unlinkSync(join(staleBranchRepo, '.env'));
  symlinkSync(join(staleBranchRepo, 'src/billing.mjs'), join(staleBranchRepo, 'src/sneaky.mjs'));
  assert.equal(cliSpawn(['update', '--check'], staleBranchRepo).code, 2);
  unlinkSync(join(staleBranchRepo, 'src/sneaky.mjs'));

  // Case 4: Clean committed branch with a broken link (missing prompt) + 1 untracked .local/config -> widens to --all and exits 1!
  const brokenBranchRepo = makeRepo(t, {
    'prompts/app.prompt.md': '# App\n\nOwn `src/app.mjs`.\n',
    'src/app.mjs': '// Prompt: prompts/app.prompt.md\n\nexport const ok = true;\n',
  });
  git(brokenBranchRepo, ['checkout', '-q', '-b', 'feat/broken-link']);
  writeFileSync(join(brokenBranchRepo, 'src/broken.mjs'), '// Prompt: prompts/deleted.prompt.md\n\nexport const x = 1;\n');
  git(brokenBranchRepo, ['add', '.']);
  git(brokenBranchRepo, ['commit', '-qm', 'add module pointing to missing prompt']);

  mkdirSync(join(brokenBranchRepo, '.local'), { recursive: true });
  writeFileSync(join(brokenBranchRepo, '.local/config'), 'local=true\n');

  const brokenWidened = cliSpawn(['update', '--check'], brokenBranchRepo);
  assert.equal(brokenWidened.code, 1, `1 untracked .local/config must NOT hide broken prompt link\nstdout: ${brokenWidened.out}\nstderr: ${brokenWidened.err}`);
  assert.match(brokenWidened.err, /Owning prompt is missing or unreadable: prompts\/deleted\.prompt\.md/);

  // Case 5: Prompt-first PR 1 (new .prompt.md with 0 code modules yet) widens to --all: healthy repo exits 0, broken repo exits 1.
  const promptFirstRepo = makeRepo(t, {
    'prompts/app.prompt.md': '# App\n\nOwn `src/app.mjs`.\n',
    'src/app.mjs': '// Prompt: prompts/app.prompt.md\n\nexport const ok = true;\n',
  });
  writeFileSync(join(promptFirstRepo, 'prompts/next.prompt.md'), '# Next\n\nOwn `src/next.mjs`.\n');
  assert.equal(cliSpawn(['update', '--check'], promptFirstRepo).code, 0);

  // Explicit `files` scope with dirty code + clean prompt -> `changed` (NOT falsely `reconciled`).
  writeFileSync(join(promptFirstRepo, 'src/app.mjs'), '// Prompt: prompts/app.prompt.md\n\nexport const ok = false;\n');
  const explicitMixed = cliSpawn(['update', 'src/app.mjs', 'prompts/app.prompt.md', '--check', '--json'], promptFirstRepo);
  assert.equal(explicitMixed.code, 0, explicitMixed.err || explicitMixed.out);
  const explicitMixedJson = JSON.parse(explicitMixed.out);
  assert.equal(explicitMixedJson.modules[0].status, 'changed');
  assert.equal(explicitMixedJson.reminders.length, 1);

  // Explicit --all + --branch mutual-exclusion guard still returns exit 2.
  assert.equal(analyzeChangedMap({ cwd: staleBranchRepo, all: true, branch: true }).exitCode, 2);
});

test('Test F (#3657): real unowned product file IS reported while tests, docs, configs, and workspace ignores are excluded', t => {
  const root = makeRepo(t, {
    'prompts/core.prompt.md': '# Core\n\nOwn `src/core.mjs`.\n',
    'src/core.mjs': '// Prompt: prompts/core.prompt.md\n\nexport const core = 1;\n',
    'src/legacy.py': 'def legacy():\n    return 42\n',
    'src/license.py': 'def verify_license():\n    return True\n',
    'src/notice.mjs': 'export const notice = "ok";\n',
    'src/authors.go': 'package main\nfunc Authors() []string { return nil }\n',
    'src/generated/client.py': 'def generated():\n    return 0\n',
    'tests/test_legacy.py': 'def test_legacy():\n    assert True\n',
    'docs/guide.md': '# Guide\n',
    'user_stories/core.md': '# Core story\n',
    'pdd-bindings.json': `${JSON.stringify({ schema_version: 'pdd.bindings.v1', modules: [] }, null, 2)}\n`,
    'pdd.json': `${JSON.stringify({ ignore: ['src/generated/**'] }, null, 2)}\n`,
    'package.json': '{"name":"demo"}\n',
    'package-lock.json': '{"lockfileVersion":3}\n',
    'eslint.config.mjs': 'export default [];\n',
    'Makefile': 'all:\n\techo ok\n',
    'Dockerfile': 'FROM node:22\n',
    'Dockerfile.prod': 'FROM node:22-alpine\n',
    'LICENSE': 'MIT\n',
    '.github/workflows/test.yml': 'name: Test\n',
    '.local/config': 'x=1\n',
  });
  // Non-product symlink (CLAUDE.md -> docs/guide.md) must not pollute unowned in --all mode.
  symlinkSync(join(root, 'docs/guide.md'), join(root, 'CLAUDE.md'));
  git(root, ['add', 'CLAUDE.md']);
  git(root, ['commit', '-qm', 'add non-product doc symlink']);

  const res = cliSpawn(['update', '--all', '--check', '--json'], root);
  assert.equal(res.code, 0, res.err || res.out);
  const report = JSON.parse(res.out);
  assert.equal(report.ok, true);
  assert.deepEqual(report.drifted, []);
  assert.deepEqual(report.unowned, [
    { path: 'src/authors.go', reason: 'no owning prompt' },
    { path: 'src/legacy.py', reason: 'no owning prompt' },
    { path: 'src/license.py', reason: 'no owning prompt' },
    { path: 'src/notice.mjs', reason: 'no owning prompt' },
  ]);

  // pdd-workspace.json allowed_paths also excludes out-of-workspace unowned files.
  writeFileSync(join(root, 'pdd-workspace.json'), `${JSON.stringify({ allowed_paths: ['src/core.mjs', 'prompts/'] }, null, 2)}\n`);
  const wsRes = cliSpawn(['update', '--all', '--check', '--json'], root);
  assert.equal(wsRes.code, 0, wsRes.err || wsRes.out);
  assert.deepEqual(JSON.parse(wsRes.out).unowned, []);
});

test('#3630: clean committed branch and single-branch repos with unpinned/drifted modules fail pdd update --check (never false-green) and support --branch / --all', async t => {
  const { inspectStatus } = await import('../src/core/status.mjs');
  const promptText = '# Billing\n\nOwn `src/billing.mjs`.\n\n## Domain decisions\n- Integer cents only.\n';
  const pinnedHash = promptHeaderHash(promptText);
  const root = makeRepo(t, {
    'prompts/billing.prompt.md': promptText,
    'src/billing.mjs': `// Generated from prompts/billing.prompt.md (sha256: ${pinnedHash}).\nexport function cents(n) { return n * 100; }\n`,
  });

  // 1. Clean default branch -> pdd update --check widens to all and exits 0 (truly current).
  const pinnedCheck = await cli(['update', '--check', '--json'], root);
  assert.equal(pinnedCheck.code, 0, pinnedCheck.err || pinnedCheck.out);
  const pinnedReport = JSON.parse(pinnedCheck.out);
  assert.equal(pinnedReport.ok, true);
  assert.equal(pinnedReport.scope.kind, 'all');
  assert.equal(pinnedReport.scope.widened_from, 'working-tree');
  assert.deepEqual(pinnedReport.drifted, []);

  // 2. Clean committed feature branch with modern hashless co-changed module exits 0 (reconciled) AND stale legacy module fails with exit 1!
  git(root, ['checkout', '-q', '-b', 'feat/branch-widening']);
  writeFileSync(
    join(root, 'prompts/ledger.prompt.md'),
    '# Ledger\n\nOwn `src/ledger.mjs`.\n\n## Domain decisions\n- Append-only entries.\n',
  );
  writeFileSync(
    join(root, 'src/ledger.mjs'),
    '// Prompt: prompts/ledger.prompt.md\n\nexport function append(entry) { return [entry]; }\n',
  );
  git(root, ['add', '.']);
  git(root, ['commit', '-qm', 'add hashless ledger module']);

  const cleanBranchCheck = await cli(['update', '--check', '--json'], root);
  assert.equal(cleanBranchCheck.code, 0, cleanBranchCheck.err || cleanBranchCheck.out);
  const cleanBranchJson = JSON.parse(cleanBranchCheck.out);
  assert.equal(cleanBranchJson.ok, true);
  assert.equal(cleanBranchJson.scope.kind, 'branch');
  assert.equal(cleanBranchJson.scope.widened_from, 'working-tree');
  assert.ok(cleanBranchJson.modules.some(m => m.path === 'src/ledger.mjs' && m.status === 'reconciled'));

  // Now commit a stale legacy sha256 mismatch on the branch -> NEVER silent false-green!
  writeFileSync(
    join(root, 'prompts/billing.prompt.md'),
    '# Billing\n\nOwn `src/billing.mjs`.\n\n## Domain decisions\n- Integer cents with tax.\n',
  );
  git(root, ['add', '.']);
  git(root, ['commit', '-qm', 'stale billing prompt hash']);

  const branchCheck = await cli(['update', '--check', '--json'], root);
  assert.equal(branchCheck.code, 1, `clean committed branch with stale module must exit 1, got: ${branchCheck.out}`);
  const branchJson = JSON.parse(branchCheck.out);
  assert.equal(branchJson.ok, false);
  assert.equal(branchJson.scope.kind, 'branch');
  assert.equal(branchJson.scope.widened_from, 'working-tree');
  assert.ok(branchJson.drifted.some(d => d.path === 'src/billing.mjs' && d.status === 'prompt-stale'));

  // status --changed also sees committed branch changes on a clean tree!
  const statusView = await inspectStatus({ cwd: root, changed: true });
  assert.ok(statusView.changed.includes('src/ledger.mjs'), `expected src/ledger.mjs in status --changed: ${JSON.stringify(statusView.changed)}`);

  // Explicit branch: true and all: true scopes + mutual-exclusion guard.
  const explicitBranch = analyzeChangedMap({ cwd: root, branch: true });
  assert.equal(explicitBranch.ok, true, explicitBranch.error);
  assert.equal(explicitBranch.report.scope.kind, 'branch');
  assert.ok(explicitBranch.report.modules.some(m => m.path === 'src/ledger.mjs'));

  const explicitAll = analyzeUpdate({ cwd: root, all: true, check: true });
  assert.equal(explicitAll.exitCode, 1);
  assert.equal(explicitAll.report.scope.kind, 'all');
  assert.ok(explicitAll.report.modules.some(m => m.path === 'src/billing.mjs' && m.status === 'prompt-stale'));
  assert.ok(explicitAll.report.modules.some(m => m.path === 'src/ledger.mjs' && m.status === 'current'));
  assert.equal(analyzeChangedMap({ cwd: root, all: true, branch: true }).exitCode, 2);

  // 3. Clean single-branch repo (main only) with stale legacy module -> widens to all and exits 1!
  const staleTaxPrompt = '# Tax\n\nOwn `src/tax.mjs`.\n\n## Domain decisions\n- 10%.\n';
  const staleTaxHash = promptHeaderHash(staleTaxPrompt);
  const singleBranch = makeRepo(t, {
    'prompts/tax.prompt.md': '# Tax\n\nOwn `src/tax.mjs`.\n\n## Domain decisions\n- 20%.\n',
    'src/tax.mjs': `// Generated from prompts/tax.prompt.md (sha256: ${staleTaxHash}).\nexport const tax = n => Math.round(n * 0.2);\n`,
  });
  const singleCheck = await cli(['update', '--check', '--json'], singleBranch);
  assert.equal(singleCheck.code, 1, `single-branch repo with stale module must exit 1, got: ${singleCheck.out}`);
  const singleJson = JSON.parse(singleCheck.out);
  assert.equal(singleJson.ok, false);
  assert.equal(singleJson.scope.kind, 'all');
  assert.equal(singleJson.drifted[0].path, 'src/tax.mjs');
  assert.equal(singleJson.drifted[0].status, 'prompt-stale');
});
