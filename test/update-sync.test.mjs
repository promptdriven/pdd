import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, symlinkSync, unlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { promptHeaderHash, parseModuleSyncPins } from '../src/file-owner.mjs';
import { extractDiffSummary, runUpdate } from '../src/update-sync.mjs';
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
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-update-sync-')));
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
    env: { PATH: dirname(GIT_BIN), HOME: cwd, PDD_RUNTIME_URL: 'invalid' },
  });
  return { code, out: stdout.text, err: stderr.text };
}

test('extractDiffSummary counts lines and classifies added, removed, and updated symbols deterministically', () => {
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

test('3447/3203 full lifecycle: plan, --check, --write, all 5 drift states, pdd owner parity, and idempotency', async t => {
  const billingPrompt = '# Billing\n\nOwn `src/billing.mjs`.\n\n## Domain decisions\n\n- Amounts use integer cents.\n\n## Security invariants\n\n- Never log raw payment tokens.\n';
  const billingHash = promptHeaderHash(billingPrompt);
  const root = makeRepo(t, {
    'prompts/billing.prompt.md': billingPrompt,
    'src/billing.mjs': `// Generated from prompts/billing.prompt.md (sha256: ${billingHash}).\nexport function totalCents(items) { return items.length * 100; }\n`,
    'README.md': '# Demo\n',
  });

  // 1. Initially unpinned: plan exits 0 (no writes), --check exits 1
  const plan = await cli(['update', 'src/billing.mjs', 'README.md', '--json'], root);
  assert.equal(plan.code, 0, plan.err);
  const planJson = JSON.parse(plan.out);
  assert.equal(planJson.schema_version, 'pdd.update-sync.v1');
  assert.equal(planJson.ok, true);
  assert.equal(planJson.scope.kind, 'files');
  assert.equal(planJson.prompts.length, 1);
  assert.equal(planJson.prompts[0].prompt, 'prompts/billing.prompt.md');
  assert.equal(planJson.prompts[0].status, 'unpinned');
  assert.equal(planJson.modules[0].status, 'unpinned');
  assert.deepEqual(planJson.unowned, [{ path: 'README.md', reason: 'no owning prompt' }]);
  assert.deepEqual(planJson.updated, []);

  const checkUnpinned = await cli(['update', 'src/billing.mjs', '--check', '--json'], root);
  assert.equal(checkUnpinned.code, 1);
  assert.equal(JSON.parse(checkUnpinned.out).ok, false);
  assert.equal(JSON.parse(checkUnpinned.out).drifted[0].status, 'unpinned');

  // 2. --write pins per-module hash inside prompt and keeps prose intact
  const write1 = await cli(['update', 'src/billing.mjs', '--write', '--json'], root);
  assert.equal(write1.code, 0, write1.err);
  const write1Json = JSON.parse(write1.out);
  assert.equal(write1Json.ok, true);
  assert.equal(write1Json.modules[0].status, 'current');
  assert.equal(write1Json.drifted.length, 0);
  assert.ok(write1Json.updated.some(u => u.path === 'prompts/billing.prompt.md' && u.kind === 'prompt-pin'));
  const updatedPromptText = readFileSync(join(root, 'prompts/billing.prompt.md'), 'utf8');
  assert.ok(updatedPromptText.includes('## Security invariants\n\n- Never log raw payment tokens.\n'));
  assert.equal(parseModuleSyncPins(updatedPromptText).has('src/billing.mjs'), true);

  // pdd owner stays 100% current with the pin comment in place!
  const ownerRes = await cli(['owner', 'src/billing.mjs', '--json'], root);
  assert.equal(ownerRes.code, 0, ownerRes.err);
  assert.equal(JSON.parse(ownerRes.out).files[0].headers[0].state, 'current');
  assert.equal(JSON.parse(ownerRes.out).files[0].headers[0].legacy, false);

  // --check now exits 0, and repeat --write makes 0 updates (idempotent)
  assert.equal((await cli(['update', 'src/billing.mjs', '--check'], root)).code, 0);
  const write2 = await cli(['update', 'src/billing.mjs', '--write', '--json'], root);
  assert.equal(write2.code, 0);
  assert.deepEqual(JSON.parse(write2.out).updated, []);

  // 3. Edit code only -> code-drifted
  writeFileSync(
    join(root, 'src/billing.mjs'),
    `// Generated from prompts/billing.prompt.md (sha256: ${billingHash}).\nexport function totalCents(items) { return items.length * 100; }\nexport function applyCap(cents, max) { return Math.min(cents, max); }\n`,
  );
  const codeDrift = await cli(['update', '--check', '--json'], root);
  assert.equal(codeDrift.code, 1);
  const codeDriftJson = JSON.parse(codeDrift.out);
  assert.equal(codeDriftJson.scope.kind, 'working-tree');
  assert.equal(codeDriftJson.modules[0].status, 'code-drifted');
  assert.equal(codeDriftJson.modules[0].diff_stats.added, 1);
  assert.deepEqual(codeDriftJson.modules[0].changed_symbols, [{ kind: 'added', symbol: 'applyCap' }]);

  // 4. Also edit prompt prose -> both-drifted
  writeFileSync(
    join(root, 'prompts/billing.prompt.md'),
    updatedPromptText.replace('Amounts use integer cents.', 'Amounts use integer cents with an optional cap.'),
  );
  const bothDrift = await cli(['update', 'src/billing.mjs', '--check', '--json'], root);
  assert.equal(bothDrift.code, 1);
  assert.equal(JSON.parse(bothDrift.out).modules[0].status, 'both-drifted');

  // 5. --write reconciles BOTH prompt pin and code header hash!
  const write3 = await cli(['update', 'src/billing.mjs', '--write', '--json'], root);
  assert.equal(write3.code, 0, write3.err);
  const write3Json = JSON.parse(write3.out);
  assert.equal(write3Json.modules[0].status, 'current');
  assert.ok(write3Json.updated.some(u => u.path === 'prompts/billing.prompt.md' && u.kind === 'prompt-pin'));
  assert.ok(write3Json.updated.some(u => u.path === 'src/billing.mjs' && u.kind === 'code-header'));
  assert.equal(JSON.parse((await cli(['owner', 'src/billing.mjs', '--json'], root)).out).files[0].headers[0].state, 'current');

  // 6. Edit prompt prose only (code unchanged) -> prompt-stale (even via default working-tree on prompt-only edit!)
  git(root, ['add', '.']);
  git(root, ['commit', '-qm', 'synced']);
  const committedPrompt = readFileSync(join(root, 'prompts/billing.prompt.md'), 'utf8');
  writeFileSync(join(root, 'prompts/billing.prompt.md'), committedPrompt.replace('optional cap.', 'explicit cap.'));
  const promptStale = await cli(['update', '--check', '--json'], root);
  assert.equal(promptStale.code, 1);
  const promptStaleJson = JSON.parse(promptStale.out);
  assert.equal(promptStaleJson.modules[0].path, 'src/billing.mjs');
  assert.equal(promptStaleJson.modules[0].status, 'prompt-stale');
  assert.equal(promptStaleJson.unowned.length, 0);
});

test('3447 scoped --from <base>..<head> and single <base>, multi-module grouping, and pdd-bindings.json untouched', async t => {
  const sharedPrompt = '# Shared\n\nOwn `src/a.mjs` and `src/b.mjs`.\n';
  const boundPrompt = '# Bound\n\nOwn `src/bound.mjs`.\n';
  const bindingsText = JSON.stringify({
    schema_version: 'pdd.bindings.v1',
    modules: [
      { module: 'src/bound.mjs', prompt: 'prompts/bound.prompt.md' },
      { module: 'src/bound-with-stories.mjs', stories: ['user_stories/s.md'], prompt: 'prompts/bound.prompt.md' },
    ],
  }, null, 2) + '\n';
  const root = makeRepo(t, {
    'pdd-bindings.json': bindingsText,
    'prompts/shared.prompt.md': sharedPrompt,
    'prompts/bound.prompt.md': boundPrompt,
    'src/a.mjs': `// Generated from prompts/shared.prompt.md (sha256: ${promptHeaderHash(sharedPrompt)}).\nexport const a = 1;\n`,
    'src/b.mjs': `// Prompt: prompts/shared.prompt.md\nexport const b = 1;\n`,
    'src/bound.mjs': 'export const bound = 1;\n',
    'src/bound-with-stories.mjs': 'export const bound2 = 1;\n',
    'docs/notes.md': 'initial\n',
  });

  // Pin all 4 initially and commit as base
  assert.equal((await cli(['update', 'src/a.mjs', 'src/b.mjs', 'src/bound.mjs', 'src/bound-with-stories.mjs', '--write'], root)).code, 0);
  // pdd-bindings.json MUST stay byte-for-byte untouched (never add unknown fields!)
  assert.equal(readFileSync(join(root, 'pdd-bindings.json'), 'utf8'), bindingsText);
  // Headerless bound files MUST NOT get synthetic // headers injected
  assert.equal(readFileSync(join(root, 'src/bound.mjs'), 'utf8'), 'export const bound = 1;\n');
  git(root, ['add', '.']);
  git(root, ['commit', '-qm', 'pinned']);
  const baseSha = git(root, ['rev-parse', 'HEAD']);

  // Commit a scoped change touching ONLY src/a.mjs, src/bound.mjs, and docs/notes.md (NOT src/b.mjs!)
  const aBefore = readFileSync(join(root, 'src/a.mjs'), 'utf8');
  writeFileSync(join(root, 'src/a.mjs'), `${aBefore}export function extraA() { return 2; }\n`);
  writeFileSync(join(root, 'src/bound.mjs'), 'export const bound = 2;\nexport function boundFn() {}\n');
  writeFileSync(join(root, 'docs/notes.md'), 'updated\n');
  git(root, ['add', '.']);
  git(root, ['commit', '-qm', 'scoped-change']);

  // --from <base>..<head> AND single --from <base> produce identical scoped results
  const rangeRes = await cli(['update', '--from', `${baseSha}..HEAD`, '--json'], root);
  const singleRes = await cli(['update', '--from', baseSha, '--json'], root);
  assert.equal(rangeRes.code, 0, rangeRes.err);
  assert.equal(singleRes.code, 0, singleRes.err);
  const rangeData = JSON.parse(rangeRes.out);
  const singleData = JSON.parse(singleRes.out);
  assert.deepEqual(rangeData.modules, singleData.modules);
  assert.deepEqual(rangeData.modules.map(m => m.path), ['src/a.mjs', 'src/bound.mjs']);
  assert.equal(rangeData.modules.some(m => m.path === 'src/b.mjs'), false, 'untouched sibling must stay out of scope');
  assert.deepEqual(rangeData.unowned, [{ path: 'docs/notes.md', reason: 'no owning prompt' }]);

  // Updating src/a.mjs in shared prompt does NOT make untouched sibling src/b.mjs stale!
  const writeScoped = await cli(['update', '--from', `${baseSha}..HEAD`, '--write', '--json'], root);
  assert.equal(writeScoped.code, 0, writeScoped.err);
  assert.equal(JSON.parse((await cli(['update', 'src/b.mjs', '--check', '--json'], root)).out).ok, true);
  assert.equal(JSON.parse((await cli(['owner', 'src/b.mjs', '--json'], root)).out).files[0].headers[0].state, 'current');

  // Empty diff range exits 0 cleanly (even under --check)
  const emptyRes = await cli(['update', '--from', 'HEAD..HEAD', '--check', '--json'], root);
  assert.equal(emptyRes.code, 0, emptyRes.err);
  assert.deepEqual(JSON.parse(emptyRes.out).prompts, []);
  assert.equal(JSON.parse(emptyRes.out).ok, true);
});

test('3203 parallel PRs modifying different modules merge with ZERO conflicts', async t => {
  const alphaPrompt = '# Alpha\n\nOwn `src/alpha.mjs`.\n';
  const betaPrompt = '# Beta\n\nOwn `src/beta.mjs`.\n';
  const root = makeRepo(t, {
    'prompts/alpha.prompt.md': alphaPrompt,
    'prompts/beta.prompt.md': betaPrompt,
    'src/alpha.mjs': `// Generated from prompts/alpha.prompt.md (sha256: ${promptHeaderHash(alphaPrompt)}).\nexport const alpha = 1;\n`,
    'src/beta.mjs': `// Generated from prompts/beta.prompt.md (sha256: ${promptHeaderHash(betaPrompt)}).\nexport const beta = 1;\n`,
  });
  assert.equal((await cli(['update', 'src/alpha.mjs', 'src/beta.mjs', '--write'], root)).code, 0);
  git(root, ['add', '.']);
  git(root, ['commit', '-qm', 'initial-pins']);

  // Branch A touches alpha only
  git(root, ['checkout', '-qb', 'pr-alpha']);
  writeFileSync(join(root, 'prompts/alpha.prompt.md'), readFileSync(join(root, 'prompts/alpha.prompt.md'), 'utf8').replace('# Alpha', '# Alpha v2'));
  writeFileSync(join(root, 'src/alpha.mjs'), `${readFileSync(join(root, 'src/alpha.mjs'), 'utf8')}export const alpha2 = 2;\n`);
  assert.equal((await cli(['update', '--write'], root)).code, 0);
  git(root, ['add', '.']);
  git(root, ['commit', '-qm', 'update-alpha']);

  // Branch B touches beta only (from main)
  git(root, ['checkout', '-q', 'main']);
  git(root, ['checkout', '-qb', 'pr-beta']);
  writeFileSync(join(root, 'prompts/beta.prompt.md'), readFileSync(join(root, 'prompts/beta.prompt.md'), 'utf8').replace('# Beta', '# Beta v2'));
  writeFileSync(join(root, 'src/beta.mjs'), `${readFileSync(join(root, 'src/beta.mjs'), 'utf8')}export const beta2 = 2;\n`);
  assert.equal((await cli(['update', '--write'], root)).code, 0);
  git(root, ['add', '.']);
  git(root, ['commit', '-qm', 'update-beta']);

  // Merge pr-alpha into pr-beta: MUST succeed cleanly with ZERO merge conflicts!
  git(root, ['merge', '--no-edit', 'pr-alpha']);
  const checkBoth = await cli(['update', 'src/alpha.mjs', 'src/beta.mjs', '--check', '--json'], root);
  assert.equal(checkBoth.code, 0, checkBoth.out + checkBoth.err);
  assert.equal(JSON.parse(checkBoth.out).ok, true);
});

test('3447 edge cases: deleted files, renamed files, non-ASCII filenames, and human-readable text output', async t => {
  const cafePrompt = '# Café\n\nOwn `src/café.mjs` and `src/old.mjs`.\n';
  const root = makeRepo(t, {
    'prompts/cafe.prompt.md': cafePrompt,
    'src/café.mjs': `// Generated from prompts/cafe.prompt.md (sha256: ${promptHeaderHash(cafePrompt)}).\nexport const café = 'espresso';\n`,
    'src/old.mjs': `// Generated from prompts/cafe.prompt.md (sha256: ${promptHeaderHash(cafePrompt)}).\nexport const oldVal = 1;\n`,
    'src/to-delete.mjs': `// Generated from prompts/cafe.prompt.md (sha256: ${promptHeaderHash(cafePrompt)}).\nexport const gone = true;\n`,
  });

  // Pin all 3
  assert.equal((await cli(['update', 'src/café.mjs', 'src/old.mjs', 'src/to-delete.mjs', '--write'], root)).code, 0);
  git(root, ['add', '.']);
  git(root, ['commit', '-qm', 'pinned']);
  const base = git(root, ['rev-parse', 'HEAD']);

  // Modify non-ASCII file, rename src/old.mjs -> src/renamed.mjs, delete src/to-delete.mjs
  writeFileSync(join(root, 'src/café.mjs'), `${readFileSync(join(root, 'src/café.mjs'), 'utf8')}export function brew() { return 'latte'; }\n`);
  git(root, ['mv', 'src/old.mjs', 'src/renamed.mjs']);
  unlinkSync(join(root, 'src/to-delete.mjs'));
  git(root, ['add', '-A']);
  git(root, ['commit', '-qm', 'rename-delete-nonascii']);

  const textRes = await cli(['update', '--from', `${base}..HEAD`], root);
  assert.equal(textRes.code, 0, textRes.err);
  assert.match(textRes.out, /prompts\/cafe\.prompt\.md/);
  assert.match(textRes.out, /src\/café\.mjs \[code-drifted\]/);
  assert.match(textRes.out, /src\/renamed\.mjs.*renamed from src\/old\.mjs/);
  assert.match(textRes.out, /src\/to-delete\.mjs \[deleted\]/);

  // --write refreshes café, migrates old.mjs pin to renamed.mjs, and prunes to-delete.mjs pin
  const writeRes = await cli(['update', '--from', `${base}..HEAD`, '--write', '--json'], root);
  assert.equal(writeRes.code, 0, writeRes.err);
  const pins = parseModuleSyncPins(readFileSync(join(root, 'prompts/cafe.prompt.md'), 'utf8'));
  assert.equal(pins.has('src/café.mjs'), true);
  assert.equal(pins.has('src/renamed.mjs'), true);
  assert.equal(pins.has('src/old.mjs'), false);
  assert.equal(pins.has('src/to-delete.mjs'), false);

  // --check after --write passes cleanly even when range includes the deleted file!
  const checkAfter = await cli(['update', '--from', `${base}..HEAD`, '--check', '--json'], root);
  assert.equal(checkAfter.code, 0, checkAfter.out + checkAfter.err);
  assert.equal(JSON.parse(checkAfter.out).ok, true);
});

test('3447 security guards: reject traversal, leading-dash injection, symlinks, secrets, binary files, bad combinations, and non-git', async t => {
  const outside = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-update-outside-')));
  t.after(() => rmSync(outside, { recursive: true, force: true }));
  writeFileSync(join(outside, 'leak.mjs'), 'export const leak = 1;\n');

  const prompt = '# Guard\n\nOwn `src/ok.mjs`.\n';
  const root = makeRepo(t, {
    'prompts/guard.prompt.md': prompt,
    'src/ok.mjs': `// Generated from prompts/guard.prompt.md (sha256: ${promptHeaderHash(prompt)}).\nexport const ok = 1;\n`,
    'src/bin.mjs': Buffer.from([0x2f, 0x2f, 0x20, 0x00, 0x01, 0x02]),
    '.env': 'SECRET=1\n',
    'credentials.json': '{"token":"x"}\n',
  });
  symlinkSync(join(outside, 'leak.mjs'), join(root, 'src/link.mjs'));

  const refused2 = [
    ['update', '--check', '--write'],
    ['update', 'src/ok.mjs', '--from', 'HEAD'],
    ['update', '--from', '--exec=bad'],
    ['update', '--from', '-HEAD'],
    ['update', '--from', 'HEAD..-bad'],
    ['update', '--from', 'HEAD...HEAD'],
    ['update', '--from', 'HEAD..'],
    ['update', '--from', 'nonexistent-ref-xyz..HEAD'],
    ['update', '--', '-badfile.mjs'],
    ['update', '../outside.mjs'],
    ['update', 'src/../src/ok.mjs'],
    ['update', join(outside, 'leak.mjs')],
    ['update', 'src/missing.mjs'],
    ['update', 'src/link.mjs'],
    ['update', '.env'],
    ['update', 'credentials.json'],
    ['update', 'src/bin.mjs'],
  ];
  for (const args of refused2) {
    const res = await cli(args, root);
    assert.equal(res.code, 2, `expected exit 2 for ${JSON.stringify(args)}, got ${res.code} (out=${res.out}, err=${res.err})`);
    assert.equal(res.out, '');
    assert.ok(res.err.trim().length > 0, `expected stderr diagnostic for ${JSON.stringify(args)}`);
  }

  // Outside a Git repo -> exit 2
  const nonGit = await cli(['update'], outside);
  assert.equal(nonGit.code, 2);
  assert.match(nonGit.err, /works inside a Git repository/);

  // Misplaced test prompt -> exit 1, 0 writes
  const badRepo = makeRepo(t, {
    'prompts/test/bad.prompt.md': '# Bad\n',
    'src/x.mjs': '// Generated from prompts/test/bad.prompt.md.\nexport const x = 1;\n',
  });
  const misplaced = await cli(['update', 'src/x.mjs', '--write'], badRepo);
  assert.equal(misplaced.code, 1);
  assert.match(misplaced.err, /misplaced test prompt/);

  // Unowned binary asset in --from is skipped cleanly under unowned without crashing
  const binRepo = makeRepo(t, {
    'prompts/app.prompt.md': '# App\n\nOwn `src/app.mjs`.\n',
    'src/app.mjs': '// Generated from prompts/app.prompt.md.\nexport const app = 1;\n',
  });
  const base = git(binRepo, ['rev-parse', 'HEAD']);
  mkdirSync(join(binRepo, 'assets'), { recursive: true });
  writeFileSync(join(binRepo, 'assets/logo.png'), Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x00, 0x01]));
  git(binRepo, ['add', '.']);
  git(binRepo, ['commit', '-qm', 'add-png']);
  const withPng = await cli(['update', '--from', `${base}..HEAD`, '--json'], binRepo);
  assert.equal(withPng.code, 0, withPng.err);
  assert.deepEqual(JSON.parse(withPng.out).unowned, [{ path: 'assets/logo.png', reason: 'binary file (skipped)' }]);

  // Direct API runUpdate returns 0 on clean repo with no touched files
  const cleanOut = capture(), cleanErr = capture();
  assert.equal(runUpdate({ cwd: binRepo, check: true }, { stdout: cleanOut, stderr: cleanErr }), 0);
  assert.match(cleanOut.text, /no touched files in scope/);
});
