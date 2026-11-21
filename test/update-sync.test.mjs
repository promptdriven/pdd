import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import {
  chmodSync,
  existsSync,
  mkdirSync,
  mkdtempSync,
  readdirSync,
  readFileSync,
  realpathSync,
  rmSync,
  statSync,
  symlinkSync,
  unlinkSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { promptHeaderHash } from '../src/file-owner.mjs';
import { extractDiffSummary, runUpdate, syncRecordPathForModule } from '../src/update-sync.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { gitFiles, promptRefusal, proseSha256, readPrompt } from '../src/runtime-seam.mjs';

const GIT_BIN = execFileSync('which', ['git'], { encoding: 'utf8' }).trim() || '/usr/bin/git';
const capture = () => ({ text: '', write(value) { this.text += value; return true; } });
const sha256 = text => createHash('sha256').update(text).digest('hex');

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

function makeIsolatedHome(t) {
  const home = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-update-home-')));
  t.after(() => rmSync(home, { recursive: true, force: true }));
  return home;
}

async function cli(argv, cwd, { home = null, extraDeps = {} } = {}) {
  const stdout = capture(), stderr = capture();
  const effHome = home ?? cwd;
  const code = await runPdd(argv, {
    stdout,
    stderr,
    cwd,
    env: {
      PATH: dirname(GIT_BIN),
      HOME: effHome,
      PDD_STATE_DIR: join(effHome, '.local', 'state', 'pdd'),
      PDD_RUNTIME_URL: 'invalid',
    },
    ...extraDeps,
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

test('3447/3203 full lifecycle: plan, --check, --write, all 5 drift states, sidecar storage, and idempotency', async t => {
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
  assert.equal(planJson.modules[0].sync_record, '.pdd/sync/src/billing.mjs.json');
  assert.deepEqual(planJson.unowned, [{ path: 'README.md', reason: 'no owning prompt' }]);
  assert.deepEqual(planJson.updated, []);
  assert.equal(existsSync(join(root, '.pdd/sync/src/billing.mjs.json')), false);

  const checkUnpinned = await cli(['update', 'src/billing.mjs', '--check', '--json'], root);
  assert.equal(checkUnpinned.code, 1);
  assert.equal(JSON.parse(checkUnpinned.out).ok, false);
  assert.equal(JSON.parse(checkUnpinned.out).drifted[0].status, 'unpinned');

  // 2. --write creates disjoint sidecar .pdd/sync/src/billing.mjs.json and NEVER modifies prompts/billing.prompt.md!
  const write1 = await cli(['update', 'src/billing.mjs', '--write', '--json'], root);
  assert.equal(write1.code, 0, write1.err);
  const write1Json = JSON.parse(write1.out);
  assert.equal(write1Json.ok, true);
  assert.equal(write1Json.modules[0].status, 'current');
  assert.equal(write1Json.drifted.length, 0);
  assert.ok(write1Json.updated.some(u => u.path === '.pdd/sync/src/billing.mjs.json' && u.kind === 'sync-record'));
  assert.equal(readFileSync(join(root, 'prompts/billing.prompt.md'), 'utf8'), billingPrompt, '.prompt.md must stay byte-for-byte unchanged');
  const sidecar = JSON.parse(readFileSync(join(root, '.pdd/sync/src/billing.mjs.json'), 'utf8'));
  assert.equal(sidecar.schema_version, 'pdd.module-sync.v1');
  assert.equal(sidecar.module, 'src/billing.mjs');
  assert.equal(sidecar.prompt, 'prompts/billing.prompt.md');
  assert.equal(sidecar.prompt_sha256, billingHash);

  // pdd owner stays 100% current
  const ownerRes = await cli(['owner', 'src/billing.mjs', '--json'], root);
  assert.equal(ownerRes.code, 0, ownerRes.err);
  assert.equal(JSON.parse(ownerRes.out).files[0].headers[0].state, 'current');
  assert.equal(JSON.parse(ownerRes.out).files[0].headers[0].legacy, false);

  // --check now exits 0, and repeat --write makes 0 updates (idempotent)
  assert.equal((await cli(['update', 'src/billing.mjs', '--check'], root)).code, 0);
  const write2 = await cli(['update', 'src/billing.mjs', '--write', '--json'], root);
  assert.equal(write2.code, 0);
  assert.deepEqual(JSON.parse(write2.out).updated, []);

  // 3. Edit code only -> code-drifted (sidecars under .pdd/sync/ are ignored from unowned)
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
  assert.deepEqual(codeDriftJson.unowned, [], '.pdd/sync/*.json must not pollute unowned');

  // 4. Also edit prompt prose -> both-drifted
  const editedPrompt = billingPrompt.replace('Amounts use integer cents.', 'Amounts use integer cents with an optional cap.');
  writeFileSync(join(root, 'prompts/billing.prompt.md'), editedPrompt);
  const bothDrift = await cli(['update', 'src/billing.mjs', '--check', '--json'], root);
  assert.equal(bothDrift.code, 1);
  assert.equal(JSON.parse(bothDrift.out).modules[0].status, 'both-drifted');

  // 5. --write reconciles BOTH sidecar and code header hash while leaving prompt bytes untouched!
  const write3 = await cli(['update', 'src/billing.mjs', '--write', '--json'], root);
  assert.equal(write3.code, 0, write3.err);
  const write3Json = JSON.parse(write3.out);
  assert.equal(write3Json.modules[0].status, 'current');
  assert.ok(write3Json.updated.some(u => u.path === '.pdd/sync/src/billing.mjs.json' && u.kind === 'sync-record'));
  assert.ok(write3Json.updated.some(u => u.path === 'src/billing.mjs' && u.kind === 'code-header'));
  assert.equal(readFileSync(join(root, 'prompts/billing.prompt.md'), 'utf8'), editedPrompt);
  assert.equal(JSON.parse((await cli(['owner', 'src/billing.mjs', '--json'], root)).out).files[0].headers[0].state, 'current');

  // 6. Edit prompt prose only (code unchanged) -> prompt-stale via working-tree default mode
  git(root, ['add', '.']);
  git(root, ['commit', '-qm', 'synced']);
  writeFileSync(join(root, 'prompts/billing.prompt.md'), editedPrompt.replace('optional cap.', 'explicit cap.'));
  const promptStale = await cli(['update', '--check', '--json'], root);
  assert.equal(promptStale.code, 1);
  const promptStaleJson = JSON.parse(promptStale.out);
  assert.equal(promptStaleJson.modules[0].path, 'src/billing.mjs');
  assert.equal(promptStaleJson.modules[0].status, 'prompt-stale');
  assert.equal(promptStaleJson.unowned.length, 0);
});

test('R1 #1 P0 regression: --write preserves prompt bytes, proseSha256, promptRefusal, no-newline prompts, legacy sibling headers, pdd files, and pdd lint --local', async t => {
  const home = makeIsolatedHome(t);
  const iface = {
    status: 'approved',
    prose_sha256: 'PLACEHOLDER',
    entries: [{
      operation: 'ping',
      input_schema: { type: 'object', properties: {}, required: [], additionalProperties: false },
      result_schema: { type: 'object', properties: { ok: { type: 'boolean' } }, required: ['ok'], additionalProperties: false },
      errors: [],
    }],
    resources: [],
    conventions: [],
    calls: [],
    limits: { max_steps: 4, max_model_calls: 2 },
  };
  const draft = `# App\n\nOwn \`src/app.mjs\` and \`src/legacy-sib.mjs\`.\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(iface)}\n\`\`\`\n</details>`; // intentionally NO trailing newline!
  const approvedPrompt = draft.replace('PLACEHOLDER', proseSha256(draft));
  const wholeSha = sha256(approvedPrompt);
  const headerSha = promptHeaderHash(approvedPrompt);

  const root = makeRepo(t, {
    'prompts/app.prompt.md': approvedPrompt,
    'src/app.mjs': `// Generated from prompts/app.prompt.md (sha256: ${headerSha}).\nexport const ok = true;\n`,
    'src/legacy-sib.mjs': `// Generated from prompts/app.prompt.md (sha256: ${wholeSha}).\nexport const legacy = true;\n`,
  });

  const beforeProse = proseSha256(approvedPrompt);
  const writeRes = await cli(['update', 'src/app.mjs', '--write', '--json'], root, { home });
  assert.equal(writeRes.code, 0, writeRes.err);

  // Prompt MUST be byte-for-byte unchanged, proseSha256 unchanged, promptRefusal === null!
  const afterPrompt = readFileSync(join(root, 'prompts/app.prompt.md'), 'utf8');
  assert.equal(afterPrompt, approvedPrompt);
  assert.equal(proseSha256(afterPrompt), beforeProse);
  const vis = new Set(gitFiles(root));
  assert.equal(promptRefusal(readPrompt(root, vis, 'prompts/app.prompt.md'), 'interface'), null);

  // Both src/app.mjs and sibling with legacy whole-file header hash remain current in pdd owner!
  const ownerRes = await cli(['owner', 'src/app.mjs', 'src/legacy-sib.mjs', '--json'], root, { home });
  assert.equal(ownerRes.code, 0, ownerRes.err);
  const ownerFiles = JSON.parse(ownerRes.out).files;
  assert.equal(ownerFiles[0].headers[0].state, 'current');
  assert.equal(ownerFiles[0].headers[0].legacy, false);
  assert.equal(ownerFiles[1].headers[0].state, 'current');
  assert.equal(ownerFiles[1].headers[0].legacy, true);

  // pdd files --json and pdd lint --local stay 100% clean with .pdd/sync/*.json committed!
  git(root, ['add', '-f', '.pdd/sync']);
  git(root, ['commit', '-qm', 'track-sidecar']);
  const filesRes = await cli(['files', '--json'], root, { home });
  assert.equal(filesRes.code, 0, filesRes.err);
  const filesJson = JSON.parse(filesRes.out);
  assert.deepEqual(filesJson.orphans, []);
  assert.deepEqual(filesJson.refusals, []);
  const lintRes = await cli(['lint', '--local', '--json'], root, { home });
  assert.equal(lintRes.code, 0, lintRes.err);
  const lintJson = JSON.parse(lintRes.out);
  assert.equal(lintJson.exit_code, 0);
  assert.equal(lintJson.local_only, true);
  assert.deepEqual(lintJson.problems ?? [], []);
});

test('R1 #1 P0 + #3203: two parallel PRs editing different modules owned by the SAME prompt merge with ZERO conflicts', async t => {
  const sharedPrompt = '# Shared\n\nOwn `src/a.mjs` and `src/b.mjs`.\n';
  const h = promptHeaderHash(sharedPrompt);
  const root = makeRepo(t, {
    'prompts/shared.prompt.md': sharedPrompt,
    'src/a.mjs': `// Generated from prompts/shared.prompt.md (sha256: ${h}).\nexport const a = 1;\n`,
    'src/b.mjs': `// Generated from prompts/shared.prompt.md (sha256: ${h}).\nexport const b = 1;\n`,
  });
  assert.equal((await cli(['update', 'src/a.mjs', 'src/b.mjs', '--write'], root)).code, 0);
  git(root, ['add', '-f', '.']);
  git(root, ['commit', '-qm', 'initial-pins']);

  // Branch A modifies ONLY src/a.mjs (owned by prompts/shared.prompt.md)
  git(root, ['checkout', '-qb', 'pr-a']);
  writeFileSync(join(root, 'src/a.mjs'), `${readFileSync(join(root, 'src/a.mjs'), 'utf8')}export const a2 = 2;\n`);
  assert.equal((await cli(['update', 'src/a.mjs', '--write'], root)).code, 0);
  git(root, ['add', '-f', '.']);
  git(root, ['commit', '-qm', 'update-a']);

  // Branch B modifies ONLY src/b.mjs (owned by the EXACT SAME prompts/shared.prompt.md!)
  git(root, ['checkout', '-q', 'main']);
  git(root, ['checkout', '-qb', 'pr-b']);
  writeFileSync(join(root, 'src/b.mjs'), `${readFileSync(join(root, 'src/b.mjs'), 'utf8')}export const b2 = 2;\n`);
  assert.equal((await cli(['update', 'src/b.mjs', '--write'], root)).code, 0);
  git(root, ['add', '-f', '.']);
  git(root, ['commit', '-qm', 'update-b']);

  // Merge pr-a into pr-b: ZERO merge conflicts because sidecars are disjoint (.pdd/sync/src/a.mjs.json vs b.mjs.json)!
  git(root, ['merge', '--no-edit', 'pr-a']);
  const checkBoth = await cli(['update', 'src/a.mjs', 'src/b.mjs', '--check', '--json'], root);
  assert.equal(checkBoth.code, 0, checkBoth.out + checkBoth.err);
  assert.equal(JSON.parse(checkBoth.out).ok, true);
});

test('3447 scoped --from <base>..<head> and single <base>, pdd-bindings.json untouched, and empty diff', async t => {
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
    'src/b.mjs': '// Prompt: prompts/shared.prompt.md\nexport const b = 1;\n',
    'src/bound.mjs': 'export const bound = 1;\n',
    'src/bound-with-stories.mjs': 'export const bound2 = 1;\n',
    'docs/notes.md': 'initial\n',
  });

  assert.equal((await cli(['update', 'src/a.mjs', 'src/b.mjs', 'src/bound.mjs', 'src/bound-with-stories.mjs', '--write'], root)).code, 0);
  assert.equal(readFileSync(join(root, 'pdd-bindings.json'), 'utf8'), bindingsText);
  assert.equal(readFileSync(join(root, 'src/bound.mjs'), 'utf8'), 'export const bound = 1;\n');
  git(root, ['add', '-f', '.']);
  git(root, ['commit', '-qm', 'pinned']);
  const baseSha = git(root, ['rev-parse', 'HEAD']);

  writeFileSync(join(root, 'src/a.mjs'), `${readFileSync(join(root, 'src/a.mjs'), 'utf8')}export function extraA() { return 2; }\n`);
  writeFileSync(join(root, 'src/bound.mjs'), 'export const bound = 2;\nexport function boundFn() {}\n');
  writeFileSync(join(root, 'docs/notes.md'), 'updated\n');
  git(root, ['add', '.']);
  git(root, ['commit', '-qm', 'scoped-change']);

  const rangeRes = await cli(['update', '--from', `${baseSha}..HEAD`, '--json'], root);
  const singleRes = await cli(['update', '--from', baseSha, '--json'], root);
  assert.equal(rangeRes.code, 0, rangeRes.err);
  assert.equal(singleRes.code, 0, singleRes.err);
  const rangeData = JSON.parse(rangeRes.out);
  assert.deepEqual(rangeData.modules, JSON.parse(singleRes.out).modules);
  assert.deepEqual(rangeData.modules.map(m => m.path), ['src/a.mjs', 'src/bound.mjs']);
  assert.equal(rangeData.modules.some(m => m.path === 'src/b.mjs'), false);
  assert.deepEqual(rangeData.unowned, [{ path: 'docs/notes.md', reason: 'no owning prompt' }]);

  const writeScoped = await cli(['update', '--from', `${baseSha}..HEAD`, '--write', '--json'], root);
  assert.equal(writeScoped.code, 0, writeScoped.err);
  assert.equal(JSON.parse((await cli(['update', 'src/b.mjs', '--check', '--json'], root)).out).ok, true);
  assert.equal(JSON.parse((await cli(['owner', 'src/b.mjs', '--json'], root)).out).files[0].headers[0].state, 'current');

  const emptyRes = await cli(['update', '--from', 'HEAD..HEAD', '--check', '--json'], root);
  assert.equal(emptyRes.code, 0, emptyRes.err);
  assert.deepEqual(JSON.parse(emptyRes.out).prompts, []);
  assert.equal(JSON.parse(emptyRes.out).ok, true);
});

test('R1 #5 regressions: renames (unowned, cross-prompt, pre-pinned) and deleted header-owned pinned modules fail --check and prune cleanly on --write', async t => {
  const promptA = '# Prompt A\n\nOwn `src/a-only.mjs`.\n';
  const promptB = '# Prompt B\n\nOwn `src/b-only.mjs`.\n';
  const hA = promptHeaderHash(promptA);
  const hB = promptHeaderHash(promptB);
  const root = makeRepo(t, {
    'prompts/a.prompt.md': promptA,
    'prompts/b.prompt.md': promptB,
    'src/sub/rename-to-unowned.mjs': `// Generated from prompts/a.prompt.md (sha256: ${hA}).\nexport const r1 = 1;\n`,
    'src/rename-cross.mjs': `// Generated from prompts/a.prompt.md (sha256: ${hA}).\nexport const r2 = 2;\n`,
    'src/gone-header-only.mjs': `// Generated from prompts/a.prompt.md (sha256: ${hA}).\nexport const g = 3;\n`,
  });

  // Pin all 3 modules under .pdd/sync/
  assert.equal((await cli(['update', 'src/sub/rename-to-unowned.mjs', 'src/rename-cross.mjs', 'src/gone-header-only.mjs', '--write'], root)).code, 0);
  git(root, ['add', '-f', '.']);
  git(root, ['commit', '-qm', 'pinned']);
  const base = git(root, ['rev-parse', 'HEAD']);

  // Scenario 5A: rename pinned src/sub/rename-to-unowned.mjs -> unowned notes/moved.txt
  mkdirSync(join(root, 'notes'), { recursive: true });
  writeFileSync(join(root, 'notes/moved.txt'), 'export const r1 = 1;\n');
  unlinkSync(join(root, 'src/sub/rename-to-unowned.mjs'));
  // Scenario 5B: rename pinned src/rename-cross.mjs (prompt A) -> src/moved-b.mjs (prompt B) AND pre-pin src/moved-b.mjs!
  writeFileSync(join(root, 'src/moved-b.mjs'), `// Generated from prompts/b.prompt.md (sha256: ${hB}).\nexport const r2 = 2;\n`);
  unlinkSync(join(root, 'src/rename-cross.mjs'));
  assert.equal((await cli(['update', 'src/moved-b.mjs', '--write'], root)).code, 0);
  // Scenario 5C: delete header-only pinned src/gone-header-only.mjs
  unlinkSync(join(root, 'src/gone-header-only.mjs'));
  git(root, ['add', '-A']);
  git(root, ['commit', '-qm', 'renames-and-delete']);

  // --check on --from MUST exit 1 because stale sidecars for all 3 old paths remain!
  const checkRange = await cli(['update', '--from', `${base}..HEAD`, '--check', '--json'], root);
  assert.equal(checkRange.code, 1, checkRange.out);
  const driftedPaths = JSON.parse(checkRange.out).drifted.map(d => d.path).sort();
  assert.deepEqual(driftedPaths, ['src/gone-header-only.mjs', 'src/rename-cross.mjs', 'src/sub/rename-to-unowned.mjs']);

  // Scenario 5C (prompt-touch): touching prompts/a.prompt.md MUST also surface deleted header-owned pinned src/gone-header-only.mjs!
  const checkPromptTouch = await cli(['update', 'prompts/a.prompt.md', '--check', '--json'], root);
  assert.equal(checkPromptTouch.code, 1, checkPromptTouch.out);
  assert.ok(JSON.parse(checkPromptTouch.out).drifted.some(d => d.path === 'src/gone-header-only.mjs' && d.status === 'deleted'));

  // --write prunes all 3 stale sidecars and cleans empty .pdd/sync/src/sub directory!
  const writeRange = await cli(['update', '--from', `${base}..HEAD`, '--write', '--json'], root);
  assert.equal(writeRange.code, 0, writeRange.err);
  assert.equal(existsSync(join(root, '.pdd/sync/src/sub/rename-to-unowned.mjs.json')), false);
  assert.equal(existsSync(join(root, '.pdd/sync/src/sub')), false, 'empty parent dir under .pdd/sync should be pruned');
  assert.equal(existsSync(join(root, '.pdd/sync/src/rename-cross.mjs.json')), false);
  assert.equal(existsSync(join(root, '.pdd/sync/src/gone-header-only.mjs.json')), false);
  assert.equal(existsSync(join(root, '.pdd/sync/src/moved-b.mjs.json')), true);

  // Subsequent --check passes with exit 0!
  assert.equal((await cli(['update', '--from', `${base}..HEAD`, '--check'], root)).code, 0);
});

test('R1 #3, #4, #6, #7, #9 regressions: secret isolation, >8KiB binary, git config/globs/untracked explicit, atomic mode preserve, malformed bindings, quoted instructions, TTY zero-network', async t => {
  const prompt = '# App\n\nOwn `src/my mod.mjs`, `src/calc[1].mjs`, and `src/brand-new.mjs`.\n';
  const h = promptHeaderHash(prompt);
  const root = makeRepo(t, {
    'prompts/app.prompt.md': prompt,
    'src/my mod.mjs': `// Generated from prompts/app.prompt.md (sha256: ${h}).\nexport function modA() { return 1; }\n`,
    'src/calc[1].mjs': `// Generated from prompts/app.prompt.md (sha256: ${h}).\nexport function calc() { return 1; }\n`,
    '.env': 'API_SECRET=supersecret\n',
    'credentials.json': '{"secret":"nope"}\n',
    'secrets/private.pem': '-----BEGIN KEY-----\n',
  });

  // R1 #3: Secret files MUST NEVER be opened when touching prompts/app.prompt.md!
  const openedPaths = [];
  const spyOut = capture(), spyErr = capture();
  const spyCode = runUpdate(
    { cwd: root, files: ['prompts/app.prompt.md'], json: true },
    {
      stdout: spyOut,
      stderr: spyErr,
      read: (p, limit) => {
        openedPaths.push(p);
        assert.equal(p === '.env' || p === 'credentials.json' || p.startsWith('secrets/'), false, `must never open secret: ${p}`);
        const full = join(root, p);
        return existsSync(full) ? readFileSync(full).subarray(0, limit) : null;
      },
    },
  );
  assert.equal(spyCode, 0, spyErr.text);
  assert.equal(openedPaths.some(p => p === '.env' || p === 'credentials.json' || p.startsWith('secrets/')), false);

  // R1 #3b: Code file claiming a secret owning prompt rejects with exit 2 without opening it!
  writeFileSync(join(root, 'src/bad-owner.mjs'), '// Generated from secrets/hidden.prompt.md.\nexport const x = 1;\n');
  const secretOwnerRes = await cli(['update', 'src/bad-owner.mjs'], root);
  assert.equal(secretOwnerRes.code, 2);
  assert.match(secretOwnerRes.err, /Secret-looking path is not allowed: secrets\/hidden\.prompt\.md/);
  unlinkSync(join(root, 'src/bad-owner.mjs'));

  // R1 #6: diff.noprefix=true + diff.mnemonicPrefix=true + glob chars + spaces + explicit untracked file
  git(root, ['config', 'diff.noprefix', 'true']);
  git(root, ['config', 'diff.mnemonicPrefix', 'true']);
  writeFileSync(join(root, 'src/my mod.mjs'), `${readFileSync(join(root, 'src/my mod.mjs'), 'utf8')}export function modB() { return 2; }\n`);
  writeFileSync(join(root, 'src/calc[1].mjs'), `${readFileSync(join(root, 'src/calc[1].mjs'), 'utf8')}export function calc2() { return 2; }\n`);
  writeFileSync(join(root, 'src/brand-new.mjs'), `// Generated from prompts/app.prompt.md (sha256: ${h}).\nexport function brandNew() { return 3; }\n`);
  const diffRes = await cli(['update', 'src/my mod.mjs', 'src/calc[1].mjs', 'src/brand-new.mjs', '--json'], root);
  assert.equal(diffRes.code, 0, diffRes.err);
  const diffJson = JSON.parse(diffRes.out);
  const byMod = Object.fromEntries(diffJson.modules.map(m => [m.path, m]));
  assert.equal(byMod['src/my mod.mjs'].diff_stats.added, 1);
  assert.deepEqual(byMod['src/my mod.mjs'].changed_symbols, [{ kind: 'added', symbol: 'modB' }]);
  assert.equal(byMod['src/calc[1].mjs'].diff_stats.added, 1);
  assert.deepEqual(byMod['src/calc[1].mjs'].changed_symbols, [{ kind: 'added', symbol: 'calc2' }]);
  assert.equal(byMod['src/brand-new.mjs'].diff_stats.added, 2, 'explicit untracked file reports full additions');
  assert.deepEqual(byMod['src/brand-new.mjs'].changed_symbols, [{ kind: 'added', symbol: 'brandNew' }]);
  // R1 #9.2: Instructions shell-quote paths with spaces and brackets!
  const instrText = diffJson.prompts[0].instructions.join('\n');
  assert.ok(instrText.includes("'src/my mod.mjs'"), `expected quoted spaced path in: ${instrText}`);
  assert.ok(instrText.includes("'src/calc[1].mjs'"), `expected quoted glob path in: ${instrText}`);

  // R1 #7: Atomic write preserves existing file permissions (0o755) and leaves 0 .pdd-tmp-* files
  chmodSync(join(root, 'src/brand-new.mjs'), 0o755);
  writeFileSync(join(root, 'src/brand-new.mjs'), '// Generated from prompts/app.prompt.md.\nexport function brandNew() { return 3; }\n');
  assert.equal((await cli(['update', 'src/brand-new.mjs', '--write'], root)).code, 0);
  assert.equal(statSync(join(root, 'src/brand-new.mjs')).mode & 0o777, 0o755, 'executable mode must be preserved');
  assert.equal(readdirSync(join(root, 'src')).some(n => n.startsWith('.pdd-tmp-')), false);
  assert.equal(readdirSync(join(root, '.pdd/sync/src')).some(n => n.startsWith('.pdd-tmp-')), false);

  // R1 #4: Unowned > 8 KiB (12 KiB) binary file with NUL bytes is accurately classified as binary file (skipped)
  const baseBin = git(root, ['rev-parse', 'HEAD']);
  mkdirSync(join(root, 'assets'), { recursive: true });
  const bigBin = Buffer.alloc(12 * 1024, 0x41);
  bigBin[100] = 0x00;
  writeFileSync(join(root, 'assets/big.bin'), bigBin);
  git(root, ['add', 'assets/big.bin']);
  git(root, ['commit', '-qm', 'add-12k-bin']);
  const bigBinRes = await cli(['update', '--from', `${baseBin}..HEAD`, '--json'], root);
  assert.equal(bigBinRes.code, 0, bigBinRes.err);
  assert.deepEqual(JSON.parse(bigBinRes.out).unowned, [{ path: 'assets/big.bin', reason: 'binary file (skipped)' }]);

  // R1 #9.1: Malformed pdd-bindings.json fails closed with exit 2!
  writeFileSync(join(root, 'pdd-bindings.json'), '{not-valid-json');
  const badBindings = await cli(['update', 'src/brand-new.mjs'], root);
  assert.equal(badBindings.code, 2);
  assert.match(badBindings.err, /pdd-bindings\.json is malformed or unreadable/);
  unlinkSync(join(root, 'pdd-bindings.json'));

  // R1 #9.3: TTY pdd update NEVER invokes releaseNotice (zero network in TTY!)
  let releaseNoticeCalls = 0;
  const ttyOut = capture();
  const ttyErr = Object.assign(capture(), { isTTY: true });
  const ttyCode = await runPdd(['update', 'src/brand-new.mjs'], {
    stdout: ttyOut,
    stderr: ttyErr,
    cwd: root,
    env: { PATH: dirname(GIT_BIN), HOME: root, PDD_RUNTIME_URL: 'invalid' },
    releaseNotice: async () => { releaseNoticeCalls++; return 'Upgrade available'; },
  });
  assert.equal(ttyCode, 0, ttyErr.text);
  assert.equal(releaseNoticeCalls, 0, 'pdd update must never run releaseNotice even in TTY');
});

test('3447 security guards: reject traversal, leading-dash injection, symlinks (including .pdd/sync), malformed sidecar, secrets, binary files, non-ASCII, and non-git', async t => {
  const outside = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-update-outside-')));
  t.after(() => rmSync(outside, { recursive: true, force: true }));
  writeFileSync(join(outside, 'leak.mjs'), 'export const leak = 1;\n');

  const prompt = '# Guard\n\nOwn `src/ok.mjs` and `src/café.mjs`.\n';
  const h = promptHeaderHash(prompt);
  const root = makeRepo(t, {
    'prompts/guard.prompt.md': prompt,
    'src/ok.mjs': `// Generated from prompts/guard.prompt.md (sha256: ${h}).\nexport const ok = 1;\n`,
    'src/café.mjs': `// Generated from prompts/guard.prompt.md (sha256: ${h}).\nexport const café = 'espresso';\n`,
    'src/bin.mjs': Buffer.from([0x2f, 0x2f, 0x20, 0x00, 0x01, 0x02]),
    '.env': 'SECRET=1\n',
    'credentials.json': '{"token":"x"}\n',
  });
  symlinkSync(join(outside, 'leak.mjs'), join(root, 'src/link.mjs'));

  // Non-ASCII filename works end-to-end
  assert.equal((await cli(['update', 'src/café.mjs', '--write'], root)).code, 0);
  assert.equal(existsSync(join(root, syncRecordPathForModule('src/café.mjs'))), true);
  assert.equal((await cli(['update', 'src/café.mjs', '--check'], root)).code, 0);

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

  // Corrupt sidecar fails closed with exit 2
  writeFileSync(join(root, '.pdd/sync/src/café.mjs.json'), '{"bad":true}');
  const corruptSidecar = await cli(['update', 'src/café.mjs', '--check'], root);
  assert.equal(corruptSidecar.code, 2);
  assert.match(corruptSidecar.err, /Invalid sync record/);

  // Symlink at .pdd/sync refuses with exit 2 and writes nothing
  rmSync(join(root, '.pdd'), { recursive: true, force: true });
  mkdirSync(join(root, '.pdd'), { recursive: true });
  symlinkSync(outside, join(root, '.pdd/sync'));
  const symlinkSyncDir = await cli(['update', 'src/ok.mjs', '--write'], root);
  assert.equal(symlinkSyncDir.code, 2);
  assert.match(symlinkSyncDir.err, /Symlinks are not allowed/);
  assert.equal(existsSync(join(outside, 'src')), false, 'must never write through symlinked .pdd/sync');

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

  // Clean repo returns exit 0
  const cleanOut = capture(), cleanErr = capture();
  assert.equal(runUpdate({ cwd: badRepo, check: true }, { stdout: cleanOut, stderr: cleanErr }), 0);
  assert.match(cleanOut.text, /no touched files in scope/);
});

test('R2 #1 regressions: deleted/renamed .prompt.md fails closed on live modules, and co-deleted module+prompt prunes sidecar cleanly', async t => {
  const promptA = '# Alpha\n\nOwn `src/alpha.mjs`.\n';
  const promptB = '# Beta\n\nOwn `src/beta.mjs`.\n';
  const root = makeRepo(t, {
    'prompts/alpha.prompt.md': promptA,
    'prompts/beta.prompt.md': promptB,
    'src/alpha.mjs': `// Generated from prompts/alpha.prompt.md (sha256: ${promptHeaderHash(promptA)}).\nexport const a = 1;\n`,
    'src/beta.mjs': `// Generated from prompts/beta.prompt.md (sha256: ${promptHeaderHash(promptB)}).\nexport const b = 1;\n`,
  });
  assert.equal((await cli(['update', 'src/alpha.mjs', 'src/beta.mjs', '--write'], root)).code, 0);
  git(root, ['add', '-f', '.']);
  git(root, ['commit', '-qm', 'pinned']);

  // R2 #1a: Delete prompts/alpha.prompt.md while src/alpha.mjs STILL exists -> --check MUST exit 1 (not 0!)
  unlinkSync(join(root, 'prompts/alpha.prompt.md'));
  const delPromptOnly = await cli(['update', '--check'], root);
  assert.equal(delPromptOnly.code, 1, `expected exit 1 when owning prompt deleted with live module, got ${delPromptOnly.code}`);
  assert.match(delPromptOnly.err, /Owning prompt is missing or unreadable: prompts\/alpha\.prompt\.md/);

  // R2 #1c: Now delete src/alpha.mjs too (co-deleted module + prompt) -> --check exits 1 with text rendering "(prompt_sha256: deleted)", --write prunes sidecar and exits 0!
  unlinkSync(join(root, 'src/alpha.mjs'));
  const coDelText = await cli(['update', '--check'], root);
  assert.equal(coDelText.code, 1, coDelText.out + coDelText.err);
  assert.match(coDelText.out, /prompts\/alpha\.prompt\.md \[deleted\] \(prompt_sha256: deleted\)/);
  assert.equal(coDelText.err, '');
  const coDelWrite = await cli(['update', '--write', '--json'], root);
  assert.equal(coDelWrite.code, 0, coDelWrite.err);
  assert.equal(existsSync(join(root, '.pdd/sync/src/alpha.mjs.json')), false);
  assert.equal((await cli(['update', '--check'], root)).code, 0);

  // Commit cleanup, then test R2 #1b: rename prompts/beta.prompt.md -> prompts/beta-v2.prompt.md while src/beta.mjs still references prompts/beta.prompt.md
  git(root, ['add', '-A']);
  git(root, ['commit', '-qm', 'cleanup-alpha']);
  const base = git(root, ['rev-parse', 'HEAD']);
  git(root, ['mv', 'prompts/beta.prompt.md', 'prompts/beta-v2.prompt.md']);
  git(root, ['commit', '-qm', 'rename-beta-prompt']);
  const renamedPromptCheck = await cli(['update', '--from', `${base}..HEAD`, '--check'], root);
  assert.equal(renamedPromptCheck.code, 1, `expected exit 1 on renamed prompt with dangling live module, got ${renamedPromptCheck.code}`);
  assert.match(renamedPromptCheck.err, /Owning prompt is missing or unreadable: prompts\/beta\.prompt\.md/);
});

test('R2 #2, #3, #4 regressions: deleted pinned module matched by stem, in-place unowned sidecar orphan, .pdd/ pre-validation (0 writes), and memoized owner reads', async t => {
  // R2 #2: Deleted pinned module matched by ANOTHER prompt via stem must still fail --check and prune sidecar on --write
  const legacyPrompt = '# Legacy\n\nLegacy contract.\n';
  const stemPrompt = '# Widget\n\nDifferent prompt matching stem.\n';
  const stemRepo = makeRepo(t, {
    'prompts/legacy.prompt.md': legacyPrompt,
    'prompts/widget.prompt.md': stemPrompt,
    'src/widget.mjs': `// Generated from prompts/legacy.prompt.md (sha256: ${promptHeaderHash(legacyPrompt)}).\nexport const w = 1;\n`,
  });
  assert.equal((await cli(['update', 'src/widget.mjs', '--write'], stemRepo)).code, 0);
  git(stemRepo, ['add', '-f', '.']);
  git(stemRepo, ['commit', '-qm', 'pinned']);
  unlinkSync(join(stemRepo, 'src/widget.mjs'));
  const stemDelCheck = await cli(['update', '--check', '--json'], stemRepo);
  assert.equal(stemDelCheck.code, 1, stemDelCheck.out);
  assert.ok(JSON.parse(stemDelCheck.out).drifted.some(d => d.path === 'src/widget.mjs' && d.owner === 'prompts/legacy.prompt.md' && d.status === 'deleted'));
  const stemDelWrite = await cli(['update', '--write', '--json'], stemRepo);
  assert.equal(stemDelWrite.code, 0, stemDelWrite.err);
  assert.equal(existsSync(join(stemRepo, '.pdd/sync/src/widget.mjs.json')), false);
  assert.equal((await cli(['update', '--check'], stemRepo)).code, 0);

  // R2 #3: Previously pinned module loses ownership in place -> --check exits 1 (both file & prompt scope), --write prunes orphan sidecar
  const ownedPrompt = '# Owned contract\n\nContract text.\n';
  const orphanRepo = makeRepo(t, {
    'prompts/owned-contract.prompt.md': ownedPrompt,
    'src/sub/detached.mjs': `// Generated from prompts/owned-contract.prompt.md (sha256: ${promptHeaderHash(ownedPrompt)}).\nexport const m = 1;\n`,
  });
  assert.equal((await cli(['update', 'src/sub/detached.mjs', '--write'], orphanRepo)).code, 0);
  git(orphanRepo, ['add', '-f', '.']);
  git(orphanRepo, ['commit', '-qm', 'pinned']);
  // Strip ownership header in place (file stays on disk, now unowned!)
  writeFileSync(join(orphanRepo, 'src/sub/detached.mjs'), 'export const m = 2;\n');
  const orphanFileCheck = await cli(['update', 'src/sub/detached.mjs', '--check', '--json'], orphanRepo);
  assert.equal(orphanFileCheck.code, 1, orphanFileCheck.out);
  assert.equal(JSON.parse(orphanFileCheck.out).drifted[0].status, 'unowned');
  const orphanPromptCheck = await cli(['update', 'prompts/owned-contract.prompt.md', '--check', '--json'], orphanRepo);
  assert.equal(orphanPromptCheck.code, 1, orphanPromptCheck.out);
  assert.equal(JSON.parse(orphanPromptCheck.out).drifted[0].path, 'src/sub/detached.mjs');
  const orphanWrite = await cli(['update', 'src/sub/detached.mjs', '--write', '--json'], orphanRepo);
  assert.equal(orphanWrite.code, 0, orphanWrite.err);
  assert.equal(existsSync(join(orphanRepo, '.pdd/sync/src/sub/detached.mjs.json')), false);
  assert.equal(existsSync(join(orphanRepo, '.pdd/sync/src/sub')), false);
  assert.equal((await cli(['update', 'src/sub/detached.mjs', '--check'], orphanRepo)).code, 0);

  // R2 #4: Owned module under .pdd/ fails pre-validation with exit 2 and ZERO writes to valid sibling module
  const pddRepo = makeRepo(t, {
    'prompts/good.prompt.md': '# Good\n\nOwn `src/good.mjs`.\n',
    'src/good.mjs': '// Generated from prompts/good.prompt.md.\nexport const good = 1;\n',
    '.pdd/evil.mjs': '// Generated from prompts/good.prompt.md.\nexport const evil = 1;\n',
  });
  const pddGuardRes = await cli(['update', 'src/good.mjs', '.pdd/evil.mjs', '--write'], pddRepo);
  assert.equal(pddGuardRes.code, 2, pddGuardRes.out + pddGuardRes.err);
  assert.match(pddGuardRes.err, /Invalid module path for sync record: \.pdd\/evil\.mjs/);
  assert.equal(existsSync(join(pddRepo, '.pdd/sync/src/good.mjs.json')), false, 'must execute 0 writes on pre-validation failure');

  // R2 #4 bonus: safeReadForOwner memoizes prompt reads across double findOwners calls when a prompt is touched
  const readCounts = new Map();
  const memOut = capture(), memErr = capture();
  const memCode = runUpdate(
    { cwd: pddRepo, files: ['prompts/good.prompt.md'], json: true },
    {
      stdout: memOut,
      stderr: memErr,
      read: (p, limit) => {
        readCounts.set(p, (readCounts.get(p) ?? 0) + 1);
        const full = join(pddRepo, p);
        return existsSync(full) ? readFileSync(full).subarray(0, limit) : null;
      },
    },
  );
  assert.equal(memCode, 0, memErr.text);
  assert.equal(readCounts.get('prompts/good.prompt.md'), 1, `expected prompt to be read once by owner port, got ${readCounts.get('prompts/good.prompt.md')}`);
});
