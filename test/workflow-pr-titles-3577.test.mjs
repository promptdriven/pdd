import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { normalizePrType, prArea, readPrFields, readablePrTitle, resolvePrTitleType } from '../src/workflow-pr-body.mjs';
import { approveRun, startRun, stepDone } from '../src/workflow-runner.mjs';
import { checkInput, interfaceBlocks, interfaceSchemaProblems } from '../src/runtime-seam.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

test('3577-1: readPrFields parses both multi-line and single-line pipe-delimited summaries in O(N) while preserving legitimate pipes and Case rows', () => {
  const inline = readPrFields([
    'Title: Add invoice rounding | Cause: float division lost 1 cent | Fix: use integer minor units',
  ]);
  assert.equal(inline.title, 'Add invoice rounding');
  assert.equal(inline.cause, 'float division lost 1 cent');
  assert.equal(inline.fix, 'use integer minor units');

  const withExtraLabels = readPrFields([
    'Title: Add retry backoff | Summary: tuned jitter | Checks: 42 passed | Risk: low | Area: billing | File: `src/billing/retry.py` — bounded backoff',
  ]);
  assert.equal(withExtraLabels.title, 'Add retry backoff');
  assert.equal(withExtraLabels.area, 'billing');
  assert.deepEqual(withExtraLabels.notes, { 'src/billing/retry.py': 'bounded backoff' });

  // Plain title containing legitimate `|` characters without recognized labels must stay intact
  const plainPipes = readPrFields([
    'Title: Support foo | bar | baz syntax in queries',
  ]);
  assert.equal(plainPipes.title, 'Support foo | bar | baz syntax in queries');
  assert.equal(plainPipes.cause, undefined);
  assert.equal(plainPipes.fix, undefined);

  // Pipes inside backtick code spans or escaped with backslash must not split
  const codeAndEscaped = readPrFields([
    'Title: Handle `a | Cause: b` and x \\| Fix: literal | Cause: missed code spans | Fix: scan code spans first',
  ]);
  assert.equal(codeAndEscaped.title, 'Handle `a | Cause: b` and x \\| Fix: literal');
  assert.equal(codeAndEscaped.cause, 'missed code spans');
  assert.equal(codeAndEscaped.fix, 'scan code spans first');

  // Case rows starting with Case: must never split on `|`, even if a cell text contains a label
  const caseRows = readPrFields([
    'Case: `a || b` | Cause: old | Fix: new\nCase: 1205 | $12.50 | $12.05 | $12.05',
  ]);
  assert.deepEqual(caseRows.cases, [
    { input: '`a || b`', before: 'Cause: old', expected: 'Fix: new' },
    { input: '1205', before: '$12.50', after: '$12.05', expected: '$12.05' },
  ]);
  assert.equal(caseRows.cause, undefined);
  assert.equal(caseRows.fix, undefined);

  // Multi-line summaries continue to work identically
  const multiline = readPrFields([
    'Title: Clean multiline title\nProblem: broken output\nCause: stale cache\nFix: invalidate cache on write',
  ]);
  assert.equal(multiline.title, 'Clean multiline title');
  assert.equal(multiline.problem, 'broken output');
  assert.equal(multiline.cause, 'stale cache');
  assert.equal(multiline.fix, 'invalidate cache on write');

  // ReDoS / O(N) guard: huge pathological backticks and pipes finish quickly
  const hostile = `Title: ${'` '.repeat(25_000)}${'a | '.repeat(25_000)}| Fix: linear scan`;
  const started = performance.now();
  const parsed = readPrFields([hostile]);
  const elapsedMs = performance.now() - started;
  assert.equal(parsed.fix, 'linear scan');
  assert.ok(elapsedMs < 500, `Expected linear O(N) parse (<500ms), took ${elapsedMs.toFixed(1)}ms`);
});

test('3577-3: readablePrTitle supports validated Conventional Commit prType/type from workflow metadata while preserving defaults', () => {
  assert.equal(normalizePrType('FEAT'), 'feat');
  assert.equal(normalizePrType('  chore  '), 'chore');
  assert.equal(normalizePrType('feat): Fixes #9'), null);
  assert.equal(normalizePrType('unknown'), null);
  assert.equal(normalizePrType(null), null);

  // Workflow defaults
  assert.equal(resolvePrTitleType({ layout: 'spec', workflow: 'feature', prType: 'feat' }), 'spec');
  assert.equal(resolvePrTitleType({ layout: 'code', workflow: 'feature' }), 'feat');
  assert.equal(resolvePrTitleType({ layout: 'code', workflow: 'product' }), 'feat');
  assert.equal(resolvePrTitleType({ layout: 'code', workflow: 'codegen' }), 'feat');
  assert.equal(resolvePrTitleType({ layout: 'code', workflow: 'bug' }), 'fix');
  assert.equal(resolvePrTitleType({ layout: 'code', workflow: 'small-change' }), 'fix');
  assert.equal(resolvePrTitleType({ layout: 'code', workflow: 'custom' }), 'fix');

  // Explicit prType / type overrides and invalid fallback
  assert.equal(
    readablePrTitle({ layout: 'code', workflow: 'codegen', prType: 'feat', area: 'billing', statement: 'add ledger', number: 14, part: null }),
    'feat(billing): add ledger (#14)',
  );
  assert.equal(
    readablePrTitle({ layout: 'code', workflow: 'custom', type: 'chore', area: 'deps', statement: 'bump lockfile', number: 21, part: 2 }),
    'chore(deps): bump lockfile (#21 · part 2: chore)',
  );
  assert.equal(
    readablePrTitle({ layout: 'code', workflow: { name: 'custom', prType: 'refactor' }, area: 'parser', statement: 'simplify tokens', number: 8, part: null }),
    'refactor(parser): simplify tokens (#8)',
  );
  assert.equal(
    readablePrTitle({ layout: 'code', workflow: 'product', area: 'roadmap', statement: 'define product contracts', number: 4, part: null }),
    'feat(roadmap): define product contracts (#4)',
  );
  assert.equal(
    readablePrTitle({ layout: 'code', workflow: 'custom', prType: 'bad-type: Fixes #9', area: 'core', statement: 'guard invalid type', number: 5, part: null }),
    'fix(core): guard invalid type (#5)',
  );

  // Embedded Runtime interface schema admits optional prType/type
  const contract = JSON.parse(interfaceBlocks(readFileSync(new URL('../prompts/cli/workflow-pr-body.prompt.md', import.meta.url), 'utf8'))[0][1]);
  assert.deepEqual(interfaceSchemaProblems(contract), []);
  const entry = contract.entries.find(item => item.operation === 'readablePrTitle');
  assert.deepEqual(
    checkInput({ layout: 'code', workflow: 'codegen', prType: 'feat', area: 'billing', statement: 'add ledger', number: 14, part: null }, entry.input_schema, 0).refusals,
    [],
  );
  assert.deepEqual(
    checkInput({ layout: 'code', workflow: 'bug', area: 'money', statement: 'pad cents', number: 1, part: 2 }, entry.input_schema, 0).refusals,
    [],
  );
});

test('3577-4: prArea ignores boilerplate filenames (__init__.py, index.*, mod.rs, lib.rs, main.*, _*.py) and falls back to meaningful parent directory', () => {
  // Real issue #3577 reproductions
  assert.equal(prArea({ files: ['carta_clone/billing/__init__.py'] }), 'billing');
  assert.equal(prArea({ files: ['carta_clone/ledger/_commit.py'] }), 'ledger');
  assert.equal(prArea({ files: ['carta_clone/billing/__init__.py', 'carta_clone/billing/invoice.py'] }), 'invoice');

  // JS/TS/Rust/Go/Python boilerplate files skip generic container dirs (src, lib, pkg, app, packages, internal)
  assert.equal(prArea({ files: ['src/auth/index.ts'] }), 'auth');
  assert.equal(prArea({ files: ['src/auth/index.mjs'] }), 'auth');
  assert.equal(prArea({ files: ['src/auth/index.js'] }), 'auth');
  assert.equal(prArea({ files: ['src/auth/index.tsx'] }), 'auth');
  assert.equal(prArea({ files: ['packages/payments/src/index.ts'] }), 'payments');
  assert.equal(prArea({ files: ['crates/lexer/src/mod.rs'] }), 'lexer');
  assert.equal(prArea({ files: ['crates/lexer/src/lib.rs'] }), 'lexer');
  assert.equal(prArea({ files: ['app/worker/main.py'] }), 'worker');
  assert.equal(prArea({ files: ['pkg/cli/main.go'] }), 'cli');
  assert.equal(prArea({ files: ['internal/parser/_helpers.py'] }), 'parser');

  // Root-only or generic-container-only boilerplate files fall back cleanly to workflow or 'pdd'
  assert.equal(prArea({ files: ['__init__.py'], workflow: 'codegen' }), 'codegen');
  assert.equal(prArea({ files: ['src/index.ts'], workflow: 'feature' }), 'feature');
  assert.equal(prArea({ files: ['lib/main.py'] }), 'pdd');
  assert.equal(prArea({ files: ['src/index.js', 'packages/app/index.tsx'], workflow: 'bug' }), 'bug');

  // Explicit Area, prompt, and Story precedence stay intact
  assert.equal(prArea({ area: 'Treasury', files: ['carta_clone/billing/__init__.py'] }), 'treasury');
  assert.equal(prArea({ files: ['carta_clone/billing/__init__.py', 'prompts/cap_table_python.prompt.md'] }), 'cap_table');
  assert.equal(prArea({ files: ['carta_clone/billing/__init__.py', 'user_stories/issue-shares.md'] }), 'issue-shares');
});

test('3577-1/2/3: runner aligns --summary guidance, PATCHes {title, body} when title changes, omits title when unchanged, and reads workflow.json prType', async t => {
  const f = await fixture(t, { agent: 'codex' });

  // Define a custom project workflow with Conventional Commit `prType: "feat"`
  const customSkillDir = join(f.source, '.agents', 'skills', 'pdd-codegen');
  mkdirSync(customSkillDir, { recursive: true });
  writeFileSync(join(customSkillDir, 'SKILL.md'), '# Codegen workflow\n');
  writeFileSync(
    join(customSkillDir, 'workflow.json'),
    JSON.stringify({
      version: 2,
      prType: 'feat',
      areas: [
        { name: 'plan', steps: ['scope'], optional: [], gate: 'approve' },
        { name: 'build', steps: ['change', 'verify'], optional: [], gate: 'pr' },
      ],
    }),
  );

  const patches = [];
  const baseExec = f.ports.execFile;
  f.ports.execFile = async (file, args, options) => {
    if (file === 'gh' && args[0] === 'api' && args.includes('PATCH')) {
      const payload = JSON.parse(options.input);
      patches.push(payload);
      const endpoint = args.find(arg => /^repos\/example\/project\/pulls\/\d+$/.test(arg));
      const pr = f.prs.find(item => item.number === Number(endpoint?.split('/').at(-1)));
      if (pr && typeof payload.title === 'string') pr.title = payload.title;
    }
    return baseExec(file, args, options);
  };

  const started = await startRun({ name: 'codegen', issue: '17', agent: 'codex', cwd: f.source, packageRoot }, f.ports);
  assert.equal(started.exitCode, 0, started.message);
  assert.equal(f.record().prType, 'feat');

  // Verify area brief no longer emits contradictory `--summary "one line"`
  const runDir = f.record().runDir;
  const startPrompt = [
    ...f.herdr.panes.flatMap(item => item.commands ?? []),
    ...readdirSync(runDir)
      .filter(name => /\.(?:txt|md)$/i.test(name))
      .map(name => readFileSync(join(runDir, name), 'utf8')),
  ].join('\n');
  assert.doesNotMatch(startPrompt, /--summary "one line"/);
  assert.match(startPrompt, /Title:\/Area:/);

  const doneStep = (step, summary) => stepDone({ step, summary, cwd: f.record().root }, f.agentPorts());
  const scopeOut = await doneStep('scope', 'Title: Initial rough title | Problem: missing billing module');
  assert.equal(scopeOut.exitCode, 0, scopeOut.message);
  const approved = await approveRun({ ref: '17', cwd: f.source, said: 'Approved for test.' }, f.ports);
  assert.equal(approved.exitCode, 0, approved.message);

  // Add a boilerplate __init__.py under billing/ so prArea resolves to `billing` (not `init`)
  const billingDir = join(f.record().root, 'src', 'billing');
  mkdirSync(billingDir, { recursive: true });
  writeFileSync(join(billingDir, '__init__.py'), 'VERSION = 1\n');
  const changeOut = await doneStep('change', 'Title: Build billing ledger | Cause: no ledger yet | Fix: add ledger package');
  assert.equal(changeOut.exitCode, 0, changeOut.message);
  assert.doesNotMatch(changeOut.message, /--summary "one line"/);

  const verifyOut = await doneStep('verify', 'Title: Build billing ledger | Fix: add ledger package');
  assert.equal(verifyOut.exitCode, 0, verifyOut.message);
  assert.equal(f.prs.length, 1);
  assert.equal(f.prs[0].title, 'feat(billing): Build billing ledger (#17)');
  assert.equal(f.record().pr[0].title, 'feat(billing): Build billing ledger (#17)');

  // Repair push changing Title + Area must PATCH { title, body } on the final update
  writeFileSync(join(billingDir, '__init__.py'), 'VERSION = 2\n');
  f.git(f.record().root, 'add', '-A');
  f.git(f.record().root, 'commit', '-qm', 'Repair title and area');
  patches.length = 0;
  const repairOut = await doneStep('verify', 'Title: Ship clean billing ledger | Area: invoices | Fix: repair ledger export');
  assert.equal(repairOut.exitCode, 0, repairOut.message);
  assert.equal(patches.length, 2, 'pending and final REST PATCH calls');
  assert.deepEqual(Object.keys(patches[0]), ['body'], 'pending pre-push update leaves PR title untouched');
  assert.equal(patches[1].title, 'feat(invoices): Ship clean billing ledger (#17)');
  assert.equal(f.prs[0].title, 'feat(invoices): Ship clean billing ledger (#17)');
  assert.equal(f.record().pr[0].title, 'feat(invoices): Ship clean billing ledger (#17)');

  // Subsequent push with unchanged Title + Area must PATCH { body } only (no redundant title)
  writeFileSync(join(billingDir, '__init__.py'), 'VERSION = 3\n');
  f.git(f.record().root, 'add', '-A');
  f.git(f.record().root, 'commit', '-qm', 'Unchanged title commit');
  patches.length = 0;
  const sameTitleOut = await doneStep('verify', 'Title: Ship clean billing ledger | Area: invoices | Fix: add version 3');
  assert.equal(sameTitleOut.exitCode, 0, sameTitleOut.message);
  assert.equal(patches.length, 2);
  for (const payload of patches) {
    assert.deepEqual(Object.keys(payload), ['body']);
  }

  // Legacy PR record missing saved `pr[0].title` repairs title via PATCH on next push
  const rec = f.record();
  delete rec.pr[0].title;
  delete rec.prType;
  writeFileSync(join(rec.runDir, 'status.json'), JSON.stringify(rec));
  writeFileSync(join(billingDir, '__init__.py'), 'VERSION = 4\n');
  f.git(f.record().root, 'add', '-A');
  f.git(f.record().root, 'commit', '-qm', 'Legacy record title repair');
  patches.length = 0;
  const legacyRepair = await doneStep('verify', 'Title: Repaired legacy title | Area: invoices | Fix: version 4');
  assert.equal(legacyRepair.exitCode, 0, legacyRepair.message);
  assert.equal(patches.at(-1).title, 'feat(invoices): Repaired legacy title (#17)', 'still resolves prType from workflow.json when missing on run');
  assert.equal(f.record().pr[0].title, 'feat(invoices): Repaired legacy title (#17)');
});
