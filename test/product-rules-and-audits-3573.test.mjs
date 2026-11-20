import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, realpathSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import {
  auditProductPlan,
  parseProductDocuments,
  productNext,
  productStart,
  productStatus,
  readProduct,
  runProduct,
} from '../src/product.mjs';
import { lintRepoProject } from '../src/repo-hygiene-lint.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

const sink = () => ({ text: '', write(v) { this.text += v; } });

function makeProductRepo(t, files, { gitInit = false } = {}) {
  const scratch = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-3573-')));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));
  const cwd = join(scratch, 'repo');
  mkdirSync(cwd, { recursive: true });
  for (const [rel, content] of Object.entries(files)) {
    const abs = join(cwd, rel);
    mkdirSync(dirname(abs), { recursive: true });
    writeFileSync(abs, content);
  }
  if (gitInit) {
    execFileSync('git', ['init', '-q'], { cwd });
    execFileSync('git', ['add', '.'], { cwd });
    execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.invalid', 'commit', '-qm', 'init'], { cwd });
  }
  const state = { issues: [], runs: [], prs: [], starts: [], createdPayloads: [] };
  const ports = {
    lockProductState: async () => ({ handle: 'lock-3573' }),
    unlockProductState: async () => ({}),
    readProductState: async () => ({ json: state.productState ?? null }),
    writeProductState: async ({ json }) => { state.productState = json; return {}; },
    now: async () => ({ milliseconds: (state.clock = (state.clock ?? 0) + 60000) }),
    resolveRepository: async () => ({ repository: 'example/ledger-app', defaultBranch: 'main' }),
    planOnBase: async () => true,
    listRuns: async () => state.runs,
    storyEvidence: async run => run.rows ?? [],
    savedStoryEvidence: async () => ({ stories: [], warnings: [] }),
    issuePage: async () => ({ items: state.issues, total_count: state.issues.length, incomplete_results: false }),
    issueByNumber: async ({ number }) => state.issues.find(item => item.number === number) ?? { status: 404, message: 'Not Found' },
    timelinePage: async () => [],
    pullRequest: async ({ number }) => state.prs.find(pr => pr.number === number),
    createIssue: async payload => {
      state.createdPayloads.push(payload);
      const number = 100 + state.issues.length;
      state.issues.push({
        number,
        state: 'OPEN',
        body: payload.body,
        author_association: 'MEMBER',
        user: { login: 'member' },
        created_at: '2026-11-19T00:00:00Z',
      });
      return { url: `https://github.com/example/ledger-app/issues/${number}` };
    },
    startRun: async args => { state.starts.push(args); return { exitCode: 0, message: `Started feature #${args.issue}.` }; },
  };
  return { scratch, cwd, state, ports };
}

const SAMPLE_MAP = [
  '# Equity Ledger: map',
  'Sentence: "Manage cap table issuances, trust approvals, and CLI operations."',
  'Size: medium (5 CORE Stories, 3 parts)',
  '',
  '## Parts',
  '| Part | Folder | What it is |',
  '|---|---|---|',
  '| ledger | prompts/ledger | Cap table core domain (headless). |',
  '| trust | prompts/trust | Audit log and approval checks (headless). |',
  '| cli | prompts/cli | Command line dispatcher. |',
  '',
  '## Stories',
  '| Id | Part | Story | Tag |',
  '|---|---|---|---|',
  '| L01 | ledger | As an admin, I want to issue shares, so that holdings stay accurate. | CORE |',
  '| L02 | ledger | As an admin, I want to view the cap table, so that ownership is clear. | CORE |',
  '| T01 | trust | As an auditor, I want an immutable audit log, so that mutations are traceable. | CORE |',
  '| T02 | trust | As an approver, I want two-person approval for grants, so that risk is controlled. | CORE |',
  '| C01 | cli | As an operator, I want a version and status command, so that I can inspect the CLI. | CORE |',
  '',
  '## Journeys',
  '| Id | Journey | Stories |',
  '|---|---|---|',
  '| J1 | Admin issues shares via CLI and auditor inspects the recorded event. | L01, T01 |',
  '',
  '## Questions',
  '| Id | Question | Recommendation | Example | Answer |',
  '|---|---|---|---|---|',
  '| Q1 | Support CSV export? | Later. | LATER | No. |',
  '',
  '## Rules to check',
  '| Id | Owner | Rule | Verified By |',
  '|---|---|---|---|',
  '| R01 | ledger | Reject negative share counts with a finite error. | native unit tests |',
  '| R02 | cli | Support `--json` output on every command. | cli e2e tests |',
  '| R03 | trust | Record every break-glass emergency access event. | audit tests |',
  '| R04 | all | Never log raw credentials or private keys. | lint + tests |',
  '| R05 | * | Keep money and share quantities as exact integers. | native unit tests |',
  '| R06 | ledger, trust | Enforce legal hold before deletion or export. | compliance tests |',
  '| R07 | billing | Separate invoice numbering per fiscal year. | - |',
].join('\n') + '\n';

const SAMPLE_PLAN = [
  '# Equity Ledger: plan',
  '',
  '## Boundaries',
  '| From | To | What crosses | Contract |',
  '|---|---|---|---|',
  '| ledger | trust | `trust/audit.record`, `trust/approval.consume` | contracts/trust.md |',
  '| cli | ledger | `ledger/cap-table.issue` | contracts/ledger.md |',
  'Never crosses: `cli/direct.bypass` must never bypass `ledger`.',
  '',
  '## Prompts',
  '| Part | Prompt | Kind |',
  '|---|---|---|',
  '| ledger | prompts/ledger/cap-table.prompt.md | checkable |',
  '| trust | prompts/trust/audit.prompt.md | checkable |',
  '| trust | prompts/trust/approval.prompt.md | checkable |',
  '| cli | prompts/cli/command.prompt.md | native-only |',
  '',
  '## Runs',
  '| Run | Part | Slice | Stories | Needs | Shared surfaces |',
  '|---|---|---|---|---|---|',
  '| trust-1 | trust | 1 | T01, T02 | plan PR | - |',
  '| ledger-1 | ledger | 1 | L01, L02 | trust-1 | cli |',
  '| cli-1 | cli | 1 | C01 | plan PR | - |',
  '| journeys | all | 1 | J1 | trust-1, ledger-1, cli-1 | - |',
].join('\n') + '\n';

test('3573: parses structured ## Rules to check table, legacy bullet/prose maps, and preserves backwards compatibility', () => {
  // 1. Structured table
  const parsed = parseProductDocuments({ mapText: SAMPLE_MAP, planText: SAMPLE_PLAN });
  assert.deepEqual(parsed.product.rulesToCheck, [
    { id: 'R01', owner: 'ledger', rule: 'Reject negative share counts with a finite error.', verifiedBy: 'native unit tests' },
    { id: 'R02', owner: 'cli', rule: 'Support `--json` output on every command.', verifiedBy: 'cli e2e tests' },
    { id: 'R03', owner: 'trust', rule: 'Record every break-glass emergency access event.', verifiedBy: 'audit tests' },
    { id: 'R04', owner: 'all', rule: 'Never log raw credentials or private keys.', verifiedBy: 'lint + tests' },
    { id: 'R05', owner: '*', rule: 'Keep money and share quantities as exact integers.', verifiedBy: 'native unit tests' },
    { id: 'R06', owner: 'ledger, trust', rule: 'Enforce legal hold before deletion or export.', verifiedBy: 'compliance tests' },
    { id: 'R07', owner: 'billing', rule: 'Separate invoice numbering per fiscal year.', verifiedBy: '' },
  ]);

  // 2. Legacy bullet lines under ## Rules to check
  const bulletMap = SAMPLE_MAP.slice(0, SAMPLE_MAP.indexOf('## Rules to check')) + [
    '## Rules to check',
    '- Reject blank input with a finite reason.',
    '- Keep timeouts below 5 seconds.',
    '',
  ].join('\n');
  const bulletParsed = parseProductDocuments({ mapText: bulletMap, planText: SAMPLE_PLAN });
  assert.deepEqual(bulletParsed.product.rulesToCheck, [
    { id: '', owner: 'all', rule: 'Reject blank input with a finite reason.', verifiedBy: '' },
    { id: '', owner: 'all', rule: 'Keep timeouts below 5 seconds.', verifiedBy: '' },
  ]);

  // 3. Legacy map without ## Rules to check omits rulesToCheck to keep existing shapes untouched
  const noRulesMap = SAMPLE_MAP.slice(0, SAMPLE_MAP.indexOf('## Rules to check'));
  const noRulesParsed = parseProductDocuments({ mapText: noRulesMap, planText: SAMPLE_PLAN });
  assert.equal(Object.hasOwn(noRulesParsed.product, 'rulesToCheck'), false);

  // 4. Case-insensitive column names and missing/duplicate validation
  const ciMap = noRulesMap + [
    '## Rules to Check',
    '| ID | OWNER | rule | Verified by |',
    '|---|---|---|---|',
    '| R1 | ledger | Escape a \\| pipe cleanly. | unit test |',
  ].join('\n');
  assert.deepEqual(parseProductDocuments({ mapText: ciMap, planText: SAMPLE_PLAN }).product.rulesToCheck, [
    { id: 'R1', owner: 'ledger', rule: 'Escape a | pipe cleanly.', verifiedBy: 'unit test' },
  ]);

  for (const badSection of [
    '## Rules to check\n| Id | Owner | Rule |\n|---|---|---|\n| R1 | ledger | Missing col |\n',
    '## Rules to check\n| Id | Owner | Rule | Verified By |\n|---|---|---|---|\n| R1 | ledger | First | t |\n| R1 | cli | Dup | t |\n',
    '## Rules to check\n| Id | Owner | Rule | Verified By |\n|---|---|---|---|\n| R1 | - | Missing owner | t |\n',
    '## Rules to check\n| Id | Owner | Rule | Verified By |\n|---|---|---|---|\n| R1 | ledger |  | t |\n',
  ]) {
    assert.throws(
      () => parseProductDocuments({ mapText: noRulesMap + badSection, planText: SAMPLE_PLAN }),
      err => err.code === 'invalid-product' && err.message.includes('product/map.md'),
      badSection,
    );
  }
});

test('3573: propagates owned primary, secondary shared-surface, and wildcard rules into pdd product start issue body while excluding unowned rules', async t => {
  const f = makeProductRepo(t, {
    'product/map.md': SAMPLE_MAP,
    'product/plan.md': SAMPLE_PLAN,
  });

  // ledger-1 has primary part `ledger` + secondary shared surface `cli`.
  const startedLedger = await productStart({ cwd: f.cwd, run: 'ledger-1', noRun: true }, f.ports);
  assert.equal(startedLedger.exitCode, 0, startedLedger.message);
  const ledgerBody = f.state.createdPayloads[0].body;
  assert.match(ledgerBody, /## Rules to check/);
  // Primary part (ledger), shared surface (cli), wildcards (all, *), and multi-owner (ledger, trust) are included:
  assert.match(ledgerBody, /- R01 \(ledger\): Reject negative share counts with a finite error\. \(Verified by: native unit tests\)/);
  assert.match(ledgerBody, /- R02 \(cli\): Support `--json` output on every command\. \(Verified by: cli e2e tests\)/);
  assert.match(ledgerBody, /- R04 \(all\): Never log raw credentials or private keys\. \(Verified by: lint \+ tests\)/);
  assert.match(ledgerBody, /- R05 \(\*\): Keep money and share quantities as exact integers\. \(Verified by: native unit tests\)/);
  assert.match(ledgerBody, /- R06 \(ledger, trust\): Enforce legal hold before deletion or export\. \(Verified by: compliance tests\)/);
  // Rules owned only by other parts (`trust` alone, `billing`) are excluded:
  assert.doesNotMatch(ledgerBody, /\bR03\b/);
  assert.doesNotMatch(ledgerBody, /\bR07\b/);
  // Secondary shared surface details (folder, prompt from ## Prompts, contracts touching ledger or cli):
  assert.match(ledgerBody, /Shared surfaces to update: cli \(prompts\/cli\) \[prompts\/cli\/command\.prompt\.md\]\./);
  assert.match(ledgerBody, /contracts\/trust\.md/);
  assert.match(ledgerBody, /contracts\/ledger\.md/);
  assert.match(ledgerBody, /contracts\/world\.md/);

  // trust-1 has primary part `trust` and NO shared surfaces -> gets trust + wildcards + multi-owner, excludes ledger-only and cli-only!
  const startedTrust = await productStart({ cwd: f.cwd, run: 'trust-1', noRun: true }, f.ports);
  assert.equal(startedTrust.exitCode, 0, startedTrust.message);
  const trustBody = f.state.createdPayloads[1].body;
  assert.match(trustBody, /- R03 \(trust\):/);
  assert.match(trustBody, /- R04 \(all\):/);
  assert.match(trustBody, /- R05 \(\*\):/);
  assert.match(trustBody, /- R06 \(ledger, trust\):/);
  assert.doesNotMatch(trustBody, /\bR01\b/);
  assert.doesNotMatch(trustBody, /\bR02\b/);
  assert.doesNotMatch(trustBody, /\bR07\b/);
  assert.doesNotMatch(trustBody, /Shared surfaces to update:/);

  // Legacy bullet rules also propagate cleanly without fabricated IDs.
  const bulletMap = SAMPLE_MAP.slice(0, SAMPLE_MAP.indexOf('## Rules to check')) + '## Rules to check\n- Always validate input bounds.\n';
  const fLegacy = makeProductRepo(t, { 'product/map.md': bulletMap, 'product/plan.md': SAMPLE_PLAN });
  const resLegacy = await productStart({ cwd: fLegacy.cwd, run: 'cli-1', noRun: true }, fLegacy.ports);
  assert.equal(resLegacy.exitCode, 0, resLegacy.message);
  assert.match(fLegacy.state.createdPayloads[0].body, /## Rules to check\n- Always validate input bounds\./);
});

test('3573: supports all shared-surface declaration syntaxes and surfaces them in readProduct, status, and next', async t => {
  // 1. Comma-separated secondary part in Part column + Updates alias + per-run line
  const planAlt = [
    '# Equity Ledger: plan',
    '',
    '## Boundaries',
    '| From | To | What crosses | Contract |',
    '|---|---|---|---|',
    '| cli | ledger | order_req | contracts/ledger.md |',
    '',
    '## Runs',
    '| Run | Part | Slice | Stories | Needs | Updates |',
    '|---|---|---|---|---|---|',
    '| trust-1 | trust | 1 | T01, T02 | plan PR | - |',
    '| ledger-1 | ledger, cli | 1 | L01, L02, C01 | trust-1 | cli |',
    '| cli-1 | cli | 1 | C01 | plan PR | - |',
    'Shared surfaces (trust-1): cli',
  ].join('\n') + '\n';

  const parsed = parseProductDocuments({ mapText: SAMPLE_MAP, planText: planAlt });
  assert.deepEqual(parsed.product.runs.find(r => r.run === 'ledger-1').sharedSurfaces, ['cli']);
  assert.deepEqual(parsed.product.runs.find(r => r.run === 'trust-1').sharedSurfaces, ['cli']);
  assert.equal(Object.hasOwn(parsed.product.runs.find(r => r.run === 'cli-1'), 'sharedSurfaces'), false);

  // 2. Unknown shared surface or unknown run in per-run line rejects cleanly with invalid-product.
  assert.throws(
    () => parseProductDocuments({ mapText: SAMPLE_MAP, planText: planAlt.replace('Shared surfaces (trust-1): cli', 'Shared surfaces (trust-1): ghost') }),
    err => err.code === 'invalid-product' && err.message.includes('ghost'),
  );
  assert.throws(
    () => parseProductDocuments({ mapText: SAMPLE_MAP, planText: planAlt.replace('Shared surfaces (trust-1): cli', 'Shared surfaces (nope-1): cli') }),
    err => err.code === 'invalid-product' && err.message.includes('nope-1'),
  );

  // 3. Status and next propagate sharedSurfaces in structured JSON and human CLI output.
  const f = makeProductRepo(t, { 'product/map.md': SAMPLE_MAP, 'product/plan.md': planAlt });
  const status = await productStatus({ cwd: f.cwd }, f.ports);
  assert.deepEqual(status.runs.find(r => r.run === 'ledger-1').sharedSurfaces, ['cli']);
  assert.equal(Object.hasOwn(status.runs.find(r => r.run === 'cli-1'), 'sharedSurfaces'), false);

  const next = await productNext({ cwd: f.cwd }, f.ports);
  assert.deepEqual(next.waiting.find(w => w.run === 'ledger-1'), { run: 'ledger-1', needs: ['trust-1'], sharedSurfaces: ['cli'] });

  const cliStatus = await runProduct({ cwd: f.cwd, command: 'status' }, f.ports);
  assert.equal(cliStatus.exitCode, 0, cliStatus.message);
  assert.match(cliStatus.message, /ledger-1: planned · shared surfaces: cli/);
  assert.match(cliStatus.message, /trust-1: planned · shared surfaces: cli/);

  const cliNext = await runProduct({ cwd: f.cwd, command: 'next' }, f.ports);
  assert.equal(cliNext.exitCode, 0, cliNext.message);
  assert.match(cliNext.message, /trust-1: shared surfaces: cli\./);
  assert.match(cliNext.message, /ledger-1: waits for trust-1 \(shared surfaces: cli\)\./);
});

test('3573: ## Prompts inventory drift audit catches missing declared prompts and extra on-disk prompts without false positives', async t => {
  // 1. Clean match -> 0 drift warnings in both lintRepoProject and productStatus
  const cleanFiles = {
    'product/map.md': SAMPLE_MAP,
    'product/plan.md': SAMPLE_PLAN,
    'prompts/ledger/cap-table.prompt.md': '# Cap table\n\nCalls `trust/audit.record` and `trust/approval.consume`.\n\n## Dependencies\nNone.\n',
    'prompts/trust/audit.prompt.md': '# Audit\n\nDefines `audit.record`.\n\n## Dependencies\nNone.\n',
    'prompts/trust/approval.prompt.md': '# Approval\n\nDefines `approval.consume`.\n\n## Dependencies\nNone.\n',
    'prompts/cli/command.prompt.md': '# CLI command\n\nCalls `ledger/cap-table.issue`.\n\n## Dependencies\nNone.\n',
    // Prompt outside tracked part folders must NOT cause false positives:
    'examples/demo/prompts/unrelated.prompt.md': '# Demo\n\nExample.\n\n## Dependencies\nNone.\n',
  };
  const cleanRepo = makeProductRepo(t, cleanFiles, { gitInit: true });
  const cleanLint = lintRepoProject({ root: cleanRepo.cwd });
  assert.deepEqual(cleanLint.findings.filter(f => f.code === 'product-prompt-inventory-drift'), []);
  assert.deepEqual(cleanLint.findings.filter(f => f.code === 'product-boundary-unwired'), []);
  const cleanStatus = await productStatus({ cwd: cleanRepo.cwd }, cleanRepo.ports);
  assert.equal(cleanStatus.warnings, undefined);

  // 2. Drift: missing declared prompt (prompts/trust/approval.prompt.md) + extra undeclared prompt on disk (prompts/ledger/extra.prompt.md)
  const driftFiles = { ...cleanFiles };
  delete driftFiles['prompts/trust/approval.prompt.md'];
  driftFiles['prompts/ledger/extra.prompt.md'] = '# Extra\n\nUnplanned prompt.\n\n## Dependencies\nNone.\n';
  const driftRepo = makeProductRepo(t, driftFiles, { gitInit: true });

  const driftLint = lintRepoProject({ root: driftRepo.cwd });
  assert.equal(driftLint.ok, true, 'advisory default severity keeps ok=true');
  const driftFindings = driftLint.findings.filter(f => f.code === 'product-prompt-inventory-drift');
  assert.equal(driftFindings.length, 2);
  assert.ok(driftFindings.some(f => f.path === 'product/plan.md' && f.message.includes('prompts/trust/approval.prompt.md') && f.message.includes('missing on disk')));
  assert.ok(driftFindings.some(f => f.path === 'prompts/ledger/extra.prompt.md' && f.message.includes('prompts/ledger') && f.message.includes('not listed')));

  // Surfaced in productStatus too!
  const driftStatus = await productStatus({ cwd: driftRepo.cwd }, driftRepo.ports);
  assert.ok(driftStatus.warnings?.some(w => w.includes('Prompt inventory drift') && w.includes('prompts/trust/approval.prompt.md')));
  assert.ok(driftStatus.warnings?.some(w => w.includes('Prompt inventory drift') && w.includes('prompts/ledger/extra.prompt.md')));

  // 3. Repos without ## Prompts or without product/plan.md emit 0 drift findings.
  const noPromptsPlan = SAMPLE_PLAN.replace(/## Prompts[\s\S]*?(?=## Runs)/, '');
  const noPromptsRepo = makeProductRepo(t, { ...driftFiles, 'product/plan.md': noPromptsPlan }, { gitInit: true });
  assert.deepEqual(lintRepoProject({ root: noPromptsRepo.cwd }).findings.filter(f => f.code === 'product-prompt-inventory-drift'), []);

  // 4. Subheading + bare basename prompt list syntax under ## Prompts
  const bulletPlan = SAMPLE_PLAN.replace(/## Prompts[\s\S]*?(?=## Runs)/, [
    '## Prompts',
    '### ledger (`prompts/ledger`)',
    '- `cap-table.prompt.md`',
    '### trust (`prompts/trust`)',
    '- [audit](prompts/trust/audit.prompt.md)',
    '- `approval.prompt.md`',
    '### cli (`prompts/cli`)',
    '- `prompts/cli/command.prompt.md`',
    '',
  ].join('\n'));
  const bulletAudit = auditProductPlan({
    mapText: SAMPLE_MAP,
    planText: bulletPlan,
    promptFiles: [
      { path: 'prompts/ledger/cap-table.prompt.md', content: 'Calls trust/audit.record and approval.consume.' },
      { path: 'prompts/trust/audit.prompt.md', content: 'Defines audit.record.' },
      { path: 'prompts/trust/approval.prompt.md', content: 'Defines approval.consume.' },
      { path: 'prompts/cli/command.prompt.md', content: 'Calls ledger/cap-table.issue.' },
    ],
  });
  assert.deepEqual(bulletAudit.findings, []);
});

test('3573: ## Boundaries wiring audit flags unwired ops, ignores self-definition and false matches, and respects pdd.json severity overrides', async t => {
  const unwiredRepo = makeProductRepo(t, {
    'product/map.md': SAMPLE_MAP,
    'product/plan.md': SAMPLE_PLAN,
    // Defining prompts mention their OWN ops, which must NOT count as consumer wiring!
    'prompts/trust/audit.prompt.md': '# Audit\n\nImplements `trust/audit.record` and `audit.record`.\n\n## Dependencies\nNone.\n',
    'prompts/trust/approval.prompt.md': '# Approval\n\nImplements `trust/approval.consume`.\n\n## Dependencies\nNone.\n',
    // Consumer wires trust/audit.record, has ONLY a comment/wrong-part/prefix mention of approval.consume!
    'prompts/ledger/cap-table.prompt.md': [
      '# Cap table',
      '',
      'Calls `trust/audit.record` after issuing shares.',
      '<!-- trust/approval.consume commented out -->',
      'Mentions `other/approval.consume` and `approval.consume_v2` and `my_approval.consume`.',
      '',
      '## Dependencies',
      '- [Approval](../trust/approval.prompt.md)',
    ].join('\n') + '\n',
    // CLI calls ledger/cap-table.issue via brace notation!
    'prompts/cli/command.prompt.md': '# CLI command\n\nCalls `cap-table.{issue, list}`.\n\n## Dependencies\nNone.\n',
  }, { gitInit: true });

  // Default advisory warn
  const resWarn = lintRepoProject({ root: unwiredRepo.cwd });
  assert.equal(resWarn.ok, true);
  const unwired = resWarn.findings.filter(f => f.code === 'product-boundary-unwired');
  assert.equal(unwired.length, 1, JSON.stringify(unwired));
  assert.equal(unwired[0].path, 'product/plan.md');
  assert.equal(unwired[0].severity, 'warn');
  assert.match(unwired[0].message, /trust\/approval\.consume/);
  // Never crosses op must NOT be flagged!
  assert.ok(!unwired.some(f => f.message.includes('cli/direct.bypass')));
  // Wired ops must NOT be flagged!
  assert.ok(!unwired.some(f => f.message.includes('trust/audit.record')));
  assert.ok(!unwired.some(f => f.message.includes('ledger/cap-table.issue')));

  // Surfaced in productStatus too!
  const status = await productStatus({ cwd: unwiredRepo.cwd }, unwiredRepo.ports);
  assert.ok(status.warnings?.some(w => w.includes('Unwired boundary operation') && w.includes('trust/approval.consume')));
  assert.ok(!status.warnings?.some(w => w.includes('trust/audit.record')));

  // pdd.json severity overrides: "off", "warn", "error"
  writeFileSync(join(unwiredRepo.cwd, 'pdd.json'), JSON.stringify({ lint: { rules: { 'product-boundary-unwired': 'off' } } }) + '\n');
  const resOff = lintRepoProject({ root: unwiredRepo.cwd });
  assert.equal(resOff.ok, true);
  assert.deepEqual(resOff.findings.filter(f => f.code === 'product-boundary-unwired'), []);

  writeFileSync(join(unwiredRepo.cwd, 'pdd.json'), JSON.stringify({ lint: { rules: { 'product-boundary-unwired': 'warn' } } }) + '\n');
  const resExplicitWarn = lintRepoProject({ root: unwiredRepo.cwd });
  assert.equal(resExplicitWarn.ok, true);
  assert.equal(resExplicitWarn.warnings.filter(w => w.includes('[product-boundary-unwired]')).length, 1);
  assert.deepEqual(resExplicitWarn.errors, []);

  writeFileSync(join(unwiredRepo.cwd, 'pdd.json'), JSON.stringify({ lint: { rules: { 'product-boundary-unwired': 'error' } } }) + '\n');
  const resErr = lintRepoProject({ root: unwiredRepo.cwd });
  assert.equal(resErr.ok, false);
  assert.equal(resErr.errors.filter(e => e.includes('[product-boundary-unwired]') && e.startsWith('Error:')).length, 1);

  // CLI pdd lint --local --json surfaces error override end-to-end
  const home = join(unwiredRepo.scratch, 'home');
  const stateDir = join(unwiredRepo.scratch, 'state');
  mkdirSync(home, { recursive: true });
  mkdirSync(stateDir, { recursive: true });
  const env = { HOME: home, PDD_STATE_DIR: stateDir, PDD_RUNTIME_URL: 'invalid' };
  const outErr = sink(), errErr = sink();
  const codeErr = await runPdd(['lint', '--local', '--json'], { cwd: unwiredRepo.cwd, env, stdout: outErr, stderr: errErr });
  assert.notEqual(codeErr, 0, 'promoted error rule exits non-zero');
  const parsedErr = JSON.parse(outErr.text);
  assert.ok(parsedErr.problems.some(p => p.includes('[product-boundary-unwired]')));

  // Back to default warn -> exits 0 with advisory warning
  rmSync(join(unwiredRepo.cwd, 'pdd.json'));
  const outWarn = sink(), errWarn = sink();
  const codeWarn = await runPdd(['lint', '--local', '--json'], { cwd: unwiredRepo.cwd, env, stdout: outWarn, stderr: errWarn });
  assert.equal(codeWarn, 0, errWarn.text);
  const parsedWarn = JSON.parse(outWarn.text);
  assert.deepEqual(parsedWarn.problems, []);
  assert.ok(parsedWarn.warnings.some(w => w.includes('[product-boundary-unwired]')));
});

test('3573: symlink safety refuses symlinked product/map.md and product/plan.md and ignores symlinked prompts', async t => {
  const f = makeProductRepo(t, {
    'prompts/trust/audit.prompt.md': '# Audit\n\nDefines `audit.record`.\n\n## Dependencies\nNone.\n',
    'prompts/trust/approval.prompt.md': '# Approval\n\nDefines `approval.consume`.\n\n## Dependencies\nNone.\n',
    'prompts/ledger/cap-table.prompt.md': '# Cap table\n\nCalls `trust/audit.record`.\n\n## Dependencies\nNone.\n',
    'prompts/cli/command.prompt.md': '# CLI\n\nCalls `ledger/cap-table.issue`.\n\n## Dependencies\nNone.\n',
  });
  const outside = join(f.scratch, 'outside');
  mkdirSync(outside, { recursive: true });
  writeFileSync(join(outside, 'secret-map.md'), SAMPLE_MAP);
  writeFileSync(join(outside, 'secret-plan.md'), SAMPLE_PLAN);
  writeFileSync(join(outside, 'evil-consumer.prompt.md'), '# Evil\n\nCalls `trust/approval.consume`.\n');

  // 1. Symlinked product/map.md -> refused with invalid-product by readProduct / productStatus / productStart
  mkdirSync(join(f.cwd, 'product'), { recursive: true });
  symlinkSync(join(outside, 'secret-map.md'), join(f.cwd, 'product/map.md'));
  writeFileSync(join(f.cwd, 'product/plan.md'), SAMPLE_PLAN);
  await assert.rejects(readProduct({ cwd: f.cwd }), err => err.code === 'invalid-product' && /symlink/i.test(err.message));
  const startMapSym = await productStart({ cwd: f.cwd, run: 'ledger-1', noRun: true }, f.ports);
  assert.equal(startMapSym.exitCode, 1);

  // 2. Real product/map.md + symlinked product/plan.md -> refused (NEVER silently treated as missing plan!)
  rmSync(join(f.cwd, 'product/map.md'));
  writeFileSync(join(f.cwd, 'product/map.md'), SAMPLE_MAP);
  rmSync(join(f.cwd, 'product/plan.md'));
  symlinkSync(join(outside, 'secret-plan.md'), join(f.cwd, 'product/plan.md'));
  await assert.rejects(readProduct({ cwd: f.cwd }), err => err.code === 'invalid-product' && /symlink/i.test(err.message));

  // lintRepoProject safely skips symlinked product/plan.md without throwing or leaking outside content
  execFileSync('git', ['init', '-q'], { cwd: f.cwd });
  execFileSync('git', ['add', '.'], { cwd: f.cwd });
  const lintWithSymlinkPlan = lintRepoProject({ root: f.cwd });
  assert.equal(lintWithSymlinkPlan.ok, true);
  assert.deepEqual(lintWithSymlinkPlan.findings.filter(item => item.code === 'product-boundary-unwired' || item.code === 'product-prompt-inventory-drift'), []);

  // 3. Real map.md and plan.md + symlinked consumer prompt -> symlinked prompt is ignored, so trust/approval.consume remains unwired!
  rmSync(join(f.cwd, 'product/plan.md'));
  writeFileSync(join(f.cwd, 'product/plan.md'), SAMPLE_PLAN);
  symlinkSync(join(outside, 'evil-consumer.prompt.md'), join(f.cwd, 'prompts/ledger/symlink-consumer.prompt.md'));
  execFileSync('git', ['add', '.'], { cwd: f.cwd });

  const lintWithSymlinkPrompt = lintRepoProject({ root: f.cwd });
  assert.ok(lintWithSymlinkPrompt.findings.some(item => item.code === 'product-boundary-unwired' && item.message.includes('trust/approval.consume')));
  assert.ok(!lintWithSymlinkPrompt.findings.some(item => item.path.includes('symlink-consumer.prompt.md')));

  const statusWithSymlinkPrompt = await productStatus({ cwd: f.cwd }, f.ports);
  assert.ok(statusWithSymlinkPrompt.warnings?.some(w => w.includes('trust/approval.consume')));
  assert.ok(!statusWithSymlinkPrompt.warnings?.some(w => w.includes('symlink-consumer.prompt.md')));

  // 4. Symlinked product/ directory itself -> refused by readProduct and safely skipped by lintRepoProject
  const dirRepo = makeProductRepo(t, { 'prompts/ledger/cap-table.prompt.md': '# Cap\n\n## Dependencies\nNone.\n' });
  const outsideProductDir = join(dirRepo.scratch, 'outside-product');
  mkdirSync(outsideProductDir, { recursive: true });
  writeFileSync(join(outsideProductDir, 'map.md'), SAMPLE_MAP);
  writeFileSync(join(outsideProductDir, 'plan.md'), SAMPLE_PLAN);
  symlinkSync(outsideProductDir, join(dirRepo.cwd, 'product'));
  await assert.rejects(readProduct({ cwd: dirRepo.cwd }), err => err.code === 'invalid-product' && /symlink/i.test(err.message));
  execFileSync('git', ['init', '-q'], { cwd: dirRepo.cwd });
  execFileSync('git', ['add', '.'], { cwd: dirRepo.cwd });
  assert.equal(lintRepoProject({ root: dirRepo.cwd }).ok, true);
});

test('3573: bare boundary ops, Runtime interface calls/resources wiring, shared owner wildcard, and subheading/section shared surfaces work cleanly', async t => {
  // 1. Bare boundary ops (audit.record, approval.consume) + Runtime interface calls/resources consumer wiring
  const barePlan = [
    '# Equity Ledger: plan',
    '',
    '## Boundaries',
    '| From | To | What crosses | Contract |',
    '|---|---|---|---|',
    '| ledger | trust | audit.record, approval.consume | contracts/trust.md |',
    '',
    '## Runs',
    '| Run | Part | Slice | Stories | Needs |',
    '|---|---|---|---|---|',
    '| trust-1 | trust | 1 | T01, T02 | plan PR |',
    '| ledger-1 | ledger | 1 | L01, L02 | trust-1 |',
    '| cli-1 | cli | 1 | C01 | plan PR |',
    '### ledger-1',
    'Also updates: cli',
  ].join('\n') + '\n';

  const parsed = parseProductDocuments({ mapText: SAMPLE_MAP.replace('| R05 | * |', '| R05 | shared |'), planText: barePlan });
  assert.deepEqual(parsed.product.runs.find(r => r.run === 'ledger-1').sharedSurfaces, ['cli']);
  assert.equal(Object.hasOwn(parsed.product.runs.find(r => r.run === 'trust-1'), 'sharedSurfaces'), false);

  // Runtime interface calls & resources satisfy consumer wiring while defining prompt entries do NOT self-wire!
  const runtimeIface = obj => `<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(obj)}\n\`\`\`\n</details>\n`;
  const auditDefiningOnly = auditProductPlan({
    mapText: SAMPLE_MAP,
    planText: barePlan,
    promptFiles: [
      { path: 'prompts/trust/audit.prompt.md', content: '# Audit\n\n' + runtimeIface({ entries: [{ operation: 'record' }], calls: [], resources: [] }) },
      { path: 'prompts/trust/approval.prompt.md', content: '# Approval\n\nDefines approval.consume.\n' },
      { path: 'prompts/ledger/cap-table.prompt.md', content: '# Cap table\n\nNo boundary refs.\n' },
    ],
  });
  assert.equal(auditDefiningOnly.unwiredBoundaries.length, 2);

  const auditWiredViaRuntimeIface = auditProductPlan({
    mapText: SAMPLE_MAP,
    planText: barePlan,
    promptFiles: [
      { path: 'prompts/trust/audit.prompt.md', content: '# Audit\n\n' + runtimeIface({ entries: [{ operation: 'record' }], calls: [], resources: [] }) },
      { path: 'prompts/trust/approval.prompt.md', content: '# Approval\n\nDefines approval.consume.\n' },
      {
        path: 'prompts/ledger/cap-table.prompt.md',
        content: '# Cap table\n\n' + runtimeIface({
          entries: [{ operation: 'issue' }],
          calls: [{ target: 'prompts/trust/audit.prompt.md', target_operation: 'record', max_calls: 1 }],
          resources: [{ name: 'approval', kind: 'port', access: 'write', operations: [{ name: 'consume', access: 'write' }] }],
        }),
      },
    ],
  });
  assert.deepEqual(auditWiredViaRuntimeIface.unwiredBoundaries, []);

  // Owner: shared wildcard propagates into generated issue bodies
  const f = makeProductRepo(t, {
    'product/map.md': SAMPLE_MAP.replace('| R05 | * |', '| R05 | shared |'),
    'product/plan.md': barePlan,
  });
  const started = await productStart({ cwd: f.cwd, run: 'trust-1', noRun: true }, f.ports);
  assert.equal(started.exitCode, 0, started.message);
  assert.match(f.state.createdPayloads[0].body, /- R05 \(shared\): Keep money and share quantities as exact integers\./);
});
