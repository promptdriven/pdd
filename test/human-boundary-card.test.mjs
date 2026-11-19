import './helpers/test-home.mjs';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { Readable, Writable } from 'node:stream';
import test from 'node:test';

import {
  BOUNDARY_CARD_MAX_LINES,
  buildHumanBoundaryCard,
  formatApproveBoundaryCard,
  summarizeBoundaryEvidence,
} from '../src/human-boundary-card.mjs';
import { runApprove } from '../src/prompt-approve.mjs';
import { DETAILS_OPEN, readablePrTop } from '../src/workflow-pr-body.mjs';
import { stepDone } from '../src/workflow-runner.mjs';

function makeGitRepo(t, files = {}) {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-boundary-card-')));
  const stateDir = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-boundary-state-')));
  t.after(() => {
    rmSync(root, { recursive: true, force: true });
    rmSync(stateDir, { recursive: true, force: true });
  });
  const git = (...args) => execFileSync('git', args, { cwd: root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  git('init', '-q', '-b', 'main');
  git('config', 'user.email', 'test@example.com');
  git('config', 'user.name', 'Test Person');
  writeFileSync(join(root, 'README.md'), '# Project\n');
  git('add', 'README.md');
  git('commit', '-qm', 'init');
  git('checkout', '-qb', 'feat/slice');
  for (const [rel, content] of Object.entries(files)) {
    mkdirSync(join(root, dirname(rel)), { recursive: true });
    writeFileSync(join(root, rel), content);
  }
  if (Object.keys(files).length) git('add', '.');
  return { root, stateDir, git };
}

function runtimePrompt({ title, prose, operation, inputProps = {}, resultSchema = { type: 'object', properties: { ok: { type: 'boolean' } }, required: ['ok'], additionalProperties: false }, resources = [], calls = [] }) {
  const iface = {
    status: 'draft',
    prose_sha256: '',
    entries: [
      {
        operation,
        input_schema: {
          type: 'object',
          properties: inputProps,
          required: Object.keys(inputProps),
          additionalProperties: false,
        },
        result_schema: resultSchema,
        errors: [],
      },
    ],
    calls,
    resources,
    limits: { max_steps: 4, max_model_calls: 2 },
  };
  return `# ${title}\n\n${prose.trim()}\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(iface, null, 2)}\n\`\`\`\n</details>\n`;
}

async function approveInteractive(root, promptRelPath, answer = 'y\n', env = {}) {
  let out = '', err = '';
  const exitCode = await runApprove({ words: [promptRelPath], cwd: root }, {
    interactive: true,
    stdin: Readable.from([answer]),
    stdout: new Writable({ write(chunk, _enc, done) { out += chunk; done(); } }),
    stderr: new Writable({ write(chunk, _enc, done) { err += chunk; done(); } }),
    env: { ...process.env, ...env },
  });
  return { exitCode, out, err };
}

function extractApproveBoundaryCard(out) {
  const lines = out.split('\n');
  const start = lines.indexOf('Human boundary card (advisory):');
  assert.ok(start >= 0, `Expected Human boundary card in output:\n${out}`);
  let end = start + 1;
  while (end < lines.length && lines[end].startsWith('  ')) end += 1;
  return lines.slice(start, end);
}

function extractPrBoundarySection(prText) {
  const lines = prText.split('\n');
  const start = lines.indexOf('## Boundary');
  assert.ok(start >= 0, `Expected ## Boundary section in PR top:\n${prText}`);
  let end = start + 1;
  while (end < lines.length && !lines[end].startsWith('## ')) end += 1;
  while (end > start && lines[end - 1] === '') end -= 1;
  return lines.slice(start, end);
}

function specFactsWithBoundary(boundary) {
  return {
    layout: 'spec',
    single: false,
    workflow: 'feature',
    number: 3297,
    baseBranch: 'main',
    mode: 'manual',
    pending: false,
    draft: false,
    issueReference: 'Part of #3297',
    stories: ['As an operator, I want outage alerts held during maintenance windows, so that on-call engineers are not paged for planned work.'],
    storyPaths: ['user_stories/link-outage.md'],
    boundary,
    fields: { problem: 'Duplicate failover pages fire during maintenance windows.' },
    thisPr: 'no code change. It holds 3 prompts, the Story and 1 test file.',
    diff: {
      added: 48,
      removed: 2,
      count: 5,
      files: [
        { path: 'prompts/impl.prompt.md', added: 18, removed: 1 },
        { path: 'prompts/guide.prompt.md', added: 10, removed: 1 },
        { path: 'prompts/simulator.prompt.md', added: 12, removed: 0 },
      ],
    },
    records: {
      promptTests: { result: '✓ 1 of 1 criterion · 1/1 checks · 1 AI call', pass: true, report: 'https://rt.example.test/r/outage-1', current: true },
      lint: { result: '1 of 1 tests pass', pass: true },
      ci: 'passing',
      checker: null,
      drafts: [],
    },
    approval: { kind: 'words', items: [{ route: 'terminal', at: Date.UTC(2026, 10, 18), words: null }] },
    pr1: null,
    pr2: null,
    stacked: false,
    carriesPr1: false,
    notFixed: false,
    updatedAt: Date.UTC(2026, 10, 18, 6, 0),
  };
}

test('3297 link-outage simulator case: flags model-returned effects needing port/native observation and unloaded changed prompts as missing owner connection', async t => {
  const storyText = [
    '# Link outage alert suppression',
    '',
    'As an operator, I want outage alerts held during maintenance blackouts, so that planned link work never pages on-call staff.',
    '',
    '## Acceptance criteria',
    '',
    '1. Suppress outbound pager alerts when a WAN link flaps during a scheduled maintenance blackout.',
    '',
    '## Rules to check',
    '',
    '- Never dispatch outbound pager alerts while a scheduled maintenance blackout is active.',
    '',
  ].join('\n');

  const simulatorPrompt = runtimePrompt({
    title: 'Standalone outage simulator',
    prose: 'Simulate an outage event and return a summary object with an effects array.',
    operation: 'simulate_outage',
    inputProps: { link: { type: 'string' }, blackout: { type: 'boolean' } },
    resultSchema: {
      type: 'object',
      properties: {
        effects: { type: 'array', items: { type: 'string' } },
      },
      required: ['effects'],
      additionalProperties: false,
    },
  });

  const implPrompt = runtimePrompt({
    title: 'Failover implementation owner',
    prose: 'When a WAN link flaps during a scheduled maintenance blackout, suppress outbound pager alerts and hold failover.',
    operation: 'handle_link_flap',
    inputProps: { link: { type: 'string' }, blackout: { type: 'boolean' } },
  });

  const guidePrompt = '# Operations routing guide\n\nDuring a scheduled maintenance blackout, never dispatch outbound pager alerts.\n';

  const scenario = {
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/link-outage.md',
    criteria: [
      { id: 'AC1', text: 'Suppress outbound pager alerts when a WAN link flaps during a scheduled maintenance blackout.' },
    ],
    initial_world: {},
    steps: [
      {
        step_id: 'flap-during-blackout',
        entry_path: 'prompts/simulator.prompt.md',
        operation: 'simulate_outage',
        input: { link: 'wan0', blackout: true },
        checks: [
          { criterion_id: 'AC1', target: 'result', path: '/effects', op: 'equals', value: [] },
        ],
      },
    ],
  };

  const { root, stateDir } = makeGitRepo(t, {
    'user_stories/link-outage.md': storyText,
    'prompts/simulator.prompt.md': simulatorPrompt,
    'prompts/impl.prompt.md': implPrompt,
    'prompts/guide.prompt.md': guidePrompt,
    'tests/link-outage.json': JSON.stringify(scenario, null, 2),
  });

  // 1) Approving prompts/impl.prompt.md stays advisory (succeeds), sits above raw schema/prose in <= 25 lines,
  //    flags missing owner connection for unloaded prompts/impl.prompt.md, and flags model-returned /effects.
  const implApproval = await approveInteractive(root, 'prompts/impl.prompt.md', 'y\n', { PDD_STATE_DIR: stateDir });
  assert.equal(implApproval.exitCode, 0, implApproval.err);
  const implCardLines = extractApproveBoundaryCard(implApproval.out);
  assert.ok(implCardLines.length <= BOUNDARY_CARD_MAX_LINES, `Card exceeded ${BOUNDARY_CARD_MAX_LINES} lines: ${implCardLines.length}`);
  assert.ok(
    implApproval.out.indexOf('Human boundary card (advisory):') < implApproval.out.indexOf('Operation handle_link_flap'),
    'Boundary card must appear above raw schema details.',
  );
  assert.ok(
    implApproval.out.indexOf('Operation handle_link_flap') < implApproval.out.indexOf('Text (no approved version'),
    'Raw schema stays above prose text.',
  );
  const implCardText = implCardLines.join('\n');
  assert.match(implCardText, /missing owner connection/);
  assert.match(implCardText, /prompts\/impl\.prompt\.md/);
  assert.match(implCardText, /prompts\/simulator\.prompt\.md/);
  assert.match(implCardText, /model-returned value.*port spy or native observation still needed/);

  // 2) Approving standalone exploratory prompts/simulator.prompt.md is ALSO non-blocking (exit 0)
  //    while flagging unloaded sibling prompts and model-returned effects.
  const simApproval = await approveInteractive(root, 'prompts/simulator.prompt.md', 'y\n', { PDD_STATE_DIR: stateDir });
  assert.equal(simApproval.exitCode, 0, simApproval.err);
  const simCardText = extractApproveBoundaryCard(simApproval.out).join('\n');
  assert.match(simCardText, /missing owner connection/);
  assert.match(simCardText, /prompts\/guide\.prompt\.md/);
  assert.match(simCardText, /model-returned value.*port spy or native observation still needed/);

  // 3) PR 1 readable top renders ## Boundary in <= 25 lines with zero forbidden PR-top jargon or extra links.
  const boundary = buildHumanBoundaryCard({
    root,
    promptPaths: ['prompts/simulator.prompt.md', 'prompts/impl.prompt.md', 'prompts/guide.prompt.md'],
    storyPaths: ['user_stories/link-outage.md'],
    env: { PDD_STATE_DIR: stateDir },
  });
  const prTop = readablePrTop(specFactsWithBoundary(boundary));
  const prBoundaryLines = extractPrBoundarySection(prTop.text);
  assert.ok(prBoundaryLines.length <= BOUNDARY_CARD_MAX_LINES, `PR Boundary exceeded 25 lines: ${prBoundaryLines.length}`);
  const prBoundaryText = prBoundaryLines.join('\n');
  assert.match(prBoundaryText, /missing owner connection/);
  assert.match(prBoundaryText, /prompts\/impl\.prompt\.md/);
  assert.match(prBoundaryText, /prompts\/guide\.prompt\.md/);
  assert.match(prBoundaryText, /model-returned value.*port spy or native observation still needed/);
  assert.equal(prTop.text.match(/https:\/\//g)?.length ?? 0, 1, 'PR readable top keeps exactly one report link.');
  assert.doesNotMatch(prTop.text, /Acceptance criteria|<details|Agent note|\bbatch\b|\brequest\b/i);
});

test('3297 focused acceptance control: removing owning rule or dependency link while synthetic scenario still passes flips card to missing owner connection', async t => {
  const storyText = [
    '# Blackout alert hold',
    '',
    'As an operator, I want blackout rules enforced before paging, so that maintenance windows remain quiet.',
    '',
    '## Acceptance criteria',
    '',
    '1. Hold pager notifications with `blackout_hold` whenever a scheduled blackout window is active.',
    '',
    '## Rules to check',
    '',
    '- Never page engineers when `blackout_hold` applies during a scheduled blackout window.',
    '',
  ].join('\n');

  const connectedOwnerPrompt = runtimePrompt({
    title: 'Alert dispatcher',
    prose: [
      '## Scheduled blackout rule',
      '',
      'Whenever a scheduled blackout window is active, hold pager notifications and return reason `blackout_hold`.',
      '',
      '## Dependencies',
      '',
      '- [Escalation policy](escalation.prompt.md#quiet-hours)',
    ].join('\n'),
    operation: 'evaluate_page',
    inputProps: { windowActive: { type: 'boolean' } },
    resultSchema: {
      type: 'object',
      properties: { status: { type: 'string' } },
      required: ['status'],
      additionalProperties: false,
    },
  });

  const escalationPrompt = '# Escalation policy\n\n## Quiet hours\n\nHold escalations during quiet hours and scheduled blackout windows.\n';

  const syntheticScenario = {
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/blackout.md',
    criteria: [
      { id: 'AC1', text: 'Hold pager notifications with `blackout_hold` whenever a scheduled blackout window is active.' },
    ],
    initial_world: {},
    steps: [
      {
        step_id: 'synthetic-blackout-case',
        entry_path: 'prompts/dispatcher.prompt.md',
        operation: 'evaluate_page',
        input: { windowActive: true },
        checks: [
          { criterion_id: 'AC1', target: 'result', path: '/status', op: 'equals', value: 'held' },
        ],
      },
    ],
  };

  const { root, stateDir, git } = makeGitRepo(t, {
    'user_stories/blackout.md': storyText,
    'prompts/dispatcher.prompt.md': connectedOwnerPrompt,
    'prompts/escalation.prompt.md': escalationPrompt,
    'tests/blackout.json': JSON.stringify(syntheticScenario, null, 2),
  });

  // Baseline: connected owning rule & dependency link -> owner is credited cleanly with no missing connection.
  const beforeCard = buildHumanBoundaryCard({ root, focusPrompt: 'prompts/dispatcher.prompt.md', env: { PDD_STATE_DIR: stateDir } });
  assert.equal(beforeCard.unloadedOwners.length, 0);
  assert.deepEqual(beforeCard.selectedSources, ['prompts/dispatcher.prompt.md', 'prompts/escalation.prompt.md']);
  assert.ok(beforeCard.provenanceRows.every(row => !row.missingConnection), 'Connected baseline must credit the exercised sources.');

  // Planted control A: keep the synthetic scenario identical and passing, but remove the owning blackout rule
  // and dependency link from prompts/dispatcher.prompt.md!
  const disconnectedPrompt = runtimePrompt({
    title: 'Alert dispatcher',
    prose: 'Return a synthetic status string for the incoming payload.',
    operation: 'evaluate_page',
    inputProps: { windowActive: { type: 'boolean' } },
    resultSchema: {
      type: 'object',
      properties: { status: { type: 'string' } },
      required: ['status'],
      additionalProperties: false,
    },
  });
  writeFileSync(join(root, 'prompts/dispatcher.prompt.md'), disconnectedPrompt);
  git('add', 'prompts/dispatcher.prompt.md');

  const afterCard = buildHumanBoundaryCard({ root, focusPrompt: 'prompts/dispatcher.prompt.md', env: { PDD_STATE_DIR: stateDir } });
  assert.ok(afterCard.unloadedOwners.includes('prompts/escalation.prompt.md'), 'Removed dependency link surfaces unloaded escalation owner.');
  assert.ok(afterCard.provenanceRows.some(row => row.missingConnection), 'Removed owning rule must trigger missing owner connection.');

  const approveOut = await approveInteractive(root, 'prompts/dispatcher.prompt.md', 'y\n', { PDD_STATE_DIR: stateDir });
  assert.equal(approveOut.exitCode, 0, 'Advisory card still allows person approval.');
  assert.match(extractApproveBoundaryCard(approveOut.out).join('\n'), /missing owner connection/);

  const prText = readablePrTop(specFactsWithBoundary(afterCard)).text;
  assert.match(extractPrBoundarySection(prText).join('\n'), /missing owner connection/);
});

test('3297 observation provenance: classifies supplied fact, model-returned value, 0 observed port calls, and preserves native-only route', async t => {
  const storyText = [
    '# Billing guardrails',
    '',
    'As a customer, I want waived invoices to skip payment charges, so that zero-balance renewals never bill my card.',
    '',
    '## Acceptance criteria',
    '',
    '1. Echo the customer account identifier unchanged on the invoice receipt.',
    '2. Compute net total 0 cents when a full waiver coupon applies.',
    '3. Make 0 charge calls to the billing gateway when net total is 0 cents.',
    '',
  ].join('\n');

  const billingPrompt = runtimePrompt({
    title: 'Invoice checkout',
    prose: 'Echo the customer account identifier, compute net total 0 cents for full waiver coupons, and never call the billing gateway charge port when net total is 0 cents.',
    operation: 'checkout_invoice',
    inputProps: { accountId: { type: 'string' }, coupon: { type: 'string' } },
    resultSchema: {
      type: 'object',
      properties: {
        accountId: { type: 'string' },
        netCents: { type: 'integer' },
      },
      required: ['accountId', 'netCents'],
      additionalProperties: false,
    },
    resources: [
      {
        name: 'gateway',
        kind: 'port',
        access: 'write',
        operations: [
          {
            name: 'charge',
            access: 'write',
            arguments_schema: { type: 'object', properties: { cents: { type: 'integer' } }, required: ['cents'], additionalProperties: false },
            result_schema: { type: 'object', properties: { charged: { type: 'boolean' } }, required: ['charged'], additionalProperties: false },
          },
        ],
      },
    ],
  });

  const nativeLockPrompt = [
    '---',
    'kind: native-only',
    'reason: OS advisory flock lifecycle verified in deterministic native lock tests',
    '---',
    '',
    '# Invoice lock file',
    '',
    'Acquire and release the POSIX advisory lock around local invoice writes.',
    '',
  ].join('\n');

  const scenario = {
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/billing.md',
    criteria: [
      { id: 'AC1', text: 'Echo the customer account identifier unchanged on the invoice receipt.' },
      { id: 'AC2', text: 'Compute net total 0 cents when a full waiver coupon applies.' },
      { id: 'AC3', text: 'Make 0 charge calls to the billing gateway when net total is 0 cents.' },
    ],
    initial_world: {},
    steps: [
      {
        step_id: 'waived-invoice',
        entry_path: 'prompts/billing.prompt.md',
        operation: 'checkout_invoice',
        input: { accountId: 'acct-9001', coupon: 'FULL_WAIVER' },
        checks: [
          { criterion_id: 'AC1', target: 'result', path: '/accountId', op: 'equals', value: 'acct-9001' },
          { criterion_id: 'AC2', target: 'result', path: '/netCents', op: 'equals', value: 0 },
          { criterion_id: 'AC3', target: 'calls', path: '/resources/billing-gateway-charge', op: 'equals', value: 0 },
        ],
      },
    ],
  };

  const { root, stateDir } = makeGitRepo(t, {
    'user_stories/billing.md': storyText,
    'prompts/billing.prompt.md': billingPrompt,
    'prompts/invoice-lock.prompt.md': nativeLockPrompt,
    'tests/billing.json': JSON.stringify(scenario, null, 2),
  });

  const card = buildHumanBoundaryCard({
    root,
    promptPaths: ['prompts/billing.prompt.md', 'prompts/invoice-lock.prompt.md'],
    storyPaths: ['user_stories/billing.md'],
    env: { PDD_STATE_DIR: stateDir },
  });

  const byLabel = Object.fromEntries(card.provenanceRows.map(r => [r.label, r]));
  assert.ok(byLabel.AC1.observations.some(o => o.includes('supplied fact')), `Expected supplied fact for AC1, got: ${byLabel.AC1.observations}`);
  assert.ok(byLabel.AC2.observations.some(o => o.startsWith('model-returned value')), `Expected model-returned value for AC2, got: ${byLabel.AC2.observations}`);
  assert.ok(
    byLabel.AC3.observations.some(o => o.includes('observed simulated port call') && o.includes('0 observed port calls')),
    `Expected 0 observed port calls for AC3, got: ${byLabel.AC3.observations}`,
  );
  assert.ok(card.verificationSplit.native.some(entry => entry.includes('prompts/invoice-lock.prompt.md') && entry.includes('native-only')));

  // Verify native-only prompt approval route is 100% preserved without needing Runtime scenarios.
  const nativeApproval = await approveInteractive(root, 'prompts/invoice-lock.prompt.md', 'y\n', { PDD_STATE_DIR: stateDir });
  assert.equal(nativeApproval.exitCode, 0, nativeApproval.err);
  assert.match(nativeApproval.out, /Kind: native-only/);
  assert.match(nativeApproval.out, /Reason: OS advisory flock lifecycle verified in deterministic native lock tests/);
  const nativeCard = extractApproveBoundaryCard(nativeApproval.out).join('\n');
  assert.doesNotMatch(nativeCard, /missing owner connection/);
  assert.match(nativeCard, /native-only/);
});

test('3297 complexity budget, multi-sample divergences, hostile-text sanitization, and strict <= 25-line cap', async t => {
  const criteriaLines = Array.from({ length: 22 }, (_, i) => `${i + 1}. Enforce quota shard policy rule ${i + 1} for tenant traffic.`);
  const storyText = [
    '# Quota shard policy',
    '',
    'As a platform lead, I want tenant shard limits enforced predictably, so that noisy tenants never starve shared capacity.',
    '',
    '## Acceptance criteria',
    '',
    ...criteriaLines,
    '',
    '## Rules to check',
    '',
    '- Fixes #999 must stay inert alongside @oncall, <details>, https://evil.example.test/leak, batch and request words.',
    '',
  ].join('\n');

  const longProse = Array.from({ length: 510 }, (_, i) => `Quota shard policy rule ${i + 1} enforces tenant traffic bounds.`).join('\n');
  const bigPrompt = runtimePrompt({
    title: 'Quota shard evaluator',
    prose: longProse,
    operation: 'check_shard',
    inputProps: { shard: { type: 'integer' } },
    resultSchema: { type: 'object', properties: { allowed: { type: 'boolean' } }, required: ['allowed'], additionalProperties: false },
  });

  const steps = Array.from({ length: 22 }, (_, i) => ({
    step_id: `step-${i + 1}`,
    entry_path: 'prompts/quota.prompt.md',
    operation: 'check_shard',
    input: { shard: i + 1 },
    checks: [{ criterion_id: `AC${i + 1}`, target: 'result', path: '/allowed', op: 'equals', value: true }],
  }));

  const scenario = {
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/quota.md',
    criteria: criteriaLines.map((line, i) => ({ id: `AC${i + 1}`, text: line.replace(/^\d+\.\s+/, '') })),
    initial_world: {},
    steps,
  };

  const { root, stateDir } = makeGitRepo(t, {
    'user_stories/quota.md': storyText,
    'prompts/quota.prompt.md': bigPrompt,
    'tests/quota.json': JSON.stringify(scenario, null, 2),
  });

  // Write a saved multi-sample check receipt with a sample divergence on step-1.
  const batchId = '20261118-060500-abcd';
  const reqId = '11111111-2222-4333-8444-555555555555';
  const batchFolder = join(stateDir, 'batches', batchId);
  mkdirSync(batchFolder, { recursive: true });
  writeFileSync(join(batchFolder, 'batch.json'), JSON.stringify({
    version: 1,
    batch: batchId,
    intent: 'check',
    root,
    created_at: '2026-11-18T06:05:00Z',
    rows: [{ test: 'tests/quota.json', story: 'user_stories/quota.md', request_ids: [reqId], ended_at: Date.UTC(2026, 10, 18, 6, 5) }],
  }));
  writeFileSync(join(batchFolder, `${reqId}.json`), JSON.stringify({
    id: reqId,
    requestId: reqId,
    command: 'check',
    state: 'passed',
    result: {
      report: {
        samples: [
          { steps: [{ step_id: 'step-1', result: { allowed: true }, world: {}, calls: {}, checks: [{ passed: true }] }] },
          { steps: [{ step_id: 'step-1', result: { allowed: false }, world: {}, calls: {}, checks: [{ passed: false }] }] },
          { steps: [{ step_id: 'step-1', result: { allowed: true }, world: {}, calls: {}, checks: [{ passed: true }] }] },
        ],
      },
    },
  }));

  const card = buildHumanBoundaryCard({
    root,
    focusPrompt: 'prompts/quota.prompt.md',
    env: { PDD_STATE_DIR: stateDir },
  });

  const approveLines = formatApproveBoundaryCard(card);
  assert.ok(approveLines.length <= BOUNDARY_CARD_MAX_LINES, `Approve card must be <= 25 lines, got ${approveLines.length}`);
  const approveText = approveLines.join('\n');
  assert.match(approveText, /over 500 budget/);
  assert.match(approveText, /22 steps >15/);
  assert.match(approveText, /advisory divergence: step-1 varied across 3 samples/);
  assert.match(approveText, /Verification split:/);
  assert.match(approveText, /Budget & samples:/);

  const prTop = readablePrTop(specFactsWithBoundary(card));
  const prBoundaryLines = extractPrBoundarySection(prTop.text);
  assert.ok(prBoundaryLines.length <= BOUNDARY_CARD_MAX_LINES, `PR Boundary section must be <= 25 lines, got ${prBoundaryLines.length}`);
  const prBoundaryText = prBoundaryLines.join('\n');
  assert.match(prBoundaryText, /over 500 budget/);
  assert.match(prBoundaryText, /advisory divergence: step-1 varied across 3 samples/);
  assert.doesNotMatch(prTop.text, /<details|Acceptance criteria|\bbatch\b|\brequest\b|Fixes #999|@oncall/i);
  assert.equal(prTop.text.match(/https:\/\//g)?.length ?? 0, 1, 'Hostile URLs inside Story rules must stay neutralized.');
});

test('3297 single-prompt rule-removal acceptance control and real workflow-runner PR 1 publication wiring', async t => {
  const storyText = [
    '# Failover drain guard',
    '',
    'As an operator, I want active sessions drained before failover completes, so that in-flight traffic is not dropped.',
    '',
    '## Acceptance criteria',
    '',
    '1. Drain active customer sessions before marking tunnel failover complete.',
    '',
  ].join('\n');

  const withRule = runtimePrompt({
    title: 'Tunnel failover',
    prose: 'Always drain active customer sessions before marking tunnel failover complete.',
    operation: 'run_failover',
    inputProps: { tunnelId: { type: 'string' } },
    resultSchema: {
      type: 'object',
      properties: { effects: { type: 'array', items: { type: 'string' } } },
      required: ['effects'],
      additionalProperties: false,
    },
  });

  const scenario = {
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/drain.md',
    criteria: [
      { id: 'AC1', text: 'Drain active customer sessions before marking tunnel failover complete.' },
    ],
    initial_world: {},
    steps: [
      {
        step_id: 'drain-first',
        entry_path: 'prompts/failover.prompt.md',
        operation: 'run_failover',
        input: { tunnelId: 'tun-7' },
        checks: [
          { criterion_id: 'AC1', target: 'result', path: '/effects', op: 'equals', value: ['drained'] },
        ],
      },
    ],
  };

  const { root, stateDir, git } = makeGitRepo(t, {
    'user_stories/drain.md': storyText,
    'prompts/failover.prompt.md': withRule,
    'tests/drain.json': JSON.stringify(scenario, null, 2),
  });

  // 1) Pure single-prompt connected baseline: no extra dependency files, rule is present -> owner credited!
  const connected = buildHumanBoundaryCard({ root, focusPrompt: 'prompts/failover.prompt.md', env: { PDD_STATE_DIR: stateDir } });
  assert.equal(connected.provenanceRows[0].missingConnection, false);
  assert.equal(connected.provenanceRows[0].owner, 'prompts/failover.prompt.md');

  // 2) Remove ONLY the owning rule prose from that single selected prompt while keeping the synthetic scenario intact ->
  //    card flags missing owner connection instead of crediting prompts/failover.prompt.md!
  const withoutRule = runtimePrompt({
    title: 'Tunnel failover',
    prose: 'Return a synthetic list of strings for test payloads.',
    operation: 'run_failover',
    inputProps: { tunnelId: { type: 'string' } },
    resultSchema: {
      type: 'object',
      properties: { effects: { type: 'array', items: { type: 'string' } } },
      required: ['effects'],
      additionalProperties: false,
    },
  });
  writeFileSync(join(root, 'prompts/failover.prompt.md'), withoutRule);
  // Also add an unloaded changed implementation prompt and commit on topic branch to verify real workflow-runner PR 1 publication!
  writeFileSync(join(root, 'prompts/session-drainer.prompt.md'), '# Session drainer\n\nDrain active customer sessions gracefully.\n');
  git('add', '.');
  git('commit', '-qm', 'prompt slice');

  const bare = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-boundary-bare-')));
  t.after(() => rmSync(bare, { recursive: true, force: true }));
  execFileSync('git', ['init', '--bare', '-q', bare]);
  const route = `url.file://${bare}.insteadOf=https://github.com/example/project.git`;
  git('remote', 'add', 'origin', 'https://github.com/example/project.git');
  execFileSync('git', ['-c', route, 'push', '-q', 'origin', 'main'], { cwd: root });
  const baseSha = git('rev-parse', 'main').trim();

  const runDir = join(root, '.git', 'pdd', 'runs', '3297');
  mkdirSync(runDir, { recursive: true });
  const run = {
    v: 1,
    runId: 'boundary-3297',
    number: 3297,
    repo: 'example/project',
    issue: { title: 'Failover drain guard', number: 3297, url: 'https://github.com/example/project/issues/3297' },
    root,
    sourceRoot: root,
    runDir,
    branch: 'feat/slice',
    baseBranch: 'main',
    baseSha,
    workflow: 'feature',
    agent: 'codex',
    areas: [
      { name: 'prompt-pr', steps: ['scope', 'check'], optional: [], gate: 'pr', then: 'ask-code' },
      { name: 'code', steps: ['build', 'verify'], optional: [], gate: 'pr' },
    ],
    area: 0,
    state: 'running',
    done: { scope: { summary: 'Problem: tunnel failover drops sessions.', at: 1 } },
    decisions: [],
    changes: [],
    chats: [],
    pr: [],
  };
  writeFileSync(join(runDir, 'status.json'), JSON.stringify(run));

  const createdPrBodies = [];
  const doneRes = await stepDone(
    { ref: '3297', step: 'check', summary: 'Title: Enforce session drain before failover', cwd: root },
    {
      stateDir,
      isTTY: true,
      env: { ...process.env, PDD_STATE_DIR: stateDir },
      confirm: async () => false,
      now: () => Date.UTC(2026, 10, 18, 7, 0),
      execFile: async (file, args, opts = {}) => {
        if (file === 'git') {
          const gitArgs = args[0] === 'remote' && args[1] === 'get-url' ? args : ['-c', route, ...args];
          try {
            const stdout = execFileSync('git', gitArgs, { cwd: opts.cwd ?? root, encoding: 'utf8', env: { ...process.env, GIT_ALLOW_PROTOCOL: 'file' }, stdio: ['ignore', 'pipe', 'pipe'] });
            return { code: 0, stdout, stderr: '' };
          } catch (err) {
            return { code: err.status ?? 1, stdout: String(err.stdout ?? ''), stderr: String(err.stderr ?? '') };
          }
        }
        if (file === 'gh') {
          const headOid = git('rev-parse', 'HEAD').trim();
          const prObj = {
            number: 42,
            url: 'https://github.com/example/project/pull/42',
            state: 'OPEN',
            isDraft: false,
            headRefName: 'feat/slice',
            baseRefName: 'main',
            headRefOid: headOid,
            body: createdPrBodies.at(-1) ?? '',
            headRepository: { name: 'project' },
            headRepositoryOwner: { login: 'example' },
            isCrossRepository: false,
            mergeCommit: null,
          };
          if (args[0] === 'pr' && args[1] === 'create') {
            createdPrBodies.push(String(opts.input ?? ''));
            return { code: 0, stdout: `${prObj.url}\n`, stderr: '' };
          }
          if (args[0] === 'pr' && args[1] === 'view') return { code: 0, stdout: JSON.stringify({ ...prObj, body: createdPrBodies.at(-1) ?? '' }), stderr: '' };
          if (args[0] === 'pr' && args[1] === 'list') return { code: 0, stdout: JSON.stringify(createdPrBodies.length ? [prObj] : []), stderr: '' };
          if (args[0] === 'label' && args[1] === 'list') return { code: 0, stdout: '[{"name":"pdd:no-verdict"}]', stderr: '' };
          if (args[0] === 'pr' && args[1] === 'edit') return { code: 0, stdout: '', stderr: '' };
          if (args[0] === 'repo') return { code: 0, stdout: '{"nameWithOwner":"example/project","defaultBranchRef":{"name":"main"},"url":"https://github.com/example/project"}', stderr: '' };
        }
        return { code: 0, stdout: '', stderr: '' };
      },
    },
  );
  assert.equal(doneRes.exitCode, 0, doneRes.message);
  assert.equal(createdPrBodies.length, 1);
  const [visiblePrTop] = createdPrBodies[0].split(DETAILS_OPEN);
  const prBoundaryLines = extractPrBoundarySection(visiblePrTop);
  assert.ok(prBoundaryLines.length <= BOUNDARY_CARD_MAX_LINES);
  const prBoundaryText = prBoundaryLines.join('\n');
  assert.match(prBoundaryText, /missing owner connection/);
  assert.match(prBoundaryText, /prompts\/session-drainer\.prompt\.md/);
  assert.match(prBoundaryText, /model-returned value.*port spy or native observation still needed/);
});

test('3297 J1-coffee-pickup & step-index fallback: no false 0 observed port calls without saved step, loaded-prompt prose budget fallback, and step_id-less zero-call evidence', t => {
  const repoRoot = realpathSync(new URL('..', import.meta.url));
  const emptyStateDir = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-j1-empty-')));
  t.after(() => rmSync(emptyStateDir, { recursive: true, force: true }));

  // 1) Real J1-coffee-pickup Story + scenario with NO saved batch:
  //    must NOT emit false "0 observed port calls on instrumented port", and must report loaded prompts' prose LOC (> 0).
  const j1Card = buildHumanBoundaryCard({
    root: repoRoot,
    storyPaths: ['user_stories/journeys/J1-coffee-pickup.md'],
    changedPaths: ['user_stories/journeys/J1-coffee-pickup.md', 'test/runtime/J1-coffee-pickup.json'],
    env: { PDD_STATE_DIR: emptyStateDir },
  });
  assert.equal(j1Card.provenanceRows.length, 2);
  for (const row of j1Card.provenanceRows) {
    assert.equal(row.zeroPortCalls, false, `Unexpected zeroPortCalls on ${row.label}: ${row.observations.join(', ')}`);
    assert.equal(row.missingConnection, false, `Expected J1 ${row.label} connected, got: ${row.owner}`);
    assert.ok(row.observations.every(o => !o.includes('0 observed port calls')));
  }
  assert.notEqual(j1Card.complexity.proseSummary, 'prose 0 LOC', 'Story-only slice must fall back to loaded prompts for prose LOC.');
  assert.match(j1Card.complexity.proseSummary, /3 prompts \(max \d+ prose LOC/);

  // 2) Step-index fallback when saved check step omits step_id (as in runtime-fake) and explicitly records 0 calls on an instrumented port.
  const storyText = [
    '# Waiver port spy',
    '',
    'As a user, I want waived orders to skip gateway calls, so that free trials never hit the payment port.',
    '',
    '## Acceptance criteria',
    '',
    '1. Return waived status true without calling the payment gateway on free trials.',
    '',
  ].join('\n');
  const promptText = runtimePrompt({
    title: 'Trial checkout',
    prose: 'Return waived status true without calling the payment gateway on free trials.',
    operation: 'run_trial',
    inputProps: { trial: { type: 'boolean' } },
    resultSchema: { type: 'object', properties: { waived: { type: 'boolean' } }, required: ['waived'], additionalProperties: false },
    resources: [{
      name: 'gateway',
      kind: 'port',
      access: 'write',
      operations: [{
        name: 'charge',
        access: 'write',
        arguments_schema: { type: 'object', properties: {}, additionalProperties: false },
        result_schema: { type: 'object', properties: {}, additionalProperties: false },
      }],
    }],
  });
  const scenario = {
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/trial.md',
    criteria: [{ id: 'AC1', text: 'Return waived status true without calling the payment gateway on free trials.' }],
    initial_world: {},
    steps: [{
      step_id: 'step-one',
      entry_path: 'prompts/trial.prompt.md',
      operation: 'run_trial',
      input: { trial: true },
      checks: [{ criterion_id: 'AC1', target: 'result', path: '/waived', op: 'equals', value: true }],
    }],
  };
  const { root, stateDir } = makeGitRepo(t, {
    'user_stories/trial.md': storyText,
    'prompts/trial.prompt.md': promptText,
    'tests/trial.json': JSON.stringify(scenario, null, 2),
  });

  // Without saved batch -> model-returned value WITHOUT 0 observed port calls.
  const beforeBatch = buildHumanBoundaryCard({ root, focusPrompt: 'prompts/trial.prompt.md', env: { PDD_STATE_DIR: stateDir } });
  assert.equal(beforeBatch.provenanceRows[0].zeroPortCalls, false);

  // With saved batch step omitting step_id and explicitly recording calls: { 'gateway.charge': 0 } -> reports 0 observed port calls!
  const batchId = '20261118-070000-idx1';
  const reqId = '22222222-2222-4222-8222-222222222222';
  const folder = join(stateDir, 'batches', batchId);
  mkdirSync(folder, { recursive: true });
  writeFileSync(join(folder, 'batch.json'), JSON.stringify({
    version: 1,
    batch: batchId,
    intent: 'check',
    root,
    created_at: '2026-11-18T07:00:00Z',
    rows: [{ test: 'tests/trial.json', story: 'user_stories/trial.md', request_ids: [reqId], ended_at: Date.UTC(2026, 10, 18, 7, 0) }],
  }));
  writeFileSync(join(folder, `${reqId}.json`), JSON.stringify({
    id: reqId,
    requestId: reqId,
    command: 'check',
    state: 'passed',
    result: {
      report: {
        samples: [{
          sample: 1,
          steps: [{
            calls: { 'gateway.charge': 0 },
            checks: [{ criterion_id: 'AC1', target: 'result', path: '/waived', passed: true }],
          }],
        }],
      },
    },
  }));
  const afterBatch = buildHumanBoundaryCard({ root, focusPrompt: 'prompts/trial.prompt.md', env: { PDD_STATE_DIR: stateDir } });
  assert.equal(afterBatch.provenanceRows[0].zeroPortCalls, true);
  assert.match(afterBatch.provenanceRows[0].observations.join(', '), /0 observed port calls on instrumented port/);
});

test('3297 #fragment section acceptance control: keeping heading and generic domain nouns while deleting rule clause or stripping section flags missing owner connection', t => {
  const storyText = [
    '# Blackout fragment guard',
    '',
    'As an operator, I want [blackout policy](prompts/owner.prompt.md#maintenance-blackout) enforced, so that planned link work never pages staff.',
    '',
    '## Acceptance criteria',
    '',
    '1. Suppress outbound pager alerts when a WAN link flaps during a scheduled maintenance blackout.',
    '',
  ].join('\n');

  const makeOwnerWithSection = sectionBody => runtimePrompt({
    title: 'Pager owner',
    prose: [
      '## Standard routing',
      '',
      'Send outbound pager alerts when an unplanned WAN link failure occurs.',
      '',
      '## Maintenance blackout <scr<script>ipt>',
      '',
      sectionBody,
    ].join('\n'),
    operation: 'evaluate_link',
    inputProps: { flap: { type: 'boolean' } },
    resultSchema: { type: 'object', properties: { status: { type: 'string' } }, required: ['status'], additionalProperties: false },
  });

  const scenario = {
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/fragment-guard.md',
    criteria: [{ id: 'AC1', text: 'Suppress outbound pager alerts when a WAN link flaps during a scheduled maintenance blackout.' }],
    initial_world: {},
    steps: [{
      step_id: 's1',
      entry_path: 'prompts/owner.prompt.md',
      operation: 'evaluate_link',
      input: { flap: true },
      checks: [{ criterion_id: 'AC1', target: 'result', path: '/status', op: 'equals', value: 'suppressed' }],
    }],
  };

  const { root, stateDir } = makeGitRepo(t, {
    'user_stories/fragment-guard.md': storyText,
    'prompts/owner.prompt.md': makeOwnerWithSection('During a scheduled maintenance blackout, suppress outbound pager alerts when a WAN link flaps.'),
    'tests/fragment-guard.json': JSON.stringify(scenario, null, 2),
  });

  // 1) Connected baseline (also verifying nested <scr<script>ipt> tag stripping in headingSlug converges cleanly to #maintenance-blackout).
  const baseline = buildHumanBoundaryCard({ root, focusPrompt: 'prompts/owner.prompt.md', env: { PDD_STATE_DIR: stateDir } });
  assert.equal(baseline.provenanceRows[0].missingConnection, false, baseline.provenanceRows[0].owner);

  // 2) Keep the ## Maintenance blackout heading AND generic domain nouns ("pager", "alerts"), but delete the specific blackout suppression clause!
  //    Even though ## Standard routing above still mentions WAN link and outbound pager alerts, narrowing to #maintenance-blackout + >=50% stem coverage flags missing connection!
  writeFileSync(join(root, 'prompts/owner.prompt.md'), makeOwnerWithSection('Pager alerts use the standard alert channel.'));
  const guttedClause = buildHumanBoundaryCard({ root, focusPrompt: 'prompts/owner.prompt.md', env: { PDD_STATE_DIR: stateDir } });
  assert.equal(guttedClause.provenanceRows[0].missingConnection, true);
  assert.match(guttedClause.provenanceRows[0].owner, /missing owner connection/);

  // 3) Keep the ## Maintenance blackout heading, but strip its section body empty!
  writeFileSync(join(root, 'prompts/owner.prompt.md'), makeOwnerWithSection('<!-- rule stripped -->'));
  const emptySection = buildHumanBoundaryCard({ root, focusPrompt: 'prompts/owner.prompt.md', env: { PDD_STATE_DIR: stateDir } });
  assert.equal(emptySection.provenanceRows[0].missingConnection, true);
  assert.match(emptySection.provenanceRows[0].owner, /empty section #maintenance-blackout/);
});

test('3297 schema alignment: newline pdd-boundary, Out-of-scope exclusion, context objects, input refs, initial_world.set, latest-batch divergences, and native-evidence-record', t => {
  const storyText = [
    '# Enterprise tier quota',
    '',
    'As a tenant admin, I want [shared rules](prompts/helper.prompt.md#shared-rules) applied to enterprise tier requests, so that seeded tiers and request limits stay consistent.',
    '',
    '```pdd-boundary',
    './prompts/core.prompt.md',
    '```',
    '',
    'Inline example `[ignored](prompts/nonexistent.prompt.md#bad)` and fenced example:',
    '',
    '```markdown',
    '[also ignored](prompts/core.prompt.md#nonexistent-heading)',
    '```',
    '',
    '## Acceptance criteria',
    '',
    '1. Echo the enterprise request correlation identifier from input.',
    '2. Keep the enterprise request limit aligned with the supplied input limit.',
    '3. Preserve the seeded enterprise account tier in world state.',
    '',
    '## Out of scope',
    '',
    '- Do not modify `prompts/out-of-scope.prompt.md`.',
    '',
    '## What must not change',
    '',
    '- Keep [untouched owner](prompts/untouched.prompt.md) unchanged.',
    '',
  ].join('\n');

  const corePrompt = runtimePrompt({
    title: 'Core enterprise handler',
    prose: [
      'Echo the enterprise request correlation identifier, keep the enterprise request limit aligned with input, and preserve the seeded enterprise account tier.',
      '',
      '## Dependencies',
      '',
      '- [Shared rules](prompts/helper.prompt.md#shared-rules)',
    ].join('\n'),
    operation: 'apply_quota',
    inputProps: { corrId: { type: 'string' }, limit: { type: 'integer' } },
    resultSchema: {
      type: 'object',
      properties: { corrId: { type: 'string' }, appliedLimit: { type: 'integer' } },
      required: ['corrId', 'appliedLimit'],
      additionalProperties: false,
    },
  });
  const helperPrompt = '# Helper\n\n## Shared rules\n\nEnterprise tier requests preserve seeded account tier and input request limits.\n';
  const ctxPromptA = '# Context A\n\nShared context A.\n';
  const ctxPromptB = '# Context B\n\nShared context B.\n';
  const outOfScopePrompt = '# Out of scope owner\n\nUnrelated legacy flow.\n';
  const untouchedPrompt = '# Untouched owner\n\nMust not change.\n';

  const scenario = {
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/nested/enterprise.md',
    criteria: [
      { id: 'AC1', text: 'Echo the enterprise request correlation identifier from input.' },
      { id: 'AC2', text: 'Keep the enterprise request limit aligned with the supplied input limit.' },
      { id: 'AC3', text: 'Preserve the seeded enterprise account tier in world state.' },
    ],
    initial_world: {
      set: {
        '/account/tier': 'enterprise',
      },
    },
    context: [
      { prompt_path: 'prompts/ctx-a.prompt.md' },
      { path: './prompts/ctx-b.prompt.md' },
    ],
    steps: [{
      step_id: 'apply',
      operation: 'apply_quota',
      input: { corrId: 'req-42', limit: 500 },
      checks: [
        { criterion_id: 'AC1', target: 'result', path: '/corrId', op: 'equals', value: { ref_target: 'input', ref_path: '/corrId' } },
        {
          criterion_id: 'AC2',
          target: 'result',
          path: '',
          op: 'integer_relation',
          value: {
            left: { field: '/appliedLimit' },
            compare: 'eq',
            right: { ref_target: 'input', ref_path: '/limit' },
          },
        },
        { criterion_id: 'AC3', target: 'world', path: '/account/tier', op: 'equals', value: 'enterprise' },
      ],
    }],
  };

  const { root, stateDir } = makeGitRepo(t, {
    'user_stories/nested/enterprise.md': storyText,
    'prompts/core.prompt.md': corePrompt,
    'prompts/helper.prompt.md': helperPrompt,
    'prompts/ctx-a.prompt.md': ctxPromptA,
    'prompts/ctx-b.prompt.md': ctxPromptB,
    'prompts/out-of-scope.prompt.md': outOfScopePrompt,
    'prompts/untouched.prompt.md': untouchedPrompt,
    'tests/enterprise.json': JSON.stringify(scenario, null, 2),
  });

  // Older batch with a historical divergence, superseded by a newer batch where 3/3 samples agree.
  const oldBatch = '20261118-010000-old1';
  const oldReq = '33333333-3333-4333-8333-333333333333';
  mkdirSync(join(stateDir, 'batches', oldBatch), { recursive: true });
  writeFileSync(join(stateDir, 'batches', oldBatch, 'batch.json'), JSON.stringify({
    version: 1,
    batch: oldBatch,
    intent: 'check',
    root,
    created_at: '2026-11-18T01:00:00Z',
    rows: [{ test: 'tests/enterprise.json', story: 'user_stories/nested/enterprise.md', request_ids: [oldReq], ended_at: Date.UTC(2026, 10, 18, 1, 0) }],
  }));
  writeFileSync(join(stateDir, 'batches', oldBatch, `${oldReq}.json`), JSON.stringify({
    id: oldReq,
    requestId: oldReq,
    command: 'check',
    state: 'failed',
    result: {
      report: {
        samples: [
          { steps: [{ step_id: 'apply', result: { corrId: 'req-42', appliedLimit: 500 }, checks: [{ passed: true }] }] },
          { steps: [{ step_id: 'apply', result: { corrId: 'req-42', appliedLimit: 100 }, checks: [{ passed: false }] }] },
        ],
      },
    },
  }));

  const newBatch = '20261118-020000-new2';
  const newReq = '44444444-4444-4444-8444-444444444444';
  mkdirSync(join(stateDir, 'batches', newBatch), { recursive: true });
  writeFileSync(join(stateDir, 'batches', newBatch, 'batch.json'), JSON.stringify({
    version: 1,
    batch: newBatch,
    intent: 'check',
    root,
    created_at: '2026-11-18T02:00:00Z',
    rows: [{ test: 'tests/enterprise.json', story: 'user_stories/nested/enterprise.md', request_ids: [newReq], ended_at: Date.UTC(2026, 10, 18, 2, 0) }],
  }));
  writeFileSync(join(stateDir, 'batches', newBatch, `${newReq}.json`), JSON.stringify({
    id: newReq,
    requestId: newReq,
    command: 'check',
    state: 'passed',
    result: {
      report: {
        samples: [
          { steps: [{ step_id: 'apply', result: { corrId: 'req-42', appliedLimit: 500 }, checks: [{ passed: true }] }] },
          { steps: [{ step_id: 'apply', result: { corrId: 'req-42', appliedLimit: 500 }, checks: [{ passed: true }] }] },
          { steps: [{ step_id: 'apply', result: { corrId: 'req-42', appliedLimit: 500 }, checks: [{ passed: true }] }] },
        ],
      },
    },
  }));

  // Saved pdd.native-evidence-record.v1 in .git/pdd/runs/99/status.json for this Story.
  const runDir = join(root, '.git', 'pdd', 'runs', '99');
  mkdirSync(runDir, { recursive: true });
  writeFileSync(join(runDir, 'status.json'), JSON.stringify({
    v: 1,
    runId: 'native-ev-99',
    root,
    evidence: [{
      native: {
        schema: 'pdd.native-evidence-record.v1',
        runId: 'native-ev-99',
        profileId: 'node-test',
        storyPath: 'user_stories/nested/enterprise.md',
      },
    }],
  }));

  const card = buildHumanBoundaryCard({
    root,
    storyPaths: ['user_stories/nested/enterprise.md'],
    promptPaths: ['prompts/core.prompt.md', 'prompts/helper.prompt.md'],
    changedPaths: ['user_stories/nested/enterprise.md', 'prompts/core.prompt.md', 'prompts/helper.prompt.md', 'tests/enterprise.json'],
    since: 0,
    env: { PDD_STATE_DIR: stateDir },
  });

  // Out-of-scope and What-must-not-change prompts are excluded from unloadedOwners!
  assert.deepEqual(card.unloadedOwners, []);
  // Context object prompt_path & path, newline pdd-boundary entry owner, and repo-root Story link are all in selectedSources!
  assert.deepEqual(card.selectedSources, [
    'prompts/core.prompt.md',
    'prompts/ctx-a.prompt.md',
    'prompts/ctx-b.prompt.md',
    'prompts/helper.prompt.md',
  ]);
  for (const row of card.provenanceRows) {
    assert.equal(row.missingConnection, false, `Unexpected missing connection on ${row.label}: ${row.owner}`);
    assert.ok(row.observations.includes('supplied fact'), `Expected supplied fact on ${row.label}, got ${row.observations}`);
    assert.ok(row.observations.includes('native test'), `Expected saved native-evidence-record to add native test on ${row.label}`);
  }
  // Superseded batch divergence is NOT reported; latest 3/3 agreement wins!
  assert.deepEqual(card.divergences, []);
  assert.equal(card.sampleSummary, '3/3 samples agreed');
});

function deepFreeze(value) {
  if (value && typeof value === 'object') {
    Object.freeze(value);
    for (const child of Object.values(value)) deepFreeze(child);
  }
  return value;
}

test('3297 summarizeBoundaryEvidence: keeps owner lookup, local SVG lint, hosted Story assertions, and receipted native checks separate without mutating inputs', () => {
  const fourObsInput = deepFreeze({
    ownerLookups: [{
      targetPath: 'src/alert-router.mjs',
      ownerPrompt: 'prompts/alert-router.prompt.md',
      source: 'header',
      certain: true,
    }],
    localLint: {
      exitCode: 0,
      state: 'partial',
      localOnly: true,
      scope: 'SVG layout only',
      warningCount: 0,
      problemCount: 0,
      incompleteSave: false,
      inspectedPrompts: ['prompts/alert-router.prompt.md'],
      inspectedTests: ['tests/alert-router.json'],
    },
    hostedStoryRuns: [{
      storyPath: 'user_stories/alert-router.md',
      testPath: 'tests/alert-router.json',
      loadedPrompts: ['prompts/alert-router.prompt.md'],
      missingOwnerConnection: false,
      state: 'passed',
      passedAssertions: [
        'AC1: suppress pager alert during blackout',
        'AC2: record suppression reason',
      ],
      totalAssertions: 2,
    }],
    nativeChecks: [{
      behavior: 'suppresses live pager webhook on staging host',
      targetHost: 'staging-east-1',
      runner: 'native-smoke',
      receipt: {
        receiptId: 'native-ev-3297-smoke-1',
        source: 'pdd.native-evidence-record.v1',
        status: 'passed',
        verifiedBehaviors: ['suppresses live pager webhook on staging host'],
      },
    }],
  });

  const combined = summarizeBoundaryEvidence(fourObsInput);
  assert.equal(combined.advisory, true);
  assert.equal(combined.entries.length, 4);
  assert.ok(combined.lines.length <= BOUNDARY_CARD_MAX_LINES);

  // 1) pdd owner resolution
  assert.deepEqual(combined.entries[0], {
    kind: 'owner-resolution',
    label: 'resolved',
    source: 'pdd owner (header)',
    scope: 'ownership lookup: src/alert-router.mjs -> prompts/alert-router.prompt.md (certain)',
    exitCode: null,
    ownerPrompt: 'prompts/alert-router.prompt.md',
    loadedPrompts: [],
    passedAssertions: [],
    receiptId: null,
    creditsPromptRules: false,
    creditsModeledAssertions: false,
    creditsNativeBehavior: false,
    note: 'ownership lookup only; checks no prompt rules or behavior',
  });
  assert.deepEqual(combined.credits.resolvedOwners, ['prompts/alert-router.prompt.md']);

  // 2) pdd lint --local exit 0 stays partial with zero prompt-rule credit
  assert.equal(combined.entries[1].kind, 'local-lint');
  assert.equal(combined.entries[1].label, 'partial');
  assert.equal(combined.entries[1].exitCode, 0);
  assert.equal(combined.entries[1].source, 'pdd lint --local');
  assert.equal(combined.entries[1].scope, 'SVG layout only; prompt rules not checked');
  assert.equal(combined.entries[1].creditsPromptRules, false);
  assert.equal(combined.credits.localLintPartial, true);
  assert.equal(combined.credits.localLintCreditsPromptRules, false);

  // 3) hosted Story run credits modeled assertions and loaded prompt rules, never native behavior
  assert.equal(combined.entries[2].kind, 'hosted-story');
  assert.equal(combined.entries[2].label, 'passed');
  assert.equal(combined.entries[2].source, 'pdd test (hosted): user_stories/alert-router.md');
  assert.deepEqual(combined.entries[2].loadedPrompts, ['prompts/alert-router.prompt.md']);
  assert.deepEqual(combined.entries[2].passedAssertions, [
    'AC1: suppress pager alert during blackout',
    'AC2: record suppression reason',
  ]);
  assert.equal(combined.entries[2].creditsPromptRules, true);
  assert.equal(combined.entries[2].creditsModeledAssertions, true);
  assert.equal(combined.entries[2].creditsNativeBehavior, false);
  assert.deepEqual(combined.credits.hostedPassedAssertions, [
    'AC1: suppress pager alert during blackout',
    'AC2: record suppression reason',
  ]);

  // 4) receipted native smoke check gets native credit only via matching passing receipt
  assert.equal(combined.entries[3].kind, 'native-check');
  assert.equal(combined.entries[3].label, 'verified');
  assert.equal(combined.entries[3].receiptId, 'native-ev-3297-smoke-1');
  assert.equal(combined.entries[3].creditsNativeBehavior, true);
  assert.deepEqual(combined.credits.nativeVerifiedBehaviors, ['suppresses live pager webhook on staging host']);
  assert.deepEqual(combined.credits.nativeUnverifiedBehaviors, []);

  // Control: mislabeled raw state="passed" with localOnly=true + incompleteSave=true still stays partial
  const localOnlyControl = summarizeBoundaryEvidence({
    ownerLookups: fourObsInput.ownerLookups,
    localLint: { ...fourObsInput.localLint, state: 'passed', incompleteSave: true },
  });
  assert.equal(localOnlyControl.entries[1].label, 'partial');
  assert.equal(localOnlyControl.entries[1].exitCode, 0);
  assert.equal(localOnlyControl.entries[1].scope, 'SVG layout only; incomplete local save; prompt rules not checked');
  assert.equal(localOnlyControl.entries[1].creditsPromptRules, false);
  assert.equal(localOnlyControl.credits.localLintPartial, true);
  assert.equal(localOnlyControl.credits.localLintCreditsPromptRules, false);
  assert.deepEqual(localOnlyControl.credits.hostedPassedAssertions, []);

  // Control: unconnected hosted Story run gets zero credit
  const unconnected = summarizeBoundaryEvidence({
    hostedStoryRuns: [{
      storyPath: 'user_stories/alert-router.md',
      testPath: 'tests/alert-router.json',
      loadedPrompts: ['prompts/simulator.prompt.md'],
      missingOwnerConnection: true,
      state: 'passed',
      passedAssertions: ['AC1: suppress pager alert during blackout'],
      totalAssertions: 1,
    }],
  });
  assert.equal(unconnected.entries[0].label, 'unconnected');
  assert.equal(unconnected.entries[0].creditsModeledAssertions, false);
  assert.equal(unconnected.entries[0].creditsPromptRules, false);
  assert.equal(unconnected.entries[0].creditsNativeBehavior, false);
  assert.deepEqual(unconnected.credits.hostedPassedAssertions, []);

  // Control: native behavior requires valid passing receipt covering that exact behavior
  const nativeControl = summarizeBoundaryEvidence({
    nativeChecks: [
      { behavior: 'drains active connections on staging host', targetHost: 'staging-east-1', runner: 'native-smoke', receipt: null },
      {
        behavior: 'rotates webhook signing key on staging host',
        targetHost: 'staging-east-1',
        runner: 'native-smoke',
        receipt: { receiptId: 'native-ev-3297-smoke-other', source: 'pdd.native-evidence-record.v1', status: 'passed', verifiedBehaviors: ['health endpoint returns 200'] },
      },
      {
        behavior: 'retries dead-letter delivery on staging host',
        targetHost: 'staging-east-1',
        runner: 'native-smoke',
        receipt: { receiptId: 'native-ev-3297-smoke-fail', source: 'pdd.native-evidence-record.v1', status: 'failed', verifiedBehaviors: ['retries dead-letter delivery on staging host'] },
      },
      {
        behavior: 'checks skipped smoke target',
        targetHost: 'staging-east-1',
        runner: 'native-smoke',
        receipt: { receiptId: 'native-ev-3297-smoke-skip', source: 'pdd.native-evidence-record.v1', status: 'skipped', verifiedBehaviors: ['checks skipped smoke target'] },
      },
      {
        behavior: 'rejects blank receipt metadata',
        targetHost: 'staging-east-1',
        runner: 'native-smoke',
        receipt: { receiptId: '   ', source: 'pdd.native-evidence-record.v1', status: 'passed', verifiedBehaviors: ['rejects blank receipt metadata'] },
      },
      {
        behavior: 'suppresses live pager webhook on staging host',
        targetHost: 'staging-east-1',
        runner: 'native-smoke',
        receipt: { receiptId: 'native-ev-3297-smoke-2', source: 'pdd.native-evidence-record.v1', status: 'passed', verifiedBehaviors: ['suppresses live pager webhook on staging host'] },
      },
    ],
  });
  assert.deepEqual(nativeControl.entries.map(e => [e.label, e.creditsNativeBehavior]), [
    ['unverified', false],
    ['unverified', false],
    ['failed', false],
    ['unverified', false],
    ['unverified', false],
    ['verified', true],
  ]);
  assert.deepEqual(nativeControl.credits.nativeVerifiedBehaviors, ['suppresses live pager webhook on staging host']);
  assert.deepEqual(nativeControl.credits.nativeUnverifiedBehaviors, [
    'drains active connections on staging host',
    'rotates webhook signing key on staging host',
    'retries dead-letter delivery on staging host',
    'checks skipped smoke target',
    'rejects blank receipt metadata',
  ]);

  // Empty evidence + overflow cap + forbidden-word sanitization
  const empty = summarizeBoundaryEvidence();
  assert.deepEqual(empty.lines, ['Human boundary card (advisory):', '  Evidence: none']);

  const overflow = summarizeBoundaryEvidence({
    ownerLookups: Array.from({ length: 30 }, (_, idx) => ({
      targetPath: `src/mod-${idx}.mjs`,
      ownerPrompt: `prompts/mod-${idx}.prompt.md`,
      source: 'header',
      certain: true,
    })),
    nativeChecks: [{
      behavior: 'handles batch request Acceptance criteria <details> Agent note',
      targetHost: 'staging-east-1',
      runner: 'native-smoke',
      receipt: null,
    }],
  });
  assert.ok(overflow.lines.length <= BOUNDARY_CARD_MAX_LINES);
  assert.match(overflow.lines.at(-1), /more evidence entries omitted/);
  for (const line of overflow.lines) {
    assert.doesNotMatch(line, /^(?:Text|Approve\s)/);
    assert.doesNotMatch(line, /Acceptance\s+criteria|<details|Agent\s+note|\bbatch\b|\brequest\b/i);
  }
});

test('3297 end-to-end 4-observation card: reads pdd owner, saved pdd lint --local partial record, hosted pdd test assertions, and native receipt for both approve and PR 1', t => {
  const storyText = [
    '# Alert router blackout guard',
    '',
    'As an on-call lead, I want pager alerts suppressed during blackout windows, so that maintenance stays quiet.',
    '',
    '## Acceptance criteria',
    '',
    '1. Suppress outbound pager alerts during an active maintenance blackout window.',
    '2. Record the blackout suppression reason on the alert router result.',
    '',
    '```pdd-boundary',
    'prompts/alert-router.prompt.md',
    '```',
    '',
  ].join('\n');

  const ownerPrompt = runtimePrompt({
    title: 'Alert router',
    prose: 'During an active maintenance blackout window, suppress outbound pager alerts and record the blackout suppression reason on the result.',
    operation: 'route_alert',
    inputProps: { alertId: { type: 'string' }, blackout: { type: 'boolean' } },
    resultSchema: {
      type: 'object',
      properties: { suppressed: { type: 'boolean' }, reason: { type: 'string' } },
      required: ['suppressed', 'reason'],
      additionalProperties: false,
    },
    resources: [{ name: 'pager', operations: [{ name: 'dispatch' }] }],
  });

  const prodCode = [
    '// Generated from prompts/alert-router.prompt.md',
    'export function routeAlert({ blackout }) {',
    '  return blackout ? { suppressed: true, reason: "maintenance_blackout" } : { suppressed: false, reason: "" };',
    '}',
    '',
  ].join('\n');

  const scenario = {
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/alert-router.md',
    criteria: [
      { id: 'AC1', text: 'Suppress outbound pager alerts during an active maintenance blackout window.' },
      { id: 'AC2', text: 'Record the blackout suppression reason on the alert router result.' },
    ],
    initial_world: {},
    steps: [{
      step_id: 'blackout-suppress',
      entry_path: 'prompts/alert-router.prompt.md',
      operation: 'route_alert',
      input: { alertId: 'a-1', blackout: true },
      checks: [
        { criterion_id: 'AC1', target: 'calls', path: '/resources/pager/dispatch', op: 'equals', value: 0 },
        { criterion_id: 'AC2', target: 'result', path: '/reason', op: 'equals', value: 'maintenance_blackout' },
      ],
    }],
  };

  const { root, stateDir } = makeGitRepo(t, {
    'user_stories/alert-router.md': storyText,
    'prompts/alert-router.prompt.md': ownerPrompt,
    'src/alert-router.mjs': prodCode,
    'tests/alert-router.json': JSON.stringify(scenario, null, 2),
  });

  // 1) Saved pdd lint --local partial batch (exit 0, 0 warnings, 0 problems, complete summary.json)
  const localBatchId = '20261118-100000-loc1';
  const localDir = join(stateDir, 'batches', localBatchId);
  mkdirSync(localDir, { recursive: true });
  const localReason = { code: 'local-only', message: 'checked SVG layout only; prompts not checked' };
  const localScope = { tests: ['tests/alert-router.json'], prompts: ['prompts/alert-router.prompt.md'] };
  const localSummaryLine = 'partial: checked SVG layout only; prompts not checked (local-only). 0 warnings. 0 AI calls. No checks were sent.';
  writeFileSync(join(localDir, 'batch.json'), JSON.stringify({
    version: 1,
    batch: localBatchId,
    root,
    created_at: '2026-11-18T10:00:00Z',
    intent: 'lint-only',
    local_only: true,
    source_sha256: null,
    local_scope: localScope,
    summary_line: localSummaryLine,
    exit_code: 0,
    warnings: [],
    problems: [],
    rows: [],
    lint: { state: 'partial', lint_state: 'partial', reason: localReason, request_ids: [] },
  }));
  writeFileSync(join(localDir, 'summary.json'), JSON.stringify({
    batch: localBatchId,
    repo: root,
    exit_code: 0,
    state: 'partial',
    lint_state: 'partial',
    reason: localReason,
    local_only: true,
    local_scope: localScope,
    summary_line: localSummaryLine,
    warnings: [],
    problems: [],
    rows: [],
    report_url: null,
  }));

  // 2) Saved hosted pdd test batch passing both modeled assertions
  const hostedBatchId = '20261118-100500-hst1';
  const hostedReqId = '55555555-5555-4555-8555-555555555555';
  const hostedDir = join(stateDir, 'batches', hostedBatchId);
  mkdirSync(hostedDir, { recursive: true });
  writeFileSync(join(hostedDir, 'batch.json'), JSON.stringify({
    version: 1,
    batch: hostedBatchId,
    intent: 'check',
    root,
    created_at: '2026-11-18T10:05:00Z',
    rows: [{ test: 'tests/alert-router.json', story: 'user_stories/alert-router.md', request_ids: [hostedReqId], ended_at: Date.UTC(2026, 10, 18, 10, 5) }],
  }));
  writeFileSync(join(hostedDir, `${hostedReqId}.json`), JSON.stringify({
    id: hostedReqId,
    requestId: hostedReqId,
    command: 'check',
    state: 'passed',
    result: {
      report: {
        samples: [{
          steps: [{
            step_id: 'blackout-suppress',
            result: { suppressed: true, reason: 'maintenance_blackout' },
            calls: { pager: { dispatch: [] } },
            checks: [
              { criterion_id: 'AC1', target: 'calls', path: '/resources/pager/dispatch', passed: true, actual: 0 },
              { criterion_id: 'AC2', target: 'result', path: '/reason', passed: true },
            ],
          }],
        }],
      },
    },
  }));

  // 3) Saved native smoke receipt in .git/pdd/runs
  const runDir = join(root, '.git', 'pdd', 'runs', '3297-smoke');
  mkdirSync(runDir, { recursive: true });
  writeFileSync(join(runDir, 'status.json'), JSON.stringify({
    v: 1,
    runId: 'native-ev-3297-smoke-1',
    root,
    evidence: [{
      native: {
        schema: 'pdd.native-evidence-record.v1',
        runId: 'native-ev-3297-smoke-1',
        receiptId: 'native-ev-3297-smoke-1',
        profileId: 'native-smoke',
        runner: 'native-smoke',
        targetHost: 'staging-east-1',
        storyPath: 'user_stories/alert-router.md',
        status: 'passed',
        verifiedBehaviors: ['suppresses live pager webhook on staging host'],
      },
    }],
  }));

  const card = buildHumanBoundaryCard({
    root,
    promptPaths: ['prompts/alert-router.prompt.md'],
    storyPaths: ['user_stories/alert-router.md'],
    changedPaths: ['src/alert-router.mjs', 'prompts/alert-router.prompt.md', 'user_stories/alert-router.md', 'tests/alert-router.json'],
    env: { PDD_STATE_DIR: stateDir },
  });

  const ev = card.evidenceSummary;
  assert.equal(ev.entries.length, 4);
  assert.deepEqual(ev.entries.map(e => [e.kind, e.label]), [
    ['owner-resolution', 'resolved'],
    ['local-lint', 'partial'],
    ['hosted-story', 'passed'],
    ['native-check', 'verified'],
  ]);
  assert.deepEqual(ev.credits.resolvedOwners, ['prompts/alert-router.prompt.md']);
  assert.equal(ev.credits.localLintPartial, true);
  assert.equal(ev.credits.localLintCreditsPromptRules, false);
  assert.equal(ev.credits.hostedPassedAssertions.length, 2);
  assert.deepEqual(ev.credits.nativeVerifiedBehaviors, ['suppresses live pager webhook on staging host']);
  assert.deepEqual(ev.credits.nativeUnverifiedBehaviors, []);

  // Verify approve card rendering (<= 25 lines, all 4 observations visible)
  const approveLines = formatApproveBoundaryCard(card);
  assert.ok(approveLines.length <= BOUNDARY_CARD_MAX_LINES, `Approve card exceeded 25 lines: ${approveLines.length}`);
  const approveText = approveLines.join('\n');
  assert.match(approveText, /Evidence:/);
  assert.match(approveText, /owner-resolution \[resolved\].*prompts\/alert-router\.prompt\.md.*pdd owner \(header\)/);
  assert.match(approveText, /local lint \[partial\] \(exit 0\).*SVG layout only; prompt rules not checked.*pdd lint --local/);
  assert.match(approveText, /hosted-story \[passed\].*modeled policy assertions \(2\/2\).*AC1:.*pdd test \(hosted\): user_stories\/alert-router\.md/);
  assert.match(approveText, /native-check \[verified\].*staging-east-1.*native-ev-3297-smoke-1.*pdd\.native-evidence-record\.v1/);

  // Verify PR 1 readable top rendering (<= 25 lines, inert Markdown, all 4 observations visible)
  const prTop = readablePrTop(specFactsWithBoundary(card));
  const prBoundaryLines = extractPrBoundarySection(prTop.text);
  assert.ok(prBoundaryLines.length <= BOUNDARY_CARD_MAX_LINES, `PR Boundary exceeded 25 lines: ${prBoundaryLines.length}`);
  const prBoundaryText = prBoundaryLines.join('\n');
  assert.match(prBoundaryText, /- \*\*Evidence:\*\*/);
  assert.match(prBoundaryText, /owner-resolution \[resolved\u200b?\].*prompts\/alert-router\.prompt\.md/);
  assert.match(prBoundaryText, /local lint \[partial\] \(exit 0\).*SVG layout only; prompt rules not checked/);
  assert.match(prBoundaryText, /hosted-story \[passed\].*modeled policy assertions \(2\/2\)/);
  assert.match(prBoundaryText, /native-check \[verified\].*native-ev-3297-smoke-1/);
  assert.equal(prTop.text.match(/https:\/\//g)?.length ?? 0, 1);
  assert.doesNotMatch(prTop.text, /Acceptance criteria|<details|Agent note|\bbatch\b|\brequest\b/i);

  // Incomplete local save (mismatched summary.json) stays partial with explicit incomplete-save scope
  writeFileSync(join(localDir, 'summary.json'), JSON.stringify({ corrupted: true }));
  const incompleteCard = buildHumanBoundaryCard({
    root,
    promptPaths: ['prompts/alert-router.prompt.md'],
    storyPaths: ['user_stories/alert-router.md'],
    changedPaths: ['src/alert-router.mjs', 'prompts/alert-router.prompt.md', 'user_stories/alert-router.md', 'tests/alert-router.json'],
    env: { PDD_STATE_DIR: stateDir },
  });
  const localEntry = incompleteCard.evidenceSummary.entries.find(e => e.kind === 'local-lint');
  assert.equal(localEntry.label, 'partial');
  assert.equal(localEntry.creditsPromptRules, false);
  assert.match(localEntry.scope, /incomplete local save; prompt rules not checked/);
});

test('3297 negative controls: bare Native validation heading and unverified native receipts give zero native credit; unloaded pdd-owner prompt marks hosted run unconnected; compaction preserves critical gaps', t => {
  const storyText = [
    '# Unreceipted webhook guard',
    '',
    'As a security lead, I want webhook egress verified by a real native receipt, so that unverified headings cannot fake native proof.',
    '',
    '## Acceptance criteria',
    '',
    '1. Suppress outbound webhook dispatch during security lockdown.',
    '',
    '## Native validation',
    '',
    '- Target host smoke test (not yet executed).',
    '',
  ].join('\n');

  const simPrompt = runtimePrompt({
    title: 'Webhook simulator',
    prose: 'Simulate security lockdown and return an effects array describing outbound webhook dispatch.',
    operation: 'sim_webhook',
    inputProps: { lockdown: { type: 'boolean' } },
    resultSchema: {
      type: 'object',
      properties: { effects: { type: 'array', items: { type: 'string' } } },
      required: ['effects'],
      additionalProperties: false,
    },
  });

  const realOwnerPrompt = runtimePrompt({
    title: 'Webhook egress owner',
    prose: 'During security lockdown, never dispatch outbound webhook notifications.',
    operation: 'dispatch_webhook',
    inputProps: { lockdown: { type: 'boolean' } },
  });

  const prodCode = '// Generated from prompts/webhook-owner.prompt.md\nexport const dispatchWebhook = () => [];\n';

  const scenario = {
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/webhook-guard.md',
    criteria: [{ id: 'AC1', text: 'Suppress outbound webhook dispatch during security lockdown.' }],
    initial_world: {},
    steps: [{
      step_id: 'lockdown',
      entry_path: 'prompts/webhook-sim.prompt.md',
      operation: 'sim_webhook',
      input: { lockdown: true },
      checks: [{ criterion_id: 'AC1', target: 'result', path: '/effects', op: 'equals', value: [] }],
    }],
  };

  const { root, stateDir } = makeGitRepo(t, {
    'user_stories/webhook-guard.md': storyText,
    'prompts/webhook-sim.prompt.md': simPrompt,
    'prompts/webhook-owner.prompt.md': realOwnerPrompt,
    'src/webhook-owner.mjs': prodCode,
    'tests/webhook-guard.json': JSON.stringify(scenario, null, 2),
  });

  // Hosted run passed on webhook-sim while real pdd-owner prompt webhook-owner.prompt.md was never loaded!
  const batchId = '20261118-110000-unc1';
  const reqId = '66666666-6666-4666-8666-666666666666';
  mkdirSync(join(stateDir, 'batches', batchId), { recursive: true });
  writeFileSync(join(stateDir, 'batches', batchId, 'batch.json'), JSON.stringify({
    version: 1,
    batch: batchId,
    intent: 'check',
    root,
    created_at: '2026-11-18T11:00:00Z',
    rows: [{ test: 'tests/webhook-guard.json', story: 'user_stories/webhook-guard.md', request_ids: [reqId], ended_at: Date.UTC(2026, 10, 18, 11, 0) }],
  }));
  writeFileSync(join(stateDir, 'batches', batchId, `${reqId}.json`), JSON.stringify({
    id: reqId,
    requestId: reqId,
    command: 'check',
    state: 'passed',
    result: {
      report: {
        samples: [{ steps: [{ step_id: 'lockdown', result: { effects: [] }, checks: [{ criterion_id: 'AC1', passed: true }] }] }],
      },
    },
  }));

  // Saved native record with intake.admission="unverified" must NOT grant native execution credit
  const runDir = join(root, '.git', 'pdd', 'runs', '3297-unverified');
  mkdirSync(runDir, { recursive: true });
  writeFileSync(join(runDir, 'status.json'), JSON.stringify({
    v: 1,
    runId: 'native-ev-unverified',
    root,
    evidence: [{
      native: {
        schema: 'pdd.native-evidence-record.v1',
        runId: 'native-ev-unverified',
        profileId: 'native-smoke',
        storyPath: 'user_stories/webhook-guard.md',
        intake: { admission: 'unverified' },
      },
    }],
  }));

  const card = buildHumanBoundaryCard({
    root,
    storyPaths: ['user_stories/webhook-guard.md'],
    changedPaths: ['src/webhook-owner.mjs', 'user_stories/webhook-guard.md', 'tests/webhook-guard.json'],
    env: { PDD_STATE_DIR: stateDir },
  });

  // Bare ## Native validation heading stays in verificationSplit.native, NEVER grants 'native test' credit
  assert.ok(card.verificationSplit.native.some(entry => entry.includes('user_stories/webhook-guard.md (Native validation)')));
  const ac1 = card.provenanceRows.find(r => r.label === 'AC1');
  assert.ok(!ac1.observations.includes('native test'), `Bare Native validation heading or unverified receipt must not grant native test credit: ${ac1.observations}`);
  assert.ok(
    ac1.observations.some(o => o.includes('port spy or native observation still needed')),
    `Bare Native validation heading must not suppress port/native warning: ${ac1.observations}`,
  );

  // pdd owner resolved prompts/webhook-owner.prompt.md from changed src/webhook-owner.mjs -> unloaded -> hosted run marked unconnected
  assert.ok(card.unloadedOwners.includes('prompts/webhook-owner.prompt.md'));
  const hostedEntry = card.evidenceSummary.entries.find(e => e.kind === 'hosted-story');
  assert.equal(hostedEntry.label, 'unconnected');
  assert.equal(hostedEntry.creditsModeledAssertions, false);
  assert.equal(hostedEntry.creditsPromptRules, false);
  assert.deepEqual(card.evidenceSummary.credits.hostedPassedAssertions, []);

  // Unverified saved native record gets zero native credit
  const nativeEntry = card.evidenceSummary.entries.find(e => e.kind === 'native-check');
  assert.equal(nativeEntry.label, 'unverified');
  assert.equal(nativeEntry.creditsNativeBehavior, false);
  assert.deepEqual(card.evidenceSummary.credits.nativeVerifiedBehaviors, []);

  // Compaction priority: critical evidence gaps + missing owner connection survive <= 25-line cap
  const heavyCard = {
    ...card,
    provenanceRows: [
      ...Array.from({ length: 18 }, (_, i) => ({
        label: `AC${i + 2}`,
        summary: `ordinary check ${i + 2}`,
        owner: 'prompts/webhook-owner.prompt.md',
        missingConnection: false,
        observations: ['model-returned value'],
        priority: 3,
      })),
      {
        label: 'AC1',
        summary: 'critical owner gap',
        owner: 'missing owner connection (unloaded prompts/webhook-owner.prompt.md)',
        missingConnection: true,
        observations: ['model-returned value (port spy or native observation still needed)'],
        priority: 0,
      },
    ],
    evidenceSummary: summarizeBoundaryEvidence({
      ownerLookups: Array.from({ length: 12 }, (_, i) => ({
        targetPath: `src/extra-${i}.mjs`,
        ownerPrompt: `prompts/extra-${i}.prompt.md`,
        source: 'header',
        certain: true,
      })),
      localLint: { exitCode: 0, state: 'passed', localOnly: true, scope: 'SVG layout only', warningCount: 0, problemCount: 0, incompleteSave: false, inspectedPrompts: [], inspectedTests: [] },
      nativeChecks: [{ behavior: 'Fixes #999 @oncall https://evil.example.test/leak unverified smoke', targetHost: 'staging-east-1', runner: 'native-smoke', receipt: null }],
    }),
  };

  const compactApprove = formatApproveBoundaryCard(heavyCard);
  assert.ok(compactApprove.length <= BOUNDARY_CARD_MAX_LINES, `Compact approve card exceeded 25 lines: ${compactApprove.length}`);
  const compactApproveText = compactApprove.join('\n');
  assert.match(compactApproveText, /local lint \[partial\]/);
  assert.match(compactApproveText, /native-check \[unverified\]/);
  assert.match(compactApproveText, /missing owner connection/);
  assert.match(compactApproveText, /Verification split:/);
  assert.match(compactApproveText, /Budget & samples:/);

  const compactPrTop = readablePrTop(specFactsWithBoundary(heavyCard));
  const compactPrLines = extractPrBoundarySection(compactPrTop.text);
  assert.ok(compactPrLines.length <= BOUNDARY_CARD_MAX_LINES, `Compact PR Boundary exceeded 25 lines: ${compactPrLines.length}`);
  const compactPrText = compactPrLines.join('\n');
  assert.match(compactPrText, /local lint \[partial\]/);
  assert.match(compactPrText, /native-check \[unverified\]/);
  assert.match(compactPrText, /missing owner connection/);
  assert.doesNotMatch(compactPrTop.text, /Fixes #999|@oncall|<details|Acceptance criteria|\bbatch\b|\brequest\b/i);
  assert.equal(compactPrTop.text.match(/https:\/\//g)?.length ?? 0, 1);
});



