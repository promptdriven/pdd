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

