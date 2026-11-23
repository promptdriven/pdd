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

  // 3) Multi-prompt buildHumanBoundaryCard renders in <= 25 lines and flags unloaded sibling prompts & model-returned effects.
  const boundary = buildHumanBoundaryCard({
    root,
    promptPaths: ['prompts/simulator.prompt.md', 'prompts/impl.prompt.md', 'prompts/guide.prompt.md'],
    storyPaths: ['user_stories/link-outage.md'],
    env: { PDD_STATE_DIR: stateDir },
  });
  const cardLines = formatApproveBoundaryCard(boundary);
  assert.ok(cardLines.length <= BOUNDARY_CARD_MAX_LINES, `Boundary card exceeded 25 lines: ${cardLines.length}`);
  const cardText = cardLines.join('\n');
  assert.match(cardText, /missing owner connection/);
  assert.match(cardText, /prompts\/impl\.prompt\.md/);
  assert.match(cardText, /prompts\/guide\.prompt\.md/);
  assert.match(cardText, /model-returned value.*port spy or native observation still needed/);
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
});

test('3297 single-prompt rule-removal acceptance control flags missing owner connection and unloaded changed prompts', async t => {
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
  // Also add an unloaded changed implementation prompt and commit on topic branch to verify unloaded owner flagging!
  writeFileSync(join(root, 'prompts/session-drainer.prompt.md'), '# Session drainer\n\nDrain active customer sessions gracefully.\n');
  git('add', '.');
  git('commit', '-qm', 'prompt slice');

  const disconnected = buildHumanBoundaryCard({
    root,
    promptPaths: ['prompts/failover.prompt.md', 'prompts/session-drainer.prompt.md'],
    storyPaths: ['user_stories/drain.md'],
    env: { PDD_STATE_DIR: stateDir },
  });
  assert.equal(disconnected.provenanceRows[0].missingConnection, true);
  assert.ok(disconnected.unloadedOwners.includes('prompts/session-drainer.prompt.md'));
  const formattedLines = formatApproveBoundaryCard(disconnected);
  assert.ok(formattedLines.length <= BOUNDARY_CARD_MAX_LINES);
  const formattedText = formattedLines.join('\n');
  assert.match(formattedText, /missing owner connection/);
  assert.match(formattedText, /prompts\/session-drainer\.prompt\.md/);
  assert.match(formattedText, /model-returned value.*port spy or native observation still needed/);
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

test('M1 regression: runtime-seam runTry wires formatBoundaryCardLines into Try approvals without creating architecture cycles', async t => {
  const { runTry } = await import('../src/runtime-seam.mjs');
  const storyText = [
    '# Checkout order',
    '',
    'As a shopper, I want my order total validated before charging, so that negative amounts fail safely.',
    '',
    '## Acceptance criteria',
    '',
    '1. Reject negative totals without charging the payment port.',
    '',
  ].join('\n');
  const promptText = runtimePrompt({
    title: 'Checkout',
    prose: 'Reject negative totals without calling payment.charge.',
    operation: 'checkout',
    inputProps: { total: { type: 'integer' } },
  });
  const { root, stateDir } = makeGitRepo(t, {
    'user_stories/checkout.md': storyText,
    'prompts/checkout.prompt.md': promptText,
  });

  let capturedAskApproval = null;
  const tryExit = await runTry(
    { cwd: root, words: ['checkout'], options: { '--no-open': true } },
    {
      env: { ...process.env, PDD_STATE_DIR: stateDir },
      runTry: async (_input, boundPorts) => {
        capturedAskApproval = boundPorts.askApproval;
        return 0;
      },
    },
  );
  assert.equal(tryExit, 0);
  assert.equal(typeof capturedAskApproval, 'function');

  let out = '';
  const approvalRes = await capturedAskApproval({
    root,
    path: 'prompts/checkout.prompt.md',
    stdout: new Writable({ write(chunk, _enc, done) { out += chunk; done(); } }),
    answers: { ask: async () => 'n', close() {} },
  });
  assert.equal(approvalRes.state, 'declined');
  const cardLines = extractApproveBoundaryCard(out);
  assert.ok(cardLines.length >= 2, `Expected rendered Try boundary card lines, got:\n${out}`);
  assert.ok(cardLines.length <= BOUNDARY_CARD_MAX_LINES);
});


