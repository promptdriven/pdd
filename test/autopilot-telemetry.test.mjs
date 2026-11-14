import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {
  AUTOPILOT_PHASES,
  CACHED_TOKEN_WEIGHT,
  DAILY_CAPACITY_TARGETS,
  DEFAULT_TIER_PROFILES,
  buildTieredAgentArgs,
  classifyStepTier,
  createPhaseTracker,
  estimateDailyCapacity,
  extractHarnessTokens,
  isModelTieringEnabled,
  normalizeAutopilotPhase,
  recordPhaseSpan,
  resolveStepModelTier,
  summarizeIssuePhases,
  summarizeIssueTelemetry,
} from '../src/autopilot-telemetry.mjs';

test('3154 canonical phases and aliases normalize cleanly without mutating caller spans', () => {
  assert.deepEqual(AUTOPILOT_PHASES, [
    'intake', 'improve', 'story/pr1', 'code/pr2', 'repair', 'check', 'ci-wait', 'merge',
  ]);
  for (const [alias, expected] of [
    ['intake', 'intake'],
    ['triage', 'intake'],
    ['improve', 'improve'],
    ['story', 'story/pr1'],
    ['pr1', 'story/pr1'],
    ['small-change', 'story/pr1'],
    ['code', 'code/pr2'],
    ['pr2', 'code/pr2'],
    ['rebase', 'repair'],
    ['review', 'check'],
    ['independent-review', 'check'],
    ['ci', 'ci-wait'],
    ['publish', 'merge'],
  ]) {
    assert.equal(normalizeAutopilotPhase(alias), expected);
  }
  assert.equal(normalizeAutopilotPhase(''), null);
  assert.equal(normalizeAutopilotPhase('unknown-phase'), null);

  const initial = { issue: 3154, repo: 'promptdriven/pdd', spans: [] };
  const updated = recordPhaseSpan(initial, { phase: 'story', startedAt: 1000, endedAt: 61_000, machine: 'mac-mini' });
  assert.equal(initial.spans.length, 0);
  assert.equal(updated.spans.length, 1);
  assert.equal(updated.spans[0].phase, 'story/pr1');
  assert.equal(updated.spans[0].durationMs, 60_000);
});

test('3154 phase tracker and multi-machine summary distinguish total phase duration from overlapping wall-clock time', () => {
  let clock = 10_000;
  const tracker = createPhaseTracker({
    issue: 3154,
    repo: 'promptdriven/pdd',
    machine: 'vm-1',
    now: () => clock,
  });

  tracker.startPhase('intake');
  clock += 30_000;
  tracker.finishPhase('intake');

  tracker.startPhase('improve');
  clock += 45_000;
  tracker.finishPhase('improve');

  // Parallel check on vm-2 overlapping with ci-wait on vm-1
  tracker.recordSpan({ phase: 'story/pr1', startedAt: 100_000, endedAt: 400_000, machine: 'vm-1' });
  tracker.recordSpan({ phase: 'code/pr2', startedAt: 400_000, endedAt: 880_000, machine: 'vm-1' });
  tracker.recordSpan({ phase: 'repair', startedAt: 880_000, endedAt: 940_000, machine: 'vm-2' });
  tracker.recordSpan({ phase: 'check', startedAt: 940_000, endedAt: 1_180_000, machine: 'vm-2' });
  tracker.recordSpan({ phase: 'ci-wait', startedAt: 960_000, endedAt: 1_260_000, machine: 'vm-1' });
  tracker.recordSpan({ phase: 'merge', startedAt: 1_260_000, endedAt: 1_290_000, machine: 'vm-1' });

  const summary = tracker.summarize();
  assert.equal(summary.issue, 3154);
  assert.deepEqual(summary.machines, ['vm-1', 'vm-2']);
  assert.equal(summary.phases.length, 8);
  assert.equal(summary.byPhase['code/pr2'].durationMs, 480_000);
  assert.equal(summary.slowestPhase.phase, 'code/pr2');
  // check (240s) and ci-wait (300s) overlap by 220s -> wallClockMs is 220_000ms less than totalDurationMs
  assert.equal(summary.totalDurationMs - summary.wallClockMs, 220_000);
});

test('3154 extractHarnessTokens parses Codex JSONL turns and deduplicates cumulative rollout token_count events', () => {
  const execStream = [
    '{"type":"thread.started","thread_id":"t1"}',
    'non-json progress banner',
    JSON.stringify({ type: 'turn.completed', usage: { input_tokens: 12_000, cached_input_tokens: 9_000, output_tokens: 1_500, reasoning_output_tokens: 600 } }),
    JSON.stringify({ type: 'turn.completed', usage: { input_tokens: 8_000, cached_input_tokens: 6_000, output_tokens: 1_000, reasoning_output_tokens: 400 } }),
  ].join('\n');

  const execUsage = extractHarnessTokens(execStream);
  assert.equal(execUsage.agent, 'codex');
  assert.equal(execUsage.observed, true);
  assert.equal(execUsage.turns, 2);
  assert.equal(execUsage.inputTokens, 20_000);
  assert.equal(execUsage.cachedInputTokens, 15_000);
  assert.equal(execUsage.uncachedInputTokens, 5_000);
  assert.equal(execUsage.outputTokens, 2_500);
  assert.equal(execUsage.reasoningTokens, 1_000);
  assert.equal(execUsage.totalTokens, 22_500);
  assert.equal(execUsage.cacheHitShare, 0.75);
  assert.equal(execUsage.effectiveTokens, 5_000 + 15_000 * CACHED_TOKEN_WEIGHT + 2_500);

  const rolloutStream = [
    JSON.stringify({ type: 'event_msg', payload: { type: 'token_count', info: { total_token_usage: { input_tokens: 10_000, cached_input_tokens: 7_000, output_tokens: 900, reasoning_output_tokens: 300, total_tokens: 10_900 } } } }),
    JSON.stringify({ type: 'event_msg', payload: { type: 'token_count', info: { total_token_usage: { input_tokens: 25_000, cached_input_tokens: 20_000, output_tokens: 2_100, reasoning_output_tokens: 800, total_tokens: 27_100 } } } }),
  ].join('\n');

  const rolloutUsage = extractHarnessTokens(rolloutStream);
  assert.equal(rolloutUsage.agent, 'codex');
  assert.equal(rolloutUsage.inputTokens, 25_000);
  assert.equal(rolloutUsage.cachedInputTokens, 20_000);
  assert.equal(rolloutUsage.outputTokens, 2_100);
  assert.equal(rolloutUsage.totalTokens, 27_100);
});

test('3154 extractHarnessTokens deduplicates Claude Code streaming message chunks and result envelopes', () => {
  const claudeStream = [
    JSON.stringify({ type: 'message_start', message: { id: 'm-1', usage: { input_tokens: 2_000, cache_creation_input_tokens: 1_000, cache_read_input_tokens: 7_000, output_tokens: 1 } } }),
    JSON.stringify({ type: 'message_delta', usage: { output_tokens: 450 } }),
    JSON.stringify({ type: 'assistant', message: { id: 'm-2', usage: { input_tokens: 1_500, cache_creation_input_tokens: 500, cache_read_input_tokens: 8_000, output_tokens: 550 } } }),
    JSON.stringify({ type: 'result', is_error: false, usage: { input_tokens: 3_500, cache_creation_input_tokens: 1_500, cache_read_input_tokens: 15_000, output_tokens: 1_000 } }),
  ].join('\n');

  const usage = extractHarnessTokens(claudeStream);
  assert.equal(usage.agent, 'claude');
  assert.equal(usage.observed, true);
  assert.equal(usage.turns, 2);
  assert.equal(usage.inputTokens, 20_000);
  assert.equal(usage.cachedInputTokens, 15_000);
  assert.equal(usage.uncachedInputTokens, 5_000);
  assert.equal(usage.outputTokens, 1_000);
  assert.equal(usage.totalTokens, 21_000);
});

test('3154 extractHarnessTokens parses Gemini stats.models and usageMetadata formats', () => {
  const geminiJson = JSON.stringify({
    response: 'Done.',
    stats: {
      models: {
        'gemini-2.5-flash': { tokens: { prompt: 14_000, cached: 10_000, candidates: 1_200, thoughts: 300, total: 15_500 } },
      },
    },
  });
  const gem = extractHarnessTokens(geminiJson);
  assert.equal(gem.agent, 'gemini');
  assert.equal(gem.inputTokens, 14_000);
  assert.equal(gem.cachedInputTokens, 10_000);
  assert.equal(gem.outputTokens, 1_200);
  assert.equal(gem.reasoningTokens, 300);
  assert.equal(gem.totalTokens, 15_500);

  const metaStream = [
    JSON.stringify({ usageMetadata: { promptTokenCount: 5_000, cachedContentTokenCount: 2_000, candidatesTokenCount: 400, thoughtsTokenCount: 100, totalTokenCount: 5_500 } }),
    JSON.stringify({ usageMetadata: { promptTokenCount: 6_000, cachedContentTokenCount: 4_000, candidatesTokenCount: 600, thoughtsTokenCount: 200, totalTokenCount: 6_800 } }),
  ].join('\n');
  const metaUsage = extractHarnessTokens(metaStream);
  assert.equal(metaUsage.agent, 'gemini');
  assert.equal(metaUsage.turns, 2);
  assert.equal(metaUsage.inputTokens, 11_000);
  assert.equal(metaUsage.cachedInputTokens, 6_000);
  assert.equal(metaUsage.outputTokens, 1_000);
  assert.equal(metaUsage.totalTokens, 12_300);
});

test('3154 summarizeIssueTelemetry aggregates multi-harness worker and reviewer streams with phase durations', () => {
  const combined = summarizeIssueTelemetry({
    issue: 3154,
    repo: 'promptdriven/pdd',
    spans: [
      { phase: 'intake', durationMs: 25_000, machine: 'vm-a' },
      { phase: 'small-change', durationMs: 180_000, machine: 'vm-a' },
      { phase: 'check', durationMs: 90_000, machine: 'vm-b' },
    ],
    streams: [
      { step: 'small-change', agent: 'codex', source: JSON.stringify({ type: 'turn.completed', usage: { input_tokens: 10_000, cached_input_tokens: 8_000, output_tokens: 900 } }) },
      { step: 'check', agent: 'claude', source: JSON.stringify({ type: 'result', usage: { input_tokens: 4_000, cache_read_input_tokens: 6_000, output_tokens: 700 } }) },
    ],
  });

  assert.equal(combined.phases.byPhase['story/pr1'].durationMs, 180_000);
  assert.equal(combined.tokens.byTier.worker.inputTokens, 10_000);
  assert.equal(combined.tokens.byTier.reviewer.inputTokens, 10_000);
  assert.equal(combined.tokens.byAgent.codex.outputTokens, 900);
  assert.equal(combined.tokens.byAgent.claude.outputTokens, 700);
  assert.equal(combined.tokens.total.totalTokens, 21_600);
});

test('3782 worker/reviewer tiering stays disabled by default and routes smaller worker vs full reviewer strength when enabled', () => {
  assert.equal(isModelTieringEnabled({}), false);
  assert.equal(isModelTieringEnabled({ env: { PDD_MODEL_TIERING: '1' } }), true);
  assert.equal(classifyStepTier('intake'), 'worker');
  assert.equal(classifyStepTier('improve'), 'worker');
  assert.equal(classifyStepTier('small-change'), 'worker');
  assert.equal(classifyStepTier('worker'), 'worker');
  assert.equal(classifyStepTier('review'), 'reviewer');
  assert.equal(classifyStepTier('check'), 'reviewer');

  // Default disabled: zero model or effort flags added unless explicit model is passed
  const off = resolveStepModelTier({ agent: 'codex', step: 'intake' });
  assert.equal(off.enabled, false);
  assert.deepEqual(buildTieredAgentArgs(off), []);
  assert.deepEqual(
    buildTieredAgentArgs({ agent: 'codex', step: 'intake', model: 'custom-model' }),
    ['--model', 'custom-model'],
  );

  // Enabled for Codex worker vs reviewer
  const codexWorker = resolveStepModelTier({ agent: 'codex', step: 'improve', tiering: true });
  assert.equal(codexWorker.enabled, true);
  assert.equal(codexWorker.tier, 'worker');
  assert.equal(codexWorker.model, DEFAULT_TIER_PROFILES.codex.worker.model);
  assert.equal(codexWorker.reasoningEffort, 'medium');
  assert.deepEqual(buildTieredAgentArgs(codexWorker), [
    '--model', DEFAULT_TIER_PROFILES.codex.worker.model,
    '-c', 'model_reasoning_effort="medium"',
  ]);

  const codexReviewer = resolveStepModelTier({ agent: 'codex', step: 'check', tiering: { enabled: true } });
  assert.equal(codexReviewer.tier, 'reviewer');
  assert.equal(codexReviewer.model, DEFAULT_TIER_PROFILES.codex.reviewer.model);
  assert.equal(codexReviewer.reasoningEffort, 'high');
  assert.deepEqual(buildTieredAgentArgs(codexReviewer), [
    '--model', DEFAULT_TIER_PROFILES.codex.reviewer.model,
    '-c', 'model_reasoning_effort="high"',
  ]);

  // Claude Code & Gemini CLI flag shapes
  assert.deepEqual(
    buildTieredAgentArgs({ agent: 'claude', step: 'small-change', tiering: true }),
    ['--model', DEFAULT_TIER_PROFILES.claude.worker.model, '--effort', 'medium'],
  );
  assert.deepEqual(
    buildTieredAgentArgs({ agent: 'claude', step: 'review', tiering: true }),
    ['--model', DEFAULT_TIER_PROFILES.claude.reviewer.model, '--effort', 'high'],
  );
  assert.deepEqual(
    buildTieredAgentArgs({ agent: 'gemini', step: 'worker', tiering: true }),
    ['--model', DEFAULT_TIER_PROFILES.gemini.worker.model],
  );
  assert.deepEqual(
    buildTieredAgentArgs({ agent: 'gemini', step: 'check', tiering: true }),
    ['--model', DEFAULT_TIER_PROFILES.gemini.reviewer.model],
  );

  // Reject unsafe model names or invalid efforts
  assert.throws(() => resolveStepModelTier({ agent: 'codex', step: 'worker', model: '--bad-flag', tiering: true }), /Invalid model name/);
  assert.throws(() => resolveStepModelTier({ agent: 'codex', step: 'worker', reasoningEffort: 'turbo', tiering: true }), /Invalid reasoning effort/);
});

test('3154 & 3782 estimateDailyCapacity models 25, 40, 70, and 80 issues/day and quantifies tiering savings', () => {
  assert.deepEqual(DAILY_CAPACITY_TARGETS, [25, 40, 70, 80]);
  const cap = estimateDailyCapacity({
    availableMachines: 2,
    availableAccounts: 2,
    dailyCiMinuteBudget: 4_000,
  });

  assert.deepEqual(cap.rows.map(r => r.targetIssuesPerDay), [25, 40, 70, 80]);
  for (const row of cap.rows) {
    assert.ok(row.tieredEffectiveTokensPerDay < row.baselineEffectiveTokensPerDay);
    assert.ok(row.tokenSavingsPercent > 40);
    assert.ok(row.accountsNeededTiered <= row.accountsNeededBaseline);
    assert.ok(row.machinesNeeded >= 1);
    assert.ok(['accounts', 'suite-slots', 'run-slots', 'ci-minutes', 'interpreter-calls'].includes(row.firstBottleneck));
  }
  assert.ok(cap.byTarget[80].interpreterCallsPerDay > cap.byTarget[25].interpreterCallsPerDay);
  assert.ok(cap.byTarget[80].ciMinutesPerDay > cap.byTarget[40].ciMinutesPerDay);
});

test('3154 & 3782 supports all real Autopilot job roles and safely normalizes unknown nonblank phases', () => {
  for (const [role, expectedPhase] of [
    ['build', 'code/pr2'],
    ['implement', 'code/pr2'],
    ['conflict', 'repair'],
    ['rebase', 'repair'],
    ['base-refresh', 'repair'],
    ['review', 'check'],
    ['suite', 'check'],
    ['vectors', 'check'],
    ['runtime', 'check'],
    ['merge-check', 'check'],
    ['improve', 'improve'],
    ['intake', 'intake'],
    ['publish', 'merge'],
  ]) {
    assert.equal(normalizeAutopilotPhase(role), expectedPhase, `expected ${role} -> ${expectedPhase}`);
  }

  for (const step of [
    'build', 'conflict', 'implement', 'rebase', 'base-refresh',
    'prompt', 'prompts', 'triage', 'sort', 'dependencies',
    'groom', 'clarify', 'improve', 'intake', 'repair',
  ]) {
    assert.equal(classifyStepTier(step), 'worker', `expected worker tier for ${step}`);
  }
  for (const step of ['review', 'check', 'independent-review', 'audit', 'merge', 'publish']) {
    assert.equal(classifyStepTier(step), 'reviewer', `expected reviewer tier for ${step}`);
  }

  // Unknown nonblank roles do not throw in recordPhaseSpan / createPhaseTracker / summarizeIssuePhases
  const customLedger = recordPhaseSpan({ issue: 99, machine: 'vm-custom' }, { phase: 'future-role', startedAt: 1000, endedAt: 4000 });
  assert.equal(customLedger.spans[0].phase, 'code/pr2');
  assert.equal(customLedger.spans[0].step, 'future-role');
  assert.equal(customLedger.spans[0].durationMs, 3000);

  let nowMs = 500;
  const tracker = createPhaseTracker({ issue: 99, machine: 'vm-custom', now: () => nowMs });
  tracker.startPhase('future-step');
  nowMs += 2500;
  const doneSpan = tracker.finishPhase('future-step');
  assert.equal(doneSpan.phase, 'code/pr2');
  assert.equal(doneSpan.step, 'future-step');
  assert.equal(doneSpan.durationMs, 2500);

  // Empty or non-string phases are still rejected
  assert.throws(() => recordPhaseSpan({}, { phase: '' }), /Invalid Autopilot phase/);
  assert.throws(() => recordPhaseSpan({}, { phase: '   ' }), /Invalid Autopilot phase/);
  assert.throws(() => recordPhaseSpan({}, { phase: null }), /Invalid Autopilot phase/);
  assert.throws(() => tracker.startPhase(''), /Invalid Autopilot phase/);
});

test('3154 extractHarnessTokens handles Codex total+last turns, session resets, Claude message-only vs multi-result, Gemini multi-stats, and agy', () => {
  // Codex token_count events carrying BOTH total_token_usage and last_token_usage + duplicate snapshot + concatenated session reset
  const codexConcatStream = [
    JSON.stringify({
      type: 'event_msg',
      payload: {
        type: 'token_count',
        info: {
          total_token_usage: { input_tokens: 10_000, cached_input_tokens: 6_000, output_tokens: 800, reasoning_output_tokens: 200, total_tokens: 10_800 },
          last_token_usage: { input_tokens: 10_000, cached_input_tokens: 6_000, output_tokens: 800, reasoning_output_tokens: 200, total_tokens: 10_800 },
        },
      },
    }),
    // Duplicate snapshot at same cumulative counts should not inflate turns
    JSON.stringify({
      type: 'event_msg',
      payload: {
        type: 'token_count',
        info: {
          total_token_usage: { input_tokens: 10_000, cached_input_tokens: 6_000, output_tokens: 800, reasoning_output_tokens: 200, total_tokens: 10_800 },
          last_token_usage: { input_tokens: 10_000, cached_input_tokens: 6_000, output_tokens: 800, reasoning_output_tokens: 200, total_tokens: 10_800 },
        },
      },
    }),
    JSON.stringify({
      type: 'event_msg',
      payload: {
        type: 'token_count',
        info: {
          total_token_usage: { input_tokens: 22_000, cached_input_tokens: 15_000, output_tokens: 1_700, reasoning_output_tokens: 500, total_tokens: 23_700 },
          last_token_usage: { input_tokens: 12_000, cached_input_tokens: 9_000, output_tokens: 900, reasoning_output_tokens: 300, total_tokens: 12_900 },
        },
      },
    }),
    // Concatenated second session resets cumulative total downward -> bank 22k/1.7k and add 5k/400
    JSON.stringify({
      type: 'event_msg',
      payload: {
        type: 'token_count',
        info: {
          total_token_usage: { input_tokens: 5_000, cached_input_tokens: 2_000, output_tokens: 400, reasoning_output_tokens: 100, total_tokens: 5_400 },
          last_token_usage: { input_tokens: 5_000, cached_input_tokens: 2_000, output_tokens: 400, reasoning_output_tokens: 100, total_tokens: 5_400 },
        },
      },
    }),
  ].join('\n');
  const codexReset = extractHarnessTokens(codexConcatStream);
  assert.equal(codexReset.agent, 'codex');
  assert.equal(codexReset.turns, 3);
  assert.equal(codexReset.inputTokens, 27_000);
  assert.equal(codexReset.cachedInputTokens, 17_000);
  assert.equal(codexReset.outputTokens, 2_100);
  assert.equal(codexReset.reasoningTokens, 600);
  assert.equal(codexReset.totalTokens, 29_100);

  // Claude: when per-message rows exist, ignore inflated result envelope; when absent, sum multiple result envelopes
  const claudeMsgPreferred = [
    JSON.stringify({ type: 'assistant', message: { id: 'msg-1', usage: { input_tokens: 1_000, cache_read_input_tokens: 3_000, output_tokens: 250 } } }),
    JSON.stringify({ type: 'result', usage: { input_tokens: 50_000, cache_read_input_tokens: 50_000, output_tokens: 9_000 } }),
  ].join('\n');
  const claudeFromMsgs = extractHarnessTokens(claudeMsgPreferred);
  assert.equal(claudeFromMsgs.turns, 1);
  assert.equal(claudeFromMsgs.inputTokens, 4_000);
  assert.equal(claudeFromMsgs.outputTokens, 250);

  const claudeTwoResults = [
    JSON.stringify({ type: 'result', usage: { input_tokens: 2_000, cache_read_input_tokens: 1_000, output_tokens: 300 } }),
    JSON.stringify({ type: 'result', usage: { input_tokens: 4_000, cache_read_input_tokens: 2_000, output_tokens: 500 } }),
  ].join('\n');
  const claudeResultSum = extractHarnessTokens(claudeTwoResults);
  assert.equal(claudeResultSum.turns, 2);
  assert.equal(claudeResultSum.inputTokens, 9_000);
  assert.equal(claudeResultSum.cachedInputTokens, 3_000);
  assert.equal(claudeResultSum.outputTokens, 800);

  // Gemini: sum multiple separate stats envelopes when usageMetadata is absent
  const geminiTwoStats = [
    JSON.stringify({ stats: { models: { 'gemini-2.5-flash': { tokens: { prompt: 3_000, cached: 1_000, candidates: 200, thoughts: 50, total: 3_250 } } } } }),
    JSON.stringify({ result: { stats: { models: { 'gemini-2.5-pro': { tokens: { prompt: 5_000, cached: 2_000, candidates: 400, thoughts: 100, total: 5_500 } } } } } }),
  ].join('\n');
  const geminiSummed = extractHarnessTokens(geminiTwoStats);
  assert.equal(geminiSummed.turns, 2);
  assert.equal(geminiSummed.inputTokens, 8_000);
  assert.equal(geminiSummed.cachedInputTokens, 3_000);
  assert.equal(geminiSummed.outputTokens, 600);
  assert.equal(geminiSummed.reasoningTokens, 150);
  assert.equal(geminiSummed.totalTokens, 8_750);

  // Unobserved streams excluded from byAgent, and 'agy' preserved distinctly from 'gemini'
  const telemetry = summarizeIssueTelemetry({
    issue: 3154,
    repo: 'promptdriven/pdd',
    spans: { machine: 'vm-main', spans: [{ phase: 'build', startedAt: 0, endedAt: 120_000, durationMs: 45_000 }] },
    streams: [
      { step: 'suite', agent: 'codex', source: '' },
      { step: 'build', agent: 'agy', source: JSON.stringify({ usageMetadata: { promptTokenCount: 4_000, cachedContentTokenCount: 1_000, candidatesTokenCount: 300, thoughtsTokenCount: 50, totalTokenCount: 4_350 } }) },
      { step: 'review', agent: 'gemini', source: JSON.stringify({ usageMetadata: { promptTokenCount: 6_000, cachedContentTokenCount: 2_000, candidatesTokenCount: 500, thoughtsTokenCount: 100, totalTokenCount: 6_600 } }) },
    ],
  });
  assert.equal(Object.hasOwn(telemetry.tokens.byAgent, 'codex'), false, 'unobserved empty stream must not populate byAgent');
  assert.equal(telemetry.tokens.byAgent.agy.agent, 'agy');
  assert.equal(telemetry.tokens.byAgent.agy.inputTokens, 4_000);
  assert.equal(telemetry.tokens.byAgent.gemini.agent, 'gemini');
  assert.equal(telemetry.tokens.byAgent.gemini.inputTokens, 6_000);
  assert.deepEqual(telemetry.phases.machines, ['vm-main'], 'record-level machine is inherited');
  assert.equal(telemetry.phases.totalDurationMs, 45_000);
  assert.equal(telemetry.phases.wallClockMs, 45_000, 'wallClockMs never exceeds explicit smaller durationMs');
});

test('3154 estimateDailyCapacity guards NaN, non-finite, and nonpositive numbers in targets and options', () => {
  const guarded = estimateDailyCapacity({
    targets: [NaN, -10, 0, Infinity, 50],
    prsPerIssue: NaN,
    interpreterCallsPerIssue: -2,
    ciMinutesPerPr: 0,
    suiteMinutesPerPr: -Infinity,
    activeMinutesPerIssue: 0,
    effectiveTokensPerIssue: -500,
    workerShare: NaN,
    workerTierDiscount: 0,
    activeHoursPerDay: -5,
    slotsPerMachine: 0,
    checkSlotsPerMachine: NaN,
    effectiveTokensPerAccountDay: 0,
    availableMachines: -1,
    availableAccounts: NaN,
    dailyCiMinuteBudget: 0,
    dailyInterpreterCallBudget: -10,
  });
  assert.deepEqual(guarded.rows.map(r => r.targetIssuesPerDay), [50]);
  for (const val of Object.values(guarded.assumptions)) {
    assert.ok(Number.isFinite(val) && val > 0, `expected positive finite assumption, got ${val}`);
  }
  const row = guarded.byTarget[50];
  assert.ok(Number.isFinite(row.baselineEffectiveTokensPerDay) && row.baselineEffectiveTokensPerDay > 0);
  assert.ok(Number.isFinite(row.tieredEffectiveTokensPerDay) && row.tieredEffectiveTokensPerDay > 0);
  assert.ok(Number.isFinite(row.machinesNeeded) && row.machinesNeeded >= 1);
  assert.ok(Number.isFinite(row.accountsNeededTiered) && row.accountsNeededTiered >= 1);

  const fallbackTargets = estimateDailyCapacity({ targets: [NaN, 0, -5] });
  assert.deepEqual(fallbackTargets.rows.map(r => r.targetIssuesPerDay), [25, 40, 70, 80]);
});
