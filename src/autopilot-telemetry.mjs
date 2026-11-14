// Generated from prompts/cli/autopilot-telemetry.prompt.md (sha256: a7f12a1bfcdc279adc3f9f6615faaaba8fd7f784b17a7eff15179f12d412a827).

export const AUTOPILOT_PHASES = Object.freeze([
  'intake',
  'improve',
  'story/pr1',
  'code/pr2',
  'repair',
  'check',
  'ci-wait',
  'merge',
]);

export const DAILY_CAPACITY_TARGETS = Object.freeze([25, 40, 70, 80]);
export const CACHED_TOKEN_WEIGHT = 0.1;

export const DEFAULT_TIER_PROFILES = Object.freeze({
  codex: Object.freeze({
    worker: Object.freeze({ model: 'gpt-5.4-mini', reasoningEffort: 'medium' }),
    reviewer: Object.freeze({ model: 'gpt-5.4', reasoningEffort: 'high' }),
  }),
  claude: Object.freeze({
    worker: Object.freeze({ model: 'claude-sonnet-4-6', reasoningEffort: 'medium' }),
    reviewer: Object.freeze({ model: 'claude-opus-4-6', reasoningEffort: 'high' }),
  }),
  gemini: Object.freeze({
    worker: Object.freeze({ model: 'gemini-2.5-flash', reasoningEffort: 'medium' }),
    reviewer: Object.freeze({ model: 'gemini-2.5-pro', reasoningEffort: 'high' }),
  }),
  agy: Object.freeze({
    worker: Object.freeze({ model: 'gemini-2.5-flash', reasoningEffort: 'medium' }),
    reviewer: Object.freeze({ model: 'gemini-2.5-pro', reasoningEffort: 'high' }),
  }),
});

const PHASE_ALIASES = new Map([
  ['intake', 'intake'],
  ['triage', 'intake'],
  ['sort', 'intake'],
  ['dependencies', 'intake'],
  ['improve', 'improve'],
  ['groom', 'improve'],
  ['clarify', 'improve'],
  ['story/pr1', 'story/pr1'],
  ['story', 'story/pr1'],
  ['pr1', 'story/pr1'],
  ['prompt', 'story/pr1'],
  ['prompts', 'story/pr1'],
  ['small-change', 'story/pr1'],
  ['code/pr2', 'code/pr2'],
  ['code', 'code/pr2'],
  ['pr2', 'code/pr2'],
  ['implement', 'code/pr2'],
  ['build', 'code/pr2'],
  ['worker', 'code/pr2'],
  ['repair', 'repair'],
  ['fix', 'repair'],
  ['rebase', 'repair'],
  ['base-refresh', 'repair'],
  ['conflict', 'repair'],
  ['check', 'check'],
  ['review', 'check'],
  ['audit', 'check'],
  ['suite', 'check'],
  ['independent-review', 'check'],
  ['vectors', 'check'],
  ['runtime', 'check'],
  ['merge-check', 'check'],
  ['ci-wait', 'ci-wait'],
  ['ci', 'ci-wait'],
  ['checks-wait', 'ci-wait'],
  ['merge', 'merge'],
  ['publish', 'merge'],
]);

const WORKER_STEPS = new Set([
  'intake', 'triage', 'sort', 'dependencies',
  'improve', 'groom', 'clarify',
  'small-change', 'worker',
  'story', 'story/pr1', 'pr1', 'prompt', 'prompts',
  'code', 'code/pr2', 'pr2', 'implement', 'build',
  'repair', 'fix', 'rebase', 'base-refresh', 'conflict',
]);
const REVIEWER_STEPS = new Set(['review', 'check', 'independent-review', 'audit', 'merge', 'publish']);
const VALID_EFFORTS = new Set(['low', 'medium', 'high', 'xhigh']);
const VALID_AGENTS = new Set(['codex', 'claude', 'gemini', 'agy']);
const ANSI_RE = /\x1b\[[0-?]*[ -/]*[@-~]/g;

const isObject = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const nonneg = value => (typeof value === 'number' && Number.isFinite(value) && value >= 0 ? value : 0);
const hasNum = value => typeof value === 'number' && Number.isFinite(value) && value >= 0;
const posNum = (value, fallback) => (typeof value === 'number' && Number.isFinite(value) && value > 0 ? value : fallback);
const round2 = value => Math.round(value * 100) / 100;
const round4 = value => Math.round(value * 10000) / 10000;

function validModelName(model) {
  return typeof model === 'string' && model.length > 0 && model === model.trim() && !/^-|[\x00-\x1f\x7f]/.test(model);
}

function normalizeModel(model) {
  if (model === undefined || model === null || model === '') return null;
  if (!validModelName(model)) throw new Error('Invalid model name: must be nonblank without control characters or a leading dash.');
  return model;
}

function normalizeEffort(effort) {
  if (effort === undefined || effort === null || effort === '') return null;
  const clean = String(effort).trim().toLowerCase();
  if (!VALID_EFFORTS.has(clean)) throw new Error('Invalid reasoning effort: choose low, medium, high, or xhigh.');
  return clean;
}

export function normalizeAutopilotPhase(phase) {
  if (typeof phase !== 'string') return null;
  const key = phase.trim().toLowerCase();
  return PHASE_ALIASES.get(key) ?? null;
}

function resolvePhaseOrFallback(rawPhase) {
  if (typeof rawPhase !== 'string' || !rawPhase.trim()) {
    throw new Error(`Invalid Autopilot phase: ${String(rawPhase ?? '')}`);
  }
  const trimmed = rawPhase.trim();
  const canonical = normalizeAutopilotPhase(trimmed);
  return {
    phase: canonical ?? 'code/pr2',
    key: canonical ?? trimmed.toLowerCase(),
    fallbackStep: canonical ? null : trimmed,
  };
}

function normalizeSpan(span = {}, fallbackMachine = null) {
  if (!isObject(span)) throw new Error('Phase span must be an object.');
  const { phase, fallbackStep } = resolvePhaseOrFallback(span.phase ?? span.step);
  const startedAt = Number.isFinite(span.startedAt) ? span.startedAt : null;
  const endedAt = Number.isFinite(span.endedAt) ? span.endedAt : null;
  const durationMs = hasNum(span.durationMs)
    ? span.durationMs
    : startedAt !== null && endedAt !== null
      ? Math.max(0, endedAt - startedAt)
      : 0;
  const rawMachine = typeof span.machine === 'string' && span.machine.trim() ? span.machine : fallbackMachine;
  const machine = typeof rawMachine === 'string' && rawMachine.trim() ? rawMachine.trim() : null;
  const agent = typeof span.agent === 'string' && span.agent.trim() ? span.agent.trim().toLowerCase() : null;
  const step = typeof span.step === 'string' && span.step.trim() ? span.step.trim() : fallbackStep;
  return { phase, startedAt, endedAt, durationMs, machine, agent, step };
}

export function recordPhaseSpan(ledger = {}, span = {}) {
  const base = isObject(ledger) ? ledger : {};
  const existing = Array.isArray(base.spans) ? base.spans.map(item => ({ ...item })) : [];
  const entry = normalizeSpan(span, base.machine ?? null);
  return {
    issue: base.issue ?? null,
    repo: base.repo ?? null,
    ...(base.machine ? { machine: base.machine } : {}),
    spans: [...existing, entry],
  };
}

export function createPhaseTracker({ issue = null, repo = null, machine = null, now = Date.now } = {}) {
  let state = { issue, repo, ...(machine ? { machine } : {}), spans: [] };
  const open = new Map();
  return {
    startPhase(phase, meta = {}) {
      const resolved = resolvePhaseOrFallback(phase);
      const startedAt = now();
      const stack = open.get(resolved.key) ?? [];
      const baseMeta = isObject(meta) ? { ...meta } : {};
      if (resolved.fallbackStep && !baseMeta.step) baseMeta.step = resolved.fallbackStep;
      stack.push({ startedAt, meta: baseMeta });
      open.set(resolved.key, stack);
      return { phase: resolved.phase, startedAt };
    },
    finishPhase(phase, meta = {}) {
      const resolved = resolvePhaseOrFallback(phase);
      const endedAt = now();
      const stack = open.get(resolved.key);
      const started = stack?.length ? stack.pop() : null;
      const startedAt = Number.isFinite(meta?.startedAt) ? meta.startedAt : (started?.startedAt ?? endedAt);
      const merged = {
        ...(started?.meta ?? {}),
        ...(isObject(meta) ? meta : {}),
        ...(resolved.fallbackStep && !meta?.step && !started?.meta?.step ? { step: resolved.fallbackStep } : {}),
        phase: resolved.phase,
        startedAt,
        endedAt,
      };
      state = recordPhaseSpan(state, merged);
      return state.spans.at(-1);
    },
    recordSpan(span) {
      state = recordPhaseSpan(state, span);
      return state.spans.at(-1);
    },
    spans() {
      return state.spans.map(item => ({ ...item }));
    },
    summarize() {
      return { issue, repo, ...summarizeIssuePhases(state) };
    },
  };
}

function mergeWallClockMs(spans) {
  const intervals = [];
  let unanchoredMs = 0;
  for (const span of spans) {
    if (Number.isFinite(span.startedAt) && Number.isFinite(span.endedAt) && span.endedAt >= span.startedAt) {
      const upper = Math.min(span.endedAt, span.startedAt + nonneg(span.durationMs));
      if (upper > span.startedAt) intervals.push([span.startedAt, upper]);
    } else {
      unanchoredMs += nonneg(span.durationMs);
    }
  }
  if (!intervals.length) return unanchoredMs;
  intervals.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
  let [curStart, curEnd] = intervals[0];
  let merged = 0;
  for (let i = 1; i < intervals.length; i++) {
    const [nextStart, nextEnd] = intervals[i];
    if (nextStart <= curEnd) curEnd = Math.max(curEnd, nextEnd);
    else {
      merged += curEnd - curStart;
      curStart = nextStart;
      curEnd = nextEnd;
    }
  }
  merged += curEnd - curStart;
  return merged + unanchoredMs;
}

export function summarizeIssuePhases(spansOrRecord = []) {
  const raw = Array.isArray(spansOrRecord) ? spansOrRecord : (isObject(spansOrRecord) && Array.isArray(spansOrRecord.spans) ? spansOrRecord.spans : []);
  const fallbackMachine = !Array.isArray(spansOrRecord) && isObject(spansOrRecord) ? spansOrRecord.machine ?? null : null;
  const normalized = [];
  for (const item of raw) {
    if (!isObject(item)) continue;
    const rawPhase = item.phase ?? item.step;
    if (typeof rawPhase !== 'string' || !rawPhase.trim()) continue;
    normalized.push(normalizeSpan(item, fallbackMachine));
  }
  const buckets = new Map(AUTOPILOT_PHASES.map(phase => [phase, { durationMs: 0, count: 0, machines: new Set() }]));
  const allMachines = new Set();
  for (const span of normalized) {
    const bucket = buckets.get(span.phase);
    bucket.durationMs += span.durationMs;
    bucket.count += 1;
    if (span.machine) {
      bucket.machines.add(span.machine);
      allMachines.add(span.machine);
    }
  }
  const totalDurationMs = [...buckets.values()].reduce((sum, item) => sum + item.durationMs, 0);
  const wallClockMs = mergeWallClockMs(normalized);
  const phases = AUTOPILOT_PHASES.map(phase => {
    const bucket = buckets.get(phase);
    return {
      phase,
      durationMs: bucket.durationMs,
      durationMinutes: round2(bucket.durationMs / 60000),
      count: bucket.count,
      share: totalDurationMs > 0 ? round4(bucket.durationMs / totalDurationMs) : 0,
      machines: [...bucket.machines].sort(),
    };
  });
  const byPhase = Object.fromEntries(phases.map(row => [row.phase, row]));
  let slowestPhase = null;
  for (const row of phases) {
    if (row.durationMs > 0 && (!slowestPhase || row.durationMs > slowestPhase.durationMs)) slowestPhase = row;
  }
  return {
    phases,
    byPhase,
    totalDurationMs,
    totalDurationMinutes: round2(totalDurationMs / 60000),
    wallClockMs,
    wallClockMinutes: round2(wallClockMs / 60000),
    slowestPhase,
    machines: [...allMachines].sort(),
  };
}

function parseEventRecords(source) {
  if (Array.isArray(source)) return source.filter(isObject);
  if (isObject(source)) return [source];
  if (typeof source !== 'string') return [];
  const cleaned = source.replace(ANSI_RE, '').trim();
  if (!cleaned) return [];
  try {
    const parsed = JSON.parse(cleaned);
    if (Array.isArray(parsed)) return parsed.filter(isObject);
    if (isObject(parsed)) return [parsed];
  } catch { /* Parse as JSONL below. */ }
  const out = [];
  for (const line of cleaned.split(/\r?\n/)) {
    const trimmed = line.trim();
    if (!trimmed) continue;
    try {
      const row = JSON.parse(trimmed);
      if (isObject(row)) out.push(row);
    } catch { /* Ignore non-JSON log lines. */ }
  }
  return out;
}

function detectHarnessAgent(records, explicitAgent) {
  if (typeof explicitAgent === 'string' && VALID_AGENTS.has(explicitAgent.trim().toLowerCase())) {
    return explicitAgent.trim().toLowerCase();
  }
  for (const row of records) {
    if (typeof row.agent === 'string' && VALID_AGENTS.has(row.agent.trim().toLowerCase())) {
      return row.agent.trim().toLowerCase();
    }
    if (row.type === 'turn.completed' || row.type === 'thread.started' || row.payload?.type === 'token_count' || row.type === 'token_count') return 'codex';
    const usage = row.usage ?? row.message?.usage;
    if (isObject(usage)) {
      if (Object.hasOwn(usage, 'cache_read_input_tokens') || Object.hasOwn(usage, 'cache_creation_input_tokens')) return 'claude';
      if (Object.hasOwn(usage, 'cached_input_tokens') || Object.hasOwn(usage, 'reasoning_output_tokens')) return 'codex';
    }
    if (row.type === 'assistant' || row.type === 'message_start' || row.type === 'message_delta' || isObject(row.modelUsage)) return 'claude';
    if (row.event === 'step_update' && isObject(row.step_update)) return 'agy';
    if (isObject(row.stats?.models) || isObject(row.usageMetadata) || isObject(row.stats) && (Object.hasOwn(row.stats, 'cached') || Object.hasOwn(row.stats, 'thoughts'))) return 'gemini';
  }
  return null;
}

function finalizeTokenSummary(agent, observed, turns, counts) {
  const inputTokens = nonneg(counts.input);
  const cachedInputTokens = Math.min(inputTokens, nonneg(counts.cached));
  const uncachedInputTokens = Math.max(0, inputTokens - cachedInputTokens);
  const outputTokens = nonneg(counts.output);
  const reasoningTokens = nonneg(counts.reasoning);
  const computedTotal = agent === 'gemini' || agent === 'agy' ? inputTokens + outputTokens + reasoningTokens : inputTokens + outputTokens;
  const totalTokens = counts.total > 0 ? Math.max(counts.total, inputTokens + outputTokens) : computedTotal;
  const cacheHitShare = observed && inputTokens > 0 ? round4(cachedInputTokens / inputTokens) : null;
  const effectiveTokens = observed
    ? round2(uncachedInputTokens + CACHED_TOKEN_WEIGHT * cachedInputTokens + outputTokens)
    : 0;
  return {
    agent,
    observed,
    turns,
    inputTokens,
    cachedInputTokens,
    uncachedInputTokens,
    outputTokens,
    reasoningTokens,
    totalTokens,
    effectiveTokens,
    cacheHitShare,
  };
}

function extractCodex(records) {
  const turnSum = { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
  const bankedCum = { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
  const sessionPeak = { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
  const lastSum = { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
  let turnCount = 0, cumTurns = 0, lastTurns = 0;
  let sawTurn = false, sawCum = false, sawLast = false, inCumSession = false;

  const bankSession = () => {
    if (!inCumSession) return;
    bankedCum.input += sessionPeak.input;
    bankedCum.cached += sessionPeak.cached;
    bankedCum.output += sessionPeak.output;
    bankedCum.reasoning += sessionPeak.reasoning;
    bankedCum.total += sessionPeak.total;
    sessionPeak.input = 0;
    sessionPeak.cached = 0;
    sessionPeak.output = 0;
    sessionPeak.reasoning = 0;
    sessionPeak.total = 0;
    inCumSession = false;
  };

  for (const row of records) {
    if (row.type === 'session_meta' || row.type === 'thread.started') {
      bankSession();
      continue;
    }
    if (row.type === 'turn.completed' && isObject(row.usage)) {
      const u = row.usage;
      if ([u.input_tokens, u.output_tokens].some(hasNum)) {
        sawTurn = true;
        turnCount += 1;
        turnSum.input += nonneg(u.input_tokens);
        turnSum.cached += nonneg(u.cached_input_tokens);
        turnSum.output += nonneg(u.output_tokens);
        turnSum.reasoning += nonneg(u.reasoning_output_tokens);
        turnSum.total += hasNum(u.total_tokens) ? u.total_tokens : nonneg(u.input_tokens) + nonneg(u.output_tokens);
      }
      continue;
    }
    const tokenPayload = row.type === 'event_msg' && row.payload?.type === 'token_count'
      ? row.payload
      : row.type === 'token_count'
        ? row
        : null;
    if (tokenPayload) {
      const total = tokenPayload.info?.total_token_usage ?? tokenPayload.total_token_usage;
      const last = tokenPayload.info?.last_token_usage ?? tokenPayload.last_token_usage;
      if (isObject(total) && [total.input_tokens, total.output_tokens, total.total_tokens].some(hasNum)) {
        sawCum = true;
        const curInput = nonneg(total.input_tokens);
        const curCached = nonneg(total.cached_input_tokens);
        const curOutput = nonneg(total.output_tokens);
        const curReasoning = nonneg(total.reasoning_output_tokens);
        const curTotal = hasNum(total.total_tokens) ? total.total_tokens : curInput + curOutput;
        if (inCumSession && (curTotal < sessionPeak.total || curInput < sessionPeak.input)) {
          bankSession();
        }
        const advanced = !inCumSession
          ? (curInput > 0 || curOutput > 0 || curTotal > 0)
          : (curTotal > sessionPeak.total || curInput > sessionPeak.input || curOutput > sessionPeak.output);
        if (advanced) cumTurns += 1;
        inCumSession = true;
        sessionPeak.input = Math.max(sessionPeak.input, curInput);
        sessionPeak.cached = Math.max(sessionPeak.cached, curCached);
        sessionPeak.output = Math.max(sessionPeak.output, curOutput);
        sessionPeak.reasoning = Math.max(sessionPeak.reasoning, curReasoning);
        sessionPeak.total = Math.max(sessionPeak.total, curTotal);
      } else if (isObject(last) && [last.input_tokens, last.output_tokens].some(hasNum)) {
        sawLast = true;
        lastTurns += 1;
        lastSum.input += nonneg(last.input_tokens);
        lastSum.cached += nonneg(last.cached_input_tokens);
        lastSum.output += nonneg(last.output_tokens);
        lastSum.reasoning += nonneg(last.reasoning_output_tokens);
        lastSum.total += hasNum(last.total_tokens) ? last.total_tokens : nonneg(last.input_tokens) + nonneg(last.output_tokens);
      }
    }
  }
  bankSession();
  const observed = sawTurn || sawCum || sawLast;
  const base = sawCum
    ? {
      input: Math.max(bankedCum.input, turnSum.input),
      cached: Math.max(bankedCum.cached, turnSum.cached),
      output: Math.max(bankedCum.output, turnSum.output),
      reasoning: Math.max(bankedCum.reasoning, turnSum.reasoning),
      total: Math.max(bankedCum.total, turnSum.total),
    }
    : sawTurn
      ? turnSum
      : lastSum;
  const resolvedTurns = sawCum && sawTurn
    ? Math.max(turnCount, cumTurns || 1)
    : sawCum
      ? (cumTurns || 1)
      : sawTurn
        ? turnCount
        : lastTurns;
  return finalizeTokenSummary('codex', observed, resolvedTurns, base);
}

function claudeUsageTuple(usage) {
  if (!isObject(usage)) return null;
  const rawIn = usage.input_tokens ?? usage.inputTokens;
  const cacheCreate = usage.cache_creation_input_tokens ?? usage.cacheCreationInputTokens ?? 0;
  const cacheRead = usage.cache_read_input_tokens ?? usage.cacheReadInputTokens ?? 0;
  const out = usage.output_tokens ?? usage.outputTokens;
  if (![rawIn, cacheCreate, cacheRead, out].some(hasNum)) return null;
  const input = nonneg(rawIn) + nonneg(cacheCreate) + nonneg(cacheRead);
  const cached = nonneg(cacheRead);
  const output = nonneg(out);
  return { input, cached, output, reasoning: 0, total: input + output };
}

function extractClaude(records) {
  const messages = new Map();
  let lastMsgKey = null, syntheticSeq = 0;
  const resultSum = { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
  let resultCount = 0;

  for (const row of records) {
    if (row.isMeta || row.isApiErrorMessage) continue;
    if (row.type === 'assistant' || row.type === 'message_start' || row.type === 'stream_event') {
      const inner = row.type === 'stream_event' && isObject(row.event) ? row.event : row;
      if (inner.type === 'message_delta' && isObject(inner.usage)) {
        const key = inner.message?.id ?? lastMsgKey ?? `anon-${++syntheticSeq}`;
        const prev = messages.get(key) ?? { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
        const tuple = claudeUsageTuple(inner.usage);
        if (tuple) {
          if (tuple.input > 0) prev.input = Math.max(prev.input, tuple.input);
          if (tuple.cached > 0) prev.cached = Math.max(prev.cached, tuple.cached);
          prev.output = Math.max(prev.output, tuple.output);
          prev.total = prev.input + prev.output;
          messages.set(key, prev);
        }
        continue;
      }
      const msg = inner.message ?? row.message;
      const tuple = claudeUsageTuple(msg?.usage ?? inner.usage);
      if (tuple) {
        const key = typeof (msg?.id ?? row.uuid) === 'string' && (msg?.id ?? row.uuid) ? (msg?.id ?? row.uuid) : `anon-${++syntheticSeq}`;
        lastMsgKey = key;
        const prev = messages.get(key) ?? { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
        prev.input = Math.max(prev.input, tuple.input);
        prev.cached = Math.max(prev.cached, tuple.cached);
        prev.output = Math.max(prev.output, tuple.output);
        prev.total = prev.input + prev.output;
        messages.set(key, prev);
      }
      continue;
    }
    if (row.type === 'message_delta' && isObject(row.usage)) {
      const key = row.message?.id ?? lastMsgKey ?? `anon-${++syntheticSeq}`;
      const prev = messages.get(key) ?? { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
      const tuple = claudeUsageTuple(row.usage);
      if (tuple) {
        if (tuple.input > 0) prev.input = Math.max(prev.input, tuple.input);
        if (tuple.cached > 0) prev.cached = Math.max(prev.cached, tuple.cached);
        prev.output = Math.max(prev.output, tuple.output);
        prev.total = prev.input + prev.output;
        messages.set(key, prev);
      }
      continue;
    }
    if (row.type === 'result' || (!row.type && (isObject(row.usage) || isObject(row.modelUsage)))) {
      if (isObject(row.modelUsage) && Object.keys(row.modelUsage).length > 0) {
        const sumModels = { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
        let any = false;
        for (const modelRow of Object.values(row.modelUsage)) {
          const tuple = claudeUsageTuple(modelRow);
          if (tuple) {
            any = true;
            sumModels.input += tuple.input;
            sumModels.cached += tuple.cached;
            sumModels.output += tuple.output;
            sumModels.total += tuple.total;
          }
        }
        if (any) {
          resultCount += 1;
          for (const k of Object.keys(resultSum)) resultSum[k] += sumModels[k];
        }
      } else {
        const tuple = claudeUsageTuple(row.usage);
        if (tuple) {
          resultCount += 1;
          for (const k of Object.keys(resultSum)) resultSum[k] += tuple[k];
        }
      }
    }
  }

  const msgSum = { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
  for (const item of messages.values()) {
    msgSum.input += item.input;
    msgSum.cached += item.cached;
    msgSum.output += item.output;
    msgSum.total += item.total;
  }
  const observed = messages.size > 0 || resultCount > 0;
  const counts = messages.size > 0 ? msgSum : resultSum;
  const turns = messages.size > 0 ? messages.size : resultCount;
  return finalizeTokenSummary('claude', observed, turns, counts);
}

function extractGemini(records, agentLabel = 'gemini') {
  const metaSum = { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
  const envSum = { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
  let metaTurns = 0, statsCount = 0;

  for (const row of records) {
    const rawStats = isObject(row.stats) ? row.stats : (isObject(row.result?.stats) ? row.result.stats : null);
    if (isObject(rawStats?.models)) {
      const snap = { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
      let any = false;
      for (const entry of Object.values(rawStats.models)) {
        const t = entry?.tokens;
        if (!isObject(t)) continue;
        const prompt = t.prompt ?? t.input ?? t.input_tokens;
        const out = t.candidates ?? t.output ?? t.output_tokens;
        if ([prompt, out, t.total].some(hasNum)) {
          any = true;
          snap.input += nonneg(prompt);
          snap.cached += nonneg(t.cached ?? t.cached_input_tokens);
          snap.output += nonneg(out);
          snap.reasoning += nonneg(t.thoughts ?? t.reasoning);
          snap.total += hasNum(t.total) ? t.total : nonneg(prompt) + nonneg(out) + nonneg(t.thoughts);
        }
      }
      if (any) {
        statsCount += 1;
        for (const k of Object.keys(envSum)) envSum[k] += snap[k];
      }
      continue;
    }
    if (isObject(rawStats)) {
      const prompt = rawStats.input_tokens ?? rawStats.prompt ?? rawStats.input;
      const out = rawStats.output_tokens ?? rawStats.candidates ?? rawStats.output;
      if ([prompt, out, rawStats.total_tokens, rawStats.total].some(hasNum)) {
        statsCount += 1;
        envSum.input += nonneg(prompt);
        envSum.cached += nonneg(rawStats.cached ?? rawStats.cached_input_tokens);
        envSum.output += nonneg(out);
        envSum.reasoning += nonneg(rawStats.thoughts ?? rawStats.reasoning_tokens);
        envSum.total += nonneg(rawStats.total_tokens ?? rawStats.total);
      }
      continue;
    }
    const meta = isObject(row.usageMetadata)
      ? row.usageMetadata
      : (isObject(row.step_update?.usageMetadata) ? row.step_update.usageMetadata : null);
    if (meta && [meta.promptTokenCount, meta.candidatesTokenCount, meta.totalTokenCount].some(hasNum)) {
      metaTurns += 1;
      metaSum.input += nonneg(meta.promptTokenCount);
      metaSum.cached += nonneg(meta.cachedContentTokenCount);
      metaSum.output += nonneg(meta.candidatesTokenCount);
      metaSum.reasoning += nonneg(meta.thoughtsTokenCount);
      metaSum.total += hasNum(meta.totalTokenCount)
        ? meta.totalTokenCount
        : nonneg(meta.promptTokenCount) + nonneg(meta.candidatesTokenCount) + nonneg(meta.thoughtsTokenCount);
    }
  }

  const observed = metaTurns > 0 || statsCount > 0;
  const counts = metaTurns > 0 ? metaSum : envSum;
  const turns = metaTurns > 0 ? metaTurns : statsCount;
  return finalizeTokenSummary(agentLabel, observed, turns, counts);
}

export function extractHarnessTokens(source, { agent = null } = {}) {
  const records = parseEventRecords(source);
  const detected = detectHarnessAgent(records, agent);
  if (!detected) return finalizeTokenSummary(null, false, 0, { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 });
  if (detected === 'codex') return extractCodex(records);
  if (detected === 'claude') return extractClaude(records);
  return extractGemini(records, detected);
}

function mergeTokenRows(rows, label = null) {
  const acc = { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
  let observed = false, turns = 0;
  for (const row of rows) {
    if (!row?.observed) continue;
    observed = true;
    turns += nonneg(row.turns);
    acc.input += nonneg(row.inputTokens);
    acc.cached += nonneg(row.cachedInputTokens);
    acc.output += nonneg(row.outputTokens);
    acc.reasoning += nonneg(row.reasoningTokens);
    acc.total += nonneg(row.totalTokens);
  }
  return finalizeTokenSummary(label, observed, turns, acc);
}

export function classifyStepTier(step) {
  if (typeof step !== 'string') return null;
  const clean = step.trim().toLowerCase();
  if (WORKER_STEPS.has(clean)) return 'worker';
  if (REVIEWER_STEPS.has(clean)) return 'reviewer';
  return null;
}

export function summarizeIssueTelemetry({ issue = null, repo = null, spans = [], streams = [] } = {}) {
  const phases = summarizeIssuePhases(spans);
  const parsedStreams = [];
  const byAgentBuckets = new Map();
  const byTierBuckets = { worker: [], reviewer: [], unclassified: [] };

  for (const item of Array.isArray(streams) ? streams : []) {
    const rawSource = isObject(item) && Object.hasOwn(item, 'source') ? item.source : item;
    const explicitAgent = isObject(item) ? item.agent ?? null : null;
    const step = isObject(item) ? item.step ?? item.phase ?? null : null;
    const explicitTier = isObject(item) && (item.tier === 'worker' || item.tier === 'reviewer') ? item.tier : classifyStepTier(step);
    const extracted = isObject(item) && typeof item.inputTokens === 'number' && typeof item.observed === 'boolean'
      ? item
      : extractHarnessTokens(rawSource, { agent: explicitAgent });
    parsedStreams.push({ ...extracted, step, tier: explicitTier });
    if (extracted.observed && extracted.agent) {
      if (!byAgentBuckets.has(extracted.agent)) byAgentBuckets.set(extracted.agent, []);
      byAgentBuckets.get(extracted.agent).push(extracted);
    }
    byTierBuckets[explicitTier ?? 'unclassified'].push(extracted);
  }

  const byAgent = Object.fromEntries(
    [...byAgentBuckets.entries()]
      .sort(([a], [b]) => a.localeCompare(b))
      .map(([agentName, list]) => [agentName, mergeTokenRows(list, agentName)]),
  );
  const byTier = {
    worker: mergeTokenRows(byTierBuckets.worker, 'worker'),
    reviewer: mergeTokenRows(byTierBuckets.reviewer, 'reviewer'),
  };
  return {
    issue,
    repo,
    phases,
    tokens: {
      total: mergeTokenRows(parsedStreams, null),
      byAgent,
      byTier,
    },
  };
}

export function isModelTieringEnabled({ tiering = null, env = {} } = {}) {
  if (tiering === true) return true;
  if (isObject(tiering) && tiering.enabled === true) return true;
  if (tiering === false || (isObject(tiering) && tiering.enabled === false)) return false;
  const flag = String(env?.PDD_MODEL_TIERING ?? '').trim().toLowerCase();
  return flag === '1' || flag === 'true';
}

export function resolveStepModelTier({ agent = 'codex', step = null, model = null, reasoningEffort = null, tiering = null, env = {} } = {}) {
  const normalizedAgent = typeof agent === 'string' && VALID_AGENTS.has(agent.trim().toLowerCase())
    ? agent.trim().toLowerCase()
    : 'codex';
  const explicitModel = normalizeModel(model);
  const explicitEffort = normalizeEffort(reasoningEffort);
  const tier = classifyStepTier(step);
  const enabled = isModelTieringEnabled({ tiering, env });

  if (!enabled || !tier) {
    return {
      enabled: false,
      tier,
      agent: normalizedAgent,
      model: explicitModel,
      reasoningEffort: explicitEffort,
    };
  }

  const cfg = isObject(tiering) ? tiering : {};
  const defaults = DEFAULT_TIER_PROFILES[normalizedAgent]?.[tier] ?? DEFAULT_TIER_PROFILES.codex[tier];
  const envModel = tier === 'worker' ? env?.PDD_WORKER_MODEL : env?.PDD_REVIEWER_MODEL;
  const envEffort = tier === 'worker' ? env?.PDD_WORKER_EFFORT : env?.PDD_REVIEWER_EFFORT;

  const configuredModel = cfg.models?.[normalizedAgent]?.[tier] ?? cfg[tier]?.model ?? envModel ?? defaults.model;
  const resolvedModel = explicitModel && cfg.overrideExplicitModel !== true
    ? explicitModel
    : normalizeModel(configuredModel);

  const configuredEffort = cfg.efforts?.[normalizedAgent]?.[tier] ?? cfg[tier]?.reasoningEffort ?? envEffort ?? defaults.reasoningEffort;
  const resolvedEffort = explicitEffort ?? normalizeEffort(configuredEffort);

  return {
    enabled: true,
    tier,
    agent: normalizedAgent,
    model: resolvedModel,
    reasoningEffort: resolvedEffort,
  };
}

export function buildTieredAgentArgs(options = {}) {
  const resolved = isObject(options) && Object.hasOwn(options, 'enabled') && Object.hasOwn(options, 'tier')
    ? options
    : resolveStepModelTier(options);
  if (!resolved.enabled) {
    return resolved.model ? ['--model', resolved.model] : [];
  }
  const args = [];
  if (resolved.model) args.push('--model', resolved.model);
  if (resolved.reasoningEffort) {
    if (resolved.agent === 'codex') args.push('-c', `model_reasoning_effort="${resolved.reasoningEffort}"`);
    else if (resolved.agent === 'claude') args.push('--effort', resolved.reasoningEffort);
  }
  return args;
}

export function estimateDailyCapacity(options = {}) {
  const opts = isObject(options) ? options : {};
  const validTargets = Array.isArray(opts.targets)
    ? opts.targets.filter(t => typeof t === 'number' && Number.isFinite(t) && t > 0)
    : [];
  const singleTarget = posNum(opts.targetIssuesPerDay, null);
  const selectedTargets = validTargets.length
    ? validTargets
    : singleTarget !== null
      ? [singleTarget]
      : [...DAILY_CAPACITY_TARGETS];

  const prsPerIssue = posNum(opts.prsPerIssue, 2);
  const interpreterCallsPerIssue = posNum(opts.interpreterCallsPerIssue, 4);
  const ciMinutesPerPr = posNum(opts.ciMinutesPerPr, 8);
  const suiteMinutesPerPr = posNum(opts.suiteMinutesPerPr, 6);
  const activeHoursPerDay = posNum(opts.activeHoursPerDay, 20);
  const slotsPerMachine = posNum(opts.slotsPerMachine, 4);
  const checkSlotsPerMachine = posNum(opts.checkSlotsPerMachine, 2);
  const effectiveTokensPerAccountDay = posNum(opts.effectiveTokensPerAccountDay, 5_000_000);
  const availableMachines = posNum(opts.availableMachines, null);
  const availableAccounts = posNum(opts.availableAccounts, null);
  const dailyCiMinuteBudget = posNum(opts.dailyCiMinuteBudget, null);
  const dailyInterpreterCallBudget = posNum(opts.dailyInterpreterCallBudget, null);

  const measuredActiveMinutes = (() => {
    const explicit = posNum(opts.activeMinutesPerIssue, null);
    if (explicit !== null) return explicit;
    if (isObject(opts.phaseSummary?.byPhase)) {
      const activePhases = ['intake', 'improve', 'story/pr1', 'code/pr2', 'repair', 'check', 'merge'];
      const sumMs = activePhases.reduce((acc, p) => acc + nonneg(opts.phaseSummary.byPhase[p]?.durationMs), 0);
      if (sumMs > 0) return sumMs / 60000;
    }
    return 28;
  })();

  const measuredTokensPerIssue = (() => {
    const explicit = posNum(opts.effectiveTokensPerIssue, null);
    if (explicit !== null) return explicit;
    const fromSummary = posNum(opts.tokenSummary?.total?.effectiveTokens ?? opts.tokenSummary?.effectiveTokens, null);
    if (fromSummary !== null) return fromSummary;
    return 180_000;
  })();

  const clampedWorkerShare = Math.min(1, posNum(opts.workerShare, 0.75));
  const clampedDiscount = Math.min(1, Math.max(0.05, posNum(opts.workerTierDiscount, 0.35)));
  const tieredMultiplier = clampedWorkerShare * clampedDiscount + (1 - clampedWorkerShare);
  const slotMinutesPerDay = Math.max(60, activeHoursPerDay * 60);

  const rows = selectedTargets.map(target => {
    const suiteMinutesPerDay = round2(target * prsPerIssue * suiteMinutesPerPr);
    const ciMinutesPerDay = round2(target * prsPerIssue * ciMinutesPerPr);
    const activeRunMinutesPerDay = round2(target * measuredActiveMinutes);
    const interpreterCallsPerDay = Math.ceil(target * interpreterCallsPerIssue);

    const runSlotsNeeded = Math.max(1, Math.ceil(activeRunMinutesPerDay / slotMinutesPerDay));
    const suiteSlotsNeeded = Math.max(1, Math.ceil(suiteMinutesPerDay / slotMinutesPerDay));
    const machinesForRuns = Math.ceil(runSlotsNeeded / Math.max(1, slotsPerMachine));
    const machinesForSuites = Math.ceil(suiteSlotsNeeded / Math.max(1, checkSlotsPerMachine));
    const machinesNeeded = Math.max(1, machinesForRuns, machinesForSuites);

    const baselineEffectiveTokensPerDay = round2(target * measuredTokensPerIssue);
    const tieredEffectiveTokensPerDay = round2(baselineEffectiveTokensPerDay * tieredMultiplier);
    const tokenSavingsPercent = baselineEffectiveTokensPerDay > 0
      ? round2(((baselineEffectiveTokensPerDay - tieredEffectiveTokensPerDay) / baselineEffectiveTokensPerDay) * 100)
      : 0;

    const accountsNeededBaseline = Math.max(1, Math.ceil(baselineEffectiveTokensPerDay / Math.max(1, effectiveTokensPerAccountDay)));
    const accountsNeededTiered = Math.max(1, Math.ceil(tieredEffectiveTokensPerDay / Math.max(1, effectiveTokensPerAccountDay)));

    const pressures = [
      { kind: 'accounts', ratio: availableAccounts !== null ? accountsNeededTiered / availableAccounts : accountsNeededTiered / 2 },
      { kind: 'suite-slots', ratio: availableMachines !== null ? machinesForSuites / availableMachines : machinesForSuites / 2 },
      { kind: 'run-slots', ratio: availableMachines !== null ? machinesForRuns / availableMachines : machinesForRuns / 2 },
      ...(dailyCiMinuteBudget !== null ? [{ kind: 'ci-minutes', ratio: ciMinutesPerDay / dailyCiMinuteBudget }] : []),
      ...(dailyInterpreterCallBudget !== null ? [{ kind: 'interpreter-calls', ratio: interpreterCallsPerDay / dailyInterpreterCallBudget }] : []),
    ];
    pressures.sort((a, b) => b.ratio - a.ratio);

    return {
      targetIssuesPerDay: target,
      runSlotsNeeded,
      suiteSlotsNeeded,
      machinesNeeded,
      accountsNeededBaseline,
      accountsNeededTiered,
      interpreterCallsPerDay,
      ciMinutesPerDay,
      suiteMinutesPerDay,
      baselineEffectiveTokensPerDay,
      tieredEffectiveTokensPerDay,
      tokenSavingsPercent,
      firstBottleneck: pressures[0].kind,
    };
  });

  return {
    assumptions: {
      activeMinutesPerIssue: round2(measuredActiveMinutes),
      effectiveTokensPerIssue: round2(measuredTokensPerIssue),
      prsPerIssue,
      interpreterCallsPerIssue,
      ciMinutesPerPr,
      suiteMinutesPerPr,
      workerShare: clampedWorkerShare,
      workerTierDiscount: clampedDiscount,
      slotMinutesPerDay,
      slotsPerMachine,
      checkSlotsPerMachine,
      effectiveTokensPerAccountDay,
    },
    rows,
    byTarget: Object.fromEntries(rows.map(row => [row.targetIssuesPerDay, row])),
  };
}
