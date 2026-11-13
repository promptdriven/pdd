// Generated from prompts/cli/autopilot-telemetry.prompt.md (sha256: 8ac368d86e675ea2ff5b0f47753ecb15de6bc777e21be41a69700d5bea20f8bf).

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
  ['repair', 'repair'],
  ['fix', 'repair'],
  ['rebase', 'repair'],
  ['base-refresh', 'repair'],
  ['check', 'check'],
  ['review', 'check'],
  ['audit', 'check'],
  ['suite', 'check'],
  ['independent-review', 'check'],
  ['ci-wait', 'ci-wait'],
  ['ci', 'ci-wait'],
  ['checks-wait', 'ci-wait'],
  ['merge', 'merge'],
  ['publish', 'merge'],
]);

const WORKER_STEPS = new Set([
  'intake', 'improve', 'small-change', 'worker',
  'story', 'story/pr1', 'pr1', 'code', 'code/pr2', 'pr2', 'repair', 'fix',
]);
const REVIEWER_STEPS = new Set(['review', 'check', 'independent-review', 'audit', 'merge']);
const VALID_EFFORTS = new Set(['low', 'medium', 'high', 'xhigh']);
const VALID_AGENTS = new Set(['codex', 'claude', 'gemini', 'agy']);
const ANSI_RE = /\x1b\[[0-?]*[ -/]*[@-~]/g;

const isObject = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const nonneg = value => (typeof value === 'number' && Number.isFinite(value) && value >= 0 ? value : 0);
const hasNum = value => typeof value === 'number' && Number.isFinite(value) && value >= 0;
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

function normalizeSpan(span = {}, fallbackMachine = null) {
  if (!isObject(span)) throw new Error('Phase span must be an object.');
  const phase = normalizeAutopilotPhase(span.phase ?? span.step);
  if (!phase) throw new Error(`Unknown Autopilot phase: ${String(span.phase ?? span.step ?? '')}`);
  const startedAt = Number.isFinite(span.startedAt) ? span.startedAt : null;
  const endedAt = Number.isFinite(span.endedAt) ? span.endedAt : null;
  const durationMs = hasNum(span.durationMs)
    ? span.durationMs
    : startedAt !== null && endedAt !== null
      ? Math.max(0, endedAt - startedAt)
      : 0;
  const machine = typeof (span.machine ?? fallbackMachine) === 'string' && (span.machine ?? fallbackMachine).trim()
    ? (span.machine ?? fallbackMachine).trim()
    : null;
  const agent = typeof span.agent === 'string' && span.agent.trim() ? span.agent.trim().toLowerCase() : null;
  const step = typeof span.step === 'string' && span.step.trim() ? span.step.trim() : null;
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
      const canonical = normalizeAutopilotPhase(phase);
      if (!canonical) throw new Error(`Unknown Autopilot phase: ${String(phase ?? '')}`);
      const startedAt = now();
      const stack = open.get(canonical) ?? [];
      stack.push({ startedAt, meta: isObject(meta) ? { ...meta } : {} });
      open.set(canonical, stack);
      return { phase: canonical, startedAt };
    },
    finishPhase(phase, meta = {}) {
      const canonical = normalizeAutopilotPhase(phase);
      if (!canonical) throw new Error(`Unknown Autopilot phase: ${String(phase ?? '')}`);
      const endedAt = now();
      const stack = open.get(canonical);
      const started = stack?.length ? stack.pop() : null;
      const startedAt = Number.isFinite(meta?.startedAt) ? meta.startedAt : (started?.startedAt ?? endedAt);
      const merged = { ...(started?.meta ?? {}), ...(isObject(meta) ? meta : {}), phase: canonical, startedAt, endedAt };
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
      intervals.push([span.startedAt, span.endedAt]);
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
  const normalized = [];
  for (const item of raw) {
    if (!isObject(item)) continue;
    const phase = normalizeAutopilotPhase(item.phase ?? item.step);
    if (!phase) continue;
    normalized.push(normalizeSpan(item));
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
    const clean = explicitAgent.trim().toLowerCase();
    return clean === 'agy' ? 'gemini' : clean;
  }
  for (const row of records) {
    if (typeof row.agent === 'string' && VALID_AGENTS.has(row.agent.toLowerCase())) {
      return row.agent.toLowerCase() === 'agy' ? 'gemini' : row.agent.toLowerCase();
    }
    if (row.type === 'turn.completed' || row.type === 'thread.started' || row.payload?.type === 'token_count' || row.type === 'token_count') return 'codex';
    const usage = row.usage ?? row.message?.usage;
    if (isObject(usage)) {
      if (Object.hasOwn(usage, 'cache_read_input_tokens') || Object.hasOwn(usage, 'cache_creation_input_tokens')) return 'claude';
      if (Object.hasOwn(usage, 'cached_input_tokens') || Object.hasOwn(usage, 'reasoning_output_tokens')) return 'codex';
    }
    if (row.type === 'assistant' || row.type === 'message_start' || row.type === 'message_delta' || isObject(row.modelUsage)) return 'claude';
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
  const computedTotal = agent === 'gemini' ? inputTokens + outputTokens + reasoningTokens : inputTokens + outputTokens;
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
  const cumMax = { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
  const lastSum = { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
  let turns = 0, sawTurn = false, sawCum = false, sawLast = false;
  for (const row of records) {
    if (row.type === 'turn.completed' && isObject(row.usage)) {
      const u = row.usage;
      if ([u.input_tokens, u.output_tokens].some(hasNum)) {
        sawTurn = true;
        turns += 1;
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
        cumMax.input = Math.max(cumMax.input, nonneg(total.input_tokens));
        cumMax.cached = Math.max(cumMax.cached, nonneg(total.cached_input_tokens));
        cumMax.output = Math.max(cumMax.output, nonneg(total.output_tokens));
        cumMax.reasoning = Math.max(cumMax.reasoning, nonneg(total.reasoning_output_tokens));
        cumMax.total = Math.max(cumMax.total, hasNum(total.total_tokens) ? total.total_tokens : nonneg(total.input_tokens) + nonneg(total.output_tokens));
      } else if (isObject(last) && [last.input_tokens, last.output_tokens].some(hasNum)) {
        sawLast = true;
        turns += 1;
        lastSum.input += nonneg(last.input_tokens);
        lastSum.cached += nonneg(last.cached_input_tokens);
        lastSum.output += nonneg(last.output_tokens);
        lastSum.reasoning += nonneg(last.reasoning_output_tokens);
        lastSum.total += hasNum(last.total_tokens) ? last.total_tokens : nonneg(last.input_tokens) + nonneg(last.output_tokens);
      }
    }
  }
  const observed = sawTurn || sawCum || sawLast;
  const base = sawCum
    ? {
      input: Math.max(cumMax.input, turnSum.input),
      cached: Math.max(cumMax.cached, turnSum.cached),
      output: Math.max(cumMax.output, turnSum.output),
      reasoning: Math.max(cumMax.reasoning, turnSum.reasoning),
      total: Math.max(cumMax.total, turnSum.total),
    }
    : sawTurn
      ? turnSum
      : lastSum;
  return finalizeTokenSummary('codex', observed, turns || (sawCum ? 1 : 0), base);
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
  const resultMax = { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
  let sawResult = false;

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
          sawResult = true;
          for (const k of Object.keys(resultMax)) resultMax[k] = Math.max(resultMax[k], sumModels[k]);
        }
      } else {
        const tuple = claudeUsageTuple(row.usage);
        if (tuple) {
          sawResult = true;
          for (const k of Object.keys(resultMax)) resultMax[k] = Math.max(resultMax[k], tuple[k]);
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
  const observed = messages.size > 0 || sawResult;
  const counts = sawResult
    ? {
      input: Math.max(msgSum.input, resultMax.input),
      cached: Math.max(msgSum.cached, resultMax.cached),
      output: Math.max(msgSum.output, resultMax.output),
      reasoning: 0,
      total: Math.max(msgSum.total, resultMax.total),
    }
    : msgSum;
  return finalizeTokenSummary('claude', observed, messages.size || (sawResult ? 1 : 0), counts);
}

function extractGemini(records) {
  const metaSum = { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
  const envMax = { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
  let metaTurns = 0, sawMeta = false, sawEnv = false;

  for (const row of records) {
    if (isObject(row.stats?.models)) {
      const snap = { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 };
      let any = false;
      for (const entry of Object.values(row.stats.models)) {
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
        sawEnv = true;
        for (const k of Object.keys(envMax)) envMax[k] = Math.max(envMax[k], snap[k]);
      }
      continue;
    }
    if (isObject(row.stats)) {
      const s = row.stats;
      const prompt = s.input_tokens ?? s.prompt ?? s.input;
      const out = s.output_tokens ?? s.candidates ?? s.output;
      if ([prompt, out, s.total_tokens, s.total].some(hasNum)) {
        sawEnv = true;
        envMax.input = Math.max(envMax.input, nonneg(prompt));
        envMax.cached = Math.max(envMax.cached, nonneg(s.cached ?? s.cached_input_tokens));
        envMax.output = Math.max(envMax.output, nonneg(out));
        envMax.reasoning = Math.max(envMax.reasoning, nonneg(s.thoughts ?? s.reasoning_tokens));
        envMax.total = Math.max(envMax.total, nonneg(s.total_tokens ?? s.total));
      }
      continue;
    }
    const meta = isObject(row.usageMetadata) ? row.usageMetadata : null;
    if (meta && [meta.promptTokenCount, meta.candidatesTokenCount, meta.totalTokenCount].some(hasNum)) {
      sawMeta = true;
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

  const observed = sawEnv || sawMeta;
  const counts = sawEnv
    ? {
      input: Math.max(envMax.input, metaSum.input),
      cached: Math.max(envMax.cached, metaSum.cached),
      output: Math.max(envMax.output, metaSum.output),
      reasoning: Math.max(envMax.reasoning, metaSum.reasoning),
      total: Math.max(envMax.total, metaSum.total),
    }
    : metaSum;
  return finalizeTokenSummary('gemini', observed, metaTurns || (sawEnv ? 1 : 0), counts);
}

export function extractHarnessTokens(source, { agent = null } = {}) {
  const records = parseEventRecords(source);
  const detected = detectHarnessAgent(records, agent);
  if (!detected) return finalizeTokenSummary(null, false, 0, { input: 0, cached: 0, output: 0, reasoning: 0, total: 0 });
  if (detected === 'codex') return extractCodex(records);
  if (detected === 'claude') return extractClaude(records);
  return extractGemini(records);
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
    if (extracted.agent) {
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

export function estimateDailyCapacity({
  targets = null,
  targetIssuesPerDay = null,
  phaseSummary = null,
  tokenSummary = null,
  prsPerIssue = 2,
  interpreterCallsPerIssue = 4,
  ciMinutesPerPr = 8,
  suiteMinutesPerPr = 6,
  activeMinutesPerIssue = null,
  effectiveTokensPerIssue = null,
  workerShare = 0.75,
  workerTierDiscount = 0.35,
  activeHoursPerDay = 20,
  slotsPerMachine = 4,
  checkSlotsPerMachine = 2,
  effectiveTokensPerAccountDay = 5_000_000,
  availableMachines = null,
  availableAccounts = null,
  dailyCiMinuteBudget = null,
  dailyInterpreterCallBudget = null,
} = {}) {
  const selectedTargets = Array.isArray(targets) && targets.length
    ? targets
    : hasNum(targetIssuesPerDay) && targetIssuesPerDay > 0
      ? [targetIssuesPerDay]
      : [...DAILY_CAPACITY_TARGETS];

  const measuredActiveMinutes = (() => {
    if (hasNum(activeMinutesPerIssue) && activeMinutesPerIssue > 0) return activeMinutesPerIssue;
    if (isObject(phaseSummary?.byPhase)) {
      const activePhases = ['intake', 'improve', 'story/pr1', 'code/pr2', 'repair', 'check', 'merge'];
      const sumMs = activePhases.reduce((acc, p) => acc + nonneg(phaseSummary.byPhase[p]?.durationMs), 0);
      if (sumMs > 0) return sumMs / 60000;
    }
    return 28;
  })();

  const measuredTokensPerIssue = (() => {
    if (hasNum(effectiveTokensPerIssue) && effectiveTokensPerIssue > 0) return effectiveTokensPerIssue;
    const fromSummary = tokenSummary?.total?.effectiveTokens ?? tokenSummary?.effectiveTokens;
    if (hasNum(fromSummary) && fromSummary > 0) return fromSummary;
    return 180_000;
  })();

  const clampedWorkerShare = Math.min(1, Math.max(0, workerShare));
  const clampedDiscount = Math.min(1, Math.max(0.05, workerTierDiscount));
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
      { kind: 'accounts', ratio: hasNum(availableAccounts) && availableAccounts > 0 ? accountsNeededTiered / availableAccounts : accountsNeededTiered / 2 },
      { kind: 'suite-slots', ratio: hasNum(availableMachines) && availableMachines > 0 ? machinesForSuites / availableMachines : machinesForSuites / 2 },
      { kind: 'run-slots', ratio: hasNum(availableMachines) && availableMachines > 0 ? machinesForRuns / availableMachines : machinesForRuns / 2 },
      ...(hasNum(dailyCiMinuteBudget) && dailyCiMinuteBudget > 0 ? [{ kind: 'ci-minutes', ratio: ciMinutesPerDay / dailyCiMinuteBudget }] : []),
      ...(hasNum(dailyInterpreterCallBudget) && dailyInterpreterCallBudget > 0 ? [{ kind: 'interpreter-calls', ratio: interpreterCallsPerDay / dailyInterpreterCallBudget }] : []),
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
