# Autopilot phase telemetry, harness token usage, and model tiering

Own `src/autopilot-telemetry.mjs`. Provide deterministic per-issue wall-clock phase measurement, cross-harness token extraction for Codex, Claude Code, and Gemini streams, opt-in worker versus reviewer model and reasoning-effort routing, and daily throughput capacity estimation.

## Phase wall-clock telemetry

Export `AUTOPILOT_PHASES` with the canonical ordered phases `["intake", "improve", "story/pr1", "code/pr2", "repair", "check", "ci-wait", "merge"]`.

Export `normalizeAutopilotPhase(phase)` mapping canonical names and workflow aliases (`triage`, `sort`, `dependencies` to `intake`; `groom`, `clarify` to `improve`; `story`, `pr1`, `prompt`, `prompts`, `small-change` to `story/pr1`; `code`, `pr2`, `implement`, `build` to `code/pr2`; `fix`, `rebase`, `base-refresh` to `repair`; `review`, `audit`, `suite`, `independent-review` to `check`; `ci`, `checks-wait` to `ci-wait`; `publish` to `merge`) and returning `null` for blank or unknown values.

Export `recordPhaseSpan(ledger, span)` and `createPhaseTracker({issue, repo, machine, now})` to record nonnegative phase spans `{phase, startedAt, endedAt, durationMs, machine, agent, step}` across one or more machines without mutating caller inputs.

Export `summarizeIssuePhases(spansOrRecord)` returning `{phases, byPhase, totalDurationMs, totalDurationMinutes, wallClockMs, wallClockMinutes, slowestPhase, machines}`:
- `phases` lists every canonical phase in `AUTOPILOT_PHASES` order with `{phase, durationMs, durationMinutes, count, share, machines}`.
- `totalDurationMs` sums recorded durations across all phases; `wallClockMs` merges overlapping `[startedAt, endedAt]` intervals when finite bounds exist (falling back to `totalDurationMs` for duration-only spans) so parallel multi-machine execution and serial wall-clock time stay distinct.
- `slowestPhase` names the highest-duration phase with `durationMs > 0`, or `null` when no positive duration is recorded.

## Cross-harness token extraction

Export `CACHED_TOKEN_WEIGHT = 0.1` as an analytical effective-token weight for cached prompt input (never a dollar billing figure).

Export `extractHarnessTokens(source, {agent} = {})` accepting JSONL text, single JSON text, a parsed event object, or an array of event objects. Skip blank and malformed lines without throwing. Detect `agent` (`codex`, `claude`, `gemini`) from explicit `agent` or event structure and return `{agent, observed, turns, inputTokens, cachedInputTokens, uncachedInputTokens, outputTokens, reasoningTokens, totalTokens, effectiveTokens, cacheHitShare}`:
- Codex: sum `turn.completed` `usage` rows (`input_tokens`, `cached_input_tokens`, `output_tokens`, `reasoning_output_tokens`) and track monotonic maximums for cumulative `event_msg` `token_count` `total_token_usage` snapshots without double-counting when both appear in one session stream.
- Claude Code: deduplicate streaming `assistant`, `message_start`, and `message_delta` usage by message identifier (`message.id` or `uuid`) using monotonic per-message deltas where total input equals `input_tokens + cache_creation_input_tokens + cache_read_input_tokens` and cached input equals `cache_read_input_tokens`, falling back to `result` `usage` only when per-message rows are absent.
- Gemini: extract `stats.models[*].tokens` (`prompt` or `input`, `cached`, `candidates` or `output`, `thoughts`, `total`), `usageMetadata` (`promptTokenCount`, `cachedContentTokenCount`, `candidatesTokenCount`, `thoughtsTokenCount`, `totalTokenCount`), and `result.stats` without double-counting cumulative result envelopes against per-turn rows.

Export `summarizeIssueTelemetry({issue, repo, spans, streams})` combining phase wall-clock summaries with aggregated token totals grouped overall, `byAgent`, and `byTier` (`worker` versus `reviewer`).

## Worker and reviewer model tiering

Export `DEFAULT_TIER_PROFILES`, `classifyStepTier(step)`, `isModelTieringEnabled({tiering, env})`, `resolveStepModelTier({agent, step, model, reasoningEffort, tiering, env})`, and `buildTieredAgentArgs(options)`.

Classify `intake`, `improve`, `small-change`, `worker`, `story`, `story/pr1`, `pr1`, `code`, `code/pr2`, `pr2`, `repair`, and `fix` as `worker`, and `review`, `check`, `independent-review`, `audit`, and `merge` as `reviewer`.

Tiering is disabled by default so existing CLI invocations stay unchanged unless `tiering === true`, `tiering?.enabled === true`, or `env.PDD_MODEL_TIERING` is `"1"` or `"true"`. When disabled, `resolveStepModelTier` preserves an explicit valid `model` and `reasoningEffort` (or `null`) and `buildTieredAgentArgs` emits only `["--model", model]` when `model` is explicitly supplied.

When enabled for a classified step, preserve an explicit caller `model` unless `tiering.overrideExplicitModel === true`; otherwise select from `tiering.models?.[agent]?.[tier]`, `tiering[tier]?.model`, `env.PDD_WORKER_MODEL` / `env.PDD_REVIEWER_MODEL`, or `DEFAULT_TIER_PROFILES[agent][tier].model`, and resolve reasoning effort (`low`, `medium`, `high`, `xhigh`) from explicit `reasoningEffort`, `tiering`, `env.PDD_WORKER_EFFORT` / `env.PDD_REVIEWER_EFFORT`, or profile defaults (`medium` for `worker`, `high` for `reviewer`). Reject model names with control characters or a leading dash. Emit `--model <model> -c model_reasoning_effort="<effort>"` for Codex, `--model <model> --effort <effort>` for Claude Code, and `--model <model>` for Gemini and Antigravity CLI.

## Daily capacity estimation

Export `DAILY_CAPACITY_TARGETS = Object.freeze([25, 40, 70, 80])` and `estimateDailyCapacity(options)` computing machine slots, harness accounts, interpreter calls, CI minutes, suite minutes, baseline versus tiered effective tokens, percentage token savings, and the first hard bottleneck for each requested daily issue target (defaulting to `25`, `40`, `70`, and `80` issues per day).

## Dependencies

None.

<details><summary>Runtime interface</summary>

```json
{"kind":"native-only","status":"approved","prose_sha256":"526387af13f31b8af3a56a875439c5850be8be8187f5fbb500a7880ae4ba8696","reason":"Exposes stateful clock-backed phase tracker handles with live JavaScript methods alongside synchronous CLI flag builders and harness stream parsers consumed directly by host agent adapters."}
```
</details>
