---
kind: native-only
reason: Reads and writes local Autopilot state directories, JSONL run logs, and atomic configuration files under ~/.local/state/pdd/autopilot
---

# Autopilot metrics local store

Own `src/autopilot-metrics.mjs`. Export `autopilotStateRoot`, `readMetricsConfig`, `setAutopilotMetricsRecording`, `recordAutopilotMetric`, and `readAutopilotMetricsState`.

## Storage layout

All Autopilot metrics state lives locally on the machine running Autopilot under `<stateDir>/autopilot/` (`env.PDD_STATE_DIR` when set, else `~/.local/state/pdd`):

- `metrics-config.json`: `{ enabled, repos, pausedSince, repoPausedSince, pausedIntervals, targets, updatedAt }`, updated atomically via temp file + rename (`0o600`). Missing or unreadable config defaults to `enabled: true` (recording ON by default) and default monthly `targets` (`convMinPct: 90`, `maxRegressionPct: 0`, `label: null`).
- `metrics/runs.jsonl`: append-only JSONL log (`0o600`) of Autopilot run snapshots `{ id, repo, issue, issues, skill, startedAt, at, status, pr, gates, gateCounts, reopened, reverted, regressionIssues, durationMinutes, promptChanged, pathsOnlyD, title }`.
- Existing Autopilot launcher configs `<stateDir>/autopilot/*.json` (excluding `autopilot-update.json` and `metrics-config.json`) and their paired `<stem>-core/` folders (`jobs/*.json`, `history.jsonl`, `flakes.jsonl`, `logs/*-evidence-*.json`, `logs/*-build-*.log`, `post-merge.json`).

## Recording and read behavior

- `recordAutopilotMetric(entry, ports)` checks `isMetricsEnabled(config, entry.repo)` from [Autopilot metrics calculator](metrics-model.prompt.md). When `false`, it writes nothing and returns `{ recorded: false, enabled: false }`. When `true`, it validates `repo` (`OWNER/REPO`) and positive integer `issue`, appends one normalized JSON line to `metrics/runs.jsonl`, and never throws into Autopilot ticks on best-effort callers.
- `setAutopilotMetricsRecording({ action, repo, stateDir, env, home, fs, now })` applies `applyMetricsToggle` from [Autopilot metrics calculator](metrics-model.prompt.md), persists `metrics-config.json` atomically, and returns the updated config.
- `readAutopilotMetricsState({ repoFilter, stateDir, env, home, fs, now })` reads `metrics-config.json`, discovers active Autopilot repositories on this machine (`enabled === true`, active `jobs/*.json`, non-empty `history.jsonl`, non-empty `flakes.jsonl`, or recorded rows in `metrics/runs.jsonl`, skipping unrelated repositories when valid `repoFilter` is supplied), records each repository's `<stem>-core/` directory path in `coreDirs` (`{ [repoLower]: string }`), reads `metrics/runs.jsonl`, reads optional symlink-safe `<stem>-core/flakes.jsonl` entries via `parseFlakeLedger` of [Autopilot regression detection](autopilot-regressions.prompt.md) (defaulting `repo` to the repo config when absent on an entry), harvests symlink-safe local investigation incidents from `<stem>-core/` (`history.jsonl` including `postMerge: true` regression rows enriched with `post-merge.json`, `flakes.jsonl`, and `reports/drafts/`) into `incidents`, and merges live `<stem>-core/` jobs, `history.jsonl` completion rows (skipping strike/hold/reset lines that have no job `outcome`), latest per-issue `logs/<issue>-evidence-<head>.json` gate verdicts (including optional `e2e` gate, numeric `gateCounts` strictly for executed checks while excluding `not-run`/`na`/`skipped`/`pending`/`running`/`none` lines, and `promptChanged` inferred strictly from executed `runtime`/`vectors`/`formal` states), build-log skill reads (`/skills/pdd-(small-change|bug|feature)/SKILL.md`), `telemetry.phases.wallClockMinutes` durations, and `post-merge.json` separate `reopened` / `reverted` flags (supporting both `merges` maps keyed by PR number and `items` arrays, including companion `issues`). Deduplicate runs by `(repoLower, issue, runKey)` using outcome rank and timestamp so `metrics/runs.jsonl` and `<stem>-core/` never double-count the same run or let an earlier failed attempt overwrite a later merged run on the same PR. Return `{ config, repos, coreDirs, runs, flakes, incidents }`.

## Dependencies

- [Autopilot metrics calculator](metrics-model.prompt.md): required for `validateRepoName`, `normalizeMetricsConfig`, `normalizeSkill`, `isMetricsEnabled`, and `applyMetricsToggle`.
- [Autopilot regression detection](autopilot-regressions.prompt.md): required for `parseFlakeLedger`.
