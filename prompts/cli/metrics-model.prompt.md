# Autopilot metrics calculator

Own `src/metrics-model.mjs`. Export pure deterministic functions `SKILLS`, `GATES`, `validateRepoName`, `normalizeSkill`, `normalizeMetricsConfig`, `isMetricsEnabled`, `applyMetricsToggle`, `calculateAutopilotMetrics`, `formatMetricsText`, and `renderMetricsHtml`. Perform no filesystem, network, process, or clock I/O, and never mutate caller inputs.

## Domain decisions

- **Autopilot-only scope.** Metrics summarize local Autopilot runs across one or more `owner/repo` repositories on this machine. There are no hardcoded personal target rows.
- **Recording switch (`on` / `off`).** Recording configuration has shape `{ enabled: boolean, repos: { [repoLower]: boolean }, pausedSince: string | null, repoPausedSince: { [repoLower]: string }, pausedIntervals: Array<{ repo: string | null, from: string, to: string | null }>, updatedAt: string | null }`. Missing or empty configuration defaults to `enabled: true` with empty `repos` and `pausedIntervals` (`normalizeMetricsConfig`).
  - `isMetricsEnabled(config, repo)` checks `config.repos[repoLower]` when boolean; otherwise returns `config.enabled !== false`.
  - `applyMetricsToggle({ config, action, repo, at })` (also accepting positional `(config, { action, repo, at })`) accepts `action` `"on"` or `"off"` (else throws code `"invalid-action"`), optional `repo` matching `OWNER/REPO` (`validateRepoName`, else throws code `"invalid-repo"`), and UTC timestamp string `at` (default `"1970-01-01T00:00:00.000Z"` if omitted in pure tests, invalid throws `"invalid-at"`).
    - Turning `"off"` globally (`repo` omitted) sets `enabled: false`, starts an open global interval `{ repo: null, from: at, to: null }` when not already globally paused, and sets `pausedSince: at`.
    - Turning `"on"` globally sets `enabled: true`, closes any open global interval (`to: at`), and clears `pausedSince: null`. `"off"` with `repo` sets `repos[repoLower] = false`, sets `repoPausedSince[repoLower] = at`, and opens `{ repo: repoLower, from: at, to: null }`; `"on"` with `repo` sets `repos[repoLower] = true` (or deletes `repos[repoLower]` when global `enabled` is true), deletes `repoPausedSince[repoLower]`, and closes open intervals for `repoLower`.
  - Any run whose start time (`startedAt`, else `at`) or completion time (`at` when `status !== "running"`) falls inside a matching global (`repo: null`) or repository (`repo: repoLower`) paused interval `[fromMs, toMs ?? Infinity)` is excluded from calculations while all runs completed before `fromMs` or started after `toMs` remain visible.
- **Repository normalization and selection.** Repository names validate as `OWNER/REPO` and deduplicate case-insensitively (`repoLower = repo.toLowerCase()`), keeping the first canonical display casing supplied in `repos` or `runs` (falling back to `repoFilter` casing when the repository is not yet in `repos` or `runs`). When `repoFilter` is given, validate `OWNER/REPO` (invalid throws `"invalid-repo"`) and restrict the report to that repository (displaying it even when it has 0 runs).
- **Time windows.** Validate `now` (ISO-8601 UTC timestamp, default `"1970-01-01T00:00:00.000Z"` if omitted in pure tests, invalid throws `"invalid-now"`) and `timezone` (valid IANA timezone via `Intl.DateTimeFormat`, default `"UTC"`, invalid throws `"invalid-timezone"`).
  - Without `date`, compute two windows:
    1. `last24h` (`label: "Last 24h"`): `[nowMs - 86400000, nowMs]`.
    2. `week` (`label: "Week (Mon-Sun)"`): local Monday `00:00:00.000` in `timezone` of the week containing `nowMs` through `nowMs` (Monday is day 1, Sunday is day 7, refreshing every Monday at `00:00` local time).
  - With `date` (`YYYY-MM-DD` real calendar date, invalid throws `"invalid-date"`), compute one window:
    1. `date` (`label: date`): local `00:00:00.000` through `23:59:59.999` on `date` in `timezone`.
  - Stages and Skills views evaluate the primary window: `date` when `date` is supplied, else `week` (`Week (Mon-Sun)`).
- **Per-issue deduplication within a window.** Each input run has `{ repo, issue, issues?, skill?, startedAt?, at, status, pr?, gates?, reopened?, reverted?, durationMinutes?, promptChanged?, pathsOnlyD?, title? }`.
  - A run belongs to window `[startMs, endMs]` when its activity time `atMs` (`Date.parse(run.at ?? run.endedAt ?? run.updatedAt ?? run.startedAt)`) satisfies `startMs <= atMs <= endMs`, or when `run.status === "running"` and `startMs <= nowMs <= endMs` with `(startedAtMs ?? atMs) <= endMs`.
  - Expand grouped runs (`issues` array of positive integers) or single `issue` so each `(repoLower, issue)` taken in the window is counted once (`Taken`). When multiple run records exist for the same `(repoLower, issue)` in one window, select the winning record by outcome rank (`merged` / `would-merge` > `running` > `needs-person` > `ended` / `failed` / `released` / `stopped` / `abandoned`), breaking ties by latest `atMs`. For `PR Created`, count distinct `(repoLower, issue)` entries with a positive integer `pr` (or `prCreated === true`). For `M/WM`, count entries whose `status` is `"merged"` or `"would-merge"`.
  - Conversion percentage `convPct` is ` Taken === 0 ? null : Math.round((mwm / taken) * 1000) / 10 `, formatted in `mwmDisplay` as `"${mwm} (${convPct.toFixed(1)}%)"` when `taken > 0`, else `"0 (n/a)"`.
  - `Open` issue count comes from `openIssues[repoLower]` (non-negative integer when available, else `null`, formatted as `"?"` in `openDisplay`). Across multiple repositories, unified `open` is the sum when every included repository has a numeric count (or when at least one has a count and none are `null`), else `null` (`"?"`) when `openIssues` is absent or any included repository is `null` (for 0 repositories, `open` is `0` when `openIssues` is an object, else `null`).

## Views and public operations

### View 1: Overview (`overview`)
- Unified (`byRepo` false): one row per window (`Last 24h`, `Week (Mon-Sun)`, or `YYYY-MM-DD`) with `{ key, label, open, openDisplay, taken, prCreated, mwm, convPct, mwmDisplay }`.
- Per-repository (`byRepo` true): `perRepoWindows` array (matching the active windows: `[week, last24h]` when `date` is unset, `[date]` when `date` is set), each containing `rows` (one row per repository in sorted `repoLower` order) and `total` (`label: "Total"`).

### View 2: Stages (`stages`)
- Evaluates the primary window across the selected repositories (`repoFilter` or unified).
- Gate states per issue in `GATES = ["runtime", "vectors", "formal", "suite", "review", "ci"]`:
  - Normalize gate values:
    - `runtime`: `"pass"` -> `"pass"`; `"fail"` -> `"fail"`; else `"na"`.
    - `vectors`: `"pass"` -> `"pass"`; `"fail"` -> `"fail"`; else `"na"`.
    - `formal`: `"proved"`, `"bounded"`, `"pass"` -> `"pass"`; `"failed"`, `"fail"` -> `"fail"`; else `"na"`.
    - `suite`: `"pass"` -> `"pass"`; `"fail"`, `"broken"`, `"hung"` -> `"fail"`; `"running"` -> `"running"`; else `"na"`.
    - `review`: `"pass"`, `"PASS"` -> `"pass"`; `"fail"`, `"FAIL"` -> `"fail"`; `"running"` -> `"running"`; else `"na"`.
    - `ci`: `"green"`, `"pass"` -> `"pass"`; `"red"`, `"fail"` -> `"fail"`; `"pending"`, `"running"` -> `"running"`; else `"na"`.
  - For each gate, `passed` is the count of `"pass"` issues and `applicable` is the count of `"pass"` or `"fail"` issues (`display: applicable === 0 ? "-" : "${passed}/${applicable}"`).
  - `reopen` counts `M/WM` issues in the window with `reopened === true || reverted === true`.
  - Non-merged breakdown (`nonMerged`): classifies every taken issue in the window whose status is neither `"merged"` nor `"would-merge"` into exactly one primary reason in priority order: `"running"` (`status === "running"`), `"needs-person"` (`status === "needs-person"`), `"failed runtime"`, `"failed vectors"`, `"failed formal"`, `"failed suite"`, `"failed review"`, `"failed ci"` (first gate with state `"fail"` in `runtime, vectors, formal, suite, review, ci` order), else `"ended"` (any other non-merged stop before or without a gate failure). `nonMergedSummary` formats `"Non-merged (0): none"` when 0 non-merged issues exist, else `"Non-merged (${count}): "` followed by nonzero buckets `"${n} ${bucket}"` joined by `" · "`.

### View 3: Skills (`skills`)
- `normalizeSkill(value, hints)` maps `"small-change"` / `"pdd-small-change"`, `"bug"` / `"pdd-bug"`, and `"feature"` / `"pdd-feature"` (case-insensitive) to `"small-change"`, `"bug"`, or `"feature"`. When `value` is absent, use `hints`: `pathsOnlyD === true` -> `"small-change"`; `/\b(?:fix|bug|regression|broken|crash|error|fail(?:ed|ing|s)?)\b/i` in `title` or `promptChanged === false` -> `"bug"`; else `"feature"`.
- Rows in fixed order `["small-change", "bug", "feature"]` plus `total` (`skill: "Total"`):
  - `{ skill, taken, prCreated, mwm, convPct, mwmDisplay, medianMinutes, medianDisplay }`.
  - `medianMinutes`: median of finite positive `durationMinutes` (`> 0`) among `"merged"` or `"would-merge"` issues in that row, rounded to nearest integer (`Math.max(1, Math.round(median))`), or `null` when none have positive duration (`medianDisplay`: `"${medianMinutes}m"` or `"n/a"`).

### Return shape and formatting
- `calculateAutopilotMetrics` validates `view` (`"overview"`, `"stages"`, `"skills"`, or `"full"`, default `"overview"`, else throws `"invalid-view"`) and returns `{ schema: "pdd.autopilot.metrics.v1", generatedAt: now, displayDate, timezone, date: date ?? null, view, byRepo: Boolean(byRepo), repoFilter: canonicalRepoFilter ?? null, recording: { enabled, globalEnabled, repoOverrides }, repos, overview: { windows, perRepoWindows }, stages: { window, taken, pr, gates, mwm, reopen, nonMerged, nonMergedSummary }, skills: { window, rows, total } }`.
- `formatMetricsText(report, { view })` renders aligned plain-text tables matching `report.view` (or explicit `view`):
  - Header line naming `PDD Autopilot Metrics`, scope (`repoFilter`, `Per Repo (${n} repos)`, or `Unified (${n} repos)`), and date; adds `Recording: OFF (existing history shown; run "pdd metrics on" to resume)` when recording is disabled for the selected scope.
  - `overview`: `Window | Open | Taken | PR Created | M/WM (Conv%)` (or per-repo `Repo | Open | Taken | PR Created | M/WM (Conv%)` with `Total` row when `byRepo` is true).
  - `stages`: `Taken | PR | Runtime | Vectors | Formal | Suite | Review | CI | M/WM | Reopen` followed by `stages.nonMergedSummary`.
  - `skills`: `Skill | Taken | PR Created | M/WM (Conv%) | Median Time` with `small-change`, `bug`, `feature`, and `Total`.
  - `full`: prints `overview`, `stages`, and `skills` separated by blank lines.
- `renderMetricsHtml(report)` returns a self-contained HTML5 document (`<!doctype html>`) escaping all dynamic strings (`&`, `<`, `>`, `"`, `'`) and rendering Overview (Unified and Per-Repo), Gate Stages + Non-merged summary, and Work Mix by Skill.

## Dependencies

None. This module is pure calculation and formatting.
