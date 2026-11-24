---
kind: native-only
reason: Invokes gh api graphql and GET-only regression scans for live GitHub open/closed issues, PR merge state, and post-merge regressions, writes HTML reports to disk, and launches the local browser
---

# Metrics command

Own `src/metrics-command.mjs`. Export `runMetrics({ argv, cwd, env, stdout, stderr, ports })`, returning an integer exit code (`0` on success, `2` on invalid input, `1` on runtime write failure).

## Subcommands and flags

- `pdd metrics [--repos] [--repo OWNER/REPO] [--date YYYY-MM-DD] [--standup] [--timezone IANA] [--json] [--html] [--file PATH]` (`view: "overview"`)
- `pdd metrics stages [--repo OWNER/REPO] [--date YYYY-MM-DD] [--standup] [--timezone IANA] [--json] [--html] [--file PATH]` (`view: "stages"`)
- `pdd metrics skills [--repo OWNER/REPO] [--date YYYY-MM-DD] [--standup] [--timezone IANA] [--json] [--html] [--file PATH]` (`view: "skills"`)
- `pdd metrics full [--repos] [--repo OWNER/REPO] [--date YYYY-MM-DD] [--standup] [--timezone IANA] [--json] [--html] [--file PATH]` (`view: "full"`)
- `pdd metrics on [--repo OWNER/REPO] [--json]`
- `pdd metrics off [--repo OWNER/REPO] [--json]`

Reject unknown subcommands, unknown or duplicate options, incompatible combinations (`--json` with `--html` or `--file`, `--file` without `--html`, `--standup` on `on` or `off`, `--repos` on `stages`, `skills`, `on`, or `off`), invalid `OWNER/REPO`, invalid `YYYY-MM-DD`, and invalid IANA timezones with one clear line on `stderr` and exit code `2`.

## Execution

- **`on` / `off`:** Call `setAutopilotMetricsRecording` from [Autopilot metrics local store](autopilot-metrics.prompt.md). Print JSON `{ ok: true, action, repo, enabled, globalEnabled, repoOverrides, updatedAt }` when `--json` is set, else one confirmation line (`Autopilot metrics recording is ON.` / `Autopilot metrics recording is OFF (existing history preserved).`, naming `for OWNER/REPO` when `--repo` is given), and return `0`.
- **Report views (`overview`, `stages`, `skills`, `full`):**
  1. Resolve `timezone` (`--timezone`, else `"America/Los_Angeles"` when `--standup` is set, else `Intl.DateTimeFormat().resolvedOptions().timeZone || "UTC"`).
  2. Read local state via `readAutopilotMetricsState` from [Autopilot metrics local store](autopilot-metrics.prompt.md). Keep scope strictly Autopilot: when `0` Autopilot repositories exist on this machine and `--repo` is unset, report `0` repos cleanly (with `0` counts and exit `0`).
     - When `--repo` is unset (unified or `--repos` rollup), exclude any repository explicitly turned off via `pdd metrics off --repo OWNER/REPO` (`localState.config.repos[repoLower] === false`) from `targetRepos` so turned-off sandbox repositories are neither shown nor queried on GitHub. When `--repo` explicitly names a turned-off repository, keep it in `targetRepos` so its pre-pause history stays inspectable with the `Recording: OFF` notice.
  3. Query live GitHub issue and PR state across `targetRepos` using batched `gh api graphql` call(s) wrapped with `nativeGithubCounter` from [GitHub calls](github-calls.prompt.md) (skipping all network calls when `0` repositories are selected; injectable via `ports.openIssues`, `ports.openIssueNumbers`, `ports.closedIssues`, `ports.prStates`):
     - Live open issues: `issues(states: OPEN, first: 100, orderBy: { field: UPDATED_AT, direction: DESC }) { totalCount pageInfo { hasNextPage endCursor } nodes { number timelineItems(last: 10, itemTypes: [REOPENED_EVENT]) { nodes { ... on ReopenedEvent { createdAt actor { login } } } } } }` (following bounded cursor pagination) -> `openIssues` counts (for `Open now`), `openIssueNumbers` lists (for exact per-window `Pool` deduplication), and GraphQL `REOPENED_EVENT` timestamps.
     - Closed issues since the earliest active window start (`min(last24hStart, weekStart)`, exact timezone-anchored `[prevDay 09:00, date 09:00)` bounds for `--standup --date YYYY-MM-DD`, or conservative `[date - 2d, date + 2d]` bounds for `--date YYYY-MM-DD` covering every IANA timezone including UTC+10 through UTC+14): `issues(states: CLOSED, filterBy: { since }, first: 100, orderBy: { field: UPDATED_AT, direction: DESC }) { pageInfo { hasNextPage endCursor } nodes { number closedAt timelineItems(last: 10, itemTypes: [REOPENED_EVENT]) { nodes { ... on ReopenedEvent { createdAt actor { login } } } } } }` (following bounded cursor pagination within window bounds) -> `closedIssues` for per-window `Pool` and GraphQL `REOPENED_EVENT` timestamps.
     - Actual PR merge state and metadata for every distinct positive integer `pr` created in the active windows' runs: `pullRequest(number: N) { number state merged mergedAt title mergeCommit { oid } }` (batched in GraphQL aliases; preserve partial `data` when an individual alias errors instead of dropping the whole report offline) -> `prStates` so PRs merged on GitHub after `observe` (`would-merge`), stopped, or assisted runs reconcile accurately as `Merged` and unmerged `would-merge` PRs stay under `Unmerged PRs`.
     - If `gh` is missing, offline, or unauthenticated, gracefully return `null` for `openIssues` / `openIssueNumbers` / `prStates` and `[]` for `closedIssues` so `Open now` and `Pool` render `?` (`null` in JSON) without failing the command.
  4. Auto-detect post-merge regressions by reusing `regressionScan` from [Autopilot regression detection](autopilot-regressions.prompt.md) (injectable via `ports.regressions`, `ports.regressionsComplete`, or `ports.regressionScan`; never invent a second regression scanner):
     - For each repository in `targetRepos` that has merged PRs in the active windows (after step 3 merge reconciliation), run `regressionScan({ root: coreDir, repo, candidates, prs, includeCi: false, boundedPulls: true, maxRequests, fs, gh, now })` scoped to those merged PRs, passing pre-resolved `{ mergeCommit, mergedAt, title }` from step 3 and a GET-only `gh` adapter wrapped with `nativeGithubCounter`.
     - Map each scanned merge's proven signals (`reopened`, `revert`, `reference`) merged with any post-merge GraphQL `REOPENED_EVENT` timestamps (`> mergedAt` and `<= untilMs`) into normalized `regressions` entries preserving `reopenedAt`, `revertedAt`, `regressionIssueAt`, `detectedAt`, and `signals` (`[{ kind, level, at, url }]`) passed to `calculateAutopilotMetrics`, and propagate `regressionsComplete` (`false` if any scan returns `complete === false`, or if `gh` is offline/unavailable with active `targetRepos` and no injected `ports.openIssues`/`ports.regressionsComplete`).
     - When `gh` is offline or a scan is unavailable, degrade cleanly to local `post-merge.json` / run regression flags with `regressionsComplete: false` so unverified counts render honestly as `?` / `N+ (X.X%+)` / `(scan incomplete)` without failing the command.
  5. Surface read-only daily investigation findings via `buildStandupInvestigationSummary` from [Autopilot metrics calculator](metrics-model.prompt.md) (strictly `writeIssues: false`): when `ports.investigation` is not supplied, collect local incidents for `targetRepos` within `[sinceMs, untilMs]` from `ports.investigationIncidents ?? localState.incidents` (excluding undated drafts on explicit historical `--date` runs), build the standup investigation summary for `date`/`timezone`/`now`, and pass `investigation` to `calculateAutopilotMetrics` whenever `summary.report.summary.uniqueFindings > 0`.
  6. Compute the report with `calculateAutopilotMetrics` from [Autopilot metrics calculator](metrics-model.prompt.md), passing `runs`, `repos`, `openIssues`, `openIssueNumbers`, `closedIssues`, `prStates`, `regressions`, `regressionsComplete`, `flakeEntries` (`ports.flakeEntries ?? localState.flakes`), optional `recurringFlakes` (`ports.recurringFlakes`), optional `investigation`, `view`, `byRepo`, `repoFilter`, `date`, `standup`, `timezone`, `now`, and `recording`.
  7. Output:
     - `--json`: write `JSON.stringify(report, null, 2) + "\n"` to `stdout`.
     - `--html`: write `renderMetricsHtml(report)` to `--file PATH` (resolved from `cwd`) or `<stateDir>/autopilot/metrics/pdd-metrics.html`, write `Wrote Autopilot metrics HTML report to <PATH>\n` to `stdout`, and open `<PATH>` in the browser when interactive (skipping browser launch when `ports.openBrowser === false`, `env.PDD_NO_OPEN === "1"`, `env.CI === "true"`, or `env.NODE_TEST_CONTEXT` is set).
     - Default text: write `formatMetricsText(report) + "\n"` to `stdout`.

## Dependencies

- [Autopilot metrics calculator](metrics-model.prompt.md): required for calculation and text/HTML rendering.
- [Autopilot metrics local store](autopilot-metrics.prompt.md): required for local Autopilot metrics state, `<stem>-core` directory lookup, and `on`/`off` persistence.
- [Autopilot regression detection](autopilot-regressions.prompt.md): required for auto-detecting post-merge regressions across `auto`-merged, `observe`-merged, and stopped-then-merged PRs.
- [GitHub calls](github-calls.prompt.md): required for counting the batched `gh api graphql` and GET-only regression scan calls.
