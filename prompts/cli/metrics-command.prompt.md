---
kind: native-only
reason: Invokes gh api graphql for live GitHub open issue counts, writes HTML reports to disk, and launches the local browser
---

# Metrics command

Own `src/metrics-command.mjs`. Export `runMetrics({ argv, cwd, env, stdout, stderr, ports })`, returning an integer exit code (`0` on success, `2` on invalid input, `1` on runtime write failure).

## Subcommands and flags

- `pdd metrics [--repos] [--repo OWNER/REPO] [--date YYYY-MM-DD] [--timezone IANA] [--json] [--html] [--file PATH]` (`view: "overview"`)
- `pdd metrics stages [--repo OWNER/REPO] [--date YYYY-MM-DD] [--timezone IANA] [--json] [--html] [--file PATH]` (`view: "stages"`)
- `pdd metrics skills [--repo OWNER/REPO] [--date YYYY-MM-DD] [--timezone IANA] [--json] [--html] [--file PATH]` (`view: "skills"`)
- `pdd metrics full [--repos] [--repo OWNER/REPO] [--date YYYY-MM-DD] [--timezone IANA] [--json] [--html] [--file PATH]` (`view: "full"`)
- `pdd metrics on [--repo OWNER/REPO] [--json]`
- `pdd metrics off [--repo OWNER/REPO] [--json]`

Reject unknown subcommands, unknown or duplicate options, incompatible combinations (`--json` with `--html` or `--file`, `--file` without `--html`, `--repos` on `stages`, `skills`, `on`, or `off`), invalid `OWNER/REPO`, invalid `YYYY-MM-DD`, and invalid IANA timezones with one clear line on `stderr` and exit code `2`.

## Execution

- **`on` / `off`:** Call `setAutopilotMetricsRecording` from [Autopilot metrics local store](autopilot-metrics.prompt.md). Print JSON `{ ok: true, action, repo, enabled, globalEnabled, repoOverrides, updatedAt }` when `--json` is set, else one confirmation line (`Autopilot metrics recording is ON.` / `Autopilot metrics recording is OFF (existing history preserved).`, naming `for OWNER/REPO` when `--repo` is given), and return `0`.
- **Report views (`overview`, `stages`, `skills`, `full`):**
  1. Resolve `timezone` (`--timezone`, else `Intl.DateTimeFormat().resolvedOptions().timeZone || "UTC"`).
  2. Read local state via `readAutopilotMetricsState` from [Autopilot metrics local store](autopilot-metrics.prompt.md). Keep scope strictly Autopilot: when `0` Autopilot repositories exist on this machine and `--repo` is unset, report `0` repos cleanly (with `0` counts and exit `0`).
  3. Query live `Open` GitHub issue counts across the included repositories in **one batched `gh api graphql` call** (`repository(owner, name) { issues(states: OPEN) { totalCount } }`), wrapped with `nativeGithubCounter` from [GitHub calls](github-calls.prompt.md). Skip the network call when `0` repositories are selected. If `gh` is missing, offline, or unauthenticated, return `null` for `openIssues` so `Open` renders `?` (`null` in JSON) without failing the command.
  4. Compute the report with `calculateAutopilotMetrics` from [Autopilot metrics calculator](metrics-model.prompt.md).
  5. Output:
     - `--json`: write `JSON.stringify(report, null, 2) + "\n"` to `stdout`.
     - `--html`: write `renderMetricsHtml(report)` to `--file PATH` (resolved from `cwd`) or `<stateDir>/autopilot/metrics/pdd-metrics.html`, write `Wrote Autopilot metrics HTML report to <PATH>\n` to `stdout`, and open `<PATH>` in the browser when interactive (skipping browser launch when `ports.openBrowser === false`, `env.PDD_NO_OPEN === "1"`, `env.CI === "true"`, or `env.NODE_TEST_CONTEXT` is set).
     - Default text: write `formatMetricsText(report) + "\n"` to `stdout`.

## Dependencies

- [Autopilot metrics calculator](metrics-model.prompt.md): required for calculation and text/HTML rendering.
- [Autopilot metrics local store](autopilot-metrics.prompt.md): required for local Autopilot metrics state and `on`/`off` persistence.
- [GitHub calls](github-calls.prompt.md): required for counting the batched `gh api graphql` open-issue query.
