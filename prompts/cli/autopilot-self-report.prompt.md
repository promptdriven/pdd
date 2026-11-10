# Automatic PDD and Runtime self-report filing

Own `src/autopilot-self-report.mjs` and the fixed subagent brief
`docs/autopilot-self-report.md`. Export `SELF_REPORT_REPO` (`"promptdriven/pdd"`),
`FORBIDDEN_RUNTIME_REPO` (`"promptdriven/prompt-runtime"`),
`DAILY_SELF_REPORT_CAP` (`5`), `CONSENT_PROMPT`
(`"May Autopilot file PDD bug reports for failures in PDD itself? auto / ask each time / off"`),
`classifyFailureCause(run, options={})`, `classifyRuntimeFailure(check, health=null)`,
`redactSelfReport(value, options={})`, `selfReportConsent(repo, config={}, state={})`,
`resolveSelfReportConsent(input, ports={})`, `diagnosePddFailure(run, cause, ports={})`,
`formatSelfReportBody(report, options={})`, `fileSelfReport(input, ports={})`,
`recordCommandCrash(input, ports={})`, and
`reconcileSelfReports(state, ports, config, runs, options={})`.

## Cause classification

When a run stops, parks, refuses or crashes, `classifyFailureCause(run, {check, health, commandError}={})`
classifies the cause from saved run records, command crash records and check/health observations into one of four classes:

| Side (`side`) | Subkinds (`kind`) | Reportable | Condition |
|---|---|---|---|
| `pdd` | `command-crash`, `invariant-broken`, `missing-command`, `autopilot-state` | `true` | Unhandled `pdd` command exception or internal error (`run.commandFailure`, `command-crash.json`, `commandError`), broken contract or state invariant (`run.invariantFailure`, invalid reply or corrupt state), supported `pdd` command/export/flag missing or wrong (`run.missingCommand`, missing export/command refusal), or Autopilot state bug in claims, parking, wake or admission (`run.autopilotBug`, custody/state invariant failure) |
| `runtime` | `no-verdict`, `runner-stopped`, `provider-error`, `server-refusal`, `timeout` | `true` | Runtime service failure (`classifyRuntimeFailure(check, health)` or `run.runtimeWait` / check batch with no verdict, stopped runner, upstream provider error, timeout, or HTTP 5xx / server refusal that is not a prompt expectation, binding or sign-in failure) |
| `user` | `user-code`, `user-tests`, `user-prompt`, `user-environment` | `false` | The user's own code, tests, prompt expectations, file-rule refusals, binding refusals, repair limits, PR CI failures, repository dependencies, or host toolchain validation |
| `person` | `person-gate`, `person-question`, `person-access`, `person-review` | `false` | Waiting for a person gate, an independent person question, strict terminal approval, PR human review, account/GitHub quota reset, or sign-in (`gh auth login`, HTTP 401/403) |

Both `pdd` and `runtime` causes are reportable (`reportable: true`) and file through the shared `fileSelfReport` path to `promptdriven/pdd`. User code/tests (`user`) and person decisions (`person`) return `reportable: false` and never file a report. Healthy running work returns `{side:"none",kind:"none",reportable:false}`.

Every reportable classification derives a stable cause signature `${code}:${module}:${fn}`:
- `code`: the stable error code or failure slug (for example `ERR_PDD_CRASH`, `TypeError`, `INVARIANT_BROKEN`, `MISSING_COMMAND`, `AUTOPILOT_STATE_BUG`, or `RUNTIME_NO_VERDICT`).
- `module`: the normalized PDD source module path (for example `src/workflow-runner.mjs`) from the first `src/*.mjs` stack frame or saved record, or `runtime-service` for Runtime causes.
- `fn`: the owning function or command operation (for example `stepDoneCommand` or `pdd-test`).

Reuse existing automatic route-question grouping (`routeQuestionsTick`, `"Missing PDD route: <kind>"`) for `pdd-route` questions without duplicating its issue creation.

## Diagnose subagent for PDD/Autopilot causes

For a `pdd`-side failure, `diagnosePddFailure(run, cause, ports)` launches at most one fresh read-only agent session per run failure occurrence (`runId` + `signature`) using the bundled brief `docs/autopilot-self-report.md` and the run's configured launch profile (`codex exec --sandbox read-only --json` or `claude -p --output-format json --permission-mode plan`). Clear inherited session, Herdr and coordinator environment markers so the subagent never joins a worker or coordinator chat. Save the subagent session metadata in `runDir/self-reports/<id>.json` for cost-ledger token attribution.

The diagnose subagent and local fallback inspector:
1. Reproduce when safe and read-only, and inspect the saved run record, crash stack, `pdd` package version and relevant PDD source file around the failing frame.
2. Locate the root cause with `file:line` evidence (for example `src/workflow-runner.mjs:1234`).
3. Search existing open and recently closed issues in `promptdriven/pdd` for the same signature (`code + module + fn`).
4. Format the report in the [issue reporting guide](../../docs/ISSUES.md) shape: Problem, Steps to reproduce, Expected vs actual, Evidence, Versions, and Suspected root cause (`file:line`).

## Shared filing path, target guard, deduplication and daily cap

`fileSelfReport(input, ports)` is the single shared filing entrypoint for both PDD/Autopilot-side (`side: "pdd"`) and Runtime-side (`side: "runtime"`) causes, including `wake-runtime` incident filing:
- **Target repository guard**: Always target `promptdriven/pdd`. Never file in the working repository unless `repository` is `promptdriven/pdd`, and never file in `promptdriven/prompt-runtime` (which is private; the PDD team moves Runtime reports there). Reject or redirect any other target repository to `promptdriven/pdd`.
- **Signature marker**: Include `<!-- pdd:self-report:SIGNATURE -->` in every issue body (and `<!-- pdd:runtime-cause:CAUSE -->` when `side === "runtime"`).
- **Search and deduplicate**: Search open and recently closed issues in `promptdriven/pdd` for the signature marker before creating an issue.
  - If an **open** issue in `promptdriven/pdd` matches the signature, add one redacted comment recording the new occurrence (run number, timestamp, PDD version and summary) and create no new issue (`action: "commented"`).
  - Otherwise, check the machine daily cap (`DAILY_SELF_REPORT_CAP = 5` new issues per machine per UTC day, persisted in `self-report-machine.json` under the Autopilot state root).
  - When the machine has already filed 5 new self-report issues on the current UTC day, create no new issue; if an existing self-report issue from today or a matching closed issue is available, add one occurrence comment (`action: "commented"`, `capped: true`), else record `action: "skipped"`, `reason: "daily-cap"`.
  - When under the daily cap, create one new issue in `promptdriven/pdd` with label `pdd:self-report` (plus `pdd:runtime-report` when `side === "runtime"`). When a PDD maintainer login is configured on the repository (`config.maintainer`, `config.pddMaintainer`, or `config.runtimeOwner`), assign the issue with `--assignee`; otherwise leave it unassigned so Autopilot does not take its own core bug.

## Privacy, redaction and consent

`redactSelfReport(value, {home, env}={})` removes sensitive data before any issue search, creation or comment:
- Strip credentials, tokens and keys (`ghp_`, `gho_`, `ghu_`, `ghs_`, `ghr_`, `github_pat_`, `sk-`, `sk-ant-`, `xox[baprs]-`, `AIza`, `Bearer ...`, `Basic ...`, key/value assignments for `token`, `secret`, `password`, `api_key`, `authorization`, `cookie`, `webhook`, Try session URLs `/s/<token>`, and secret values from `env`).
- Strip request bodies (`requestBody`, `request_body`), model response prose (`responseProse`, `response_prose`), and user source code snippets (`userSource`, `sourceCode`), keeping only PDD command names, error codes, PDD `src/` stack frames and version metadata.
- Redact filesystem paths under the user's `home` directory to `~/<redacted>`, except PDD's own state and skill paths (`~/.local/state/pdd/...`, `~/.pdd/...`, `~/.config/pdd/...`, `~/.agents/skills/pdd-...`, `~/.claude/skills/pdd-...`), which normalize the home prefix to `~` while preserving the PDD state subpath.

`selfReportConsent(repo, config, state)` and `resolveSelfReportConsent({repo, config, state, ask}, ports)` enforce repository consent:
- Respect explicit `autopilot.selfReport` (`"auto" | "ask" | "off"`) in `pdd.json`.
- When unset, default to `"auto"` when `repo` belongs to the `promptdriven` organization (`promptdriven/*`).
- Outside `promptdriven/*` when unset, default to asking the person once with `CONSENT_PROMPT` (`"May Autopilot file PDD bug reports for failures in PDD itself? auto / ask each time / off"`). Persist an `"auto"` or `"off"` answer in state so the person is not asked again; `"ask"` asks on each reportable failure; `"off"` or an unanswered noninteractive prompt records `action: "skipped"` and makes no GitHub write.

## Parking, wake and status/cost accounting

When a reportable failure files or matches issue `#N` in `promptdriven/pdd`, `reconcileSelfReports` records `blockedOn: {kind: side === "runtime" ? "runtime" : "pdd", until: "#N"}` (or `String(N)` for runtime) on the run and returns the blocker so Autopilot parks the run naming `#N`. When `#N` closes in `promptdriven/pdd`, the blocker clears and Autopilot wakes the parked run.

Record every outcome (`filed`, `commented`, `skipped`) in `run.selfReports` and `state.selfReports` (`{filed, commented, skipped}`). `pdd autopilot status`, `pdd autopilot status --json` and the cost ledger (`costReport` and `costStatusLines`) report `filed`, `commented` and `skipped` counts.

## Dependencies

- [Issue reporting guide](../../docs/ISSUES.md): required report sections, version check and pre-filing search rules.
- [Fixed self-report brief](../../docs/autopilot-self-report.md): required instructions for the read-only diagnose subagent.
- [Launch profile](workflow-launch-profile.prompt.md): saved agent command, account and model selection.
- [Cost ledger](cost-ledger.prompt.md): subagent session token capture and self-report status/report counts.

<details><summary>Runtime interface</summary>

```json
{"prose_sha256":"6703e4b175ddd7f5e78fd86cc007a543ca0f196a22473c9c3179c4152b3c5612","status":"draft","entries":[],"calls":[],"resources":[],"limits":{"max_steps":12,"max_model_calls":6},"conventions":[]}
```
</details>
