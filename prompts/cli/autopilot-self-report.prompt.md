# PDD self-report filing and shared Runtime filing entrypoint

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
| `runtime` | `no-verdict`, `runner-stopped`, `provider-error`, `server-refusal`, `timeout` | `true` | Runtime service failure (`classifyRuntimeFailure(check, health)` or `run.runtimeWait` / check batch with no verdict, stopped runner, upstream provider error, timeout, or HTTP 5xx / server refusal that is not a prompt expectation, binding or sign-in failure). Provider/account/budget limits, including HTTP 429, `provider-call-cap`, and `call-cap-reached`, are person/account causes and are never Runtime defects. |
| `user` | `user-code`, `user-tests`, `user-prompt`, `user-environment` | `false` | The user's own code, tests, prompt expectations, file-rule refusals, binding refusals, repair limits, PR CI failures, repository dependencies, or host toolchain validation |
| `person` | `person-gate`, `person-question`, `person-access`, `person-review`, `account` | `false` | Waiting for a person gate, an independent person question, strict terminal approval, PR human review, account/GitHub quota reset, sign-in (`gh auth login`, HTTP 401/403), or provider/account/budget caps (`HTTP 429`, `provider-call-cap`, `call-cap-reached`). |

Both `pdd` and `runtime` causes are reportable (`reportable: true`) and the shared `fileSelfReport` helper accepts either side. The launcher currently reconciles only PDD/Autopilot causes; automatic Runtime filing and wake require a separate shared-adapter integration. PDD reports target `promptdriven/pdd`. Runtime reports target `promptdriven/prompt-runtime` only when repository permission evidence confirms `WRITE`, `MAINTAIN`, or `ADMIN`; otherwise they target public `promptdriven/pdd` and include `pdd:runtime-report`. User code/tests (`user`) and person decisions (`person`) return `reportable: false` and never file a report. Healthy running work returns `{side:"none",kind:"none",reportable:false}`.

Every reportable classification derives the canonical cause signature `${code}:${module}:${fn}`. Search also accepts the earlier `${code}+${module}+${fn}` marker for compatibility, but new issue markers and comments use the canonical colon form:
- `code`: the stable error code or failure slug (for example `ERR_PDD_CRASH`, `TypeError`, `INVARIANT_BROKEN`, `MISSING_COMMAND`, `AUTOPILOT_STATE_BUG`, or `RUNTIME_NO_VERDICT`).
- `module`: the normalized PDD source module path (for example `src/workflow-runner.mjs`) from the first `src/*.mjs` stack frame or saved record, or `runtime-service` for Runtime causes.
- `fn`: the owning function or command operation (for example `stepDoneCommand` or `pdd-test`).

Reuse existing automatic route-question grouping (`routeQuestionsTick`, `"Missing PDD route: <kind>"`) for `pdd-route` questions without duplicating its issue creation.

## Diagnose subagent for PDD/Autopilot causes

For a `pdd`-side failure, `diagnosePddFailure(run, cause, ports)` launches at most one fresh read-only agent session per run failure occurrence (`runId` + canonical `signature`) using the bundled brief `docs/autopilot-self-report.md` and the run's saved launch profile, including its actual agent, model and account directory (`codex exec --sandbox read-only --json` or `claude -p --output-format json --permission-mode plan`). Merge the base environment and the saved agent-definition environment first, set or clear the profile account variable to match the saved `configDir`, then remove the workflow-chat session markers from the final environment so overrides cannot restore a worker or coordinator session. Do not claim or use a different account. Save the actual agent, `configDir` and session metadata in `run.selfReports` for cost-ledger attribution. Treat every subagent field as untrusted. Build the public report only from bounded, validated structured PDD facts and fixed summaries; never copy free-form subagent, source, request or response text. Publish a diagnosis `file:line` only when the checked-out PDD source verifies that the named function owns that line; otherwise omit the location. Regex redaction is defense in depth, not the publication filter. Keep private run and batch identifiers out of issue bodies and comments.

The diagnose subagent and local fallback inspector:
1. Reproduce when safe and read-only, and inspect the saved run record, crash stack, `pdd` package version and relevant PDD source file around the failing frame.
2. Locate the root cause with `file:line` evidence (for example `src/workflow-runner.mjs:1234`). Before returning it, verify against the checked-out PDD source that the named function owns that line; omit the location when it cannot be verified.
3. Search existing open and recently closed issues in `promptdriven/pdd` for the same canonical signature (`code:module:fn`) and the earlier plus-separated marker for compatibility.
4. Format the report in the [issue reporting guide](../../docs/ISSUES.md) shape: Problem, Steps to reproduce, Expected vs actual, Evidence, Versions, and Suspected root cause (`file:line`).

## Shared filing path, target guard, deduplication and daily cap

`fileSelfReport(input, ports)` accepts both PDD/Autopilot-side (`side: "pdd"`) and Runtime-side (`side: "runtime"`) causes. Autopilot currently reconciles PDD/Autopilot causes only; automatic Runtime filing and its wake path require the shared-adapter integration and are not wired here:
- **Target repository guard**: PDD causes always target `promptdriven/pdd`. For a Runtime cause, use `ports.repoPermission(repo)` when available, else read `gh repo view promptdriven/prompt-runtime --json viewerPermission`. Only `WRITE`, `MAINTAIN`, or `ADMIN` confirms private write access and selects `promptdriven/prompt-runtime`. An unavailable, failed or other permission result selects public `promptdriven/pdd` and label `pdd:runtime-report`. Never file in the working repository or an arbitrary target.
- **Signature marker**: Include the canonical `<!-- pdd:self-report:CODE:MODULE:FUNCTION -->` in every new issue body (and `<!-- pdd:runtime-cause:CAUSE -->` when `side === "runtime"`). Search for both the canonical colon marker and the earlier plus-separated marker; new comments and issue bodies use the canonical marker.
- **Search and deduplicate**: Search open and recently closed issues in the selected target repository for the signature marker before creating an issue.
  - A matching open issue normally gets one redacted occurrence comment and no new issue (`action: "commented"`). If a durable pending create reservation for this run and signature exists, reconcile the matching open or closed issue into that reservation and record `action: "filed"` without a comment. Do not publish run or batch identifiers.
  - Before a new issue write, hold the existing claim-safe machine-state lock, reload `self-report-machine.json`, and reserve one slot with the filing intent. Persist the reservation before the GitHub issue write. Pending reservations count toward `DAILY_SELF_REPORT_CAP = 5` new issues per machine per UTC day. Reuse the same day's reservation on retry. If failure occurs before issue creation starts, release the reservation; after issue creation starts, keep it until an issue search resolves the outcome.
  - When the machine has already reserved 5 new self-report issues on the current UTC day and this filing has no reservation, create no new issue; if an existing self-report issue from today or a matching closed issue is available, add one occurrence comment (`action: "commented"`, `capped: true`), else record `action: "skipped"`, `reason: "daily-cap"`.
  - When under the daily cap, create one new issue in the selected repository only after its reservation is durable. PDD issues use `pdd:self-report`; public Runtime fallback issues use both `pdd:self-report` and `pdd:runtime-report`. Do not assume labels exist on the private Runtime repository. When a maintainer login is configured for the selected repository, assign the issue; otherwise leave it unassigned.

## Privacy, redaction and consent

`redactSelfReport(value, {home, env}={})` removes sensitive data before any issue search, creation or comment. First construct every public title, issue body and comment from known public structured fields and bounded safe summaries. Never publish raw diagnosis output, arbitrary source snippets, request/response prose, run IDs or batch IDs. Regex redaction is defense in depth, not a substitute for this allowlist. The function also:
- Strip credentials, tokens and keys (`ghp_`, `gho_`, `ghu_`, `ghs_`, `ghr_`, `github_pat_`, `sk-`, `sk-ant-`, `xox[baprs]-`, `AIza`, `Bearer ...`, `Basic ...`, key/value assignments for `token`, `secret`, `password`, `api_key`, `authorization`, `cookie`, `webhook`, Try session URLs `/s/<token>`, and secret values from `env`).
- Strip request bodies (`requestBody`, `request_body`), model response prose (`responseProse`, `response_prose`), and user source code snippets (`userSource`, `sourceCode`), keeping only PDD command names, error codes, PDD `src/` stack frames and version metadata.
- Redact filesystem paths under the user's `home` directory to `~/<redacted>`, except PDD's own state and skill paths (`~/.local/state/pdd/...`, `~/.pdd/...`, `~/.config/pdd/...`, `~/.agents/skills/pdd-...`, `~/.claude/skills/pdd-...`), which normalize the home prefix to `~` while preserving the PDD state subpath.

`selfReportConsent(repo, config, state)` and `resolveSelfReportConsent({repo, config, state, ask}, ports)` enforce repository consent. Resolve consent for every filing unless the caller explicitly passes `checkConsent: false` after resolving it. Missing repository context is outside the `promptdriven` organization and therefore asks once by default; without an ask port, record a consent skip and make no GitHub read or write:
- Respect explicit `autopilot.selfReport` (`"auto" | "ask" | "off"`) in `pdd.json`.
- When unset, default to `"auto"` when `repo` belongs to the `promptdriven` organization (`promptdriven/*`).
- Outside `promptdriven/*` when unset, default to asking the person once with `CONSENT_PROMPT` (`"May Autopilot file PDD bug reports for failures in PDD itself? auto / ask each time / off"`). Persist an `"auto"` or `"off"` answer in state so the person is not asked again; `"ask"` asks on each reportable failure; `"off"` or an unanswered noninteractive prompt records `action: "skipped"` and makes no GitHub write.

## Parking, wake and status/cost accounting

When a PDD/Autopilot failure files or matches issue `#N` in `promptdriven/pdd`, `reconcileSelfReports` records a PDD blocker on the run and returns it so Autopilot parks the run naming `#N`. When `#N` closes, the blocker clears and Autopilot wakes the parked run. The helper can represent Runtime blockers, but this launcher does not enable automatic Runtime reconciliation or wake.

Record an outcome only after its required write succeeds: `filed` after a confirmed or reconciled issue create, `commented` after a confirmed comment, and `skipped` when filing does not occur. A missing comment writer is an error and must not increment counters or record an outcome. Store outcomes in `run.selfReports` and `state.selfReports` (`{filed, commented, skipped}`). Use distinct IDs for distinct actions. Record the diagnosis attempt, its safe result, session metadata and filing attempt count in the existing self-report ledger before side effects. Reuse a saved diagnosis after filing errors and retry filing at most twice; never repeat paid diagnosis on every tick. A diagnosis-only `run.selfReports` entry may carry the actual session for cost accounting, but it does not increment outcome counts. `pdd autopilot status`, `pdd autopilot status --json` and the cost ledger (`costReport` and `costStatusLines`) report only `filed`, `commented` and `skipped` outcomes.

## Dependencies

- [Issue reporting guide](../../docs/ISSUES.md): required report sections, version check and pre-filing search rules.
- [Fixed self-report brief](../../docs/autopilot-self-report.md): required instructions for the read-only diagnose subagent.
- [Launch profile](workflow-launch-profile.prompt.md): saved agent command, account and model selection.
- [Cost ledger](cost-ledger.prompt.md): subagent session token capture and self-report status/report counts.

<details><summary>Runtime interface</summary>

```json
{"prose_sha256":"6795dd6feaec282298faca686b6a2f7bc2178d6148b4c8d26ed21ba85f61871c","status":"draft","entries":[],"calls":[],"resources":[],"limits":{"max_steps":12,"max_model_calls":6},"conventions":[]}
```
</details>
