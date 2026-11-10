# Local Autopilot metrics observations

`src/autopilot-metrics-source.mjs` owns read-only native collection and a small
durable hook used by core lifecycle transitions. The reader never starts work or records approvals.

`readAutopilotMetrics({timezone,observedAt},ports={})` returns the scorecard.
Ports: synchronous `fs`, `env`, `homedir`, `stateRoot`, async
`github(repo,path)` returning parsed JSON, or `execFile` for the native gh adapter
(an injected runner is not wrapped). Default root matches the launcher:
HOME (homedir fallback) + `.local/state/pdd/autopilot`. Read launcher records
named 20 lowercase hex digits + `.json`, including stopped records. Each supplies
`repo` and sibling `<id>-core/history.jsonl` and `jobs/<issue>.json`. Skip missing
files, malformed records and partial JSONL lines. Other filesystem failures
propagate. Never follow saved cwd/worktree/log paths or symlinks.

History accepts `{metric: event}` from the hook. Existing core rows
`{at,issue,outcome,pr?}` establish work and PR association only: even `merged`
can mean core observed a person's merge, so ambiguous historical outcomes never
establish Autopilot attribution. Active `pdd.core-job.v1` files provide `started`,
`prAt` and agent/review.agent/suite.agent `started` work timestamps.

Pass evidence and validation come only from durable local hook events recorded
by core at the owning transition. PR bodies and public comments are mutable and
unauthenticated: neither their text nor their timestamps establishes a check,
validation or merge. Missing local evidence counts zero, even when public text
claims success. Core owns stable per-head observations and exact-head gate
attestations; historical reports must not move when a PR or comment is edited.

For locally associated PRs only, make GitHub GETs for PR and exact merge-commit
check runs and commit statuses (`commits/SHA/statuses`). Native pagination retains
every page. Only a local merged metric establishes Autopilot attribution; never
move its occurrence time using mutable PR metadata. For a recorded Autopilot
merge, a completed check run with matching `head_sha` and conclusion `failure`,
`timed_out`, `action_required`, `startup_failure`, `cancelled` or `stale` records
`merge-ci-red` at `completed_at`. A commit status with matching `sha` and state
`failure` or `error` records it at `created_at` (a status is an immutable occurrence).
A missing or foreign SHA supplies no evidence. Check/status observations dedupe
by issue and reporting day through the scorecard. Reverts and BAD audits require
explicit hook records with discovery time. Independent GitHub read failures stay
local and do not suppress the other CI source. Do not emit raw bodies, names or
commands. Native calls use the counted gh runner, purpose other.

`recordAutopilotMetric({root,repo,issue,kind,at,pr,head,evidence,validation,reason},
ports={})` is the lifecycle integration hook: validate the scorecard event domain
and any supplied PR/SHA or throw `Invalid Autopilot metric`. Keep only named
fields, lowercase repo/head, append `{metric:event}` to root/history.jsonl.
Repair a cut trailing line with newline first. Directory/file modes: 0700/0600.
All filesystem effects use `ports.fs`. The reporting reader never calls it.

## Dependencies

- [Scorecard](autopilot-metrics.prompt.md): required event domain and calculation
  for generation and native verification.
- [GitHub calls](github-calls.prompt.md): required counted runner behavior.
- Node fs/path/OS/child-process facilities back the injected native ports.

<details><summary>Runtime interface</summary>

```json
{"kind":"partial","status":"draft","prose_sha256":"","entries":[],"calls":[],"resources":[],"limits":{"max_steps":4,"max_model_calls":2},"conventions":[]}
```

</details>
