# Local Autopilot metrics observations

`src/autopilot-metrics-source.mjs` owns native collection and a small
durable hook used by core lifecycle transitions. The reader never starts work or records approvals.

`readAutopilotMetrics({timezone,observedAt},ports={})` returns the scorecard.
Ports: synchronous `fs`, `env`, `homedir`, `stateRoot`, `now` (epoch ms,
default Date.now; distinct from a historical report cutoff), `auditRoot` (default
sibling `autopilot-audits` of the launcher state root), async
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
by core at the owning transition. Core binds allowlisted PR-body and merge-comment Evidence to the verified
job head before writing the local observation. Public text and timestamps never
establish validation, merge attribution or an earlier observation time. Missing local evidence counts zero, even when public text
claims success. Core owns stable per-head observations and exact-head gate
attestations; historical reports must not move when a PR or comment is edited.

For locally associated PRs only, make GitHub GETs for PR and exact merge-commit
check runs and commit statuses (`commits/SHA/statuses`). Native pagination retains
every page, with a 15-second subprocess timeout. Only a local merged metric establishes Autopilot attribution; never
move its occurrence time using mutable PR metadata. For a recorded Autopilot
merge, a completed check run with matching `head_sha` and conclusion `failure`,
`timed_out`, `action_required`, `startup_failure`, `cancelled` or `stale` records
`merge-ci-red` at `completed_at`. Commit statuses returned by the exact-SHA endpoint with state `failure` or
`error` record it at `created_at` (a status is an immutable occurrence). The
endpoint binds normal status objects, which omit `sha`; reject an explicitly
foreign `sha` when supplied. Check runs require a matching `head_sha`. Check/status observations dedupe
by issue and reporting day through the scorecard.

For an explicitly attributed local merge only, collect existing structured BAD
audit records from `auditRoot/HASH/records/IDENTITY.json`, using the audit owner's
repository hash, identity and recorded-result schema. Require matching repository,
PR and exact merge SHA; discovery time is the saved `completedAt`. Malformed,
foreign, manual-merge and unrelated findings count zero. If multiple matching BAD records exist before the first read, use the earliest
`completedAt`, regardless of directory order. Exact locally saved merge SHAs
permit this audit collection even when GitHub is unavailable. No auditor is launched.
Also GET the merged PR's base-branch commits since its recorded merge time. Only
a reachable commit with a valid SHA and a standard git-revert line naming that
exact merge (`This reverts commit SHA.` or `This reverts commit SHA, reversing`)
establishes a revert discovery. A recommendation or unmerged revert branch does
not. Revert discovery time is `now()`, never mutable commit dates or report cutoff.
Persist allowlisted BAD/revert observations in their owning core history, retaining
the first `(repo,issue,pr,mergeCommit,reason)` occurrence through later reports and
cleanup; append failures warn locally and keep the observed report available.
Historical cutoffs cannot backdate discoveries. Existing local metric records
retain their original times. Daily issue deduplication combines BAD/revert/CI
findings. Group base-history reads by repo/base and restrict them to known merges. Independent GitHub read failures stay
local and do not suppress the other CI source. Do not emit raw bodies, names or
commands. Native calls use the counted gh runner, purpose other.

`recordAutopilotMetric({root,repo,issue,kind,at,pr,head,mergeCommit,evidence,validation,reason},
ports={})` is the lifecycle integration hook: validate the scorecard event domain
and any supplied PR/SHA or throw `Invalid Autopilot metric`. Keep only named
fields, lowercase repo/head, append `{metric:event}` to root/history.jsonl.
Repair a cut trailing line with newline first. Directory/file modes: 0700/0600.
All filesystem effects use `ports.fs`. The reporting reader uses it only for the discovered BAD/revert observations
above; it never changes jobs, workflow state, approvals or public objects.

## Dependencies

- [Scorecard](autopilot-metrics.prompt.md): required event domain and calculation
  for generation and native verification.
- [Audit records](autopilot-audit.prompt.md): required shared-record schema,
  repository hash and identity calculation for read-only finding collection.
- [GitHub calls](github-calls.prompt.md): required counted runner behavior.
- Node fs/path/OS/child-process facilities back the injected native ports.

<details><summary>Runtime interface</summary>

```json
{"kind":"partial","status":"draft","prose_sha256":"","entries":[],"calls":[],"resources":[],"limits":{"max_steps":4,"max_model_calls":2},"conventions":[]}
```

</details>
