# Local Autopilot metrics observations

`src/autopilot-metrics-source.mjs` owns read-only native collection and a small
hook core may call later. It never starts work, records approvals or edits core.

`readAutopilotMetrics({timezone,observedAt},ports={})` returns the scorecard.
Ports: synchronous `fs`, `env`, `homedir`, `stateRoot`, async
`github(repo,path)` returning parsed JSON, or `execFile` for the native gh adapter
(an injected runner is not wrapped). Default root matches the launcher:
HOME (homedir fallback) + `.local/state/pdd/autopilot`. Read launcher records
named 20 lowercase hex digits + `.json`, including stopped records. Each supplies
`repo` and sibling `<id>-core/history.jsonl` and `jobs/<issue>.json`. Skip missing
files, malformed records and partial JSONL lines. Other filesystem failures
propagate. Never follow saved cwd/worktree/log paths or symlinks.

History accepts `{metric: event}` from the hook and existing core rows
`{at,issue,outcome,pr?}`: outcomes are work, `merged` is also an Autopilot merge.
Never infer removed jobs' starts from ends. Active `pdd.core-job.v1` files provide
`started`, `prAt` and agent/review.agent/suite.agent `started` work timestamps;
their fixed `evidence` line uses `prAt`. No evidence line means no recorded pass.

For locally associated PRs only, make GitHub GETs for PR, comments and exact
merge-commit checks. Native pagination must retain every page. PR body evidence
uses `updated_at` and `head.sha`; a body without an Evidence line supplies no
work observation. Core merge comments need both exact
`<!-- pdd:autopilot-core:merge:HEAD -->` and
`Autopilot merge check passed for head HEAD.` with the PR's head SHA, at
`created_at`. Evidence can come from that comment. Validation additionally needs
fixed-line tests pass and lines `- Full test suite: pass`,
`- Review: PASS from a fresh reviewer`, `- CI: green (N check(s))`, N > 0.
Those core attestations establish fresh independent review, suite and CI on
that exact head; CI none, missing lines and stale heads count zero.
PR merged_at plus a matching preceding core merge comment establishes an
Autopilot merge; a manual merge without this evidence or merged history does not.
For a locally recorded merge associated with a PR, its valid merged_at refines
the history timestamp (which can reflect cleanup). Count the PR's actual merge
day once, rather than two days when cleanup crosses 09:00.
For a recorded Autopilot merge, a completed failure/timed_out/action_required
check with head_sha equal to merge_commit_sha records `merge-ci-red` at
completed_at. Reverts and BAD audits require explicit hook records with their
discovery time. GitHub failure supplies no unrecorded success. Do not emit raw
bodies, names or commands. Native calls use the counted gh runner, purpose other.

`recordAutopilotMetric({root,repo,issue,kind,at,pr,head,evidence,validation,reason},
ports={})` is the future integration hook: validate the scorecard event domain
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
