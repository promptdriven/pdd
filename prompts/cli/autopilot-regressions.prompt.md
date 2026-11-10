# Autopilot regression detection

Own `src/autopilot-regressions.mjs`. New behavior authorized by the regression
builder brief: inspect core merge history and GitHub evidence without changing
GitHub, running agents, rerunning tests, reverting, or changing engine state.
The core engine and its prompt remain unchanged. Existing CLI behavior is preserved.

## Scan contract

Export async `regressionScan(ports)`, a small hook for a later core caller.
Required ports are `root` (the repository's core state directory), `repo`
(owner/name), and async `gh(args)` returning `{code,stdout,stderr}` like the core
port. `fs.readFileSync(path,'utf8')` and `now()` are injectable, with native fs and
Date.now defaults. All decisions use these ports. Read only root/history.jsonl;
an absent file means no merges. Skip invalid JSON/non-object lines, reporting
incompleteness, and ignore outcomes other than `merged`. Deduplicate by repository
(case insensitive) and positive integer PR. Core rows have `at` (epoch ms),
`issue`, `pr`; optional row `repo` must match the supplied repository. Missing PR
identity is reported as incomplete, never silently counted as ok.

Resolve each PR through REST, requiring merged_at and merge_commit_sha; read the
commit and its first parent. Core history has no SHA, so the PR supplies it.
Missing required identity, a failed read or malformed response adds an error;
continue other merges and signals. A missing parent is incomplete. No error
includes raw process output. Never turn unavailable evidence into an ok verdict.

Read all pages of check runs (filter all), commit statuses, timelines on the PR
and recorded issue, repository issues updated since the earliest merge, repository
PRs (all states), and commits on the default branch since the earliest merge.
Follow GitHub next links only within that repository's REST namespace; cycles,
invalid links and failed pages are errors rather than successful truncation.
Use explicit GET for every GitHub call. Do not use search's limited result set.

Each signal has `kind` (`ci`, `revert`, `reopened`, `reference`, `unavailable`),
`level` (`suspect` or `proven`), `at` (ISO UTC timestamp or null), `url` (evidence
link or null), `detail` (safe single-line explanation), and `parentUrl` (comparison
check link or null). Collect evidence after the original merge and no later than
now; undated red checks remain suspect. Classification is proven if any signal
is proven, otherwise suspect if any signal exists, otherwise ok.

| Evidence | Classification |
|---|---|
| Latest check run for the same app id/name is failure, timed_out, cancelled, action_required, startup_failure, or stale; or latest status context is failure/error | suspect |
| That red result is dated at/after the merge and its matching parent result is success | proven (the brief's CI rule; no claim of deflaking) |
| Pending, neutral, skipped, or absent checks | no regression signal; absence/pending does not prove health |
| Later default-branch commit says `This reverts commit FULL_SHA.` matching the merge | proven |
| Later PR explicitly says `Reverts owner/repo#PR`, `Reverts #PR`, or `Reverts` followed by the exact PR URL | proven if merged, suspect if only proposed; closed unmerged PRs stay suspect |
| A later PR title is exactly `Revert "ORIGINAL_TITLE"`, without an exact target | suspect |
| New issue title/body explicitly says `Regressed by #PR`, qualified repository reference, or exact PR URL | proven |
| New issue mentions this PR or recorded issue through a number, same-repo qualified reference or URL; or a timeline cross-reference originates in a new same-repo issue | suspect |
| Recorded issue has a later `reopened` event | suspect |

Match complete reference identities, never number prefixes or references to
another repository. Cross-references and reopens alone do not establish cause.
Ignore a reopen carrying a `<!-- pdd:... -->` marker or with a same-actor marked
comment within five minutes: machine actions cannot establish a human reopen.
Do not suppress other people's events on the basis of the account name alone.
Do not treat an old issue or an event before the merge as new evidence.
Select latest CI observations by timestamp then numeric id; status and check-run
names occupy separate namespaces. A later successful rerun clears an earlier red.

Return exactly `{schema, scannedAt, complete, merges, counts, days, errors}`:
`schema` is `pdd.autopilot-regressions.v1`, `scannedAt` is now as ISO UTC;
`complete` is true only if `errors` is empty. `merges` follows first history
appearance, with exactly `{repo, pr, issue, mergeCommit, parent, mergedAt,
classification, provenAt, signals}`. `issue` is the recorded positive issue or
null; SHA/time values unavailable after a read failure are null. `provenAt` is
the earliest dated proven signal or null. `counts` has integer `ok`, `suspect`,
`proven`; `days` is an ascending array of `{date, proven}` (UTC YYYY-MM-DD,
distinct PRs first proven that day). Multiple signals count a merge only once,
including duplicate history lines. Never count suspects or undated proof in a
daily total. `errors` is an array of safe diagnostic strings. A repeated scan
recomputes from evidence, with no saved ledger or metric write. Reporting days
are UTC; a future scorecard consumer owns its timezone/window conversion.

## Command adapter

Export async `runAutopilotRegressions({cwd,env,json,file}, ports={})` returning
`{exitCode,message}`. Native filesystem and process effects belong here: injected
`fs`, `run(file,args,{cwd,env,...})`, `gh`, `now`, `stateRoot` and optional `root`
can replace them. Resolve Git root with `git rev-parse --show-toplevel`; hash it
with sha256 truncated to 20 hex as the launcher does. Read the saved launcher
JSON from stateRoot/HASH.json, default stateRoot HOME/.local/state/pdd/autopilot,
and scan HASH-core. No folder creation, timer, sign-in probe or launcher call.
Require its repo, or, for no saved state, resolve origin with the shared GitHub
origin parser. An explicit ports.root bypasses state discovery but still requires
ports.repo. GitHub uses the counted process adapter by default.

JSON mode prints the scan object. Text starts with the counts and one line per
merge with classification and signals, plus any errors. Zero means a complete
scan (even if proven); one means incomplete scan or discovery/output failure.
Empty history is a complete scan with zero counts, meaning none detected.
`--file PATH` exclusively creates a local UTF-8 report with the same rendered
content plus newline (relative to cwd); existing files and symlinks are refused,
and no parent directories are created. It never overwrites state or source files.
File errors give exit 1. Successful file output still prints the report.

## Dependencies

- [Core engine](autopilot-core.prompt.md), State: required generation/verification
  context for history records and root layout; the scanner does not invoke ticks.
- [GitHub calls](github-calls.prompt.md): required native adapter context for
  counted GitHub process calls.
- [Workflow worktree](workflow-worktree.prompt.md): required native context for
  `githubOriginRepository` parsing of origin in CLI discovery.
- [Secret redaction](secret-redaction.prompt.md): required for diagnostic and
  displayed external names. Node fs/path/crypto and the native process adapter
  supply local I/O, path resolution and deterministic SHA256 identity.

<details>
<summary>Runtime interface</summary>

```json
{"kind":"partial","status":"draft","prose_sha256":"","entries":[],"calls":[],"resources":[],"limits":{"max_steps":10,"max_model_calls":12},"conventions":[]}
```

</details>
