# Autopilot regression detection

Own `src/autopilot-regressions.mjs`. Inspect core merge history and GitHub
evidence without changing GitHub, running agents, rerunning tests, or reverting.
Provide both the stateless full-scan API (`regressionScan` and CLI command
`runAutopilotRegressions`) and the bounded incremental post-merge check
(`checkPostMergeRegressions`) used by [Autopilot core](autopilot-core.prompt.md)
(`#3182`).

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
Validate check identity/app, status context, conclusion/state, PR/issue identity
and event shapes; malformed observations make the affected merge incomplete.
Keep already-read pages if a later page fails.
Follow GitHub next links only within that repository's REST namespace; cycles,
invalid links and failed pages are errors rather than successful truncation.
Use explicit GET for every GitHub call. Do not use search's limited result set.

One scan may issue at most 100 GitHub requests in total, including failed reads
and every page, across all merges and shared evidence. Before request 101, stop
all further GitHub reads. Also stop further reads immediately after HTTP 429,
any Retry-After response header, or x-ratelimit-remaining at or below zero
(regardless of reset time). Observe headers even when gh throws with stdout.
A successful response that exhausts the allowance still supplies its evidence.
Keep the stop reason and request count only in memory; do not retry, wait for a
reset, or write a ledger. Subsequent required reads add safe unavailable signals
and errors naming the rate limit, Retry-After or request budget. Preserve all
collected pages and proof; unexamined merges remain incomplete/suspect rather
than ok. Ordinary read failures still allow other merges within the budget.

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
| Later default-branch commit says `This reverts commit FULL_SHA.` or the standard merge-revert form `This reverts commit FULL_SHA, reversing` followed by whitespace and `changes made to PARENT.` | proven when FULL_SHA matches the exact merge SHA, case insensitive; shorter, longer and different SHAs never match |
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

## Incremental post-merge check

Export async `checkPostMergeRegressions(ports)` for [Autopilot core](autopilot-core.prompt.md)
post-merge monitoring (`#3182`). Required ports are `root`, `repo` and GET-only
`gh(args)`; optional ports are `fs`, `now`, `maxRequests` (default `40`),
`maxMerges` (default `10`) and `minRecheckMs` (default `900000`, 15 minutes).
Read distinct `outcome === "merged"` rows from `root/history.jsonl` (recording
both `issue` and any companion `issues` array) and persist incremental state
atomically at `root/post-merge.json` (`schema: "pdd.autopilot-post-merge.v1"`).
When no merged PRs exist in history, return zero counts without calling GitHub
or writing `post-merge.json`.

Each call starts at the saved `cursor`, skips merges merged in the current tick
(`at >= now`) or checked within `minRecheckMs`, and examines at most `maxMerges`
eligible merges within `maxRequests` GET calls (caching immutable resolved PR
`mergeCommit`, `mergedAt`, `title`, and first `parent` once read, and setting
`parentChecked: true` only after all parent CI pages succeed with no pending or
in-progress check runs or commit statuses). Follow GitHub `Link: <...>;
rel="next"` pagination strictly within the repository REST namespace across all
list reads (`check-runs`, `statuses`, `issues/N/timeline`, `commits?since=...`,
and `pulls?state=all&sort=updated&direction=desc`, stopping PR pagination early
once a descending-`updated_at` page reaches `updated_at <= since`), validating
row shapes and counting every page against `maxRequests`. When `budgetStop`
interrupts pagination mid-merge or mid-shared scan, persist resumable compact
stream cursors in `post-merge.json` (`activeSweep`) so subsequent ticks continue
from the next unread page instead of restarting at page 1. Stop further GitHub
reads before exceeding `maxRequests` or after HTTP 429, `Retry-After`, or
`x-ratelimit-remaining <= 0`, setting `budgetStopped: true` and `stopReason`.
Record and emit any `proven` regression signals immediately as each independent
signal stream (`check-runs`, `statuses`, each issue's `timeline`, and each
shared commit or PR page) finishes so a later HTTP error or budget stop on
another stream never drops observed proof; meanwhile, any failed, malformed,
pending-parent-CI (`parentChecked: false`) or budget-stopped read keeps the
merge unverified (never turning a merge with pending parent CI or unavailable
evidence into `ok` and never advancing `checkedAt`), leaving unexamined merges
at their prior state (`pending` when never checked).

For each examined merge, detect three actionable post-merge regression signals
after `mergedAt` (up to `now`):
- `reopened`: any recorded issue of the merge has a later non-machine `reopened`
  timeline event (ignoring `<!-- pdd:... -->` markers as above) or is currently
  `open` on GitHub without a machine-marked reopen;
- `revert`: a later default-branch commit reverts `mergeCommit` (`This reverts
  commit FULL_SHA...`) or a later merged PR explicitly `Reverts` the PR;
- `ci`: a red check run or commit status on `mergeCommit` dated at or after
  `mergedAt` whose matching parent observation was `success`.

Persist per-merge status (`pending`, `ok`, `reopened`, `reverted`, `ci`,
`suspect`), `reportedKeys`, `cursor`, and aggregate `counts` (`tracked`,
`pending`, `ok`, `reopened`, `reverted`, `ci`, `regressions`, `reopenOrRevert`,
`suspect`, where `regressions` targets `0`). Return
`{state, counts, newlyDetected, budgetStopped, stopReason, requests}`, emitting
each newly seen signal key once in `newlyDetected` (`{pr, issue, issues,
mergeCommit, mergedAt, kind, code, at, url, detail}`, with `code` equal to
`post-merge-reopen`, `post-merge-revert` or `post-merge-ci`).

### Safety circuit-breaker and shard-flake helpers (#3484)

Export synchronous `selectCircuitBreakerRegression(newlyDetected, {now}?)`. Choose
the first `revert`/`reverted` (`post-merge-revert`) item, or else the first
`ci`/`ci_broken` (`post-merge-ci`) item, from `newlyDetected`; ignore `reopened`
(`post-merge-reopen`). Return `{active: true, kind, code, pr, issue, trippedAt,
url, reason}` with redacted single-line detail, or `null` when none qualifies.

Export synchronous `evaluateShardFlakeRerun({checkRuns, statuses, headSha,
flakeRerunHead})`. Return `{action: none}` when `headSha` is empty,
`flakeRerunHead === headSha`, any commit status failed, zero or more than two
check runs failed, or any failed check run is outside a matrix shard family
(such as `lint`, `build`, `CI (lint)` or an unsharded job). When 1 or 2 matrix
shard check runs fail: if sibling shards in a failed group or checks sharing a
failed workflow run are still pending (or fewer than 4 checks have completed
while total checks are at least 4 and passing plus pending siblings are at least
3), return `{action: wait-siblings}`; once those pending checks finish, require
at least 4 completed check runs and at least 3 `success` sibling shards in every
failed shard group, returning `{action: rerun, runIds, checkIds, failedNames,
staleTokens}` (otherwise `{action: none}`).

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
ports.repo. GitHub uses a plain process adapter by default: no accounting, cache, cost ledger
or other Autopilot state writes. A core caller owns its supplied gh port.

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
- [GitHub calls](github-calls.prompt.md): required native context only for
  parsing `githubReply`; this command does not use its write-capable counter.
- [Workflow worktree](workflow-worktree.prompt.md): required native context for
  `githubOriginRepository` parsing of origin in CLI discovery.
- [Secret redaction](secret-redaction.prompt.md): required for diagnostic and
  displayed external names. Node fs/path/crypto and the native process adapter
  supply local I/O, path resolution and deterministic SHA256 identity.

The partial Runtime entry covers `regressionScan`; command discovery/output are
native-test coverage. Transport root/repo bind the same ports; numeric now binds
`now()`. Resource `fs.readFileSync` binds the actual UTF-8 read: `{text,code}`
wraps returned text with code empty, or a failed read with code ENOENT/other and
empty text, which the adapter raises as that filesystem error. Resource
`github.gh` binds the actual gh port arguments and process reply. These are
adapter shapes, not additional production exports. No live Runtime check is
claimed by this draft.

<details>
<summary>Runtime interface</summary>

```json
{"kind":"partial","status":"draft","prose_sha256":"","entries":[{"operation":"regressionScan","input_schema":{"type":"object","properties":{"root":{"type":"string"},"repo":{"type":"string"},"now":{"type":"number"}},"required":["root","repo","now"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"schema":{"type":"string","const":"pdd.autopilot-regressions.v1"},"scannedAt":{"type":"string"},"complete":{"type":"boolean"},"merges":{"type":"array","items":{"type":"object","properties":{"repo":{"type":"string"},"pr":{"type":"integer"},"issue":{"oneOf":[{"type":"integer"},{"type":"null"}]},"mergeCommit":{"oneOf":[{"type":"string"},{"type":"null"}]},"parent":{"oneOf":[{"type":"string"},{"type":"null"}]},"mergedAt":{"oneOf":[{"type":"string"},{"type":"null"}]},"classification":{"type":"string","enum":["ok","suspect","proven"]},"provenAt":{"oneOf":[{"type":"string"},{"type":"null"}]},"signals":{"type":"array","items":{"type":"object","properties":{"kind":{"type":"string","enum":["ci","revert","reopened","reference","unavailable"]},"level":{"type":"string","enum":["suspect","proven"]},"at":{"oneOf":[{"type":"string"},{"type":"null"}]},"url":{"oneOf":[{"type":"string"},{"type":"null"}]},"detail":{"type":"string"},"parentUrl":{"oneOf":[{"type":"string"},{"type":"null"}]}},"required":["kind","level","at","url","detail","parentUrl"],"additionalProperties":false}}},"required":["repo","pr","issue","mergeCommit","parent","mergedAt","classification","provenAt","signals"],"additionalProperties":false}},"counts":{"type":"object","properties":{"ok":{"type":"integer"},"suspect":{"type":"integer"},"proven":{"type":"integer"}},"required":["ok","suspect","proven"],"additionalProperties":false},"days":{"type":"array","items":{"type":"object","properties":{"date":{"type":"string"},"proven":{"type":"integer"}},"required":["date","proven"],"additionalProperties":false}},"errors":{"type":"array","items":{"type":"string"}}},"required":["schema","scannedAt","complete","merges","counts","days","errors"],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[{"name":"fs","kind":"port","access":"read","operations":[{"name":"readFileSync","access":"read","arguments_schema":{"type":"object","properties":{"path":{"type":"string"},"encoding":{"type":"string","const":"utf8"}},"required":["path","encoding"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"text":{"type":"string"},"code":{"type":"string"}},"required":["text","code"],"additionalProperties":false}}]},{"name":"github","kind":"port","access":"read","operations":[{"name":"gh","access":"read","arguments_schema":{"type":"object","properties":{"args":{"type":"array","items":{"type":"string"}}},"required":["args"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"code":{"type":"integer"},"stdout":{"type":"string"},"stderr":{"type":"string"}},"required":["code","stdout","stderr"],"additionalProperties":false}}]}],"limits":{"max_steps":10,"max_model_calls":12},"conventions":[]}
```

</details>
