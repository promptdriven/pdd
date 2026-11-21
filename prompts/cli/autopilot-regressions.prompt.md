# Autopilot regression detection

Own `src/autopilot-regressions.mjs`. Inspect core merge history and GitHub
evidence without changing GitHub, running agents, rerunning tests, or reverting.
Provide both the stateless full-scan API (`regressionScan` and CLI command
`runAutopilotRegressions`) and the bounded incremental post-merge check
(`checkPostMergeRegressions`) called by Autopilot core (`#3182`).

## Scan contract

Export async `regressionScan(ports)`, a shared scanner reused by `pdd autopilot regressions` and `pdd metrics`.
Required ports are `root` (the repository's core state directory, or `null` when only `candidates` are supplied), `repo`
(`owner/name`), and async `gh(args)` returning `{code, stdout, stderr}` like the core
port. `fs.readFileSync(path, 'utf8')` and `now()` are injectable, with native fs and
Date.now defaults. Optional ports: `candidates` (array of `{pr, issue?, issues?, outcome?, mergeCommit?, mergedAt?, title?}`
records from callers such as `pdd metrics`), `prs` (optional non-empty array of positive integer
PR numbers restricting which PRs are scanned), `includeCi` (boolean, default `true`; when `false`,
reuse valid pre-resolved `mergeCommit`, `mergedAt <= now`, and `title` on `candidates` and skip
per-PR `pulls/{pr}`, `commits/{sha}`, `check-runs`, and `statuses` reads), `boundedPulls` (boolean,
default `false`; when `true`, read `pulls?state=all&sort=updated&direction=desc&per_page=100` and
stop pagination early once a descending-`updated_at` page reaches `updated_at <= since`), and
`maxRequests` (positive integer request budget, default `100`). All decisions use these ports.

Read `root/history.jsonl` when `root` is provided; an absent `ENOENT` file means no history rows.
Skip invalid JSON/non-object lines, reporting incompleteness (`"Invalid core history line."`).
Include PRs from **both** `auto`-merged runs (`outcome === "merged"`) **and** non-`merged` runs
that created a PR (`outcome` such as `"would-merge"` in `observe` mode, `"stopped"`, `"ended"`,
`"needs-person"`, `"released"`, or `"abandoned"` with a positive integer `pr`) so PRs merged on
GitHub after `observe`, stopped, or assisted runs are scanned identically to `auto`-merged PRs:
- Optional row `repo` must be valid `owner/name` (else report error and skip) and match `ports.repo`
  case-insensitively (different repo is skipped).
- For `outcome === "merged"`, require a positive integer `pr`; missing/invalid `pr` is reported as
  incomplete (`"Merged history row has no valid PR."`), never silently counted as ok. Mark these
  rows `claimedMerged = true`.
- For non-`merged` rows (including `"would-merge"`, `"stopped"`, `"ended"`, `"needs-person"`,
  `"released"`, `"abandoned"`, or metadata rows without an outcome), if `pr` is absent/null/non-positive,
  skip quietly with no error; if `pr` is a positive integer, record it as a candidate PR with
  `claimedMerged = false`.
- Merge optional `ports.candidates` using the same rules, deduplicating by repository
  (case-insensitive) and positive integer `pr` in first appearance order. If the same `pr` appears
  multiple times across outcomes, keep one entry, upgrade `claimedMerged` to `true` if any row has
  `outcome === "merged"`, keep the first positive `issue`, and union all positive companion `issues`
  (`row.issue` and `row.issues`). When `ports.prs` is provided, keep only entries whose `pr` is in `ports.prs`.

Resolve each candidate PR through `GET repos/{repo}/pulls/{pr}`:
- For `claimedMerged === false` (observe/stopped/assisted candidates): when the PR read succeeds
  (HTTP 200, valid object with `number === pr`) and `merged_at == null` (open or closed unmerged on
  GitHub), exclude that PR cleanly from `merges` with no error. When it has a valid `merged_at <= now`
  and valid 40-hex `merge_commit_sha`, include it in `merges` and scan it identically to an
  `auto`-merged PR.
- For `claimedMerged === true`, require `merged_at <= now` and 40-hex `merge_commit_sha`.
- For any candidate, a failed read, malformed response, future `merged_at > now`, or missing
  `merge_commit_sha` on a merged PR adds an error and keeps the entry in `merges` with an
  `unavailable` suspect signal; continue other merges and signals. Read the merge commit and its
  first parent; a missing parent is incomplete. No error includes raw process output. Never turn
  unavailable evidence into an ok verdict.

Read all pages of check runs (filter all), commit statuses, timelines on the PR
and all recorded `issues` (primary `issue` plus companion `issues`), repository issues updated since
the earliest merge, repository PRs (all states), and commits on the default branch since the earliest merge.
Validate check identity/app, status context, conclusion/state, PR/issue identity
and event shapes; malformed observations make the affected merge incomplete.
Keep already-read pages if a later page fails.
Follow GitHub next links only within that repository's REST namespace (matching
`/repos/{repo}/` case-insensitively and rewriting matching same-endpoint canonical
`/repositories/<id>/<subpath>` next links back onto `repos/{repo}/<subpath>`); cycles,
invalid links and failed pages are errors rather than successful truncation.
Use explicit GET for every GitHub call. Do not use search's limited result set.

One scan may issue at most `maxRequests` (default `100`) GitHub requests in total, including failed reads
and every page, across all merges and shared evidence. Before exceeding the budget, stop
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
| New same-repo issue title/body explicitly blames this PR with `Regressed by`, `Regression from`, `Regression in`, `Broken by`, `Caused by`, or `Introduced by` followed by optional `PR ` and `#PR`, qualified `owner/repo#PR`, or exact PR URL | proven (`kind: "reference"`, `detail` naming `Issue #<number>`) |
| New same-repo issue carrying label `regression` (case-insensitive match on label `name` or string label) that references this PR or any recorded issue of the merge (same-repo `#N`, qualified `owner/repo#N`, URL, or timeline `cross-referenced` event) | proven (`kind: "reference"`, `detail` naming `Issue #<number>`) |
| Unlabeled new issue mentions this PR or recorded issue through a number, same-repo qualified reference or URL; or an unlabeled timeline cross-reference originates in a new same-repo issue | suspect (`kind: "reference"`) |
| Any recorded issue of the merge has a later `reopened` event | suspect (`kind: "reopened"`) |

Match complete reference identities, never number prefixes or references to
another repository. Cross-references and reopens alone do not establish cause in
the standalone `regressionScan` `proven` verdict (consumers such as `pdd metrics`
count `reopened` signals explicitly in their reopened breakdown).
Ignore a reopen carrying a `<!-- pdd:... -->` marker or with a same-actor marked
comment within five minutes: machine actions cannot establish a human reopen.
Do not suppress other people's events on the basis of the account name alone.
Do not treat an old issue or an event before the merge as new evidence.
Select latest CI observations by timestamp then numeric id; status and check-run
names occupy separate namespaces. A later successful rerun clears an earlier red.

Return exactly `{schema, scannedAt, complete, merges, counts, days, errors}`:
`schema` is `pdd.autopilot-regressions.v1`, `scannedAt` is now as ISO UTC;
`complete` is true only if `errors` is empty. `merges` follows first history
appearance (excluding unmerged non-`merged` candidates), with `{repo, pr, issue,
mergeCommit, parent, mergedAt, classification, provenAt, signals}`. `issue` is the
recorded positive issue or null; SHA/time values unavailable after a read failure
are null. `provenAt` is the earliest dated proven signal or null. `counts` has
integer `ok`, `suspect`, `proven`; `days` is an ascending array of `{date, proven}`
(UTC YYYY-MM-DD, distinct PRs first proven that day). Multiple signals count a merge
only once, including duplicate history lines. Never count suspects or undated proof
in a daily total. `errors` is an array of safe diagnostic strings. A repeated scan
recomputes from evidence, with no saved ledger or metric write. Reporting days are
UTC; scorecard consumers (`metrics-model`) own timezone/window conversion.

## Incremental post-merge check

Export async `checkPostMergeRegressions(ports)` for Autopilot core
post-merge monitoring (`#3182`). Required ports are `root`, `repo` and GET-only
`gh(args)`; optional ports are `fs`, `now`, `maxRequests` (default `40`),
`maxMerges` (default `10`) and `minRecheckMs` (default `900000`, 15 minutes).
Read distinct PR-bearing rows from `root/history.jsonl` — both `outcome === "merged"`
and non-`merged` outcomes with a positive integer `pr` (`would-merge`, `stopped`,
`ended`, `needs-person`, `released`, `abandoned`, skipping unmerged PRs once resolved
on GitHub and persisting `closedUnmerged: true` for closed-unmerged PRs so they are
not re-polled on later ticks; recording both `issue` and any companion `issues` array) — and persist
incremental state atomically at `root/post-merge.json` (`schema: "pdd.autopilot-post-merge.v1"`).
When no qualifying PRs exist in history, return zero counts without calling GitHub
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

Export synchronous `selectCircuitBreakerRegression(newlyDetected, {now,
clearedAfter}?)`. Ignore `reopened` (`post-merge-reopen`) and, when finite
`clearedAfter` (epoch ms or ISO string) is supplied, ignore items with
`at <= clearedAfter` (and `post-merge-ci` or undated items with
`mergedAt <= clearedAfter`). Choose the first remaining `revert`/`reverted`
(`post-merge-revert`) item, or else the first `ci`/`ci_broken`
(`post-merge-ci`) item. Return `{active: true, kind, code, pr, issue, trippedAt,
url, reason}` with redacted single-line detail, or `null` when none qualifies.

Export synchronous `evaluateShardFlakeRerun({checkRuns, statuses, headSha,
flakeRerunHead})`. Reject check names over 300 characters and parse shard
families by linear bracket/suffix slicing without backtracking regexes.
Normalize check `status`, `conclusion` and commit-status `state` to lowercase;
treat `completed` with `skipped` or `neutral` as finished non-failures, count a
check run as `pending` strictly when `status` is `queued`, `in_progress`,
`waiting`, `requested` or `pending`, and extract workflow run IDs from
`run_id`/`runId` or `details_url`/`detailsUrl`/`html_url`/`htmlUrl`. Return
`{action: none}` when `headSha` is empty, `flakeRerunHead === headSha`, any
commit status failed, zero or more than two check runs failed, or any failed
check run is outside a matrix shard family (such as `lint`, `build` or
`CI (lint)`). When 1 or 2 matrix shard check runs fail: if pending checks share
a failed workflow run or a failed shard group still has pending siblings (or
fewer than 4 checks have completed while total checks are at least 4 and passing
plus pending siblings are at least 3), return `{action: wait-siblings}`; once
those pending checks finish, require at least 4 completed check runs and at
least 3 `success` sibling shards in every failed shard group, returning
`{action: rerun, runIds, checkIds, failedNames, staleTokens, shards}` (otherwise
`{action: none}`).

### Cross-job flake ledger helpers (#3562)

Export pure deterministic constants `FLAKE_LEDGER_MAX_ENTRIES = 500`,
`FLAKE_REPEAT_THRESHOLD = 3`, `FLAKE_WINDOW_DAYS = 7`, and synchronous helpers:

- `normalizeFlakeEntry(entry, {now, requireTs}?)`: validate a plain object into
  `{ts, repo, issue, pr, head, target, outcome, detail}` or return `null` when
  invalid. `outcome` must be strictly one of `'flaked-then-passed'`,
  `'reproduced-red'`, or `'base-test-red'`. `target` must be a string and is
  secret-redacted, stripped of control characters and newlines,
  whitespace-collapsed, and capped to 200 characters (non-string or empty
  returns `null`). `ts` is ISO-8601 UTC within valid ECMAScript Date bounds
  (`|ms| <= 8.64e15`, defaulting to `now()` only when `entry.ts === undefined`
  and `!requireTs`; invalid, out-of-range, or required-missing returns `null`
  without throwing). `repo` is a valid `owner/name` or `null`; `issue` and `pr`
  are positive safe integers or `null`; `head` is trimmed and bounded to 40
  characters (lowercased when 7–40 hex) or `null`; `detail` is a safe redacted
  single-line string bounded to 300 characters or `null`.
- `parseFlakeLedger(raw)`: parse newline-delimited JSON fail-safely without
  throwing, ignoring blank, malformed, or timestamp-less lines via
  `normalizeFlakeEntry(parsed, {requireTs: true})`.
- `appendBoundedFlakeEntries(existingRaw, newEntries, {maxEntries = FLAKE_LEDGER_MAX_ENTRIES, now}?)`:
  parse `existingRaw`, normalize `newEntries`, deduplicate identical
  `(repo, head, target, outcome)` entries case-insensitively (using
  `(repo, '', issue, pr, target, outcome)` when `head` is `null`) so repeated
  ticks never append duplicates, keep at most the newest positive-integer
  `maxEntries` records, and serialize newline-terminated JSONL (or `""` when
  empty).
- `summarizeRecurringFlakes(entries, {nowMs = Date.now(), windowDays = FLAKE_WINDOW_DAYS, threshold = FLAKE_REPEAT_THRESHOLD, repo}?)`:
  accept parsed entries or raw JSONL, filter to entries within
  `[nowMs - windowDays * 86400000, nowMs]` (and optional case-insensitive
  `repo`), count per `(repo, target)`, keep only targets with `count >= threshold`,
  and return `{totalEntries, windowDays, threshold, recurring}` where
  `totalEntries` is the count of valid in-window entries and `recurring` is
  sorted by `count` descending then `target` ascending then `repo` ascending,
  with `{repo, target, count, outcomes: {'flaked-then-passed', 'reproduced-red', 'base-test-red'}, lastSeen, issues, prs}`.
- `formatRecurringFlakesLine(summary, {includeRepo = false, maxTargets = 5}?)`:
  format a concise single-line summary (`Recurring flakes (<windowDays>d, >=<threshold>): ...`)
  when `summary.recurring.length > 0`, or return `null` when empty.

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

- [Secret redaction](secret-redaction.prompt.md): required for diagnostic and
  displayed external names.
- Native runtime adapters only (not invoked by `regressionScan` runtime checks):
  `githubReply` (from `src/github-calls.mjs`) parses HTTP status line,
  `x-ratelimit-remaining`, `retry-after`, and `link` headers plus JSON body
  after the blank header/body separator; `githubOriginRepository` (from
  `src/workflow-worktree.mjs`) parses Git origin in CLI discovery; Node
  fs/path/crypto and the native process adapter supply local I/O, path
  resolution, and deterministic SHA256 identity.

## Ports for `regressionScan`

For runtime checks, `regressionScan` takes `{ root: string | null, repo: string, now: number, candidates?: Array<{ pr: integer, issue?: integer | null, issues?: integer[], outcome?: string }>, prs?: integer[], maxRequests?: integer }` and reads outside state exclusively through two injected read ports:
- `fs.readFileSync({ path: string })` returning `{ text: string, code: string }` (`code: ""` on success, or `"ENOENT"` / error code with empty `text` on failure).
- `github.get({ endpoint: string })` returning `{ code: integer, stdout: string, stderr: string }` (the runtime counterpart of `gh(["api", "--include", "--method", "GET", endpoint])`, where `stdout` contains HTTP status line and headers separated from the JSON body by `\r\n\r\n` or `\n\n`), using exact REST endpoints under `repos/${repo}/`:
  - `repos/${repo}/pulls/${pr}`
  - `repos/${repo}/commits/${mergeCommit}`
  - `repos/${repo}/commits/${ref}/check-runs?filter=all&per_page=100`
  - `repos/${repo}/commits/${ref}/statuses?per_page=100`
  - `repos/${repo}/issues?state=all&since=${encodeURIComponent(since)}&per_page=100` (where `since` is the earliest merged PR's UTC ISO timestamp `YYYY-MM-DDTHH:MM:SS.000Z`)
  - `repos/${repo}/pulls?state=all&per_page=100`
  - `repos/${repo}/commits?since=${encodeURIComponent(since)}&per_page=100`
  - `repos/${repo}/issues/${number}/timeline?per_page=100`

Command discovery and `--file` output in `runAutopilotRegressions` are covered by native tests.
