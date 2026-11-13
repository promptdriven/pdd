# Autopilot reports

Own `src/autopilot-reports.mjs`. When the [Autopilot core](autopilot-core.prompt.md)
ends a job because of a Runtime or PDD problem, or stops one of its own steps (a
`pdd`-owned stop: the job waits and tries again), this module files one deduplicated
issue for the people who own that part, keeps a local draft, or does nothing, as
the repository chooses. The job never waits for the report or its fix.

Why the limits: automatic issues from many machines can flood a tracker, reach the
wrong owner or leak a person's code. So each cause has one issue, the destination is
fixed by the cause kind, a public issue holds only fixed fields, and each machine
comments on a known cause at most once a day.

## Rules

- Only causes of kind `runtime` and `pdd` produce reports. Kind `job` and mode `off`
  return `{state: "off"}` and write nothing.
- Stable causes: before the fingerprint, the code becomes one fixed word
  (`stableCode`): merge-check-tool, suite-broken, adopt-pdd (its body asks to adopt
  PDD for the modules that the local draft lists), no-verdict, maintenance (the
  interpreter stayed in maintenance, so the check was never sent: the
  [core](autopilot-core.prompt.md) waits 12 hours first, #3241), scenario-limit,
  vector-replay, runtime-case, lint-refusal, interface-refusal, binding-refusal,
  input-refusal (any other refusal or rejection of our input: `refus` or `reject`),
  interpreter-error, server-internal (a server-side internal error: server-internal,
  internal-server, server-error, a 5NN status as its own word, unavailable or
  bad-gateway), server-incompatible, crash,
  claim-error, not-run, base-check, step-quiet, stop-loop, timeout,
  cli-error (matched in this order on the slug), else `other-HASH`: the first 8 hex
  digits of the SHA-256 of `STEP:CODE` (the step and the code slug without digits;
  never the agent's text, paths or numbers). The component becomes one fixed word (`stableComponent`):
  autopilot-core, pdd-lint, pdd-approve, pdd-workflow, pdd-test (also runtime,
  interpreter, verdict, scenario, vector), pdd, agent, else other. So spellings of one
  cause are one report. A new `other-…` cause files at most one new report per machine
  per day (the ledger); the rest stay drafts (a person's send has no such cap). The
  owner follows Serhan's boundary: everything that goes INTO Runtime is PDD's (prompts,
  interface blocks, bindings, Stories, test vectors, tests, up to the call); everything
  inside Runtime after the call until the result comes back is Runtime's. So kind
  `runtime` stays only for the Runtime codes (`RUNTIME_CODES`) no-verdict,
  maintenance, interpreter-error, server-incompatible and server-internal. Every other runtime cause,
  also interface-refusal, binding-refusal, lint-refusal and input-refusal (a refusal of
  our input is ours to fix first), is a PDD report.
- Fingerprint: `reportFingerprint({kind, component, code, version})` is
  `KIND.COMPONENT.CODE.MINOR`, each part lowercased with runs of other characters
  as `-` (at most 40 characters; empty is `unknown`), and MINOR is the first two
  numbers of the PDD version, for example `runtime.pdd-test.no-verdict.0.1`. The
  report body ends with the hidden marker `<!-- pdd:autopilot-report:FP -->`.
- Owner: PDD reports go to `promptdriven/pdd` with label `pdd:autopilot-report` and
  no assignee. Runtime reports have label `pdd:runtime`; in validated auto-filing they
  default to `DEFAULT_RUNTIME_REPORT_REPOSITORY` (`promptdriven/prompt-runtime`) unless
  another `runtimeRepo` (`OWNER/NAME`) is configured, and in direct `file` mode they use
  the caller's `runtimeRepo` when given. A Runtime report goes to that Runtime
  repository when `GET repos/RUNTIME_REPO` succeeds on this machine at send time, else
  to `promptdriven/pdd`. A report has no assignee unless the operator configures one:
  `runtimeOwner` (a GitHub login) is the assignee of a Runtime report that goes to the
  configured `runtimeRepo`, and of no other report. The product names no person. A draft
  keeps its `kind`, `runtimeRepo` and `runtimeOwner`, so a later send resolves the
  destination and assignee the same way. Test vectors are PDD's, not Runtime's:
  `reportKind(cause)` makes a `runtime` cause kind `pdd` when its component or code
  (as slugs) names a scenario, vector, replay, safe integer, integer out of range,
  Runtime case or test case (for example `scenario-integer-out-of-range`), before the
  fingerprint, title, label and owner. Kind `runtime` stays for what happens inside
  Runtime after the call: interpreter errors, no verdict, server internal errors and
  server compatibility.
- Validated auto-filing (three checks before creating an automatic GitHub issue):
  1. **Real defect filter (`classifyNonDefect`)**: non-defects and service or caller
     noise are never auto-filed to GitHub. Filtered categories are quota or credit
     exhaustion (`quota`, `rate-limit`, `usage-limit`, `billing`, `credit`,
     `out-of-quota`), authentication or login expiry (`auth`, `token-expired`,
     `unauthorized`, `login`), operator or caller stops (`operator-stop`, `cancelled`,
     `canceled`, `user-stop`, `caller`), maintenance or AI provider capacity
     (`maintenance`, `capacity`, `overloaded`), transient network blips (`econnreset`,
     `etimedout`, `enotfound`, `network-blip`), and repository content or allowed
     `"not run"` causes (`no-story`, `not-run`, `unchecked-criteria`,
     `story-criterion-mismatch`, `content`). Filtered causes return
     `{state: "filtered", reason, category, owner, fingerprint}` without writing an
     issue to GitHub.
  2. **Verified owner and scrubbed proof (`validateReportDraft`)**: before auto-filing
     (unless forced by manual `sendReportDraft` or unvalidated direct `mode: "file"`), a
     draft must carry verified proof: either reproduced (`reproduced: true`), or seen at
     least twice (`count >= 2`, or across at least two distinct `issues`, `heads` or
     `occurrences`), together with a concrete step or scrubbed command (an unverified
     single-occurrence cause or a vague `other-…` cause without step/command proof stays
     a local `draft`). Validated auto-filing respects a per-machine daily cap on new
     issues (`DEFAULT_DAILY_REPORT_LIMIT = 3` within 24 hours; additional new causes
     stay local drafts). If a matching issue in the target repository was closed as
     `not_planned` or carries an `invalid` or `wontfix` label, automatic filing stops
     and returns `{state: "needs-person", reason, number, id, ref, fingerprint}` instead
     of opening or re-opening an issue.
  3. **Live duplicate check across versions**: before creating an issue, query `state=all`
     issues for the target label (up to 5 pages) and match either the exact
     `reportMarker(fingerprint)` or the same `(kind, component, code)` cause across
     versions (marker prefix, fixed `Kind`/`Component`/`Error code` lines, or standard
     title prefix). Prefer an open match; otherwise stop on a rejected closed match
     (`not_planned`, `invalid`, `wontfix`), or match an issue closed less than 14 days
     ago. When an open or recent issue matches, never open a duplicate: post at most one
     `"Seen again"` comment per `(cause, version)` per machine per 24 hours (recording
     the version and machine count without any host name) and return `state: "seen"`, or
     `state: "counted"` when already commented in the last 24 hours.
- Safe text: the title names the kind, component, code and PDD minor version. The
  public body starts with a fixed sentence for what the job did: it ended, or, for a
  cause with `shipped: true` (Runtime could not check), it shipped its PR with
  "Runtime: not run", or, for a `shipped` cause of the component `autopilot-core` with the code `vector-replay` (the
  core could not run the replay or formal tests of a PR), it went on with that claim
  marked as not checked, or, for a cause with `stopped: true` (a core step made no
  progress), "Autopilot stopped one of its own steps for one job: it made no progress.
  The issue gets no strike, and Autopilot tries again later." (for the code `stop-loop`:
  "Autopilot holds one issue: its own steps or a service stopped 3 jobs of it in 24
  hours. The issue gets no strike; Autopilot takes it again after a new engine version or
  a person's comment on it."), or,
  for `adopt-pdd`, a fixed request to adopt PDD. Then it has
  only fixed, scrubbed fields: the kind, component, error code, step, optional scrubbed
  command and safe Runtime batch/report identifiers, the PDD, Node, platform
  and agent versions, optional proof summary (`reproduced` or distinct counts), how many
  times this machine saw the cause (1, or the draft's
  count) and the fingerprint marker. It never holds free-form text: no cause text,
  no detail, no issue text, no secrets, no filesystem paths, no URLs and no repository
  code. The detail stays local: the draft
  file keeps a redacted detail tail of at most 20 lines of 200 characters as
  `detail` for the operator ([secret redaction](secret-redaction.prompt.md) first,
  then URLs become `[url]`, absolute or multi-segment paths become `[path]`, and the
  repository's full name, owner and name become `[repository]`). Every send builds the
  title and body again from the fixed fields, also for a draft written earlier whose
  `body` carries a detail, so no send posts a draft's `body` or `detail`.
- Failure handling: in unvalidated direct `file` mode there is no 3-per-day cap (unknown
  `other-…` causes still limit to one per 24 hours); in validated mode new issues cap at
  `dailyLimit` (default 3) per 24 hours. When a GitHub call fails, keep a local draft
  instead, so nothing is lost and nothing throws.
- Daily conversion-drop summary (`summarizeConversionDrops`): builds a deterministic,
  secret-free JSON object for the `stats` branch with the four stage conversion ratios
  (`backlogToClaimable`, `claimedToClearSpec`, `clearSpecToPrOpened`,
  `prOpenedToMergedOrWouldMerge` as `{numerator, denominator, rate}`), non-merged drop
  counts grouped by root-cause owner (`pdd`, `runtime`, `content`, `quota_or_service`,
  `operator`, `person_decision`), and `reports` separating `verifiedIssues`,
  `pendingDrafts` and `filteredNoise`.

The machine ledger is `ROOT/ledger.json`: `filed` (fingerprint, number, time, the
last 24 hours) and `seen` (cause-and-version key to last seen-again comment time).

## Public contract

- `DEFAULT_RUNTIME_REPORT_REPOSITORY` is `"promptdriven/prompt-runtime"` and
  `DEFAULT_DAILY_REPORT_LIMIT` is `3`.
- `classifyNonDefect(causeOrDraft)` returns `null` for a candidate defect, or
  `{reason, category, owner}` when Rule 1 filters the cause.
- `validateReportDraft(draft, {dailyFiledCount, dailyLimit})` checks Rule 1 and Rule 2
  proof/cap readiness and returns `{ok, state, reason?, category?, owner?, targetRepository}`.
- `fileReport({cause, mode, validate, dailyLimit, root, machine, versions, step, words, runtimeRepo, runtimeOwner}, ports)`
  returns `{state, reason?, category?, owner?, number?, id?, ref?, fingerprint}`.
  `state` is `filed` or `seen` (with `number`, `id`, `ref`, `fingerprint`), `counted`,
  `needs-person`, `filtered`, `draft` or `off`. Mode `validated` (or `mode: "file"` with
  `validate: true`) enforces all three rules and `dailyLimit`; mode `file` sends with
  live dedup and unambiguous noise/rejection guards; mode `draft` records the local
  draft (`count`, `reproduced`, `issues`, `heads`, `occurrences`, `rawCode`, scrubbed
  `command`, `batchId`, `reportId`); mode `off` does nothing. Every non-`off` result
  includes `fingerprint`.
- `autoFileValidatedReports({root, machine, runtimeRepo, runtimeOwner, dailyLimit}, ports)`
  validates all local drafts in `ROOT/drafts` and sends only drafts that pass Rules 1, 2
  and 3, returning `{results, filed, seen, counted, filtered, needsPerson, drafts}`.
- `summarizeConversionDrops({runs, backlogCount, claimableCount, claimedCount, clearSpecCount, prOpenedCount, mergedOrWouldMergeCount, drafts, filed, filtered, date})`
  returns `{date, totals, stages, dropsByOwner, reports}`.
- A draft is `ROOT/drafts/FP.json` with `fingerprint`, `kind`, `component`, `code`,
  `rawCode`, `step`, `command`, `batchId`, `reportId`, `reproduced`, `issues`, `heads`,
  `occurrences`, `versions`, `shipped`, `stopped`, `runtimeRepo`, `runtimeOwner`,
  `repository`, `title`, `body` (the public text), `detail` (local only), `labels`,
  `count`, `firstAt` and `lastAt`; a repeat merges proof fields and raises the count. A
  draft written earlier without the fixed fields takes kind, component and code from its
  fingerprint, and `unknown` for the rest.
- `listReportDrafts({root}, ports)` returns the drafts, ordered by file name.
- `sendReportDraft({root, fingerprint, machine, runtimeRepo}, ports)` sends one draft
  through the owner and live dedup rules without proof or daily-cap blocks, deletes the
  draft when filed or counted (keeping it if `needs-person` or failed), and returns
  `{exitCode, message, state?}`.

Ports: `gh(args, {input})` returning `{code, stdout, stderr}` (REST through
`gh api --include`), `now()`, `fs` and `warn(text)`.

## Dependencies

- [Secret redaction](secret-redaction.prompt.md): required for the detail tail.
