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
  no assignee. Runtime reports have label `pdd:runtime`; they go to the configured
  Runtime repository (`runtimeRepo`, `OWNER/NAME`) when `GET repos/RUNTIME_REPO`
  succeeds on this machine at send time, else to `promptdriven/pdd`. A report has no
  assignee unless the operator configures one: `runtimeOwner` (a GitHub login) is the
  assignee of a Runtime report that goes to the configured `runtimeRepo`, and of no
  other report. The product names no person. A draft keeps its `kind`, `runtimeRepo`
  and `runtimeOwner`, so a later send resolves the destination and assignee the same
  way. Test vectors are PDD's, not Runtime's:
  `reportKind(cause)` makes a `runtime` cause kind `pdd` when its component or code
  (as slugs) names a scenario, vector, replay, safe integer, integer out of range,
  Runtime case or test case (for example `scenario-integer-out-of-range`), before the
  fingerprint, title, label and owner. Kind `runtime` stays for what goes in and out
  of Runtime: interface and binding refusals, interpreter errors, no verdict, server
  compatibility.
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
  only fixed fields: the kind, component, error code, step, the PDD, Node, platform
  and agent versions, how many times this machine saw the cause (1, or the draft's
  count) and the fingerprint marker. It never holds free-form text: no cause text,
  no detail, no issue text and no repository code. The detail stays local: the draft
  file keeps a redacted detail tail of at most 20 lines of 200 characters as
  `detail` for the operator ([secret redaction](secret-redaction.prompt.md) first,
  then URLs become `[url]`, absolute paths become `[path]`, and the repository's full
  name, owner and name become `[repository]`). Every send builds the title and body
  again from the fixed fields, also for a draft written earlier whose `body` carries a
  detail, so no send posts a draft's `body` or `detail`.
- Dedup: before filing, read the label's issues (`state=all`, up to 5 pages) and
  match the marker on an open issue or one closed less than 14 days ago, in the owner
  repository. On a match, add at most one "Seen again on one more Autopilot machine
  run at T" comment per fingerprint per machine per 24 hours (no host name); otherwise
  only count it. Filing a new issue does not use that comment allowance.
- No daily cap: each new cause is filed (one issue per cause by the dedup). When a
  GitHub call fails, keep a local draft instead, so nothing is lost and nothing
  throws.

The machine ledger is `ROOT/ledger.json`: `filed` (fingerprint, number, time, the
last 24 hours) and `seen` (fingerprint to last seen-again comment time).

## Public contract

- `fileReport({cause, mode, root, machine, versions, step, words, runtimeRepo, runtimeOwner}, ports)` returns
  `{state, number?, id?, ref?, fingerprint}`. `state` is `filed` or `seen` (with the
  issue number, the issue's GitHub `id` for dependency links, and `ref`
  `promptdriven/pdd#N`), `counted` (a match already
  commented today), `draft` or `off`. Mode `file` sends; mode `draft` only keeps
  the draft; mode `off` does nothing.
- A draft is `ROOT/drafts/FP.json` with `fingerprint`, `kind`, `component`, `code`,
  `step`, `versions`, `shipped`, `stopped`, `runtimeRepo`, `runtimeOwner`, `repository`, `title`,
  `body` (the public text), `detail` (local only), `labels`, `count`, `firstAt` and
  `lastAt`; a repeat raises the count. A draft written earlier without the fixed
  fields takes kind, component and code from its fingerprint, and `unknown` for the
  rest.
- `listReportDrafts({root}, ports)` returns the drafts, ordered by file name.
- `sendReportDraft({root, fingerprint, machine}, ports)` sends one draft through
  the same dedup and owner rules, deletes
  the draft and returns `{exitCode: 0, message: "Filed promptdriven/pdd#N."}` or
  `"Counted on …"`. A missing draft or a failed send returns exit code 1 and keeps
  the draft.

Ports: `gh(args, {input})` returning `{code, stdout, stderr}` (REST through
`gh api --include`), `now()`, `fs` and `warn(text)`.

## Dependencies

- [Secret redaction](secret-redaction.prompt.md): required for the detail tail.
