# Autopilot reports

Own `src/autopilot-reports.mjs`. When the [Autopilot core](autopilot-core.prompt.md)
ends a job because of a Runtime or PDD problem, this module files one deduplicated
issue for the people who own that part, keeps a local draft, or does nothing, as
the repository chooses. The job never waits for the report or its fix.

Why the limits: automatic issues from many machines can flood a tracker, reach the
wrong owner or leak a person's code. So each cause has one issue, the owner is fixed
by the cause kind, the text is safe, and each machine has a daily limit.

## Rules

- Only causes of kind `runtime` and `pdd` produce reports. Kind `job` and mode `off`
  return `{state: "off"}` and write nothing.
- Fingerprint: `reportFingerprint({kind, component, code, version})` is
  `KIND.COMPONENT.CODE.MINOR`, each part lowercased with runs of other characters
  as `-` (at most 40 characters; empty is `unknown`), and MINOR is the first two
  numbers of the PDD version, for example `runtime.pdd-test.no-verdict.0.1`. The
  report body ends with the hidden marker `<!-- pdd:autopilot-report:FP -->`.
- Owner: every report goes to `promptdriven/pdd`. Runtime reports have label
  `pdd:runtime` and assignee `agarwal-ishaan`; PDD reports have label
  `pdd:autopilot-report` and no assignee.
- Safe text: the title names the kind, component, code and PDD minor version. The
  body has the kind, component, error code, step, the PDD, Node, platform and agent
  versions, how many times this machine saw the cause (1, or the draft's count),
  and a redacted detail tail of at most 20 lines of 200 characters:
  [secret redaction](secret-redaction.prompt.md) first, then URLs become `[url]`,
  absolute paths become `[path]`, and the repository's full name, owner and name
  become `[repository]`. It never includes the issue text or repository code.
- Dedup: before filing, read the label's issues (`state=all`, up to 5 pages) and
  match the marker on an open issue or one closed less than 14 days ago. On a match,
  add at most one "Seen again on machine M at T" comment per fingerprint per machine
  per 24 hours; otherwise only count it. Filing a new issue does not use that
  comment allowance.
- Limit: at most 3 new issues per machine per 24 hours. Over the limit, or when a
  GitHub call fails, keep a local draft instead, so nothing is lost and nothing
  throws.

The machine ledger is `ROOT/ledger.json`: `filed` (fingerprint, number, time, the
last 24 hours) and `seen` (fingerprint to last seen-again comment time).

## Public contract

- `fileReport({cause, mode, root, machine, versions, step, words}, ports)` returns
  `{state, number?, ref?, fingerprint}`. `state` is `filed` or `seen` (with the
  issue number and `ref` `promptdriven/pdd#N`), `counted` (a match already
  commented today), `draft` or `off`. Mode `file` sends; mode `draft` only keeps
  the draft; mode `off` does nothing.
- A draft is `ROOT/drafts/FP.json` with `fingerprint`, `repository`, `title`,
  `body`, `labels`, `assignees`, `count`, `firstAt` and `lastAt`; a repeat raises the
  count.
- `listReportDrafts({root}, ports)` returns the drafts, ordered by file name.
- `sendReportDraft({root, fingerprint, machine}, ports)` sends one draft through
  the same dedup rules, without the daily limit because a person asked, deletes
  the draft and returns `{exitCode: 0, message: "Filed promptdriven/pdd#N."}` or
  `"Counted on …"`. A missing draft or a failed send returns exit code 1 and keeps
  the draft.

Ports: `gh(args, {input})` returning `{code, stdout, stderr}` (REST through
`gh api --include`), `now()`, `fs` and `warn(text)`.

## Dependencies

- [Secret redaction](secret-redaction.prompt.md): required for the detail tail.
