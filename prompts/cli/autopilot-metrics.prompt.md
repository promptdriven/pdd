# Autopilot scorecard

`src/autopilot-metrics.mjs` owns pure calculation, fixed-line evidence parsing
and the text table. Count only recorded local Autopilot work across repositories.

`parseAutopilotEvidence(text)` returns exactly four booleans: `runtime`, `vectors`,
`formal`, `tests`. Accept a complete line in this order:
`Evidence: runtime=pass (3/3); vectors=pass (2/2); formal=not-run; tests=pass (4/4)`.
Each status is exactly `pass`, `fail` or `not-run`; optional counts `(n/m)` are
nonnegative safe integers with n <= m. Counted pass requires n = m and m > 0;
uncounted pass is recorded success. Missing, malformed, extra/duplicate/unknown
fields yield four false values. Multiple lines must agree or all values are false.
Do not interpret free prose or commands as evidence.

`canonicalAutopilotEvidence(text)` validates the entire observation using those
same rules and returns one normalized fixed line, or null when absent/invalid.
Identical duplicate lines, CRLF, surrounding whitespace, semicolon spacing and
equivalent integer spellings have the same canonical result. Preserve all four
statuses and optional counts; do not collapse distinct failing/not-run facts.

`calculateAutopilotMetrics({events,timezone,observedAt})` accepts events with
`repo` (owner/name), positive integer `issue`, `kind`, `at` (epoch ms or UTC ISO),
optional `head` and `mergeCommit` (40 hex SHAs), `pr` (positive integer), `evidence` (fixed line),
`validation`, `reason`. Ignore invalid identities/times, future events and unknown
kinds. Kinds are `started`, `worked`, `evidence`, `validated`, `merged`,
`regression`. Every valid event is work. Validation needs `head` and
`validation: {review:{head,verdict:PASS,fresh:true},tests:{head,state:pass},
ci:{head,state:pass}}`, all heads equal the event SHA. A regression requires
reason `reverted`, `bad-audit` or `merge-ci-red` and an earlier Autopilot merge
for the same repo/issue and PR when supplied. A merge alone proves no checks.
Deduplicate each day by lowercase repository + issue, across jobs/retries/PRs.
Before selecting reporting windows, reconcile evidence events with a recorded
head by `(repo, issue, head, canonical evidence)`, retaining the earliest valid
timestamp regardless of input order or PR number. This repairs duplicate durable
facts after a failed job save or crash; without an execution identity they cannot
represent another check. Different heads or canonical facts remain independent.
`autopilotEvidenceIdentity(event)` returns that JSON tuple string for a normalized
valid evidence event with head and complete canonical evidence, otherwise null.
The writer reuses it for durable deduplication; headless historical events retain
their existing daily treatment.

`normalizeAutopilotMetric(event)` returns a fresh allowlisted event with lowercase
repo/head/mergeCommit and UTC ISO at, or null for an invalid event. Drop unknown fields,
including inside validation, where only SHA heads, PASS/FAIL/NOT SURE review
verdicts, boolean freshness and pass/fail/not-run states survive.
Evidence and reason must be strings when supplied.
The collector and write hook reuse this normalization.

Days run local 09:00 inclusive to next 09:00 exclusive and use their start date.
Default zone is the machine's Intl zone; calendar arithmetic must handle DST.
Report the last finished day. Week starts Monday 09:00 and averages only finished
days. If none of the current week's days are finished, report the previous full
seven days as `Last week`. Invalid zone/cutoff throws `Invalid timezone` /
`Invalid cutoff`.

Return exactly `scope: local-autopilot`, `timezone`, `observedAt` (UTC ISO),
`day: {date,label,start,end}` (local YYYY-MM-DD, English short weekday, UTC ISO
bounds), `week: {label,start,end,finishedDays}` (label `Week avg` or `Last week`,
UTC ISO bounds, positive day count), and ordered `rows`. Each row has `key`,
`label`, `day`, `weekAverage` (numbers, percentage may be null).
Order/key/label: `started` / Issues started; `worked` / Issues worked on;
`runtime` / Runtime passed; `vectors` / Test vectors passed; `formal` / Formal
verification; `validated` / Validation passed; `merged` / Merged by Autopilot;
`regressions` / Regressions; `startedToMerged` / Started-to-merged %.
Weekly counts sum daily distinct counts / finishedDays, including zeros.
Conversion is the percentage of distinct started issues also merged in that
window, null with no starts. Weekly conversion uses the whole finished-week
cohort, not averaged percentages. JSON numbers retain precision.

`renderAutopilotMetrics(report)` returns a compact table with date and timezone
in its title and row-label, day-label, week-label columns. Numbers use at most
two decimals, percentage appends `%`, null displays `n/a`; end with newline.

## Dependencies

Use deterministic JavaScript arithmetic and Intl calendar/timezone facilities.
Callers supply observations; calculation has no outside effects.

<details><summary>Runtime interface</summary>

```json
{"kind":"partial","status":"draft","prose_sha256":"","entries":[{"operation":"parseAutopilotEvidence","input_schema":{"type":"object","properties":{"text":{"type":"string"}},"required":["text"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"runtime":{"type":"boolean"},"vectors":{"type":"boolean"},"formal":{"type":"boolean"},"tests":{"type":"boolean"}},"required":["runtime","vectors","formal","tests"],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[],"limits":{"max_steps":4,"max_model_calls":2},"conventions":[]}
```

</details>
