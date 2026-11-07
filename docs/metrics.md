# Metrics

Run `pdd metrics` from a GitHub repository to see its current open issue queue. The report uses a saved queue snapshot and shows unknown selection where no Autopilot selector observation is available. The command reads local workflow records and the metrics ledger; missing machines and historical facts remain coverage gaps.

- `pdd metrics --json` prints the same report as JSON.
- `pdd metrics --date 2026-11-05 --timezone America/New_York` reports activity on that local calendar date.
- `pdd metrics --snapshot ID` follows the issue membership of a saved snapshot.
- `pdd metrics export FILE` writes a shareable bundle; `pdd metrics import FILE` combines a compatible bundle for the current repository. Export explicitly from each participating machine; importing one machine does not establish complete participation.
- `pdd metrics record FILE` records one event object or an array of event objects in JSON. Use this for explicitly evidenced required outcomes, human reports and recovery facts that are not captured automatically. Supply the event schema described below; use stable source and event IDs so re-importing a fact does not count it twice.

An event has `schema` (`pdd.metrics.event.v1`), `id`, lowercase `repo` (`owner/name`), positive `issue`, `type`, UTC `at` and `observedAt`, `source`, optional `attempt` (workflow run ID), and `data`. For example, a human report must include `type: "report"` and data containing `classification: "failed-fix"`, `humanReported: true`, and an HTTPS `evidence` link to the actual complaint. Record an administrative reopen, new scope, or revert with its matching classification instead. A recovery is an `assistance` event with `classification: "recovery"` and evidence; a required outcome is an `outcome` event with `requiredOutcome: "code"` or `"prompt-only"`. Do not put issue bodies, chats, credentials or local paths in event files.

An independent check is distinct from a test run and is tied to the candidate head and supporting evidence. Missing results are unknown. Metrics report evidence; they do not approve a workflow or authorize a merge. Queue snapshots and imported events may include only participating sources, so a missing report does not establish that a fix remained successful or that an execution was unassisted.

Exports include all retained events for the repository, without an implicit selected-date filter, and retain imported source coverage metadata and declared scopes when passed between machines. A source without a declared scope has unknown scope. A GitHub observation can show the current PR head or a merged code PR; a matching checker comment alone does not establish that its review met the independent-check rules. Current head and checker evidence do not establish that a PR is still open or awaiting merge; its closure state is unclassified. When GitHub is unavailable, remote evidence is unknown. Workflow creation timestamps do not establish that a worker started.

Use `--at 2026-11-05T12:00:00Z` with `--date` or `--snapshot` for a cutoff and use `--expected-source ID...` for machines expected in the report. An expected source with no observed events is listed as a coverage gap.

The terminal report shows the same stage and transition fractions as JSON, with unknown counts and activity. Implementation readiness is measured against confirmed Autopilot starts; PR creation is a separate transition. Current-head CI observations are separate from independent checker verdicts.

An explicit human failed-fix complaint with a public evidence link is retained at issue level. Add the relevant `attempt` or `data.pr` when the complaint identifies a particular delivery; otherwise its delivery attribution remains unknown, including in 7- and 30-day follow-up.
