# Small-change request evidence

Own `src/workflow-small-change.mjs`. Preserve every issue request through a
small-change plan, publication and independent review. This module checks
structured evidence, not the truth of agent claims or arbitrary English intent.

`readSmallChangeChecklist(run)` reads only `<runDir>/small-change-checklist.json`.
Use a regular file, at most 1 MiB. The record is `{schema_version:
"pdd.small-change-checklist.v1", run_id, source:{kind:"git-content-v1",sha256},
items}`. `run_id` must match. The source fingerprint must match the current
Git-visible content. Missing, malformed and stale evidence returns `{status,
items:[],mustFix:[{id,code}]}` with the corresponding status and code. A valid
record returns `{status:"recorded",items,mustFix}`. Keep every item in order.
Each item has unique nonblank `id`, `request`, `source` (issue or trusted comment
URL), `quote` (the exact request excerpt), `state` (`pending`, `done`, `excluded`).
Done needs nonblank `evidence`. Excluded needs `exclusion:{reason,quote}`;
that quote must support exclusion in the issue itself. No plan-only exemption.
Missing completion evidence is a must-fix, not a schema error. Empty inventories
are malformed. Do not truncate an inventory to make it pass.

`reviewSmallChangeChecklist(checklist, requests)` returns must-fix objects
`{id,code}`. `requests` is an independent issue-derived inventory, with the same
id/request/source/quote fields and optional `exclusion_quote`: the exact issue
text the checker judged authorizes exclusion. Match by source, request and quote,
not by the builder's id. Missing requests give `missing-request`; extra checklist
items give no coverage of another request. Validate every checklist row by its
own unique id, including extra rows and rows with identical request/source/quote.
A completed row cannot supply another row's state, evidence or exclusion.
Pending items give `pending-request`;
done without evidence gives `missing-evidence`; exclusions without a reason and
an exact match to a matching independent request's `exclusion_quote` give
`unsupported-exclusion`. Report completion findings with the checklist row's id;
report missing requests with the independent request's id.
The reader uses the same completion checks without an independent inventory;
it does not claim semantic completeness or authorize an exclusion. The checker
must derive requests from the full issue and trusted follow-ups, never the plan.

## Dependencies

- [Replay evidence](workflow-replay.prompt.md): required fingerprint contract
  `sourceFingerprint` for current Git-visible content. File I/O uses Node fs;
  callers supply the run folder and repository root. Tests use disposable files.

Small-change checklist and Formal check facts remain in detailed text status and JSON run rows. Preserve compact list/all text rows; these views keep existing Runtime coverage lines but do not add the detailed small-change evidence block. The saved evidence remains available through the run detail and JSON.
