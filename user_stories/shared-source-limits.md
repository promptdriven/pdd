# I get a clear refusal before shared source becomes too large

## Acceptance criteria

1. A source file above 10,485,760 bytes is refused before its contents are read, including a raw file replaced for upload.
2. A selected payload above 10,000 files or 10,485,760 total bytes is refused before reading the selection that exceeds its limit.
3. A shared record graph that would expand beyond 10,485,760 bytes stops during expansion with a finite too-big error and no upload.
4. A normal source and a source exactly at the read or expansion boundary remain eligible for the existing later validation and tar limits.

## Rules to check

Apply the per-file upload refusal only to actual upload candidates, including their raw bytes before replacement. Keep bounded stat-before-read protection for resolver/preparation inputs required by selected effective source. Oversized discovery-only documents are skipped or warned before content allocation; oversized unselected sibling documents leave an unavailable footprint and cannot refuse selected good work. A 12 MiB unrelated transcript under user_stories must not stop Check, Try or local contract commands, and a sparse 2 GiB ignored document must never be read into memory. Catalog-only oversized documents are skipped or warned without claiming complete record/use evidence.

Check the existing selected-source totals before selected reads. Reference/preparation-only raw inputs do not accumulate again as selected payload; unrelated files do not count. Stat metadata alone does not allocate file contents. Expanded size is accounted once per reference result, including annotations/overrides, without repeated full-size walks at every enclosing schema node; a fitting depth-400 schema remains eligible with no tight timing gate.

Resolver stat/expansion overflow uses contract-invalid with consumer and target; native preflight keeps exit 4 and its too-big report. No native allocation exception, partial expansion, upload, sign-in or model call may escape these refusals. The tar still has its independent 10 MiB limit: eligibility at an input boundary does not promise an accepted archive. Preserve synchronous public calls, generated/replaced file selection, exact numbers and all existing privacy/snapshot checks.

Runtime check: native host reads, allocation bounds, source totals and archive effects are unbound; supplied file replies cannot prove these effects. Native cases use fake read/stat observations and real sparse temporary files; no live runtime or model call.
