# I get a clear refusal before shared source becomes too large

## Acceptance criteria

1. A source file above 10,485,760 bytes is refused before its contents are read, including a raw file replaced for upload.
2. A selected payload above 10,000 files or 10,485,760 total bytes is refused before reading the selection that exceeds its limit.
3. A shared record graph that would expand beyond 10,485,760 bytes stops during expansion with a finite too-big error and no upload.
4. A normal source and a source exactly at the read or expansion boundary remain eligible for the existing later validation and tar limits.

## Rules to check

Check every individual raw file against 10 MiB before native reads through local file ports and capture/preparation ports. Check the existing selected-source totals before selected reads. Reference/preparation-only raw inputs do not accumulate again as selected payload; unrelated files do not count. Stat metadata alone does not allocate file contents. Resolver stat/expansion overflow uses contract-invalid with consumer and target; native preflight keeps exit 4 and its too-big report. No native allocation exception, partial expansion, upload, sign-in or model call may escape these refusals. The tar still has its independent 10 MiB limit: eligibility at an input boundary does not promise an accepted archive. Preserve synchronous public calls, generated/replaced file selection, exact numbers and all existing privacy/snapshot checks.

Runtime check: native host reads, allocation bounds, source totals and archive effects are unbound; supplied file replies cannot prove these effects. Native cases use fake read/stat observations and real sparse temporary files; no live runtime or model call.
