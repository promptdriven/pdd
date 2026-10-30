# Inspect local runtime jobs

I can inspect local runtime work with `pdd jobs` without contacting the runtime.

## Acceptance criteria

1. I can inspect the active and waiting local runtime jobs, retaining their kinds, process IDs and request IDs, without contacting the runtime.
2. The listing puts active jobs first and waiting jobs in oldest-first order, with stable identity order for equal times.

## Rules to check

The [slots prompt](../prompts/cli/runtime-slots.prompt.md#local-inspection) owns the local snapshot and CLI formatting. Listing is read-only: it never reclaims reservations or hides an unreadable record as no work. The runtime scenario supplies filesystem records to the real listRuntimeJobs boundary; it proves forwarding, sorting and preserved fields, not OS file access, CLI dispatch or absence of native network calls. Native tests must run `pdd jobs` outside a repository, with gh/fetch traps, mixed active/waiting records, no folder and a read error; verify catalog/help/completion and the documented form. No exact human wording is asserted.

Runtime check: NOT RUN. One draft snapshot step bind files.listRecords. CLI routing, private filesystem permissions and multi-process effects are NOT REPLAYED and require native tests. No model calls were made.
