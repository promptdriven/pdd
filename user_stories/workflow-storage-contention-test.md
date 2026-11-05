# Check workflow storage contention reliably

I can trust the storage contention check to report a real contract violation
without failing solely because a worker was scheduled late.

## Acceptance criteria

1. While a native callback owns a workflow record, a compatible whole-record write cannot publish until the callback commits.
2. A whole-record write that succeeds records its intended effect after the callback commits; a finite contention refusal reports failure and leaves the callback's committed state intact.
3. The check does not treat a worker announcing its attempt as proof of acquisition or depend on a fixed sleep, and it preserves the existing storage checks and successful unrelated-progress protections.

## Rules to check

A failed write must not claim a commit. A successful public progress update must
not lose unrelated successful progress. A whole-record write has its existing
explicit replacement semantics; it does not infer an untracked caller's intent.
The runtime ownership and wait policy stays unchanged.

## Native checks

The [native case inventory](../test/workflow-storage-contention-test/cases.json)
is requirement-derived data, not an Interpreter scenario or execution report.
Native worker scheduling and filesystem ownership are unbound to the Interpreter.
