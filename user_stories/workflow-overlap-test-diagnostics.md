# Explain and stabilize the overlapping completion regression

I can understand why the completion regression fails and check that stale
commands keep successfully saved progress, without changing product behavior.

## Acceptance criteria

1. A failed completion assertion shows its pair, mode, worker, step names, both full returned messages or errors and exit codes, and the observed saved completion values.
2. In the overlapping cases, both commands select the same initial run before either is released; one finishes successfully before the other is released, and both release orders are exercised.
3. All four sequential controls, sixteen small-record pairs and sixteen large-summary pairs still require both successful completions to remain saved; each large-summary pair also preserves its prior 65,536-character summary and the rest of that prior completion record.
4. Worker errors, timeouts, unsuccessful saves and missing successful completion records still fail with useful evidence, and held workers are cleaned up even on failure.
5. The test correction keeps existing contention coverage and product ownership behavior; it does not retry away a lost successful completion. If diagnostics reveal such a loss, stop and report it for review.

## Rules to check

The forbidden result is a passing test after a successful completion disappeared.
Both initial selections must precede the first release; the second release must
follow the first success. A successful stale completion must preserve the other
completion and any prior completion. Finite ownership refusal remains a product
outcome, not evidence that a successful save disappeared. The deterministic union
schedule avoids simultaneous lock contention; separate native ownership tests
continue to check contention. No production behavior change is authorized.

## Native cases to verify

- Diagnostic case: a worker returns an ownership refusal; the failure includes
  the complete returned cause, both outcomes and actual saved records.
- Small-record stale selection: hold both commands, release A then B; repeat
  with B then A. Expect two successes and both full completion records.
- Large-summary stale selection: the same two orders preserve both new records
  and the full prior record with its 65,536-character summary.
- Sequential control: finish A before starting B; expect both records.
- Failure controls: a worker error, timeout or missing successful completion
  remains a failure with context and cleanup; do not mask it with a retry.

The owning [test contract](../prompts/test/workflow-concurrent-progress-overlap.prompt.md)
has no executable Interpreter entry. These cases require the real Node test,
worker barriers and scratch storage; they are requirements, not a passing test
report. A supplied-outcome simulation cannot prove native scheduling or Node
assertion diagnostics. No synthetic check-only operation or Interpreter scenario
is introduced. Native implementation and verification follow approval.
