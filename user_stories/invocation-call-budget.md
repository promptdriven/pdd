# Bound total interpreter calls and control restart replacements

As a PDD user running `pdd test`, I want an invocation-wide logical call ceiling (`--max-total-calls N`) and an explicit control to decline `service-restarted` replacement checks (`--no-restart-replacement`), so that multi-Story runs and restart replacements stay inside my chosen call budget.

`--max-calls N` remains the per-request bound (`1..1000`). Default runs without `--max-total-calls` or `--no-restart-replacement` keep their current behavior.

## Acceptance criteria

1. When `--max-total-calls` is `18` and an `18`-call Check ends with `service-restarted` and unresolved usage, the original attempt retains its `18`-call reservation, `0` calls remain, no replacement Check is sent, and the original `unknown` uncertainty is retained.
2. When `--max-total-calls` is `36` with an `18`-call per-request cap and an `18`-call Check ends with `service-restarted` and unresolved usage, `18` calls remain so at most one eligible replacement Check is permitted at `effective_max_calls: 18` while retaining prior uncertainty; any second `service-restarted` replacement on that test is refused (`restart-limit-reached`).
3. Across multiple Stories in one invocation, complete-zero pre-execution capacity refusals consume `0` calls, settled attempts consume `known_calls` and return unused allowance to the invocation pool, in-flight attempts hold candidates needing more calls (`awaiting-in-flight-settlement`) when settlement could free allowance, partial remaining allowance after settlement clamps `effective_max_calls`, and `0` remaining allowance blocks further dispatch (`call-budget-exhausted`).
4. When `--no-restart-replacement` (or `PDD_CHECK_SINGLE_ATTEMPT=1`) sets `single_attempt`, the plan disables restart replacement (`1` Check request per test, `1x` unbounded maximum) and refuses any `service-restarted` replacement (`restart-replacement-disabled`) while retaining the original `unknown` uncertainty across fresh runs, `--read`, and `--retry`.
5. Pre-dispatch budget planning surfaces effective `per_request_caps`, `max_total_calls`, `restart_replacement` policy, `unbounded_maximum` versus capped `planned_maximum`, `planned_check_requests`, and `unresolved_prior_reservations` separately from the current batch's `committed_calls`, scoped strictly to `logical-interpreter-calls`.

## Rules to check

- Never treat interrupted claims, lost replies, `unknown` usage, `accounting_complete: false`, `unknown_calls > 0`, or unresolved `service-restarted` attempts as `0` calls; retain at least `max(requested_max_calls, known_calls + unknown_calls)`.
- Never permit more than one `service-restarted` replacement per test, even when `--max-total-calls` has remaining allowance.
- Never claim dollar, token, physical provider-attempt, or provider-cancellation guarantees; keep requested logical call limits separate from actual usage evidence.

## Coverage boundary

```pdd-boundary
prompts/cli/runtime-check-plan.prompt.md
```

The Runtime scenario checks pure `evaluateCheckBudget` planning, conserved accounting, and candidate dispatch/replacement decisions on supplied attempt records. Native cases must establish CLI option parsing and mode rejection, `batch.json` and `.dispatch.json` persistence across `--read` and `--retry`, live concurrent wait/clamp/block orchestration, `.restart.json` fuse preservation, and stderr/JSON Check plan visibility.
