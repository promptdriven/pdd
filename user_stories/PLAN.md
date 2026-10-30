# SVG layout spec

1. [Keep the built screen aligned with its drawing](svg-layout-spec.md): local prompt/drawing warnings and a failing browser comparison for missing layout parts.

# Shared runtime admission (#2631)

Build on the saved-lint continuation contract. The existing Stories also cover owner heartbeat expiry, contention progress, bounded maintenance, fail-open advisory capacity, phase-specific lint waits, truthful wait-end text and per-process read reuse. Prompts and expected cases are reviewed before code. Native tests use fake transport/clock plus real temporary state and child processes; do not claim supplied port replies prove atomic exclusion. Each Story has one case file. Five native case files use pdd.native-cases.v1 and are not discovered as executable Runtime scenarios; the jobs snapshot has a real Runtime scenario.

- [runtime-local-slots](runtime-local-slots.md) — [native cases](../test/runtime-admission/runtime-local-slots.json). Runtime check: NOT REPLAYED (#2548); native cases in Story.
- [runtime-local-queue](runtime-local-queue.md) — [native cases](../test/runtime-admission/runtime-local-queue.json). Runtime check: NOT REPLAYED (#2548); native cases in Story.
- [runtime-capacity-wait](runtime-capacity-wait.md) — [native cases](../test/runtime-admission/runtime-capacity-wait.json). Runtime check: NOT REPLAYED (#2548); native cases in Story.
- [runtime-maintenance-wait](runtime-maintenance-wait.md) — [native cases](../test/runtime-admission/runtime-maintenance-wait.json). Runtime check: NOT REPLAYED (#2548); native cases in Story.
- [runtime-restart-retry](runtime-restart-retry.md) — [native cases](../test/runtime-admission/runtime-restart-retry.json). Runtime check: NOT REPLAYED (#2548); native cases in Story.
- [runtime-jobs](runtime-jobs.md) — [scenario](../test/runtime/runtime-jobs.json). Runtime check: snapshot binding only; CLI/native effects NOT REPLAYED.

Live maintenance/drain remains unverified until prompt-runtime #453 supplies a staging window. No runtime-server implementation belongs to this plan.
