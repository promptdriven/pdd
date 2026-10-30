# SVG layout spec

1. [Keep the built screen aligned with its drawing](svg-layout-spec.md): local prompt/drawing warnings and a failing browser comparison for missing layout parts.

## Product plans

1. [Choose a product path](product-map.md): read the durable map and the small one-run path.
2. [Track product progress](product-status.md): current, stale and not-run Stories by part and slice.
3. [Find the next product runs](product-next.md): ready runs and waiting needs.
4. [Start a planned run once](product-start.md): reuse its issue and optionally launch the feature workflow.

- [Compose a product Try](product-compose-try.md) — Runtime check: test/runtime/product-compose-try.json
- [Seed a journey](product-journey-seed.md) — Runtime check: test/runtime/product-journey-seed.json
- [Choose journey checks](product-choose-journeys.md) — Runtime check: test/runtime/product-choose-journeys.json
- [Coffee journey](journeys/J1-coffee-pickup.md) — Runtime check: test/runtime/J1-coffee-pickup.json

# Shared runtime admission (#2631)

Build on the saved-lint continuation contract. Prompts and expected cases are reviewed before code. Native tests use fake transport/clock plus real temporary state and child processes; do not claim supplied port replies prove atomic exclusion. Each Story has one case file. Five native case files use pdd.native-cases.v1 and are not discovered as executable Runtime scenarios; the jobs snapshot has a real Runtime scenario.

- [runtime-local-slots](runtime-local-slots.md) — [native cases](../test/runtime-admission/runtime-local-slots.json). Runtime check: NOT REPLAYED (#2548); native cases in Story.
- [runtime-local-queue](runtime-local-queue.md) — [native cases](../test/runtime-admission/runtime-local-queue.json). Runtime check: NOT REPLAYED (#2548); native cases in Story.
- [runtime-capacity-wait](runtime-capacity-wait.md) — [native cases](../test/runtime-admission/runtime-capacity-wait.json). Runtime check: NOT REPLAYED (#2548); native cases in Story.
- [runtime-maintenance-wait](runtime-maintenance-wait.md) — [native cases](../test/runtime-admission/runtime-maintenance-wait.json). Runtime check: NOT REPLAYED (#2548); native cases in Story.
- [runtime-restart-retry](runtime-restart-retry.md) — [native cases](../test/runtime-admission/runtime-restart-retry.json). Runtime check: NOT REPLAYED (#2548); native cases in Story.
- [runtime-jobs](runtime-jobs.md) — [scenario](../test/runtime/runtime-jobs.json). Runtime check: snapshot binding only; CLI/native effects NOT REPLAYED.

Live maintenance/drain remains unverified until prompt-runtime #453 supplies a staging window. No runtime-server implementation belongs to this plan.

# Shared records (#2629)

Each Story has one case file. The expansion entries use actual file-resource
ports; catalog/history, CLI, capture and write effects require native verification.

- [shared-records](shared-records.md) — [scenario](../test/runtime/shared-records.json). Runtime check: expansion binding only.
- [shared-seed](shared-seed.md) — [scenario](../test/runtime/shared-seed.json). Runtime check: expansion binding only.
- [shared-contract-status](shared-contract-status.md) — [native cases](../test/shared-contracts/shared-contract-status.json). Runtime check: native effects unbound.
- [shared-contract-drift](shared-contract-drift.md) — [native cases](../test/shared-contracts/shared-contract-drift.json). Runtime check: CLI advice unbound.
- [shared-contract-sync](shared-contract-sync.md) — [native cases](../test/shared-contracts/shared-contract-sync.json). Runtime check: native writes unbound.
