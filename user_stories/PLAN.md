# SVG layout spec

1. [Keep the built screen aligned with its drawing](svg-layout-spec.md): local prompt/drawing warnings and a failing browser comparison for missing layout parts.

# Shared runtime admission (#2631)

Build on the saved-lint continuation contract. The existing Stories also cover owner heartbeat expiry, contention progress, bounded maintenance, fail-open advisory capacity, phase-specific lint waits, truthful wait-end text and per-process read reuse. Prompts and expected cases are reviewed before code. Native tests use fake transport/clock plus real temporary state and child processes; do not claim supplied port replies prove atomic exclusion. Follow-up native checks cover wall-clock jumps during acquisition, interruption between admission and submission, long observer timers and cached unclear capacity; check causal order, no resend, exclusion and completion with generous watchdogs. These native timer/process effects are not Runtime-replayed. Each Story has one case file. Five native case files use pdd.native-cases.v1 and are not discovered as executable Runtime scenarios; the jobs snapshot has a real Runtime scenario.

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

- [shared-source-limits](shared-source-limits.md) — [native cases](../test/shared-contracts/shared-source-limits.json). Runtime check: native read/allocation/archive effects unbound.

2. [Recognize checks with no verdict](check-no-verdict.md): distinguish failed, no-verdict, open and busy summaries.

3. [Recover retried check results](recover-retried-check-results.md): recover same-ID receipts and accounting without duplicate execution.

## Code PR test inventory (#2570)

Not checked: Runtime prompt checks (#2579); the current source has 13 criteria and 45 unjudged checks, with 0 AI calls. No more staging checks are authorized.

1. [See which test cases disappeared](workflow-test-inventory.md). Test: `test/runtime/workflow-test-inventory.json`. Runtime check (workflow-test-inventory): NOT RUN; 3 criteria and 10 checks unjudged.
2. [See changed expectations in kept tests](workflow-assertion-changes.md). Test: `test/runtime/workflow-assertion-changes.json`. Runtime check (workflow-assertion-changes): NOT RUN; 3 criteria and 11 checks unjudged.
3. [See newly skipped or pending tests](workflow-new-skips.md). Test: `test/runtime/workflow-new-skips.json`. Runtime check (workflow-new-skips): NOT RUN; 3 criteria and 12 checks unjudged.
4. [Read source text safely in the code PR report](workflow-inventory-code-spans.md). Test: `test/runtime/workflow-inventory-code-spans.json`. Runtime check (workflow-inventory-code-spans): NOT RUN; 4 criteria and 12 checks unjudged.

Two historical attempts each selected 42 checks and dispatched none (#2579); the three new checks were not attempted. Root reviewed the marker-preservation clause, fourth criterion and three exact expectations, then approved the owner at the terminal. This is contract approval, not a Runtime pass. All 42 existing checks and original inputs remain unchanged. Code acceptance requires all 45 native checks, real default Git/process and marker-safe publisher proof, final GitHub rendering with zero mention or issue anchors, fresh verify/formal/review, and the full suite. The frozen original replay remains BLOCKED (#2633); the exhausted repair history is not reset. The independent SVG plan above is unchanged.

## Committed proof and PR evidence (#2594)

1. [workflow-prove](workflow-prove.md): explicitly compare committed regression tests on the fetched-base merge-base old code and committed new code.
2. [workflow-proof-pr](workflow-proof-pr.md): publish the current machine proof, including failed, stale and unavailable results.
3. [workflow-pr-labels](workflow-pr-labels.md): lift defect/proof/review lines and "Not checked:" immediately after "Not fixed yet:" on both PRs, and keep warning-light-only issues open.

Each Story has its own `test/runtime/<story>.json`. The root, acting as the person under the flow lead's instructions, reviewed and approved the revised Stories and all 247 expected checks from REVIEW-2594 and the latest FLOW-R label contract. The final re-check adds literal-command/control display and a diagnostic tail before a TAP summary while preserving the prior checks except the reviewed command display correction. The prove and PR-evidence Runtime interfaces were approved through the actual CLI; the native-only runner integration received separate source review and retains its existing interface shape. Runtime execution remains unjudged: no Runtime or staging call was made for this source revision. Prior receipts and the original 157-check/37-step historical baseline do not establish this revision. That original baseline remains recorded outside source; the revised files contain 55 steps, 247 checks and 19 criteria.

Runtime check (workflow-prove): not run; 8 criteria, 24 steps and 128 checks unjudged.
Runtime check (workflow-proof-pr): not run; 4 criteria, 18 steps and 87 checks unjudged.
Runtime check (workflow-pr-labels): not run; 7 criteria, 13 steps and 32 checks unjudged.

Native verification still must establish real fetched merge-base selection after a base merge, default Git/process isolation, interrupt/stale-owned-worktree cleanup, exact writer filtering in actual publication, GitHub rendering without mentions/issue links, and display of all lifted lines above every replay block. Fake Runtime ports establish none of those native effects.

The v2 record now requires interruptSignal independently of phase signals. Parent-interruption snapshots (including pre-process/interphase and cleanup-error precedence) and deterministic short failure tails are covered by added synthetic publication cases; actual native signal exits remain unproved by those records.

The seven workflow Stories retain their separately approved contracts and all 280 exact checks (45 inventory + 235 proof/labels). The draft combined runner preserves the inventory slot after machine proof and before Review, with the entire evidence block above every replay status. Its combined source still requires root/person approval; native integration acceptance and Runtime execution remain unjudged.

## Product plans

1. [Choose a product path](product-map.md): read the durable map and the small one-run path.
2. [Track product progress](product-status.md): current, stale and not-run Stories by part and slice.
3. [Find the next product runs](product-next.md): ready runs and waiting needs.
4. [Start a planned run once](product-start.md): reuse its issue and optionally launch the feature workflow.
5. [Keep my prepared run issue](product-issue-binding.md): durable issue identity before search indexing.
6. [Reuse one product search](product-search-cache.md): one shared query and a short local snapshot across commands.
7. [Continue when my account lookup is unavailable](product-unavailable-actor.md): untrusted claims cannot break product commands.
8. [Repair one broken run link](product-repair-link.md): isolate a deleted link and relink it explicitly.
9. [Keep an uncertain run link](product-unresolved-link.md): retain unresolved hints without blocking other runs.
10. [Reuse my run link in another checkout](product-worktree-links.md): reuse compatible legacy state across worktrees.
11. [Keep my other saved run links](product-state-updates.md): preserve other bindings during coordinated updates.

## Runtime interruption and recovery

- [Keep a truthful interruption message during recovery](runtime-interruption-recovery.md) — [native cases](../test/runtime-admission/runtime-interruption-recovery.json). Runtime check: NOT REPLAYED (#2548); native claim, interruption, ownership and retry effects require code-step checks.

## Busy Check upload waits

- [Wait before uploading a busy check again](runtime-busy-upload-wait.md) — [native cases](../test/runtime-admission/runtime-busy-upload-wait.json). Runtime check: NOT REPLAYED (#2548); upload timing, capacity observation and saved-retry effects require code-step checks.
