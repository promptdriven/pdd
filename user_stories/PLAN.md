# SVG layout spec

1. [Keep the built screen aligned with its drawing](svg-layout-spec.md): local prompt/drawing warnings and a failing browser comparison for missing layout parts.

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
