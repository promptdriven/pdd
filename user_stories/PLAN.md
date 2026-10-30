# SVG layout spec

1. [Keep the built screen aligned with its drawing](svg-layout-spec.md): local prompt/drawing warnings and a failing browser comparison for missing layout parts.

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
