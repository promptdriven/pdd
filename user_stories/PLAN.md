# SVG layout spec

1. [Keep the built screen aligned with its drawing](svg-layout-spec.md): local prompt/drawing warnings and a failing browser comparison for missing layout parts.

## Committed proof and PR evidence (#2594)

1. [workflow-prove](workflow-prove.md): explicitly compare committed regression tests on saved old code and committed new code.
2. [workflow-proof-pr](workflow-proof-pr.md): publish the current machine proof, including failed, stale and unavailable results.
3. [workflow-pr-labels](workflow-pr-labels.md): lift defect/proof/review lines and "Not checked:" immediately after "Not fixed yet:" on both PRs, and keep warning-light-only issues open.

Each Story has its own `test/runtime/<story>.json`. The person approved the revised contract and all 157 expected checks. The latest Runtime attempt judged none: required parser/catalog context was refused at admission, with 0 AI calls. Prior receipts do not establish this source revision. Source/native fallback review is pending; prompt approval is separate from Story approval.

Runtime check (workflow-prove): not run; 8 criteria and 84 checks unjudged.
Runtime check (workflow-proof-pr): not run; 4 criteria and 47 checks unjudged.
Runtime check (workflow-pr-labels): not run; 7 criteria and 26 checks unjudged.
