# SVG layout spec

1. [Keep the built screen aligned with its drawing](svg-layout-spec.md): local prompt/drawing warnings and a failing browser comparison for missing layout parts.

## Code PR test inventory (#2570)

Not checked: Runtime prompt checks (#2579); the current source has 13 criteria and 45 unjudged checks, with 0 AI calls. No more staging checks are authorized.

1. [See which test cases disappeared](workflow-test-inventory.md). Test: `test/runtime/workflow-test-inventory.json`. Runtime check (workflow-test-inventory): NOT RUN; 3 criteria and 10 checks unjudged.
2. [See changed expectations in kept tests](workflow-assertion-changes.md). Test: `test/runtime/workflow-assertion-changes.json`. Runtime check (workflow-assertion-changes): NOT RUN; 3 criteria and 11 checks unjudged.
3. [See newly skipped or pending tests](workflow-new-skips.md). Test: `test/runtime/workflow-new-skips.json`. Runtime check (workflow-new-skips): NOT RUN; 3 criteria and 12 checks unjudged.
4. [Read source text safely in the code PR report](workflow-inventory-code-spans.md). Test: `test/runtime/workflow-inventory-code-spans.json`. Runtime check (workflow-inventory-code-spans): NOT RUN; 4 criteria and 12 checks unjudged.

Two historical attempts each selected 42 checks and dispatched none (#2579); the three new checks were not attempted. Root reviewed the marker-preservation clause, fourth criterion and three exact expectations, then approved the owner at the terminal. This is contract approval, not a Runtime pass. All 42 existing checks and original inputs remain unchanged. Code acceptance requires all 45 native checks, real default Git/process and marker-safe publisher proof, final GitHub rendering with zero mention or issue anchors, fresh verify/formal/review, and the full suite. The frozen original replay remains BLOCKED (#2633); the exhausted repair history is not reset. The independent SVG plan above is unchanged.

## Committed proof and PR evidence (#2594)

1. [workflow-prove](workflow-prove.md): explicitly compare committed regression tests on saved old code and committed new code.
2. [workflow-proof-pr](workflow-proof-pr.md): publish the current machine proof, including failed, stale and unavailable results.
3. [workflow-pr-labels](workflow-pr-labels.md): lift defect/proof/review lines and "Not checked:" immediately after "Not fixed yet:" on both PRs, and keep warning-light-only issues open.

Each Story has its own `test/runtime/<story>.json`. The person approved the revised contract and all 157 expected checks. The latest Runtime attempt judged none: required parser/catalog context was refused at admission (#2549), with 0 AI calls. Prior receipts do not establish this source revision. The three Runtime-interface owners have terminal approval. The native-only runner source was reviewed separately and has no Runtime interface to approve; Runtime admission/approval limitations (#2549) do not establish a Runtime pass. Final code verification and review remain pending; prompt approval is separate from Story approval.

Runtime check (workflow-prove): not run; 8 criteria and 84 checks unjudged.
Runtime check (workflow-proof-pr): not run; 4 criteria and 47 checks unjudged.
Runtime check (workflow-pr-labels): not run; 7 criteria and 26 checks unjudged.

The seven workflow Stories retain their separately approved contracts and all 202 exact checks (45 inventory + 157 proof/labels). The runner combines their evidence without changing their owner prompts or scenario expectations: replay/failure preambles remain first, machine proof precedes inventory, and inventory precedes Review. Integration native acceptance is pending; neither historical receipts nor source approval establishes a current Runtime pass.
