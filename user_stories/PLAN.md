# SVG layout spec

1. [Keep the built screen aligned with its drawing](svg-layout-spec.md): local prompt/drawing warnings and a failing browser comparison for missing layout parts.

# Code PR test inventory (#2570)

Not checked: Runtime prompt checks (lint wait/continuation limit; #2579). The person approved the contract; all 12 criteria and 42 checks remain unjudged, with 0 AI calls.

1. [See which test cases disappeared](workflow-test-inventory.md). Test: `test/runtime/workflow-test-inventory.json`. Runtime check (workflow-test-inventory): NOT RUN; 3 criteria and 10 checks unjudged.
2. [See changed expectations in kept tests](workflow-assertion-changes.md). Test: `test/runtime/workflow-assertion-changes.json`. Runtime check (workflow-assertion-changes): NOT RUN; 3 criteria and 11 checks unjudged.
3. [See newly skipped or pending tests](workflow-new-skips.md). Test: `test/runtime/workflow-new-skips.json`. Runtime check (workflow-new-skips): NOT RUN; 3 criteria and 12 checks unjudged.
4. [Read source text safely in the code PR report](workflow-inventory-code-spans.md). Test: `test/runtime/workflow-inventory-code-spans.json`. Runtime check (workflow-inventory-code-spans): NOT RUN; 3 criteria and 9 checks unjudged.

The person reviewed all 16 formatting-only value changes and nine additive checks; the other 17 values and all original inputs, criteria, steps and check metadata are unchanged. Both attempts passed lint but sent no Story checks; receipts remain in external run notes. Code acceptance requires all 42 native checks, real Git and final GitHub-render proof, fresh verification and review, and the full suite. The frozen original replay remains BLOCKED (#2633); the exhausted repair history is not reset. The independent SVG plan above is unchanged.
