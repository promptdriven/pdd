# SVG layout spec

1. [Keep the built screen aligned with its drawing](svg-layout-spec.md): local prompt/drawing warnings and a failing browser comparison for missing layout parts.

# Code PR test inventory (#2570)

Not checked: Runtime prompt checks (#2579); the current source has 13 criteria and 45 unjudged checks, with 0 AI calls. No more staging checks are authorized.

1. [See which test cases disappeared](workflow-test-inventory.md). Test: `test/runtime/workflow-test-inventory.json`. Runtime check (workflow-test-inventory): NOT RUN; 3 criteria and 10 checks unjudged.
2. [See changed expectations in kept tests](workflow-assertion-changes.md). Test: `test/runtime/workflow-assertion-changes.json`. Runtime check (workflow-assertion-changes): NOT RUN; 3 criteria and 11 checks unjudged.
3. [See newly skipped or pending tests](workflow-new-skips.md). Test: `test/runtime/workflow-new-skips.json`. Runtime check (workflow-new-skips): NOT RUN; 3 criteria and 12 checks unjudged.
4. [Read source text safely in the code PR report](workflow-inventory-code-spans.md). Test: `test/runtime/workflow-inventory-code-spans.json`. Runtime check (workflow-inventory-code-spans): NOT RUN; 4 criteria and 12 checks unjudged.

The earlier receipts cover 42 checks attempted and 0 dispatched; the three new checks were not attempted. Root reviewed the marker-preservation clause, fourth criterion and three exact expectations, then approved the owner at the terminal. This is contract approval, not a Runtime pass. All 42 existing checks and original inputs remain unchanged. Code acceptance requires all 45 native checks, real default Git/process and marker-safe publisher proof, final GitHub rendering with zero mention or issue anchors, fresh verify/formal/review, and the full suite. The frozen original replay remains BLOCKED (#2633); the exhausted repair history is not reset. The independent SVG plan above is unchanged.
