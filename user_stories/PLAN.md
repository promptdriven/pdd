# SVG layout spec

1. [Keep the built screen aligned with its drawing](svg-layout-spec.md): local prompt/drawing warnings and a failing browser comparison for missing layout parts.

# Code PR test inventory (#2570)

1. [See which test cases disappeared](workflow-test-inventory.md): saved-base counts, named removals, renamed/deleted/added files and unavailable comparisons. Test: `test/runtime/workflow-test-inventory.json`. Runtime check (workflow-test-inventory): not run (Story gate draft).
2. [See changed expectations in kept tests](workflow-assertion-changes.md): unchanged counts, old → new assertion lines, removed assertions and unchanged expectations. Test: `test/runtime/workflow-assertion-changes.json`. Runtime check (workflow-assertion-changes): not run (Story gate draft).
3. [See newly skipped or pending tests](workflow-new-skips.md): newly introduced skip/todo/xfail markers, explicit none and invalid baselines. Test: `test/runtime/workflow-new-skips.json`. Runtime check (workflow-new-skips): not run (Story gate draft).

The existing SVG plan above is independent. These three Stories and their expected results are drafts for review. Native Git and PR integration tests belong to the later code area.
