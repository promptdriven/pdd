# SVG layout spec

1. [Keep the built screen aligned with its drawing](svg-layout-spec.md): local prompt/drawing warnings and a failing browser comparison for missing layout parts.

# Code PR test inventory (#2570)

1. [See which test cases disappeared](workflow-test-inventory.md): resolved-comparison counts, named removals, renamed/deleted/added files and unavailable comparisons. Test: `test/runtime/workflow-test-inventory.json`. Runtime check (workflow-test-inventory) (DRAFT): ✓ 3 of 3 criteria · 10/10 checks · 4 AI calls. Report: `5c994d0d-74a4-4bc8-8b87-12ef72207364` (receipt in run check-prompt-amendment.md).
2. [See changed expectations in kept tests](workflow-assertion-changes.md): unchanged counts, old → new assertion lines, removed assertions and unchanged expectations. Test: `test/runtime/workflow-assertion-changes.json`. Runtime check (workflow-assertion-changes) (DRAFT): ✓ 3 of 3 criteria · 11/11 checks · 4 AI calls. Report: `c7fbafe4-3340-44ff-9dcf-024fbf7d7e11` (receipt in run check-prompt-amendment.md).
3. [See newly skipped or pending tests](workflow-new-skips.md): newly introduced skip/todo/xfail markers, explicit none and invalid baselines. Test: `test/runtime/workflow-new-skips.json`. Runtime check (workflow-new-skips) (DRAFT): ✓ 3 of 3 criteria · 12/12 checks · 4 AI calls. Report: `cad58a3d-3da1-461e-b587-f3af1e7bab70` (receipt in run check-prompt-amendment.md).

The existing SVG plan above is independent. The person approved the prompt after the fresh check passed. The 31 other expected checks remain unchanged; two report strings received person-approved @-escaping updates. Inputs, criteria and step identities are unchanged. Earlier results remain in run check.md and PR #2616 history. New edges await native Git and publication proof; these synthetic passes do not validate the frozen original replay anchor (issue #2633).
