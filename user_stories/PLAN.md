# SVG layout spec

1. [Keep the built screen aligned with its drawing](svg-layout-spec.md): local prompt/drawing warnings and a failing browser comparison for missing layout parts.

# Code PR test inventory (#2570)

1. [See which test cases disappeared](workflow-test-inventory.md): resolved-comparison counts, named removals, renamed/deleted/added files and unavailable comparisons. Test: `test/runtime/workflow-test-inventory.json`. Historical Runtime check (workflow-test-inventory): ✓ 3 of 3 criteria · 10/10 checks · 4 AI calls. Report: `5dc76699-c3db-4181-a3b5-0b1f8cbd017c` (link in PR #2616 and run check.md).
2. [See changed expectations in kept tests](workflow-assertion-changes.md): unchanged counts, old → new assertion lines, removed assertions and unchanged expectations. Test: `test/runtime/workflow-assertion-changes.json`. Historical Runtime check (workflow-assertion-changes): ✓ 3 of 3 criteria · 11/11 checks · 4 AI calls. Report: `474d986f-c6ab-4399-97be-38301255358d` (link in PR #2616 and run check.md).
3. [See newly skipped or pending tests](workflow-new-skips.md): newly introduced skip/todo/xfail markers, explicit none and invalid baselines. Test: `test/runtime/workflow-new-skips.json`. Historical Runtime check (workflow-new-skips): ✓ 3 of 3 criteria · 12/12 checks · 4 AI calls. Report: `f15175cf-ec98-4169-89fb-060bcdc335c8` (link in PR #2616 and run check.md).

The existing SVG plan above is independent. These results are historical evidence for the approved contract at 4b5ce8885 / 875d38ce9; report links may expire. The revised draft has not been checked or approved. The 31 other expected checks remain unchanged; two report strings received explicitly reviewed @-escaping updates. Scenario inputs, criteria and step identities are unchanged. New required edges need native Git and publication regression proof in the code area; the historical prompt-runtime passes do not establish those effects.
