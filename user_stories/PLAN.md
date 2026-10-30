# SVG layout spec

1. [Keep the built screen aligned with its drawing](svg-layout-spec.md): local prompt/drawing warnings and a failing browser comparison for missing layout parts.

# Code PR test inventory (#2570)

1. [See which test cases disappeared](workflow-test-inventory.md): resolved-comparison counts, named removals, renamed/deleted/added files and unavailable comparisons. Test: `test/runtime/workflow-test-inventory.json`. Historical Runtime check (workflow-test-inventory): ✓ 3 of 3 criteria · 10/10 checks · 4 AI calls. [Report](https://runtime.34-123-197-119.sslip.io/r/5dc76699-c3db-4181-a3b5-0b1f8cbd017c).
2. [See changed expectations in kept tests](workflow-assertion-changes.md): unchanged counts, old → new assertion lines, removed assertions and unchanged expectations. Test: `test/runtime/workflow-assertion-changes.json`. Historical Runtime check (workflow-assertion-changes): ✓ 3 of 3 criteria · 11/11 checks · 4 AI calls. [Report](https://runtime.34-123-197-119.sslip.io/r/474d986f-c6ab-4399-97be-38301255358d).
3. [See newly skipped or pending tests](workflow-new-skips.md): newly introduced skip/todo/xfail markers, explicit none and invalid baselines. Test: `test/runtime/workflow-new-skips.json`. Historical Runtime check (workflow-new-skips): ✓ 3 of 3 criteria · 12/12 checks · 4 AI calls. [Report](https://runtime.34-123-197-119.sslip.io/r/f15175cf-ec98-4169-89fb-060bcdc335c8).

The existing SVG plan above is independent. These results are historical evidence for the approved contract at 4b5ce8885 / 875d38ce9; report links may expire. The revised draft has not been checked or approved. Original scenario files and all 33 expected checks remain unchanged. New required edges need native Git and publication regression proof in the code area; the historical prompt-runtime passes do not establish those effects.
