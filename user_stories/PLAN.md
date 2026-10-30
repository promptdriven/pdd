# SVG layout spec

1. [Keep the built screen aligned with its drawing](svg-layout-spec.md): local prompt/drawing warnings and a failing browser comparison for missing layout parts.

# Code PR test inventory (#2570)

1. [See which test cases disappeared](workflow-test-inventory.md): resolved-comparison counts, named removals, renamed/deleted/added files and unavailable comparisons. Test: `test/runtime/workflow-test-inventory.json`. Runtime check (workflow-test-inventory) (DRAFT): ✓ 3 of 3 criteria · 10/10 checks · 4 AI calls. Report: `5c994d0d-74a4-4bc8-8b87-12ef72207364` (receipt in run check-prompt-amendment.md).
2. [See changed expectations in kept tests](workflow-assertion-changes.md): unchanged counts, old → new assertion lines, removed assertions and unchanged expectations. Test: `test/runtime/workflow-assertion-changes.json`. Runtime check (workflow-assertion-changes) (DRAFT): ✓ 3 of 3 criteria · 11/11 checks · 4 AI calls. Report: `c7fbafe4-3340-44ff-9dcf-024fbf7d7e11` (receipt in run check-prompt-amendment.md).
3. [See newly skipped or pending tests](workflow-new-skips.md): newly introduced skip/todo/xfail markers, explicit none and invalid baselines. Test: `test/runtime/workflow-new-skips.json`. Runtime check (workflow-new-skips) (DRAFT): ✓ 3 of 3 criteria · 12/12 checks · 4 AI calls. Report: `cad58a3d-3da1-461e-b587-f3af1e7bab70` (receipt in run check-prompt-amendment.md).

The existing SVG plan above is independent. The fresh scoped check passed the current reviewed contract: 9 of 9 criteria, 33/33 checks and 12 AI calls. It ran as DRAFT before the person approved the prompt in 737926a39. Batch `20261030-002041-6rdr` captured HEAD `b0df4ec5c` with source SHA-256 `38668783910a44d417390de190d409b57d1a135eb923c582c8de9f48bdf199a9`. Later PLAN, prompt-approval and Story review-status metadata changes preserve the contract and checks, but current source bytes differ from that captured receipt. The 31 other expected checks remain unchanged; two report strings received explicitly person-approved @-escaping updates. Scenario inputs, criteria and step identities are unchanged.

The earlier 33/33 result at 4b5ce8885 / 875d38ce9 remains historical evidence for the prior approved contract in run check.md and PR #2616 history; report links may expire. New required edges still need native Git and publication regression proof in the code area. These synthetic passes do not establish those effects or validate the original frozen replay anchor; the amendment limitation is tracked in issue #2633.
