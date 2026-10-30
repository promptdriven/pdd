# I check shared plan contracts locally

## Acceptance criteria

1. I can check a plan before parts have prompts, Stories or tests, with no server, model, authentication, runtime slot or file change.
2. I see a nonzero result with a file, record and field when a shared schema, reference or eligible inline copy is wrong.
3. I can link each world key explicitly to its schema and check every present seed value with one declared writer.
4. I can leave a declared world key out of the starting seed and repeat an identical ownership row without failing.
5. I see unavailable validation instead of a pass or an invented mismatch when a required selected schema or value predicate cannot be established locally.
6. I can use array and primitive component schemas, JSON schema containers and seed data without confusing their roles.
7. I keep exact JSON numbers and own keys, and my local check leaves all source and expected values unchanged.
8. I can still list contracts and preview migration with their advisory behavior; invalid check combinations are command errors.
9. I can plan without world files when both are absent, while a missing partner or broken explicit schema link identifies what needs fixing.

## Rules to check

Exit 0 requires complete local evidence for every applicable schema, reference,
eligible copy agreement and present world value. Definite contract problems exit
4; absent a definite problem, unavailable selected-schema/predicate evidence exits 5.
Syntax/no repository exits 2. No check authenticates, reserves a runtime slot,
contacts a server/model, reads Check history or writes a file. Declared absent
world keys are allowed; uncovered seed keys fail ownership checks. Optional
schemas leave an honest unchecked-values warning; selected schemas validate
present values. Lossy numeric comparison and unknown pattern membership can
never establish a pass. Ordinary listing/sync and Runtime P9 remain unchanged.

Runtime check: Not run: native Git/filesystem and CLI effects are specified in
`test/shared-contracts/local-contract-check.json`; no server call is part of this
plan check. Native replay and independent verification are required in code space.
