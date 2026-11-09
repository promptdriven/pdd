# Keep reproduced bug findings

I can see a reproduced bug’s cause and its discovered relations in the run and PR 1.

As a maintainer, I want to keep reproduced bug findings, so that related bug work is grounded in evidence.

## Acceptance criteria

1. A successful reproduction retains the exact cause, flaw and class and each discovered relation with its actual quote and source in the run and PR 1, including after refresh.
2. An empty relation search is recorded honestly; a failed reproduction never invents a cause.
3. Agent findings remain inert in PR text and never become check results.

## Rules to check

Retain actual findings and distinguish an empty search from an unavailable search. A failed reproduction must not produce a guessed cause.

## Must not change

Keep existing approvals and check receipts separate from agent findings; preserve non-bug workflow behavior.

## Native cases for the code step

[Requirement-derived cases](../test/bug-relations/bug-findings-record-cases.json) need native tests against the public workflow and GitHub adapter with injected ports. Native effects and run/PR storage are not Runtime-replayed; no pass is claimed.

## Native validation

[Draft native profile](../prompts/cli/workflow-runner.prompt.md#native-validation-profile-bug-findings-record) names required future test identities and source paths. Those tests, native capture and evidence intake are prerequisites; this declaration is not proof.
