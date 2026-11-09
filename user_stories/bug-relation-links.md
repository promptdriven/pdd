# Apply chosen native relations

I can have my evidence-backed relation choices reflected in safe native issue links.

As a maintainer, I want to apply chosen native relations, so that related bug work is grounded in evidence.

## Acceptance criteria

1. Only a necessary-before needs choice may create a dependency in the supplied direction; other classifications do not automatically become dependencies.
2. An explicitly selected existing Class parent may receive the selected sub-issue; an explicit duplicate is marked with verified native readback.
3. Existing links, human removals, graph cycles, ownership, incomplete observations and uncertain mutation outcomes are respected.

## Rules to check

Only an explicitly necessary-before `needs` choice may add a dependency. A cycle, confirmed human removal or undone duplicate must not be recreated. An unknown dispatch must not be resent.

## Must not change

Keep existing trust, ownership and graph rules, approvals, check receipts and non-bug workflow behavior.

## Native cases for the code step

[Requirement-derived cases](../test/bug-relations/bug-relation-links-cases.json) need native tests against the public workflow and GitHub adapter with injected ports. Native effects and run/PR storage are not Runtime-replayed; no pass is claimed.

## Native validation

[Draft native profile](../prompts/cli/issue-dependencies-github.prompt.md#native-validation-profile-bug-relation-links) names required future test identities and source paths. Those tests, native capture and evidence intake are prerequisites; this declaration is not proof.
