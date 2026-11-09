# Check relation evidence

I can have the evidence for each proposed bug relation checked before any link is written.

As a maintainer, I want check relation evidence, so that related bug work is grounded in evidence.

## Acceptance criteria

1. Every proposed quote must exist exactly in its current trusted issue or code source before any batch mutation.
2. Missing, changed, inaccessible, unavailable or untrusted evidence holds the batch; a matching quote does not determine a relation.
3. Evidence and authority are checked again before an effect if observations can have changed.

## Native cases for the code step

[Requirement-derived cases](../test/bug-relations/bug-relation-evidence-cases.json) need native tests against the public workflow and GitHub adapter with injected ports. Native effects and run/PR storage are not Runtime-replayed; no pass is claimed.

## Native validation

[Draft native profile](../prompts/cli/issue-dependencies-github.prompt.md#native-validation-profile-bug-relation-evidence) names required future test identities and source paths. Those tests, native capture and evidence intake are prerequisites; this declaration is not proof.
