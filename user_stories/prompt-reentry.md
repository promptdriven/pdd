As a person reviewing PR 2, I want to correct its prompt in the open PR 1 and bring PR 1 up to date with main, so that I can regenerate and verify PR 2 through the same run.

## Acceptance criteria

1. I can return from code to the open PR 1 with `pdd workflow open ISSUE prompt-pr` or `story`. PDD keeps both PRs, the issue claim and the decisions that still apply. It clears old code results and resumes the selected prompt chat. I can replace that returned chat with `--new`.
2. PDD fetches PR 1 and merges the current saved base into PR 1 without rewriting published history. Conflicts stay on PR 1 for resolution. The integrated prompt source needs fresh checks before publication. Unrelated scenarios from main do not enter this run's changed-scenario anchor.
3. A changed Story or expected contract returns to the Story gate. A prompt-only correction keeps the Story approval. The normal Story card and its saved code-or-stop choice still apply. A covered automatic run needs no person question when current checks pass. Strict approval still requires the person.
4. Code entry checks the exact fetched PR 1 source. A later fetched Story or expected-value change cannot enter code under the earlier approval. Other changed scenario bytes require prompt checks, publication and an updated anchor. PDD saves no code-entry decision for a refused entry.
5. PDD merges a pinned, validated PR 1 commit into the existing code branch and checks the resulting contract. It keeps peer and code commits. I regenerate the code and run its checks again. PDD updates the same PR 2 and refuses prompt changes in its code publication.

## What must not change

The run identity, immutable saved base identity, claim ownership checks, strict terminal approvals, Story card, adopted-corpus authority and both PR identities stay in force. PDD does not run the tests or merge a PR.

## Rules to check

A code-entry decision requires the fetched source and the resulting code merge to retain the approved contract. A changed expected value requires Story approval. A moving remote reference cannot change a pinned merge source. Source publication must use the checked commit.

## Native verification

Use [the local verification recipe](../docs/prompt-reentry-verification.md). The native workflow operations in these cases are not declared interpreter entries. The Node tests exercise their public boundaries directly.
