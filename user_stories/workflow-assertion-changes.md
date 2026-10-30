# See changed expectations in kept tests

I can see old and new assertion lines even when the number of tests stays the same.

## Acceptance criteria

1. Keeping "PATH2" while changing its assertion from an empty error stream to a PATH warning shows 1 → 1 tests and the exact old → new line.
2. Removing one assertion in a kept case shows its old line → (removed); assertions in a wholly removed case appear only as a named test removal.
3. An unchanged assertion produces no changed-assertion entry, and a newly added assertion shows (added) → its exact line.

## Rules to check

A changed test count cannot stand in for comparing assertion lines. Associate assertions with kept cases only, compare exact lines and retain source order. Do not approve changed expectations or rewrite tests. Preserve exact assertion bytes, including a line-ending carriage return; optional CRLF normalization is deferred. If old assertion count times new assertion count exceeds 1,000,000, report "too many assertion lines to compare" for that kept test alone. At exactly the limit compare normally, with the existing tie and source-order results. Counts, removals, skips and other tests must survive a capped assertion comparison. Matching below the cap must use bounded quadratic work without rebuilding a full table at every mismatch. This report cannot judge whether an expectation is correct.

## Review status

Revised draft for review, not checked or approved. All four original synthetic cases and expected checks remain unchanged; historical passes apply to the prior approved contract. New cap boundary, unchanged tie ordering and a 2,000-line case finishing in under two seconds require native proof in the code area. A model's prompt-runtime duration proves no native timing bound. Real Git enumeration and publication remain separate native obligations.
