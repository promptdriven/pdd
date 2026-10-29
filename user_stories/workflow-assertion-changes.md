# See changed expectations in kept tests

I can see old and new assertion lines even when the number of tests stays the same.

## Acceptance criteria

1. Keeping "PATH2" while changing its assertion from an empty error stream to a PATH warning shows 1 → 1 tests and the exact old → new line.
2. Removing one assertion in a kept case shows its old line → (removed); assertions in a wholly removed case appear only as a named test removal.
3. An unchanged assertion produces no changed-assertion entry, and a newly added assertion shows (added) → its exact line.

## Rules to check

A changed test count cannot stand in for comparing assertion lines. Associate assertions with kept cases only, compare exact lines and retain source order. Do not approve changed expectations or rewrite tests. The bounded line and case matching conventions are draft assumptions for review; this report cannot judge whether an expectation is correct.

## Review status

Draft for the person's review; expectations have not been approved. The runtime cases check the informational report with synthetic snapshots. Real Git enumeration, committed-head timing, PR placement/refresh and report-only publication require native tests in the code area; they are not proved by these scenarios.
