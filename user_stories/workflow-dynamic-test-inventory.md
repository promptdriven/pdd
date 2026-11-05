# Dynamic test inventory

I can review a static test inventory without mistaking generated test counts for known zero.

## Acceptance criteria

1. A generated test file whose cases have computed names reports an unknown count, rather than claiming zero tests or known removals, assertion changes, or skips.
