# Dynamic test inventory

I can review a static test inventory without mistaking generated test counts for known zero.

## Acceptance criteria

1. A generated test file whose cases have computed names reports an unknown count, rather than claiming zero tests or known removals, assertion changes, or skips.
2. Import-only and visibly dynamic declarations make their file pair unknown, including mixed files and renames or deletions.
3. Healthy static files retain their counts and changes, while genuinely empty or absent sides remain known zero.

## Rules to check

An unknown file pair cannot claim a count, removals, assertion changes or skips. Other healthy files keep their evidence; an absent or empty side is known zero. The inventory does not execute source or load imports.
