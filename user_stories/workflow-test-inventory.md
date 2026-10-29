# See which test cases disappeared

I can review named test removals against the saved start of my run before reviewing the code PR.

## Acceptance criteria

1. For three named cases reduced to two by removing "gone" and "also gone" and adding "new", the report shows 3 → 2 tests and names both removed cases "gone" and "also gone".
2. A renamed test file keeps matching case names; a deleted test file names its removed case, and an added file shows 0 → 1 tests, preserving unusual paths.
3. Comparison requests retain the exact saved base and committed head; unavailable data is shown as unavailable rather than none.

## Rules to check

Use the run's saved start commit even for a stacked code PR; refresh on code PR creation, update and retry after committing. PR 1 keeps its existing body. A reported removal never blocks publication. Static names plus their occurrence within a matched file pair define kept cases; renaming a case counts as removal plus addition. Empty categories say "none"; failed reads must never claim no removals. Detection bounds and the small-change single-PR inclusion are draft contract choices in the inventory and runner prompts.

## Review status

Draft for the person's review; expectations have not been approved. The runtime cases check the informational report with synthetic snapshots. Real Git enumeration, committed-head timing, PR placement/refresh and report-only publication require native tests in the code area; they are not proved by these scenarios.
