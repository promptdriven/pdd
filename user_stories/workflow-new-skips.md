# See newly skipped or pending tests

I can see newly skipped, pending or expected-failure cases in the code PR report.

## Acceptance criteria

1. Changing "kept" to skip and adding "later" as todo lists both new marker lines, while an existing unchanged skip is not listed as new.
2. Adding an expected-failure decorator to a kept Python test lists that new marker; a Go test remains counted by name.
3. No changed test files produces explicit none categories; invalid commit identities produce unavailable without reading a snapshot.

## Rules to check

Skips are differences from the saved start commit, including xfail under "New skips:". Do not remove a skip or introduce an approval gate. JS literal options and t.skip/t.todo, plus contiguous pytest skip/skipif/xfail decorators, are included as draft static conventions; dynamic/generated markers and Go t.Skip are outside scope. Reports are escaped and bounded; full details belong in the run folder when saved successfully.

## Review status

Draft for the person's review; expectations have not been approved. The runtime cases check the informational report with synthetic snapshots. Real Git enumeration, committed-head timing, PR placement/refresh and report-only publication require native tests in the code area; they are not proved by these scenarios.
