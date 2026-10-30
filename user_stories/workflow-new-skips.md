# See newly skipped or pending tests

I can see newly skipped, pending or expected-failure cases in the code PR report.

## Acceptance criteria

1. Changing "kept" to skip and adding "later" as todo lists both new marker lines, while an existing unchanged skip is not listed as new.
2. Adding an expected-failure decorator to a kept Python test lists that new marker; a Go test remains counted by name.
3. No changed test files produces explicit none categories; invalid commit identities produce unavailable without reading a snapshot.

## Rules to check

Skips are differences between the exact resolved comparison commits, including xfail under "New skips:". Do not remove a skip or introduce an approval gate. JS literal true options and nonempty static string skip options, t.skip/t.todo, xit, describe.skip, pytest.skip calls and contiguous pytest skip/skipif/xfail decorators are included. Count xit as a test and a skip. A suite marker has its own exact static name and occurrence identity, displays as a suite, and never adds a test or copies its marker onto every child. Dynamic/generated markers and Go t.Skip remain outside scope. Reports are escaped and bounded; full details belong in the run folder when saved successfully.

## Review status

Current formatting draft: NOT CHECKED / NOT APPROVED. The earlier scoped result of 3/3 criteria and 12/12 checks is historical and does not validate this draft. The original inputs, criteria, check positions and operators remain unchanged; only report-value formatting changes are proposed for person review. The earlier two person-approved @-entity expectation changes remain historical; this draft replaces that format with the inventory owner's JSON-literal code spans.

Native regression proof must cover each skip form, repeated suite names, unchanged suite markers, suite/test identity separation and xit's count. The supplied snapshots do not prove Git, process transport, macOS fixture ownership or publication effects.
