# Read native issue dependencies

I can read native prerequisites and see why work waits.

## Acceptance criteria

1. A reviewed independent issue is current and dependency-clear; an unchecked issue is not eligible.
2. CRM issue 42 waits for schema issue 42 in another repository; completed work releases the native blocker, but not-planned, unknown, reopened or required-deployment work does not.
3. A native human edge with no saved reason remains visible. Merge alone does not satisfy an open prerequisite.
4. Self edges, duplicate additions and same- or cross-repository cycles are refused. Existing native cycles remain visible.
5. Claims, open PRs, stuck work, unknown trust and incomplete reads keep their separate holds and do not become eligible.

## Rules to check

Only a current completed review plus the model prerequisites can give dependency eligibility. No missing review, partial page, merge-only fact, unknown prerequisite or scheduling hold may become eligible. Native edges are authoritative. Full repository identity must survive every edge.
