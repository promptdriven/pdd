# See which test cases disappeared

I can review named test removals against the current shared base of my branch and the original run base branch before reviewing the code PR.

## Acceptance criteria

1. For three named cases reduced to two by removing "gone" and "also gone" and adding "new", the report shows 3 → 2 tests and names both removed cases "gone" and "also gone".
2. A renamed test file keeps matching case names; a deleted test file names its removed case, and an added file shows 0 → 1 tests, preserving unusual paths.
3. Comparison requests retain the exact saved base and committed head; unavailable data is shown as unavailable rather than none.

## Rules to check

For the code PR, fetch the original run base branch and compare its merge-base with committed head; stacking on PR 1 must keep PR 1's tests in the report. Merging a newer base must not blame this PR for base-only changes. Keep the saved start commit unchanged for replay and old-code proof. Refresh after automatic commits on code PR creation, update and retry; PR 1 keeps its existing body. A base fetch or merge-base failure reports unavailable without using stale data, and never blocks publication.

The synthetic AC3 checks only that the collector preserves the exact supplied comparison pair and discloses unavailable data. Its acceptance criteria, input and check structure remain unchanged in this revision; resolving the runner's comparison base requires a real repository test. A case name change still counts as removal plus addition; optional added-name presentation is deferred.

Only candidate test records count toward 1,000. A candidate blob over 1 MiB, binary or invalid UTF-8 gets its own unavailable file lines while healthy files remain visible. A failed snapshot/command/NUL parse, more than 1,000 candidate records, or more than 16 MiB of otherwise usable candidate content remains whole-comparison unavailable. Unavailable categories never claim none.

The first inventory line starts "Tests vs base:". Short compared-commit provenance follows at the end of the block; full identities stay in local metadata and the complete artifact. Source-derived test and suite names use the inventory owner's JSON-literal code-span format; assertion and skip lines use that same format. Exact identities remain unchanged. The run record stores bounded text and artifact/provenance metadata, with full detail only in test-inventory.json and an honest disclosure if saving fails. Publication refreshes send the body on stdin and preserve ownership and replay safeguards.

## Review status

Current formatting draft: NOT CHECKED / NOT APPROVED. The earlier scoped result of 3/3 criteria and 10/10 checks is historical and does not validate this draft. The original inputs, criteria, check positions and operators remain unchanged; only report-value formatting changes are proposed for person review. Full old/new values and historical receipts are outside the repository in the run notes.

Native proof must cover fetched-base merges (including retained PR 1 tests), unavailable fetch/merge-base, candidate-only limits and bad-file isolation, code-span rendering, first-line/provenance order, bounded status custody and artifact failures. Publication proof uses real Git and a local bare remote, a gh fake that consumes process input, and a test through the default process path. Canonicalize temporary fixture roots with realpath so a macOS /var symlink cannot fail worktree ownership. These effects are not proved by the supplied snapshots.
