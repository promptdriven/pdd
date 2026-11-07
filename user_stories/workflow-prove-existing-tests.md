# Prove a code-only repair with landed tests

I can use my already landed regression tests to compare old and repaired code when my code PR changes only maps, styles or adapters.

## Acceptance criteria

1. For a code-only change to a map, stylesheet and adapter, when the regression tests already landed in the base, the supplied command runs in both committed snapshots without overlay; old exit 1 with "code: map-route-defect" and new exit 0 produce "proved", exit 0 and an empty copied-path list.
2. A fixture-only change also runs the supplied command in both committed snapshots without overlay; if both exit 0, the result is "old-passes" and exit 1, with an empty copied-path list.
3. If a changed regression test imports a native module absent from the old snapshot, the test alone is overlaid; an old ERR_MODULE_NOT_FOUND failure and new exit 0 produce "setup-error" and exit 1 even when the missing-module message contains the expected literal; both worktrees are cleaned up.

## Rules to check

The explicit command runs even when no eligible changed test entry exists. In that case no files are overlaid, including changed supplemental fixtures. Valid setup and cleanup, an ordinary nonzero old exit with the supplied literal and a zero new exit are required for proof. An empty copied-path list must not force "no-changed-tests" or prevent proof. A known missing-module failure must never count as behavioral proof or authorize copying implementation or selecting another old commit.

## What must not change

The old snapshot stays the merge-base of committed HEAD with the fetched selected base branch. Existing changed-test overlay conventions, byte/mode safety, dirty-byte exclusion, exact command/literal handling, bounded process execution, setup-error precedence, cleanup and evidence formatting remain governed by the owning prompt. No new selection option or automatic alternative baseline is introduced.

The scenario supplies synthetic run, Git and process replies. It checks decisions and exact host requests; it does not execute native tests, establish browser appearance or prove Git isolation, setup-diagnostic detection, process termination or cleanup effects. Native verification must run the same landed tests on real old/head snapshots and include map, CSS and adapter mutation controls.
