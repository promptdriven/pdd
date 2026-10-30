# Compare committed tests with old code

I can explicitly compare my committed regression test on the saved old code and committed new code, and see whether it detects the intended defect.

Draft for person review; these proposed policies and expected values are not approved.

## Acceptance criteria

1. With a committed changed test, a nonzero old-code exit containing the literal "defect-x" and a zero new-code exit produce a successful old-code proof and exit 0.
2. If the old code passes, or fails with "other-error" instead of "defect-x", the report distinguishes "old-passes" from "wrong-reason", includes the observed wrong-reason excerpt and exits 1.
3. If the new code fails, the report says "head-fails" and exits 1 even when the old code fails with "defect-x".
4. Each phase requests a 120-second limit, a 2-second process-group kill grace and a 1 MiB output cap; base timeout, head timeout, output overflow and signals have distinct unsuccessful reports and exit 1.
5. No changed test gives "no-changed-tests"; missing commits, unsafe overlay setup and known missing-fixture/import failures give "setup-error" even when their output contains "defect-x"; none exits 0.
6. The proof selects committed regular added, modified or renamed tests and supplemental files under the documented test/fixture convention, ignores deleted files and implementation, and uses separate base and head snapshots.
7. The saved result keeps run/base/head identity, the exact command and expectation, selected paths, both phase exits, final output lines and the observed error excerpt even when it precedes those final lines; allocated snapshots are cleaned up even after a failed comparison.
8. The quoted command "node --test test/new.test.mjs" and expectation "defect x" reach the proof unchanged; missing, duplicate or blank options and extra operands exit 2 before proof execution.

## Rules to check

Success requires valid setup and cleanup, an ordinary nonzero old exit with the exact literal, and a zero new exit. A timeout, signal, output cap, known setup failure or absent changed test must never become success. Proposed default is fixed at 120 seconds per phase with no override. Files follow the convention in the owning prompt: changed regular test entries plus supplemental test/fixture files; a fixture-only change is not a test. Dirty and untracked bytes must never enter either snapshot. Literal matching alone cannot prove assertion causality for unrecognized diagnostics or detect message-only fixes.

## What must not change

Ordinary workflow/status/replay commands do not execute supplied commands. Prove never approves, opens a PR, commits or cleans the person's worktree. Synthetic Runtime cases establish decisions and exact port requests; real Git snapshots, byte/mode handling, unsafe ancestry, process-group killing, cleanup and atomic persistence require native verification.
