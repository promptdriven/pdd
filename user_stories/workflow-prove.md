# Compare committed tests with old code

I can explicitly compare my committed regression test on the fetched-base merge-base old code and committed new code, and see whether it detects the intended defect.

Person-reviewed source contract and expected cases approved by the root acting as the person under the flow lead's instructions. The prove and PR-evidence Runtime interfaces were approved through the actual CLI; the native-only runner integration received separate source review. Runtime check: not run; this Story's 24 steps and 128 checks remain unjudged (247 revised checks total). Native verification remains pending; the original 157-check baseline is historical evidence only.

## Acceptance criteria

1. With a committed changed test, a nonzero old-code exit containing the literal "defect-x" and a zero new-code exit produce a successful old-code proof and exit 0.
2. If the old code passes, or fails with "other-error" instead of "defect-x", the report distinguishes "old-passes" from "wrong-reason", includes the observed wrong-reason excerpt and exits 1.
3. If the new code fails, the report says "head-fails", includes the observed cause and short actual output tail before a trailing TAP summary when available and exits 1 even when the old code fails with "defect-x".
4. Each phase requests a 120-second limit, a 2-second process-group kill grace and a 1 MiB output cap; base timeout, head timeout, output overflow and child signals have distinct unsuccessful reports and exit 1.
5. No changed test gives "no-changed-tests"; missing commits, unsafe overlay setup, exit 126/127 and known missing-fixture/import failures give "setup-error" with a cause and short actual output tail when available even when output contains "defect-x"; setup-looking output from a passing phase does not disqualify proof.
6. The proof compares committed regular added, modified or renamed tests and supplemental files against the merge-base of HEAD with the fetched selected base branch, excluding base-branch changes already merged into HEAD, and ignores deleted files and implementation.
7. The v2 saved result keeps parent interruption separately from child signals, the computed old base and captured head, exact command and expectation, copied paths, phase exits, final output and observed excerpt; the immutable saved run base stays unchanged, cleanup always runs, and each report names the command and actual base/head exits with safe code spans preserving literal command quotes and backslashes with visible control escapes rather than claiming copied files were executed tests.
8. The quoted command "node --test test/new.test.mjs" and expectation "defect x" reach the proof unchanged; missing, duplicate or blank options and extra operands exit 2 before proof execution.

## Rules to check

Success requires valid setup and cleanup, an ordinary nonzero old exit with the exact literal, and a zero new exit. A timeout, signal, output cap, known setup failure or absent changed test must never become success. Proposed default is fixed at 120 seconds per phase with no override. Files follow the convention in the owning prompt: changed regular test entries plus supplemental test/fixture files; a fixture-only change is not a test. Dirty and untracked bytes must never enter either snapshot. Literal matching alone cannot prove assertion causality for unrecognized diagnostics or detect message-only fixes.

## What must not change

Ordinary workflow/status/replay commands do not execute supplied commands. Prove never approves, opens a PR, commits or cleans the person's worktree. Synthetic Runtime cases establish decisions and exact port requests; real Git snapshots, byte/mode handling, unsafe ancestry, process-group killing, cleanup and atomic persistence require native verification.

Native parent interrupts SIGINT/SIGTERM/SIGHUP are recorded in required interruptSignal, stop phase scheduling, kill an active child group, clean both owned snapshots and exit 130/143/129 even if cleanup/save fails. Before-process/interphase interruption never invents a phase signal. Setup/cleanup errors keep saved-outcome priority; otherwise parent interruption is signalled before no-changed-tests. A child signal alone exits 1. Stale cleanup needs positive ownership and inactive-owner proof, never repo-wide prune. Runtime fakes do not prove signals, stale ownership or real merge-base behavior.
