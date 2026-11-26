# SOLVE — Issue-Fixing Runbook

You have full, independent access to the repository, git history, GitHub issues/comments, and real local test repos. Choose your own approach.

## 1. Understand the Real Problem
- Read the live issue and every comment yourself: `gh issue view <N> --json url,title,state,body,comments,updatedAt`.
- Treat the issue and comments as the problem statement, not an implementation spec — any fix idea in the thread is a guess, not an order.
- Reproduce the failure first on the current released build against a real repo (not just a toy fixture).

## 2. Fix the Root, Not the Symptom
- Check git history and grep for similar logic across the repo. If this area breaks repeatedly or duplicates logic across files, fix the underlying design rather than adding a patch or growing regex/deny lists.
- Favor **deep modules with narrow interfaces** (one clear owner per concept; no shallow wrappers, leaking internals, or cycles).
- When the existing code is messy or duplicated, split into **2 small sequential PRs** (never stacked):
  1. **PR 1 (Consolidate/Clean):** unify or simplify with **zero behavior change** -> merge.
  2. **PR 2 (Fix):** make the small, clean behavior change on top.

## 3. When to Stop for a 10-Line Fork Card
Stop and write a **10-line Fork Card** (Options A vs B vs C, each measured on real repos, with one recommendation) **only** if the best fix requires any of:
1. Removing user-visible behavior or deleting tests for it.
2. Changing a public contract, schema, CLI flag, or exit code.
3. Coordinating a change in another repository.
4. Editing protected checks, branch rules, or CI workflows.
5. Failing the same check 3 times (explain why instead of thrashing).
6. A bug that does not reproduce on the current release.

## 4. Definition of Done
- Build and install the real artifact (package or binary) in an isolated environment and run differential verification (`pdd prove` or the project evidence harness):
  - The reported repro **fails on Old** and **passes on New** on a real repo.
  - Real-repo checks show **zero unexpected diffs**, neighbor controls behave properly, and seeded fault controls stay **red**.
- Hand off for a fresh independent break-test (`BREAK-IT.md`).
- Report exact commands, observed outputs, and explicitly mark anything not run as `Not proved`.
