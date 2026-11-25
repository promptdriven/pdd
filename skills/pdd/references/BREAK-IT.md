# BREAK-IT — Independent Break-Test Runbook

Start in a clean context after coding is done. You have full access to the built tool, the live issue + comments, and the real local test repos.

## Rules
- **Do not just review the diff.** Install and run the **real built tool** (not unit mocks) against real repos and adversarial edge cases.
- Read the live issue and every comment (`gh issue view <N> --json url,title,state,body,comments,updatedAt`) and test **every** requirement, reopen note, and boundary condition — not just the happy path.
- Try actively to break the fix: malformed inputs, missing files, cold starts, dirty state, neighbor features, and regression cases that *must* still fail red.
- **No unverified claims:** drop all style opinions, speculation, and "looks like it might fail" guesses.

## Evidence Standard (Every Surviving Finding)
A finding survives **only** if it includes all four items:
1. **Exact command** run against the real installed build (and repo/commit/fixture used).
2. **Real output & exit code** from the **New** build showing the failure.
3. **Baseline check** running the same command on the **Old** release, labeled `new regression` (Old passed, New failed) or `pre-existing / incomplete fix` (Old also failed).
4. **Requirement link** pointing to the exact line in the issue, comment, or real-repo contract violated.

## Output Format
1. **Requirements Matrix:** every requirement from the issue body + comments mapped to `PASS`, `FAIL`, or `Not proved` (with exact command + short output).
2. **Verified Findings:** numbered list of surviving failures only (or `None — all break attempts held`).
3. **Gaps:** anything you could not execute (e.g., offline service), explicitly marked `Not proved`.
