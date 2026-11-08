# Limit PRs waiting for review

As a repository owner, I want Autopilot to hold new issue work in an owner area
when its review queue is full, so that agents do not overload reviewers.

## Acceptance criteria

1. With a limit of 2 and two Autopilot PRs waiting for review in the CLI area, new CLI work waits. Work in the docs area can start.
2. Status shows the full area and the number of PRs waiting for review. Status reads saved observations.
3. Closing, merging or approving a PR frees its review slot on the next reconciliation, even when the new issue has not changed.
4. PRs waiting only for CI and manual PRs do not use review slots. A pending requested review uses a slot.
5. The default limit is 5. A configured positive integer replaces it. Invalid settings use 5 and remain unchanged on disk.
6. Claimed work keeps moving at the limit. Unknown review observations hold fresh work until a complete read succeeds.

## Rules to check

For a positive limit N, no new work enters an area with at least N waiting PRs.
Each PR counts once in each area. A merged, closed or CI-only PR counts zero.

## Native verification

Run `node --test test/autopilot-pr-limit.test.mjs` from a checkout with Node.js
22.16.0 or newer. The tests use a temporary Git repository, fake GitHub and fake
Herdr. They exercise launcher start, tick, status and automatic-start admission.
They make no live service or model call. Temporary state is deleted after each
case. This Story has native tests only; no interpreter result is claimed.
