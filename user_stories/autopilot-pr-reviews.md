# Autopilot wakes for a trusted PR review

As a person using Autopilot, I can have a new trusted review on a related pull request bring the agent back to the work.

## Acceptance criteria

1. After an observe-mode issue with an open related pull request has a quiet baseline, a new review requesting changes from the repository owner wakes the idle agent once, even when issue and pull request listing metadata is unchanged.
2. A later tick with no new work does not wake the agent again for the same review.
3. A new review from an untrusted person does not wake the agent or forward that review text.
4. If the agent is busy when a trusted review arrives, the review remains pending until an idle delivery succeeds.
5. The tick checks for work without making an AI call itself.

## Rules to check

A new review is unseen work only if its author is currently trusted. A review from an untrusted person must neither trigger a wake nor have its text forwarded. A successfully delivered review must not cause a second wake when nothing else changes.
