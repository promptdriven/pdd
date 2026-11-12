# Replay approved native cases

As a maintainer, I can approve and replay native cases for a prose prompt without an established faithful Runtime operation, so that the code is checked against the same cases without claiming a Runtime verdict.

## Acceptance criteria

1. Native cases appear with the Story for approval and are pinned at prompt publication with their original values and identities.
2. A frozen empty anchor cannot pass in code space; returning to prompt space, approving and publishing cases creates a new anchor before code resumes.
3. A replay passes only with every approved case executed on its native public boundary, current source identity and a semantic assertion-failure control.
4. Native cases do not claim a Runtime pass or authorize an automatic full-check pass. An explicit approval is required for publication when no Runtime verdict exists.

## What must not change

Runtime scenario replay, strict approvals, and the distinction between formal checks and replay remain intact.

## Rules to check

An empty anchor, missing operation, stale source or ineffective mutation control cannot establish a replay pass.
