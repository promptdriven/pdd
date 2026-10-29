# Read the current machine proof

I can see which committed old-code comparison supports the code PR, including an honest unsuccessful, stale or unavailable result.

Draft for person review; these proposed policies and expected values are not approved.

## Acceptance criteria

1. A current machine proof for the same run, saved base and current committed head appears as a successful "Old-code proof:" line on the code PR.
2. A current unsuccessful proof remains visible with its actual outcome and does not become a publication gate.
3. An older committed head is shown as "stale"; missing proof is "not run"; malformed, foreign-run or foreign-base proof is "unavailable". None shows current success.
4. An agent-written "Old-code proof:" line cannot replace missing machine evidence, and the prompt-space PR carries no machine proof line.

## Rules to check

Only a valid machine record with exact run/base/Git-observed head identity may assert current success. Recompute classification from its phase facts. A changed head invalidates success until explicit prove runs again. Missing, malformed and stale proofs remain publishable. Replay BLOCKED/publication-pending warnings must remain above ordinary evidence; full lifecycle ordering is native verification.

## What must not change

Proof preparation never executes the command found in a record. Existing replay and approval safeguards, marker rejection, redaction and body limits remain. Runtime checks exercise the real proposed publication preparation export; native tests must prove the actual create/update path calls it and preserves publication ordering.
