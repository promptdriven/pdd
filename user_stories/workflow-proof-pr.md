# Read the current machine proof

I can see which committed old-code comparison supports the code PR, including an honest unsuccessful, stale or unavailable result.

Person-reviewed source contract and expected cases approved by the root acting as the person under the flow lead's instructions. The prove and PR-evidence Runtime interfaces were approved through the actual CLI; the native-only runner integration received separate source review. Runtime check: not run; this Story's 18 steps and 87 checks remain unjudged (235 revised checks total). Native verification remains pending; the original 157-check baseline is historical evidence only.

## Acceptance criteria

1. A current v2 machine proof for the same run and freshly computed merge-base/current committed head appears as a successful "Old-code proof:" line naming the exact command, old/new exits and expected output text in safe code spans.
2. A current unsuccessful proof remains visible with its actual outcome, observed/host cause and short actual output tail when available; parent interruption is distinct from child signals even before or between phases, setup/cleanup errors retain priority, and proof is not a publication gate.
3. An older committed head or computed base is "stale"; missing proof is "not run"; legacy v1, malformed (including a missing required parent-interruption field) or foreign-run proof is "unavailable". The immutable saved run base is not the current proof comparison base.
4. An agent-written "Old-code proof:" line cannot replace missing machine evidence, and the prompt-space PR carries no machine proof line.

## Rules to check

Only a valid machine record with exact run/computed-base/Git-observed head identity may assert current success. Recompute classification from its phase facts. A changed head invalidates success until explicit prove runs again. Missing, malformed and stale proofs remain publishable. Every top evidence line precedes replay status; pending-before-push safeguards remain intact. Full lifecycle ordering is native verification.

## What must not change

Proof preparation never executes the command found in a record. Existing replay and approval safeguards, marker rejection, redaction and body limits remain. Runtime checks exercise the real proposed publication preparation export; native tests must prove the actual create/update path calls it and preserves publication ordering.
