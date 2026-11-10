# Send executable declarations without PDD bookkeeping

As a person using PDD, I want it to send the selected operations and tests to the interpreter, so that its own coverage label does not block those tests.

Draft for review. These cases are proposed, not approved.

## Acceptance criteria

1. A selected operation declared with `kind: partial` can reach interpreter admission without that label in its uploaded Runtime interface; PDD keeps the authored partial declaration unchanged.
2. Explicit `kind: full` uses the same executable transport; a declaration with no kind keeps its existing upload bytes unchanged.
3. Removing the upload label changes no other interface value, number spelling, string escape, prose, resource kind, nested kind, selected operation, test input or expected result.
4. Files preview, lint, Check, Try and recapture use one consistent projected source, with exact uploaded sizes and source hashes; authored hashes retain local kind changes for freshness checks.
5. Invalid declarations keep their refusals, native-only work stays not run with its reason, and unknown fields are not silently removed to force admission.
6. Results report only the checks that ran; partial declarations never become claims that all module behavior or untested criteria passed.

## Rules to check

Omit only a recognized top-level full/partial kind from the upload copy of one valid Runtime interface. Preserve authored bytes and all other source tokens. Forbidden: deleting a resource kind, accepting an invalid declaration through filtering, changing expectations, claiming full behavior coverage, or reusing a saved receipt with a changed source identity.

[Native cases](../test/fixtures/runtime-interface-transport/cases.json) define the proposed observations. Replay capture and the public CLI/client boundaries in isolated Git fixtures. The owning preflight prompt currently has no executable Runtime interface for its Git/file/archive effects; these native cases are not a Runtime scenario or a prompt-test pass. After implementation, repeat hosted lint and one bounded fresh AI control using the projected declaration, retaining the original admission refusal separately.
