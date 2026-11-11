# Explain only the selected entry's declared resource needs

As a PDD user checking a partial module, I want local binding advice to respect
the selected entry's resource list, so that a pure entry does not ask me for a
process fixture used only by another entry.

Draft for review. This follows the transport contract in PR #3210 and addresses
the local resource-advice part of Runtime issue #817.

## Acceptance criteria

1. A selected pure entry with a valid empty `resource_operations` list has no
   local missing-binding advice for a different entry's process port. Selecting
   that other entry still reports its missing binding or exact supplied fixture.
2. Required source closure, context module resource advice, uploaded operations,
   schemas, approval status, prose hashes, inputs and expectations are preserved.
3. Missing, malformed, incomplete or ambiguous entry scopes cannot remove
   resource advice. Calls to a different operation in the same module retain
   conservative advice for that module.
4. The plan remains local advice. Runtime decides admission. A lint, capture or
   native unit test does not establish a fresh AI behavior pass.
5. Workspace policy callbacks use the repository-relative control-file path
   already owned by the adapter. Existing saved-evidence cases remain in the
   native suite, with their original inputs and expected results; unsupported
   filesystem/locking behavior is never presented as a passing Runtime check.

## Native checks

[Entry-scope cases](../test/runtime-interface-admission.test.mjs) check the local
plan. [Capture integration](../test/runtime-interface-kind-transport.test.mjs)
checks exact transport and authored source preservation. No native integration
or model result is inferred from those checks.
