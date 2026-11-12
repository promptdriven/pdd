# Native verification recipe

As a developer, I can run requirement-derived cases against an existing native
public function and see whether each return or error matches, including values
outside its Runtime interface.

## Acceptance criteria

1. A matching return or matching error name and message passes its case.
2. A wrong return, wrong error, missing expected error or unexpected error fails its case and the command exits nonzero.
3. Missing exports, malformed cases and setup failures exit nonzero without claiming a case passed.

The [native cases](../examples/native-replay/cases.json) are synthetic examples,
not Runtime scenarios or a prompt-check verdict. Their expected values are
chosen before execution. The command's [contract](../examples/native-replay/replay.prompt.md)
does not alter the target function's contract or its Runtime interface.

The fixture is synthetic; it does not reproduce either sandbox issue.

## Native validation

[Replay owner](../examples/native-replay/replay.prompt.md#native-validation-profile-replay)
