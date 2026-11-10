As a contributor, I want my offline validation result and output to reach the caller under shared-machine load, so that a completed test run is not reported as missing its receipt.

## Acceptance criteria

1. A validation that exits with status 7 retains that status, its complete output and its final test counts when the caller resumes reading after the terminal receipt is saved.
2. Small output and output large enough to queue IPC writes follow the same completion rules, without repeating the validation command.

## Native verification

The [suite queue](../prompts/cli/test-suite-queue.prompt.md) owns recorder custody and completion. The [native cases](../test/runtime-admission/validation-recorder-completion-cases.json) run the real recorder with a caller that pauses IPC reads until the terminal receipt is durable. The existing public queue tests retain caller-loss, unknown ownership and nonzero-status coverage.

There is no Runtime interface for this native process and IPC boundary. Native tests provide the execution evidence.
