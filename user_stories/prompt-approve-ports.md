# Prompt approve command ports

I can update a prompt's Runtime interface status and prose SHA-256 hash, approve a Git-visible prompt via `--said` in easy mode while recording durable evidence, refuse `--said` in strict mode, and reject missing `prose_sha256` keys or invalid working directories.

```pdd-boundary
prompts/cli/prompt-approve.prompt.md
```

## Acceptance criteria

1. `approvePromptText` sets the top-level `"status"` to `"approved"` and `"prose_sha256"` to the `compute.hash_utf8` digest of the trimmed prose while leaving nested `"status"` fields untouched, and raises `missing-prose-sha256` when `"prose_sha256"` is absent.
2. `runApprove` in easy mode with valid `said` words verifies that the target is a Git-visible `*.prompt.md` file, writes the approved prompt text, records durable approval evidence via `policy.appendApproval`, prints `Approved prompts/cli/sample.prompt.md.`, and returns `{exitCode: 0}`.
3. `runApprove` in strict mode (`strictApprovals: true`) refuses `--said` with `{exitCode: 2}` and `pdd approve is for a person at a terminal.` on `output.stderr` without writing the prompt or recording an approval.
4. `runApprove` raises `invalid-approve-cwd` before invoking Git when `cwd` is blank.
