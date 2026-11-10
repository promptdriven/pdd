# Prompt approval ports

The approval command displays the current prompt, accepts a person decision, and records durable evidence through the shared approval-policy owner.

```pdd-boundary
prompts/cli/prompt-approve.prompt.md
prompts/cli/approval-policy.prompt.md
```

## Acceptance criteria

1. approvePromptText sets only the top-level approval fields using the native prose hash, leaves nested status fields untouched, and returns null when the interface cannot be safely updated.
2. runApprove with accepted said words writes the approved prompt and records complete durable evidence through the shared approval-policy owner.
3. runApprove in strict mode refuses said words with exit code 2 before it writes the prompt or records approval evidence.
4. runApprove with blank cwd returns exit code 2 with the Git repository diagnostic before file or policy reads.
