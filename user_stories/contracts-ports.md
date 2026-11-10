# List and sync shared contracts through Runtime ports

I can list shared contract records and their stale Stories, preview schema migrations, and apply migrations through declared Git, file, history and output ports.

```pdd-boundary
prompts/cli/contracts.prompt.md
```

## Acceptance criteria

1. Running `pdd contracts` lists shared contract records, their prompt users and Stories, and reports Stories whose baseline reference snapshot changed as `stale: needs a new check`.
2. Running `pdd contracts sync` previews matching schema copies without modifying files, and `pdd contracts sync --write` writes the updated prompt and reports the updated count.
3. Invalid command syntax or running outside a Git repository writes a diagnostic to stderr and exits 2, and an empty `cwd` fails with `invalid-contracts-input`.
