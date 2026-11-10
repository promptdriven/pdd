# Register Try tools with local agents ports

I can preview and register the `pdd mcp` server with detected local agents after explicit consent, preserve declined setups without writing, and reject symlinked or invalid paths.

```pdd-boundary
prompts/cli/agent-mcp-setup.prompt.md
```

## Acceptance criteria

1. When `prompt.confirm` returns `y`, `setupAgentMcp` previews the config patches, rechecks target files, writes the pinned `execPath` and `packageRoot/bin/pdd.mjs` `"mcp"` registration for detected agents, and returns `{exitCode: 0}`.
2. When `prompt.confirm` returns any answer other than `y`, `setupAgentMcp` writes no files and returns `{exitCode: 0}`.
3. When a candidate configuration file is a symbolic link or malformed, `setupAgentMcp` emits a `pdd setup:` diagnostic to `output.stderr`, asks no confirmation question, writes nothing, and returns `{exitCode: 1}`.
4. `setupAgentMcp` raises `invalid-setup-context` before probing agents when `packageRoot` or `execPath` is not an absolute path.
