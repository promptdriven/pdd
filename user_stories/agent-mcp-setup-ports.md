# Register Try tools with local agents ports

I can preview and register the `pdd mcp` server with detected local agents after explicit consent, preserve declined setups without writing, and reject symlinked or invalid paths.

```pdd-boundary
prompts/cli/agent-mcp-setup.prompt.md
```

The registration command comes from the Node process that runs setup; callers do not supply an executable path.

## Acceptance criteria

1. When I accept setup, each registration uses the running Node executable and the selected package's `bin/pdd.mjs` entry with `mcp` arguments, writes the previewed config, and reports success.
2. When `prompt.confirm` returns any answer other than `y`, `setupAgentMcp` writes no files and returns `{exitCode: 0}`.
3. When a candidate configuration file is a symbolic link or malformed, `setupAgentMcp` emits a `pdd setup:` diagnostic to `output.stderr`, asks no confirmation question, writes nothing, and returns `{exitCode: 1}`.
