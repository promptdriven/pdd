# Serve Try tools and stdio MCP requests through Runtime ports

I can open, inspect, run, check and save Try cases through `createTryTools` and `call`, and serve stdio JSON-RPC requests through `runMcp`, using declared client and stdio ports.

```pdd-boundary
prompts/cli/try-mcp.prompt.md
```

## Acceptance criteria

1. `createTryTools` stores initial session state and `call` inspects, runs, checks and saves confirmed runs and retained pending cases through the client port.
2. `runMcp` processes stdio JSON-RPC `initialize` and `ping` requests and writes newline-delimited responses to stdout.
3. Empty working directories or invalid tool invocations fail with `invalid-try-tools-cwd`, `invalid-tool-call` and `invalid-mcp-cwd`.
