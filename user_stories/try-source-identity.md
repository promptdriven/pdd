# Inspect uploaded Try source digest and engine build locally

As a developer using `pdd test --files`, `pdd simulate` or `pdd mcp`, I want to see the uploaded source archive SHA-256 and engine build in the terminal and Try tools, so that I can match my local files to a Try session.

## Acceptance criteria

1. `pdd test --files` prints `Source SHA-256: <64-hex>` immediately after the file-count summary line without network access, and `pdd test --files --json` includes top-level `source_sha256` matching the uploaded archive digest.
2. Starting or reusing a Try with `pdd simulate` prints `Try source: sha256:<64-hex>; engine: <engine_sha>` immediately after the Try budget line (or `Try source: sha256:<64-hex>` when `engine_sha` is unknown or absent), to stdout in browser mode and to stderr in `--cli` or `--serve` mode.
3. Calling `try_open` or `try_state` in `pdd mcp` returns `source_sha256` and `engine_sha` for the active Try session alongside its entries, saved data and budget.

## What must not change

- Existing `--files` file lines, byte totals, exit codes, unmatched-file warnings and coverage stderr lines remain unchanged.
- Existing `pdd simulate` session reuse, budget validation, door stdout losslessness and `--stop` behavior remain unchanged (`test/runtime-try.test.mjs` updates its exact `first.out` expectation to include the `Try source:` line).

## Rules to check

- The digest printed by `pdd test --files` must come from the exact `captureSource` archive bytes that `pdd test`, `pdd lint` and `pdd simulate` upload.
- In `--cli` and `--serve` door modes, `Try source:` goes to `stderr` alongside `Try budget` so `stdout` stays reserved for the simulated program.

## Cases and Runtime boundary

[Synthetic native draft cases](../test/runtime/try-source-identity-cases.json) hold the issue-derived expectations and preservation controls. The owners are [Runtime client](../prompts/cli/runtime-client.prompt.md) and [Try MCP](../prompts/cli/try-mcp.prompt.md), whose real public boundaries have no Runtime interfaces because Git repository discovery, tar archive hashing, private state persistence and stdio JSON-RPC framing are native and unbound.
