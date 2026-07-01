<!-- pdd-story-contract derived-from-story="../story__pdd_generate.md" story-hash="<auto>" issue-ref="https://github.com/promptdriven/pdd/issues/1703" -->

# Contract: pdd generate

## Covers

- R1: `pdd generate` is exposed as a first-class CLI command.
- R2: The command documents prompt-file input and output-file selection.
- R3: The command can be inspected without API keys or cloud credentials.

## Context

This story seeds executable regression coverage for the high-traffic `generate` flow.

## Acceptance Criteria

1. Given a public checkout with no API keys, when a user asks for `pdd generate --help`, then the command help renders successfully.
2. Given the help output, then it names prompt input and output controls needed to generate runnable code.

## Oracle

These details matter for pass/fail:
- `pdd generate --help` exits successfully.
- The help output includes the command name and `--output` option.
- The top-level CLI lists `generate` as an available command.

## Non-Oracle

These details should not matter:
- exact terminal styling
- exact option ordering
- exact model/provider configuration text

## Negative Cases

- Inspecting the generate workflow must not require live LLM credentials.
- The top-level CLI must not hide the `generate` command.

## Non-Goals

This seed story does not verify generated code content.
