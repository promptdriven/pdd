<!-- pdd-story-contract derived-from-story="../story__pdd_update.md" story-hash="<auto>" issue-ref="https://github.com/promptdriven/pdd/issues/1703" -->

# Contract: pdd update

## Covers

- R1: `pdd update` is exposed as a first-class CLI command.
- R2: The command documents prompt/code reconciliation inputs.
- R3: The command can be inspected without API keys or cloud credentials.

## Context

This story seeds executable regression coverage for the high-traffic `update` flow.

## Acceptance Criteria

1. Given a public checkout with no API keys, when a user asks for `pdd update --help`, then the command help renders successfully.
2. Given the help output, then it names the update workflow and positional input expectations.

## Oracle

These details matter for pass/fail:
- `pdd update --help` exits successfully.
- The help output includes the command name.
- The top-level CLI lists `update` as an available command.

## Non-Oracle

These details should not matter:
- exact terminal styling
- exact option ordering
- exact model/provider configuration text

## Negative Cases

- Inspecting the update workflow must not require live LLM credentials.
- The top-level CLI must not hide the `update` command.

## Non-Goals

This seed story does not verify prompt rewrite quality.
