<!-- pdd-story-contract derived-from-story="../story__pdd_generate.md" story-hash="<auto>" issue-ref="https://github.com/promptdriven/pdd/issues/1703" -->

# Contract: pdd generate

## Covers

- R1: The `generate` command remains available from the public CLI surface.
- R2: The command routes prompt-file generation independently from story/test/fix/change modes.

## Oracle

- `pdd generate --help` documents prompt-file generation as a supported command.
- The generate command can be imported and inspected without requiring API keys.

## Negative Cases

- Story-regression execution must not make live LLM or cloud calls.
- The generate command must not disappear from the top-level CLI registration.

## Non-Goals

- This contract does not require live code generation during the public-safe story lane.
