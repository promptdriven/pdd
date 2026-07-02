<!-- pdd-story-contract derived-from-story="../story__pdd_update.md" story-hash="<auto>" issue-ref="https://github.com/promptdriven/pdd/issues/1703" -->

# Contract: pdd update

## Covers

- R1: The `update` command remains available from the public CLI surface.
- R2: The command is distinct from `change`, `fix`, and `sync` in help/registration.

## Oracle

- `pdd update --help` documents update behavior as a supported command.
- The update command can be imported and inspected without requiring API keys.

## Negative Cases

- Story-regression execution must not make live LLM or cloud calls.
- The update command must not disappear from the top-level CLI registration.

## Non-Goals

- This contract does not require live update execution during the public-safe story lane.
