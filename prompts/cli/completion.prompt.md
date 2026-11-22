# Local shell completion

Own `src/completion.mjs`; export `renderCompletion(shell)`. Derive suggestions only from the local [Command catalog](command-catalog.prompt.md), including supported option names, option choices, and shell operands. Return a newline-terminated `bash` or `zsh` script, otherwise `TypeError`. Shell scripts must be usable when loaded by that shell. Do not suggest excluded, hidden, quiet, or removed commands (`check`, `try`, `sim`, `workflow`), and do not invoke any application or backend during completion.

## Domain decisions

- Derive `test`, `lint`, and `simulate` command words from `NAMES` in the catalog.
- Never offer hidden options (such as `--request`, `--lint`, `--local`, `--pool`, or hidden `--write` on `update`).
- Scope option choice completions to the command prefix plus option (for example `product start --agent` offers `codex`, `claude`, `gemini`, `agy`; `simulate --tab` offers `call`, `screen`, `terminal`, `world`; `simulate --agent` does not restrict custom launcher names to a fixed provider list).

## Dependencies

- Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before authoring prompts or Stories.
- Follow the [public boundary](public-boundary.prompt.md) for scope and the shared local command contract.
- [Command catalog](command-catalog.prompt.md): required authoring/generation/verification/testing context for canonical command/option suggestions.
