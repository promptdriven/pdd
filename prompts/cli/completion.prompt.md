# Local shell completion

Own `src/completion.mjs`; export `renderCompletion(shell)`. Derive suggestions only from the local [Command catalog](command-catalog.prompt.md), including supported option names, option choices, and shell operands. Return a newline-terminated `bash` or `zsh` script, otherwise `TypeError`. Shell scripts must be usable when loaded by that shell. Do not suggest excluded, hidden, quiet, or removed commands (`check`, `try`, `sim`, `simulate`, `workflow`), and do not invoke any application or backend during completion.

## Domain decisions

- Derive `test` and `lint` command words from `NAMES` in the catalog; empty-prefix routes (direct Prompt Interpreter execution) contribute their non-hidden option choice values (such as `--tab` -> `call`, `screen`, `terminal`, `world`) without inventing a subcommand word or `help` entry.
- Never offer hidden options (such as `--request`, `--lint`, `--local`, `--pool`, or hidden `--write` on `update`).
- Scope option choice completions to the command prefix plus option (for example `product start --agent` offers `codex`, `claude`, `gemini`, `agy`; direct `--tab` offers `call`, `screen`, `terminal`, `world`; `--agent` on direct execution does not restrict custom launcher names to a fixed provider list).

## Dependencies

- Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before authoring prompts or Stories.
- Follow the [public boundary](public-boundary.prompt.md) for scope and the shared local command contract.
- [Command catalog](command-catalog.prompt.md): required authoring/generation/verification/testing context for canonical command/option suggestions.
