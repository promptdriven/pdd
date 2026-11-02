# Local shell completion

Own `src/completion.mjs`; export `renderCompletion(shell)`. Derive suggestions only from the local command catalog, including supported option names and shell operands. Return newline-terminated bash or zsh script, otherwise TypeError. Shell scripts must be usable when loaded by that shell. Do not suggest excluded commands or invoke any application/backend during completion.

## Dependencies

- [Command catalog](command-catalog.prompt.md): required authoring/generation/verification/testing context for canonical command/option suggestions.

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

The words test, lint, simulate and run are the [NAMES](command-catalog.prompt.md#names) words. Offer only these words, never a removed or quiet word (`check`, `try`, `sim`, `workflow start`).

Offer the catalog's workflow routes and supported options, including --said for approval. For NAME after workflow run, obtain validated actual project+bundled names from local `pdd workflow list --json`; this local read is the sole exception to the no-application-call completion rule. Parse only its JSON workflows name fields via installed Node, keep safe names, never shell-evaluate output or invoke workflow execution/native/network. Invalid/unavailable listing yields no names. Keep catalog-owned option choices and complete them at any argument position, including after NAME and ISSUE.

Offer `test`, `lint` and `simulate` with their options and the `--tab` choices. Never offer an option marked `hidden` (`--request`, and `--lint` and `--local` on `test`).

Choice completion is scoped to the command prefix as well as the option: workflow --agent offers only codex/claude, while simulate --agent offers codex/claude/gemini, at any argument position. A same-named option on another command cannot widen choices.
