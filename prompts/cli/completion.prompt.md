# Local shell completion

Own `src/completion.mjs`; export `renderCompletion(shell)`. Derive suggestions only from the local command catalog, including supported option names and shell operands. Return newline-terminated bash or zsh script, otherwise TypeError. Shell scripts must be usable when loaded by that shell. Do not suggest excluded commands or invoke any application/backend during completion.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

Offer workflow run/resume, three named workflow operands for run, --agent choices codex/claude and --decision approve/skip. Complete choices immediately after each option at any argument position, including after NAME and ISSUE. No status command.

Offer workflow attach as well as run/resume. For NAME after workflow run, obtain validated actual project+bundled names from local `pdd workflow list --json`; this local read is the sole exception to the former no-application-call completion rule. Parse only its JSON workflows name fields via installed Node, keep safe names, never shell-evaluate output or invoke run/attach/native/network. Invalid/unavailable listing yields no names. Keep the --agent choices.

Offer `check` and `try` with their options and the `--tab` choices. Never offer an option marked `hidden` (`--request`).

Choice completion is scoped to the command prefix as well as the option: workflow --agent offers only codex/claude, while try --agent offers codex/claude/gemini, at any argument position. A same-named option on another command cannot widen choices.
