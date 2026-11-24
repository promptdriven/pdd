# Local argument parser

Own `src/argument-parser.mjs`; export `CommandInputError` (exitCode 2) and `parseArgv(argv)`. Use only `PUBLIC_COMMAND_ROUTES` and `REMOVED_COMMANDS` from the [Command catalog](command-catalog.prompt.md) to resolve exact prefixes and declared operand/flag types. Return a fresh immutable local plan `{commandId, local, operands, options}`. Do not emit service-adapter arguments or dispositions, private validators, or an execution-service enum.

Empty argv, root `--help`/`-h`/`-help`/`help`, a [help topic](#help-topics), and known exact command/group help succeed; `-help` is accepted wherever `--help` is. Unknown command plus `--help`/`-h` still refuses with exit 2. A first word that is no known command, no removed command, and no option refuses with exactly `Unknown command "WORD". Run pdd --help to see the commands.`, with control characters in `WORD` shown as spaces. The catalog's version routes accept no unrelated arguments. `completion` requires exactly `bash` or `zsh`. Only a catalog route explicitly marked `passthrough: true` (`accounts.codex`) collects trailing arguments verbatim into `operands` (consuming at most one leading `--` separator right after the route prefix, while returning local help when a single help flag immediately follows the prefix); no other route forwards native flags. Unknown/duplicate options, NUL/nonstrings, missing/extra operands, and excluded commands refuse clearly without printing raw invalid input. Never mutate the caller's array. A help flag cannot hide invalid trailing arguments.

## Authoring

Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before authoring prompts or Stories. Follow the [public boundary](public-boundary.prompt.md) for scope and shared local command policy.

## Removed names

Check for removed commands first, before any other rule, also right after `help`:

1. Route-owned removed words ([Names](command-catalog.prompt.md#names)): `check` and `try` are known first words, so they never get `Unknown command` and never run. Every input whose command word is `check` or `try` (`pdd check …`, `pdd try …`, `pdd help check`, `pdd help try`) throws `CommandInputError` (exit 2) with one line:

| Input | Line |
|---|---|
| `check`, and `--lint` is one of the words after it | `pdd check --lint was removed. Use pdd lint.` |
| `check`, any other words | `pdd check was removed. Use pdd test.` |
| `try`, any words | `pdd try was removed. Use pdd simulate.` |

2. Standalone retired commands (`REMOVED_COMMANDS` in the catalog): `pdd workflow` (with any subcommand, flags, or after `help`) throws `CommandInputError` (exit 2) with an actionable pointer to `/pdd` (or `$pdd`), `pdd prove`, and `pdd autopilot` instead of bare `Unknown command "workflow"`; `pdd approve` (with any operands, flags, or after `help`) throws `CommandInputError` (exit 2) pointing to chat or GitHub PR review instead of bare `Unknown command "approve"`.

## Help topics

A help topic is a word after `help` that the catalog's `help` route lists as a topic (`prompting`). `pdd help prompting`, exactly these two words, returns the help plan with an empty `helpPrefix` and `topic: 'prompting'`. Any other word after the topic, also a help flag, is unsupported input (exit 2). A topic is no command: `pdd prompting` gets `Unknown command`, and `pdd prompting --help` refuses with exit 2.

## Quiet names

A quiet word (`sim`, `-V`) parses like the prefix of its route: same operands, options, validation, help, and plan, with nothing added. `pdd test --lint` resolves to the `lint` route's local disposition. No plan has a `notice`.

## Argument validation

Routes accept exactly their catalogued operands and options:
- `text`: any one nonblank value, preserving exact bytes including leading/trailing spaces and option-like strings such as `--help`.
- `text-list`: one or more nonblank words up to the next `-` token or end of argv.
- `integer`: decimal digits with no sign and no leading zero (`0` only when `min` is `0`), within `min..max`.
- `optional-integer`: consumes the next token when decimal digits within `min..max`, else stores the catalog default string.
- `optional-text`: consumes the next token when present and not starting with `-` (nonblank), else stores Boolean `true`.
- `uuid`: standard 8-4-4-4-12 hex UUID.
- `value`: exact match against `option.choices`.
- `issue` operand: positive number, `owner/repo#number`, or GitHub issue URL.
- Routes whose last operand is repeated `text` accept `--` to end options.

## Dependencies

- [Command catalog](command-catalog.prompt.md): required authoring/generation/runtime/verification/testing context for `PUBLIC_COMMAND_ROUTES`, `REMOVED_COMMANDS`, exact prefixes, operand/option declarations, and local dispositions.
- [Runtime seam](runtime-seam.prompt.md): owns downstream combination checks for `test`, `lint`, and `simulate`; parsing never imports it.
