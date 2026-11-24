# Local argument parser

Own `src/argument-parser.mjs`; export `CommandInputError` (exitCode 2) and `parseArgv(argv, { resolveTarget } = {})`. Use only `PUBLIC_COMMAND_ROUTES` and `REMOVED_COMMANDS` from the [Command catalog](command-catalog.prompt.md) to resolve exact prefixes, direct Prompt Interpreter invocations, and declared operand/flag types with zero filesystem I/O inside this module. Return a fresh immutable local plan `{commandId, local, operands, options}` (or help plan). Do not emit service-adapter arguments or dispositions, private validators, or an execution-service enum.

Empty argv, root `--help`/`-h`/`-help`/`help`, a [help topic](#help-topics), known exact command/group help, and direct interpreter help (`pdd . --help`, `pdd help .`, or valid leading direct interpreter options followed by a help flag) succeed; `-help` is accepted wherever `--help` is. Unknown command plus `--help`/`-h` still refuses with exit 2. A first word that is no known command, no removed command, no direct prompt/`.` target, no matched local Story/prompt stem from optional `resolveTarget`, and no option refuses with exactly `Unknown command "WORD". Run pdd --help to see the commands.`, with control characters in `WORD` shown as spaces. The catalog's version routes accept no unrelated arguments. `completion` requires exactly `bash` or `zsh`. Only a catalog route explicitly marked `passthrough: true` (`accounts.codex`) or direct prompt file execution collects trailing arguments verbatim into `operands`; no other route forwards native flags. Unknown/duplicate options, NUL/nonstrings, missing/extra operands, and excluded commands refuse clearly without printing raw invalid input. Never mutate the caller's array. A help flag cannot hide invalid trailing arguments.

## Authoring

Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before authoring prompts or Stories. Follow the [public boundary](public-boundary.prompt.md) for scope and shared local command policy.

## Removed names

Check for removed commands first, before any other rule, also right after `help`:

1. Route-owned removed words ([Names](command-catalog.prompt.md#names)): `check` is a known first word, so it never gets `Unknown command` and never runs. Every input whose command word is `check` (`pdd check …`, `pdd help check`) throws `CommandInputError` (exit 2) with one line:

| Input | Line |
|---|---|
| `check`, and `--lint` is one of the words after it | `pdd check --lint was removed. Use pdd lint.` |
| `check`, any other words | `pdd check was removed. Use pdd test.` |

2. Standalone retired commands (`REMOVED_COMMANDS` in the catalog): every input whose command word is `simulate`, `sim`, `try`, `workflow`, or `approve` (with any subcommand, operands, flags, invalid options, or after `help`) throws `CommandInputError` (exit 2) with one line and zero side effects:

| Input | Line |
|---|---|
| `simulate`, any words | `pdd simulate was removed. Run pdd <PROMPT.md|STORY> instead.` |
| `sim`, any words | `pdd sim was removed. Run pdd <PROMPT.md|STORY> instead.` |
| `try`, any words | `pdd try was removed. Run pdd <PROMPT.md|STORY> instead.` |
| `workflow`, any words | Actionable pointer to `/pdd` (or `$pdd`), `pdd prove`, and `pdd autopilot`. |
| `approve`, any words | Actionable pointer to review and approve prompt changes directly in chat or GitHub PR review. |

## Help topics

A help topic is a word after `help` that the catalog's `help` route lists as a topic (`prompting`). `pdd help prompting`, exactly these two words, returns the help plan with an empty `helpPrefix` and `topic: 'prompting'`. Any other word after the topic, also a help flag, is unsupported input (exit 2). A topic is no command: `pdd prompting` gets `Unknown command`, and `pdd prompting --help` refuses with exit 2.

## Quiet names

A quiet word (`-V`) parses like the prefix of its route (`--version`): same operands, options, validation, help, and plan, with nothing added. `pdd test --lint` resolves to the `lint` route's local disposition. No plan has a `notice`.

## Direct prompt and Story execution

After removed commands, help, and all explicit subcommands (`prefix.length > 0`), `parseArgv` recognizes direct Prompt Interpreter invocations (route `id: 'try'`, `local: 'runtime-try'`) in this exact order:

1. **Direct prompt file target (`*.prompt.md` with non-blank stem and not starting with `-`), with optional Python-style prefix options:**
   - Leading options before the `.prompt.md` target belong strictly to `pdd` (validated against the `try` route's options; unknown/duplicate/invalid values refuse with exit 2). Flag-like tokens starting with `-` (such as `--foo.prompt.md` or `-x.prompt.md`) and blank stems (`"   .prompt.md"`) are never treated as file targets.
   - After the `.prompt.md` target:
     - If the first trailing token is `--`, consume that one `--` delimiter and pass all remaining tokens verbatim after the file operand.
     - Else if every trailing token parses cleanly as trailing PDD interactive options (`--agent`, `--tab`, `--new`, `--fresh`, `--page`, `--cli`, `--shell`, `--serve`, `--max-calls`, `--no-open`, `--stop`, `--app-map`, `--no-wait`, with zero extra positional tokens, valid values, and no duplicates with prefix options), merge them into `options` with `operands: [file]`.
     - Otherwise pass every trailing token verbatim after `file` in `operands` (including `--help`, `--flag`, empty strings, and positional arguments).
2. **Direct `app-map.json` target (not starting with `-`):** `pdd [OPTIONS] <path/app-map.json> [OPTIONS]` parses strictly against the `try` route (1 operand + valid `try` options; trailing `--help`/`-h`/`-help` returns focused help `helpPrefix: ['.']`; extra positional arguments refuse with exit 2).
3. **Whole-project `.` target:** `pdd . [OPTIONS]` (or `pdd [OPTIONS] . [OPTIONS]`) normalizes to `operands: []` with validated `try` options; trailing `--help`/`-h`/`-help` returns focused direct-execution help (`helpPrefix: ['.']`).
4. **Leading direct interpreter options without a file target:** `pdd --product ...`, `pdd --stop [TARGET]`, `pdd --save-last [STORY]`, `pdd --page [TARGET]`, `pdd --cli [--shell] [TARGET]`, `pdd --serve [PORT] [TARGET]`, `pdd --fresh [TARGET]`, etc. validate prefix options strictly against the `try` route. Unknown leading flags (such as `--no-such-flag` or `--skill`) refuse with exit 2. When `--stop`, `--save-last`, or `--product` is already present in prefix options, parse remaining arguments strictly against `parseDirectTail` (max 1 operand, never rewriting a bare Story/stem name to a `.prompt.md` file or swallowing `--help` as a program arg). Otherwise, when a bare operand follows valid prefix options and `resolveTarget(word)` returns `{ kind: 'prompt', operand }`, parse as a direct prompt file target with those prefix options so `pdd --fresh todo add "Buy milk"` passes program args cleanly. A trailing help flag after valid direct interpreter options (with no `.prompt.md`/resolved-prompt target before it) returns `helpPrefix: ['.']`.
5. **Bare target resolution via pure injected `resolveTarget(word)`:** When `argv[0]` is a bare word not matched above and `typeof resolveTarget === 'function'`, call `resolveTarget(argv[0])`. If it returns `{ kind: 'prompt', operand }`, parse as a direct prompt file target using `operand`; if it returns `{ kind: 'story', operand }`, parse `[operand, ...argv.slice(1)]` strictly against the `try` route (1 operand + valid `try` options, or focused help on trailing help flag). Otherwise refuse with `Unknown command "WORD". Run pdd --help to see the commands.` (or unsupported syntax when a trailing help flag was given).

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
- [Runtime seam](runtime-seam.prompt.md): owns downstream combination checks for `test`, `lint`, and direct Prompt Interpreter execution; parsing never imports it.
