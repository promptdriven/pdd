# Local argument parser

Own `src/argument-parser.mjs`; export `CommandInputError` (exitCode2) and `parseArgv(argv)`. Use only `PUBLIC_COMMAND_ROUTES` to resolve exact prefixes and declared operand/flag types. Return a fresh immutable local plan `{commandId,local,operands,options}`, with `notice` only for [former names](#former-names). Do not emit service-adapter arguments or dispositions, private validators or an execution-service enum.

Empty argv, root --help/-h/-help/help, and known exact command/group help succeed; `-help` is accepted wherever `--help` is. Unknown command plus --help/-h still refuses2. A first word that is no known command and no option refuses with exactly `Unknown command "WORD". Run pdd --help to see the commands.`, with control characters in WORD shown as spaces. `--version` accepts no unrelated arguments. `completion` requires exactly bash or zsh. `workflow list` accepts one optional --json and no operands. `setup` takes no operands and no options. No route forwards native flags. Unknown/duplicate options, NUL/nonstrings, missing/extra operands and excluded commands refuse clearly without printing raw invalid input. Never mutate the caller's array. A help flag cannot hide invalid trailing arguments.

## Authoring

Read the full [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. The [public alpha boundary](public-boundary.prompt.md) remains required native authoring/generation context for scope. These authoring instructions are not inputs to runtime parsing; the pure parser uses the catalog and the validation rules owned here.

## Former names

The catalog's `formerly` words ([Names](command-catalog.prompt.md#names)) still parse like the new words of their route: same operands, options, validation and plan. `check` and `try` are known first words, so they never get `Unknown command`. The former `check` parses with the `check` route (`test`) and keeps every option that it had, `--lint` and `--local` included.

A plan from former words also has `notice`: one plain line, `pdd FORMER is now pdd NEW.`, with no backticks or quotes. The four lines are `pdd check is now pdd test.`, `pdd check --lint is now pdd lint.` (the former `check` with the flag `--lint` anywhere in its options), `pdd try is now pdd simulate.` and `pdd workflow run is now pdd workflow start.`
- Help of a former name (`pdd check --help`, `pdd check -h`, `pdd help try`, `pdd workflow run --help`) is the help of the new name, with the same notice. `check --lint` with a help flag gets the help of `lint`.
- New words never get a notice. `pdd test --lint` works like `pdd lint`. `sim` is the short form of `simulate`: it parses like `simulate`, with the same plan, and gets no notice.
- A refused input is a `CommandInputError` with no notice, so a usage error prints only its own message (exit 2).

## Missing workflow name

When the first operand after `workflow start`, or after the former `workflow run`, is a positive decimal issue number
(the existing digits-only issue form), reject it with `CommandInputError` and
message `Name the workflow: pdd workflow WORD small-change NUMBER (or bug, feature). See pdd workflow list.`,
replacing WORD with the word that the person typed (`run` or `start`) and NUMBER with that operand. This identifies the missing name rather than
using the generic unsupported-input diagnostic. Never infer or start a workflow.
Preserve all other command parsing, help, option validation and issue forms;
this rule changes only the diagnostic for a number in the workflow-name position.

## Argument validation

Runner routes accept exactly their catalogued operands and options. An option of kind `text` takes any one nonblank value (`--summary`). A route whose last operand is repeated text (workflow.changes) supports `--` to end options, and a help word after `--` is text. Issue operands are a positive number, `owner/repo#number` or a GitHub issue URL. Workflow and step names are lowercase words joined by single hyphens, at most 64 characters. Whether a workflow, run or step exists belongs to the runner. Reject unsafe names, unsupported issues, unknown options and extra operands with exit 2 before any effect. Help for every route is local.

Option kind `integer` takes decimal digits with no sign, within the option's `min` and `max`. Option kind `uuid` takes one UUID (8-4-4-4-12 hex digits). Which `check` and `try` options go together belongs to the [runtime client](runtime-client.prompt.md).

Option kind `optional-integer` consumes the following word only when it is decimal digits; validate against
min/max and store it as a string. With no number, store the catalog's default as a string. A subsequent option
or Story operand remains available for ordinary parsing. This supports --serve [PORT].

Accept the catalog's `pdd mcp` route without operands or options; normal local help forms apply. Parsing never starts the server or registers it.

## Dependencies

- [Command catalog](command-catalog.prompt.md): required authoring/generation/runtime/verification/testing context for `PUBLIC_COMMAND_ROUTES`, exact prefixes, operand/option declarations and local dispositions. Parsing uses these route facts, with no outside calls.
- Native authoring/generation also uses the repository context identified in Authoring above. The runtime-client link in Argument validation identifies ownership of downstream combination checks; parsing never calls it and needs no runtime client/session/token context.
