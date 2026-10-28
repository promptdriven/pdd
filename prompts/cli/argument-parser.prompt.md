# Alpha local argument parser

Own `src/argument-parser.mjs`; export `CommandInputError` (exitCode2) and `parseArgv(argv)`. Use only `PUBLIC_COMMAND_ROUTES` to resolve exact prefixes and declared operand/flag types. Return a fresh immutable local plan `{commandId,local,operands,options}`. Do not emit service-adapter arguments or dispositions, private validators or an execution-service enum.

Empty argv, root --help/-h/-help/help, and known exact command/group help succeed; `-help` is accepted wherever `--help` is. Unknown command plus --help/-h still refuses2. A first word that is no known command and no option refuses with exactly `Unknown command "WORD". Run pdd --help to see the commands.`, with control characters in WORD shown as spaces. `--version` accepts no unrelated arguments. `completion` requires exactly bash or zsh. `workflow list` accepts one optional --json and no operands. `setup` takes no operands and no options. No route forwards native flags. Unknown/duplicate options, NUL/nonstrings, missing/extra operands and excluded commands refuse clearly without printing raw invalid input. Never mutate the caller's array. A help flag cannot hide invalid trailing arguments.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

Runner routes accept exactly their catalogued operands and options. An option of kind `text` takes any one nonblank value (`--summary`). A route whose last operand is repeated text (workflow.changes) supports `--` to end options, and a help word after `--` is text. Issue operands are a positive number, `owner/repo#number` or a GitHub issue URL. Workflow and step names are lowercase words joined by single hyphens, at most 64 characters. Whether a workflow, run or step exists belongs to the runner. Reject unsafe names, unsupported issues, unknown options and extra operands with exit 2 before any effect. Help for every route is local.

Option kind `integer` takes decimal digits with no sign, within the option's `min` and `max`. Option kind `uuid` takes one UUID (8-4-4-4-12 hex digits). Which `check` and `try` options go together belongs to the [runtime client](runtime-client.prompt.md).

Option kind `optional-integer` consumes the following word only when it is decimal digits; validate against
min/max and store it as a string. With no number, store the catalog's default as a string. A subsequent option
or Story operand remains available for ordinary parsing. This supports --serve [PORT].
