# Alpha local argument parser

Own `src/argument-parser.mjs`; export `CommandInputError` (exitCode2) and `parseArgv(argv)`. Use only `PUBLIC_COMMAND_ROUTES` to resolve exact prefixes and declared operand/flag types. Return a fresh immutable local plan `{commandId,local,operands,options}`. Do not emit service-adapter arguments or dispositions, private validators or an execution-service enum.

Empty argv, root --help/-h/-help/help, and known exact command/group help succeed; `-help` is accepted wherever `--help` is. Unknown command plus --help/-h still refuses2. A first word that is no known command and no option refuses with exactly `Unknown command "WORD". Run pdd --help to see the commands.`, with control characters in WORD shown as spaces. `--version` accepts no unrelated arguments. `completion` requires exactly bash or zsh. `workflow list` accepts one optional --json and no operands. `session` defaults to codex, permits one optional --agent codex|claude plus optional request words (joined as one request), and supports -- to end its options. It does not forward native flags. Unknown/duplicate options, NUL/nonstrings, missing/extra operands and excluded commands refuse clearly without printing raw invalid input. Never mutate the caller's array. A help flag cannot hide invalid trailing arguments.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

Named workflow routes have the same session options/request text/literal -- behavior, and preserve the catalogued workflow name in the immutable plan. Unknown names with or without help refuse2 before any reads or child. Known recipe help is local0.

workflow.run requires exactly a safe free workflow name and syntactic issue reference plus optional --agent. workflow.resume requires exactly UUIDv4 run ID plus optional --decision approve|skip, with omitted decision absent. Live issue/repo/journal/agent/decision eligibility belongs to runner. Reject unsafe names/unsupported issues/UUIDs/options/extras with2 before guidance/runner/native. Known run/resume help is local.

workflow.run accepts exactly safe free NAME (lowercase letter followed by lowercase letters/digits and single hyphen-separated nonempty segments, max64) plus existing ISSUE and agent; do not reject a syntactically valid custom name based on bundled catalog. Definition existence/graph/content belongs solely to loader/main. workflow.attach takes exactly UUIDv4, no options or other operands; route/help admission has no backend effect.
