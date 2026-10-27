# Alpha local argument parser

Own `src/argument-parser.mjs`; export `CommandInputError` (exitCode2) and `parseArgv(argv)`. Use only `PUBLIC_COMMAND_ROUTES` to resolve exact prefixes and declared operand/flag types. Return a fresh immutable local plan `{commandId,local,operands,options}`. Do not emit service-adapter arguments or dispositions, private validators or an execution-service enum.

Empty argv, root --help/-h/help, and known exact command/group help succeed. Unknown command plus --help/-h still refuses2. `--version` and `--skill` accept no unrelated arguments. `completion` requires exactly bash or zsh. `workflow list` accepts one optional --json and no operands. `session` defaults to codex, permits one optional --agent codex|claude plus optional request words (joined as one request), and supports -- to end its options. It does not forward native flags. Unknown/duplicate options, NUL/nonstrings, missing/extra operands and excluded commands refuse clearly without printing raw invalid input. Never mutate the caller's array. A help flag cannot hide invalid trailing arguments.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

Named workflow routes have the same session options/request text/literal -- behavior, and preserve the catalogued workflow name in the immutable plan. Unknown names with or without help refuse2 before any reads or child. Known recipe help is local0.

workflow.run requires exactly a safe free workflow name and syntactic issue reference plus optional --agent. workflow.resume requires exactly UUIDv4 run ID plus optional --decision approve|skip, with omitted decision absent. Live issue/repo/journal/agent/decision eligibility belongs to runner. Reject unsafe names/unsupported issues/UUIDs/options/extras with2 before guidance/runner/native. Known run/resume help is local.

workflow.run accepts exactly safe free NAME (lowercase letter followed by lowercase letters/digits and single hyphen-separated nonempty segments, max64) plus existing ISSUE and agent; do not reject a syntactically valid custom name based on bundled catalog. Definition existence/graph/content belongs solely to loader/main. workflow.attach takes exactly UUIDv4, no options or other operands; route/help admission has no backend effect.

## Optional command syntax

The catalog also admits the explicitly declared optional client routes, returning the same immutable plan without service-specific DTOs. A value option without enumerated choices accepts nonempty text that does not start with `--`; missing values and duplicates refuse2. Preserve original argv token boundaries for subsequent adapter dispatch; the parser never invokes a client.

For optional commands, --id must be UUIDv4 and --rev a positive safe integer. agent send/keys/resume/stop require --id; stop also requires --how. accounts quota-decide requires --decision and --rev. accounts add permits --from-pool only for codex and --replace only for non-codex. accounts allow requires --machine. accounts policy supplies --pinned and --then together or neither. These syntax refusals precede adapter access, including with trailing help. The client owns remaining domain validation.
