# Alpha local argument parser

Own `src/argument-parser.mjs`; export `CommandInputError` (exitCode2) and `parseArgv(argv)`. Use only `PUBLIC_COMMAND_ROUTES` to resolve exact prefixes and declared operand/flag types. Return a fresh immutable local plan `{commandId,local,operands,options}`. Do not emit service-adapter arguments or dispositions, private validators or an execution-service enum.

Empty argv, root --help/-h/-help/help, and known exact command/group help succeed; `-help` is accepted wherever `--help` is. Unknown command plus --help/-h still refuses2. A first word that is no known command and no option refuses with exactly `Unknown command "WORD". Run pdd --help to see the commands.`, with control characters in WORD shown as spaces. `--version` and `--skill` accept no unrelated arguments. `completion` requires exactly bash or zsh. `workflow list` accepts one optional --json and no operands. `session` defaults to codex, permits one optional --agent codex|claude plus optional request words (joined as one request), and supports -- to end its options. It does not forward native flags. Unknown/duplicate options, NUL/nonstrings, missing/extra operands and excluded commands refuse clearly without printing raw invalid input. Never mutate the caller's array. A help flag cannot hide invalid trailing arguments.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

Named workflow routes have the same session options/request text/literal -- behavior, and preserve the catalogued workflow name in the immutable plan. Unknown names with or without help refuse2 before any reads or child. Known recipe help is local0.

workflow.run requires exactly a safe free workflow name and syntactic issue reference plus optional --agent. workflow.resume accepts an optional saved-run reference plus optional --decision approve|skip, with omitted decision absent. Live issue/repo/journal/agent/decision eligibility belongs to runner. Reject unsafe names/unsupported issues/UUIDs/options/extras with2 before guidance/runner/native. Known run/resume help is local.

workflow.run accepts exactly safe free NAME (lowercase letter followed by lowercase letters/digits and single hyphen-separated nonempty segments, max64) plus existing ISSUE and agent; do not reject a syntactically valid custom name based on bundled catalog. Definition existence/graph/content belongs solely to loader/main. workflow.attach takes exactly one saved-run reference, no options or other operands; route/help admission has no backend effect.

Short workflow commands use a saved run reference: a positive issue number (including `#N`), `repo#N`, `owner/repo#N`, the canonical GitHub issue URL, a unique eight-or-more-character run-ID prefix, or a full UUIDv4. Catalog `workflow approve [REF] [--yes]`, `workflow changes REF [text]`, `workflow skip REF`, `workflow status [--all]`, and `workflow watch [REF]`. Resume and attach accept the same reference, with an omitted resume reference resolved only when the current repository has one unambiguous run.

workflow.decide requires its decision, id, expected-stage and expected-seq options.
Validate the saved-run reference, UUIDv4 decision id, safe stage, canonical positive decimal safe integer and changes
text (1–4000 Unicode characters, controls except tab/newline refused); reject
text on other decisions. yes/json are Boolean flags. Value options without a
choices list accept exactly one non-option string, then their route validation
applies. Missing, duplicate, unknown and malformed arguments refuse2 before I/O.

Decide phone transport accepts exactly --via phone --phone PHONE_ID --approval
TOKEN together; missing companions refuse before any runner call. Validation of
signature, phone identity and ledger eligibility belongs to the verifier.

Short decision phone flags must be supplied together; partial phone mode fails before lookup. All saved-run selectors admit issue forms and IDs.
