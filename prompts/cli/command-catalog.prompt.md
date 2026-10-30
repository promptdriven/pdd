# Alpha local command catalog

Own `src/command-catalog.mjs`; export only `PUBLIC_COMMAND_ROUTES`, `PUBLIC_COMMAND_IDS`, `PUBLIC_COMMAND_MANIFEST`, and `BUNDLED_WORKFLOW_NAMES` (feature, bug, small-change, product). Catalog the complete small alpha surface: root help, --version, completion bash|zsh, workflow list [--json] and setup (`pdd setup`, local `setup`, no operands or options; its help says that it installs the PDD skills for Codex and Claude if they are missing, adds the short PDD block to CLAUDE.md, else AGENTS.md, and that a second run changes nothing). Each route has stable id, exact prefix, local disposition, operand/option specs and plain help forms. Expose no excluded command, private schema/type, service flag or hosted execution operation. Help, parser and completion share this one authority.

## Authoring

Read the full [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow the [public alpha boundary](public-boundary.prompt.md) for native authoring/generation scope and shared local command policy. These authoring obligations do not add runtime facts: the complete catalog route declarations below own what the pure data module exposes.

## Public routes

There is no `session` route and no `workflow feature|bug|small-change` chat route: people call the PDD skills in their own chat. No arbitrary path or workflow creation route.

Catalog the area-chat runner routes ([runner](workflow-runner.prompt.md)):
- workflow.run `workflow run NAME ISSUE [--agent codex|claude] [--base BRANCH]`: NAME is a safe workflow name, ISSUE is a number, `owner/repo#number` or `https://github.com/owner/repo/issues/number`. Default agent codex. `--base` is a text option naming an existing origin branch; omitted means the actual repository default. Help describes that selection.
- workflow.done `workflow done STEP [--summary TEXT]`: STEP is a safe step name; the summary is free text.
- workflow.ask `workflow ask QUESTION…`: the question words join into one text; `--` ends options.
- workflow.approve `workflow approve [ISSUE]`, workflow.status `workflow status [ISSUE] [--all] [--cancelled] [--json]` (flags).
- workflow.changes `workflow changes ISSUE TEXT…`: the text words join into one request; `--` ends options.
- workflow.cancel `workflow cancel ISSUE`, workflow.open `workflow open ISSUE`.
- workflow.view `workflow view ISSUE` (local `workflow-view`): one required issue operand, no options. Help says it shows a read-only review of gates, approvals, files, PRs and Try links without starting or resuming a chat.
- workflow.list `workflow list [--json]`.
- workflow.prove `workflow prove ISSUE --test COMMAND --expect TEXT` (local `workflow-prove`): one required issue operand and two text options. Help says it runs committed changed tests on the merge-base of committed head with the fetched base branch and committed head, with a 120-second limit per phase, and saves a non-gating report. No timeout override or native option passthrough. Both text options are required by CLI dispatch before effects; parser retains ordinary text/duplicate/blank validation. [Old-code proof](workflow-prove.prompt.md) owns execution, outcome and saved-result policy (required generation/runtime/verification context).
No resume, attach, run IDs, decisions flag or native argument passthrough. The areas module decides which workflow names exist.

## Workflow runner help

Describe the runner routes in plain words without preview labels. workflow.run says that pdd starts a chat and exits, and that pdd later pushes the branch and opens a real PR. Keep route IDs, prefixes, local dispositions, operands/options/forms and parser/completion behavior consistent with their contracts.

## Runtime routes

Catalog `approve` (local `prompt-approve`, [prompt approve](prompt-approve.prompt.md)) with the form `pdd approve PROMPT`: one required text operand, no options. Its help says that it shows the interface and the text changes since the last approval, and that it is for a person at a terminal.

Catalog `check` (local `runtime-check`) with the forms `pdd check [STORY...] [--json] [--details] [--timeout MIN] [--max-calls N]` (help: it waits for every check, with no limit in a terminal and at most 90 s for an agent, and prints a progress line every 30 s; `--timeout MIN` sets the limit), `pdd check --read [BATCH|CALL_ID] [--json] [--timeout MIN]`, `pdd check --fill-hash`, `pdd check --files [STORY...] [--app-map PATH]` and `pdd check --lint [STORY...] [--json] [--timeout MIN]` (help: it runs only the runtime lint and sends no checks), and `try` (local `runtime-try`) with the forms `pdd try [STORY] [--max-calls N] [--tab call|screen|terminal|world] [--app-map PATH] [--new] [--no-open] [--no-wait] [--agent NAME]` (`--app-map` is an option of kind `text`) and `pdd try --stop [STORY]`. `--app-map` on check is a text option accepted only with `--files`, to preview a Try map. STORY words are free text. `--timeout` is an option of kind `integer` from 1 to 120 and Check `--max-calls` from 1 to 1000. Try accepts `--max-calls` as a positive integer up to 1000, the server cap. Help states that a new Try defaults to400calls and both Check and Try accept --max-calls1..1000. `--request` (kind `uuid`) is hidden: no help form and no completion show it. These two routes are the one exception to the no-hosted-operation rule above: they call the PDD runtime through the [runtime client](runtime-client.prompt.md), and their help says that they use the person's gh login.

Check also catalogs `--local` (flag), `--screen` (text URL) and `--drawing` (text PATH), with forms `pdd check --lint --local [STORY...] [--json]` and `pdd check --screen URL --drawing PATH [--json]`. The first checks linked SVG layout parts locally with warning diagnostics and 0 AI/network calls; the second compares the real page in installed headless Chrome/Chromium at the drawing viewport, with no AI/runtime call. Existing `--lint` help says it prints local SVG layout warnings before the runtime lint, and that with no discovered tests, no test-candidate hints and no Story operand it lints existing source (plans, contracts, prompts and seeds). [Runtime client](runtime-client.prompt.md#local-drawing-checks) owns combinations, selection, output and exit codes; ordinary remote lint keeps its existing behavior.

Check also catalogs `--retry` as a text option with form `pdd check --retry BATCH [--json] [--details] [--timeout MIN]`. Help says it retries only proven unstarted checks for the saved identical source, preserving completed/running results.

Try also catalogs flags --cli, --shell and --save-last and optional-integer --serve (1..65535, default 8080).
Help forms: `pdd try [STORY] --cli [--shell] [--max-calls N] [--new]`, `pdd try [STORY] --serve [PORT] [--max-calls N] [--new]`,
`pdd try --save-last`. Describe real terminal commands, localhost HTTP requests and saving the last command
into its original test. --shell compatibility and mode conflicts belong to runtime-client.

`pdd workflow evidence ISSUE --summary FILE` records newer source-verified saved check JSON without rerunning workflow steps or publication; require ISSUE and --summary, no extra operands/options.
Try catalogs --agent as nonempty text NAME: accept quoted custom display names as one argument as well as the default codex, claude and gemini names. Agent discovery and unknown-name errors belong to the local agent bridge; parsing does not read configuration or execute a launcher. Workflow --agent keeps its codex|claude value choices. Completion must not present a fixed provider-only list for Try agent names. Its help says pdd stays running to connect the person’s own agent when stdout is a terminal or --agent is explicit; ordinary non-terminal Try returns after collecting saved cases once. --agent selects a configured name and --no-wait skips the bridge. Runtime-client owns conflicts/lifecycle.

Catalog `mcp` (local `mcp`) with the form `pdd mcp`, no operands or options. Help describes a stdio MCP server for the current repository's Try tools. Setup help says "show exact config changes", without a preview-status label, and states that it offers detected Codex, Claude Code and Gemini registrations after showing exact config changes and asking once with y/N.

Remote lint uses the Check caller wait, including --timeout; no separate120second cap. Read help explains that a saved normal Check held for lint may safely continue its original checks; other reads remain GET-only. Runtime-client owns the continuation safeguards and finite recovery wait.

Catalog `jobs` (stable id `jobs`, local disposition `runtime-jobs`) with the sole form `pdd jobs`, no operands or options. Help says it lists active and waiting runtime jobs on this machine without contacting the runtime. Root help and shell completion include jobs. The [slots helper](runtime-slots.prompt.md) owns listing; this route does not authenticate or import the runtime client.

## Shared contract routes

Catalog `contracts` (stable id `contracts`, local `contracts`) with form
`pdd contracts`, no operands/options: list shared records, users and Stories made
stale since their last check. Catalog `contracts.sync` (local `contracts-sync`)
with form `pdd contracts sync [--write]`, no operands and only flag `--write`.
Help says preview moving copies to references, and apply only with --write.
Both routes are local, use working files and make no runtime call. Include them
in root help and completion; do not import the runtime client for parsing/help.

## Product routes

Catalog `product.status` (`product status`, local `product-status`, optional flag
`--json`), `product.next` (`product next`, local `product-next`, no operands or
options), and `product.start` (`product start`, local `product-start`, required
text operand RUN, flags `--no-run` and value `--agent` with codex|claude). Forms:
`pdd product status [--json]`, `pdd product next`, and
`pdd product start RUN [--no-run] [--agent codex|claude]`. Help says status counts
Stories by part and slice, next shows ready runs, and start creates or reuses one
issue then starts a normal feature run unless `--no-run`. All three make zero
runtime calls. [Product](product.prompt.md) owns their behavior.

## Dependencies

No outside values or callback replies are required for this data-only module. All runtime route IDs, prefixes, dispositions, operand/option types, forms and help facts are owned here. Native authoring/generation uses the repository contracts linked above to identify the receiving modules and public boundary; links in route descriptions are native integration/ownership navigation, not a request to load their unrelated implementation/runtime policies when parsing catalog data.
