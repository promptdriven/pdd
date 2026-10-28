# Alpha local command catalog

Own `src/command-catalog.mjs`; export only `PUBLIC_COMMAND_ROUTES`, `PUBLIC_COMMAND_IDS`, `PUBLIC_COMMAND_MANIFEST`, and `BUNDLED_WORKFLOW_NAMES` (feature, bug, small-change). Catalog the complete small alpha surface: root help, --version, completion bash|zsh, workflow list [--json] and setup (`pdd setup`, local `setup`, no operands or options; its help says that it installs the PDD skills for Codex and Claude if they are missing, adds the short PDD block to CLAUDE.md, else AGENTS.md, and that a second run changes nothing). Each route has stable id, exact prefix, local disposition, operand/option specs and plain help forms. Expose no excluded command, private schema/type, service flag or hosted execution operation. Help, parser and completion share this one authority.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

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
No resume, attach, run IDs, decisions flag or native argument passthrough. The areas module decides which workflow names exist.

## Workflow runner help

Describe the runner routes in plain words without preview labels. workflow.run says that pdd starts a chat and exits, and that pdd later pushes the branch and opens a real PR. Keep route IDs, prefixes, local dispositions, operands/options/forms and parser/completion behavior consistent with their contracts.

## Runtime routes

Catalog `approve` (local `prompt-approve`, [prompt approve](prompt-approve.prompt.md)) with the form `pdd approve PROMPT`: one required text operand, no options. Its help says that it shows the interface and the text changes since the last approval, and that it is for a person at a terminal.

Catalog `check` (local `runtime-check`) with the forms `pdd check [STORY...] [--json] [--details] [--timeout MIN] [--max-calls N]` (help: it waits for every check, with no limit in a terminal and at most 90 s for an agent, and prints a progress line every 30 s; `--timeout MIN` sets the limit), `pdd check --read [BATCH] [--json]`, `pdd check --fill-hash`, `pdd check --files [STORY...] [--app-map PATH]` and `pdd check --lint [STORY...] [--json]` (help: it runs only the runtime lint and sends no checks), and `try` (local `runtime-try`) with the forms `pdd try [STORY] [--max-calls N] [--tab call|screen|terminal|world] [--app-map PATH] [--new] [--no-open] [--no-wait] [--agent codex|claude|gemini]` (`--app-map` is an option of kind `text`) and `pdd try --stop [STORY]`. `--app-map` on check is a text option accepted only with `--files`, to preview a Try map. STORY words are free text. `--timeout` is an option of kind `integer` from 1 to 120 and Check `--max-calls` from 1 to 100. Try accepts `--max-calls` as a positive integer up to 999999; the runtime enforces its supported session maximum. `--request` (kind `uuid`) is hidden: no help form and no completion show it. These two routes are the one exception to the no-hosted-operation rule above: they call the PDD runtime through the [runtime client](runtime-client.prompt.md), and their help says that they use the person's gh login.

Check also catalogs `--retry` as a text option with form `pdd check --retry BATCH [--json] [--details] [--timeout MIN]`. Help says it retries only proven unstarted checks for the saved identical source, preserving completed/running results.

Try also catalogs flags --cli, --shell and --save-last and optional-integer --serve (1..65535, default 8080).
Help forms: `pdd try [STORY] --cli [--shell] [--max-calls N] [--new]`, `pdd try [STORY] --serve [PORT] [--max-calls N] [--new]`,
`pdd try --save-last`. Describe real terminal commands, localhost HTTP requests and saving the last command
into its original test. --shell compatibility and mode conflicts belong to runtime-client.

`pdd workflow evidence ISSUE --summary FILE` records newer source-verified saved check JSON without rerunning workflow steps or publication; require ISSUE and --summary, no extra operands/options.
Try catalogs --agent as a value choice codex|claude|gemini. Its help says pdd stays running to connect the person’s own agent, --agent selects it and --no-wait skips the bridge. Runtime-client owns conflicts/lifecycle.
