# Alpha local command catalog

Own `src/command-catalog.mjs`; export only `PUBLIC_COMMAND_ROUTES`, `PUBLIC_COMMAND_IDS`, `PUBLIC_COMMAND_MANIFEST`, and `BUNDLED_WORKFLOW_NAMES` (feature, bug, small-change). Catalog the complete small alpha surface: root help, --version, completion bash|zsh, workflow list [--json] and setup (`pdd setup`, local `setup`, no operands or options; its help says that it installs the PDD skills for Codex and Claude if they are missing, adds the short PDD block to CLAUDE.md, else AGENTS.md, and that a second run changes nothing). Each route has stable id, exact prefix, local disposition, operand/option specs and plain help forms. Expose no excluded command, private schema/type, service flag or hosted execution operation. Help, parser and completion share this one authority.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

There is no `session` route and no `workflow feature|bug|small-change` chat route: people call the PDD skills in their own chat. No arbitrary path or workflow creation route.

Catalog the area-chat runner routes ([runner](workflow-runner.prompt.md)):
- workflow.run `workflow run NAME ISSUE [--agent codex|claude]`: NAME is a safe workflow name, ISSUE is a number, `owner/repo#number` or `https://github.com/owner/repo/issues/number`. Default agent codex.
- workflow.done `workflow done STEP [--summary TEXT]`: STEP is a safe step name; the summary is free text.
- workflow.ask `workflow ask QUESTION…`: the question words join into one text; `--` ends options.
- workflow.approve `workflow approve [ISSUE]`, workflow.status `workflow status [ISSUE] [--all] [--cancelled] [--json]` (flags).
- workflow.changes `workflow changes ISSUE TEXT…`: the text words join into one request; `--` ends options.
- workflow.cancel `workflow cancel ISSUE`, workflow.open `workflow open ISSUE`.
- workflow.list `workflow list [--json]`.
No resume, attach, run IDs, decisions flag or native argument passthrough. The areas module decides which workflow names exist.

## Workflow runner help

Describe the runner routes in plain words without preview labels. workflow.run says that pdd starts a chat and exits, and that pdd later pushes the branch and opens a real PR. Keep route IDs, prefixes, local dispositions, operands/options/forms and parser/completion behavior consistent with their contracts.

## Runtime routes

Catalog `approve` (local `prompt-approve`, [prompt approve](prompt-approve.prompt.md)) with the form `pdd approve PROMPT`: one required text operand, no options. Its help says that it is for a person at a terminal.

Catalog `check` (local `runtime-check`) with the forms `pdd check [STORY...] [--json] [--details] [--timeout MIN] [--max-calls N]` (help: it waits for every check, with no limit in a terminal and at most 8 min for an agent, and prints a progress line every 30 s; `--timeout MIN` sets the limit), `pdd check --read [BATCH] [--json]`, `pdd check --fill-hash`, `pdd check --files` and `pdd check --lint [STORY...] [--json]` (help: it runs only the runtime lint and sends no checks), and `try` (local `runtime-try`) with the forms `pdd try [STORY] [--tab call|screen|terminal|world] [--app-map PATH] [--new] [--no-open] [--no-wait]` (`--app-map` is an option of kind `text`) and `pdd try --stop [STORY]`. STORY words are free text. `--timeout` is an option of kind `integer` from 1 to 120 and `--max-calls` from 1 to 100. `--request` (kind `uuid`) is hidden: no help form and no completion show it. These two routes are the one exception to the no-hosted-operation rule above: they call the PDD runtime through the [runtime client](runtime-client.prompt.md), and their help says that they use the person's gh login.
