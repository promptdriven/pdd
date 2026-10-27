# Alpha local command catalog

Own `src/command-catalog.mjs`; export only `PUBLIC_COMMAND_ROUTES`, `PUBLIC_COMMAND_IDS`, `PUBLIC_COMMAND_MANIFEST`, and `BUNDLED_WORKFLOW_NAMES` (feature, bug, small-change). Catalog the complete small alpha surface: root help, --version, completion bash|zsh workflow list [--json], and session [--agent codex|claude] [request text]. Each route has stable id, exact prefix, local disposition, operand/option specs and plain help forms. Expose no excluded command, private schema/type, service flag or hosted execution operation. Help, parser and completion share this one authority.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

Catalog one local native route for each bundled workflow name. Each has the same optional --agent choices/default and request operands as session, and carries its exact workflow name in the local plan. No arbitrary path or workflow creation route. Session help says that it opens the coding agent with the short PDD intro and that the agent loads the PDD skills when needed. Each shortcut's help names its pdd-NAME skill.

Catalog workflow.run (`workflow run`) with required safe free workflow NAME and ISSUE number|owner/repo#positive-number|https://github.com/owner/repo/issues/positive-number; optional --agent codex|claude defaults codex. Catalog workflow.resume (`workflow resume`) with one UUIDv4 RUN_ID and optional --decision approve|skip. Resume has no agent override. No extra request text/native flags/status command.

For editable workflow execution, workflow.run NAME is a safe free workflow-name operand, not a three-name enum. The dedicated definition loader alone decides available definitions/semantic validity. Preserve the three bundled direct conversation shortcuts as separate foreground routes. Add workflow.attach: `pdd workflow attach RUN_ID`, one UUIDv4, no agent/decision/native/path flags; main resolves actual active saved identity or finite archived information. List describes validated project/bundled definitions; no private route.


## Workflow runner help

Describe workflow.run, workflow.resume and workflow.attach without preview labels. Keep their route IDs, prefixes, local dispositions, operands/options/forms and parser/completion behavior consistent with their contracts.

## Runtime routes

Catalog `check` (local `runtime-check`) with the forms `pdd check [STORY...] [--json] [--details] [--timeout MIN] [--max-calls N]`, `pdd check --read [BATCH] [--json]`, `pdd check --fill-hash` and `pdd check --files`, and `try` (local `runtime-try`) with the forms `pdd try [STORY] [--tab call|screen|terminal|world] [--new] [--no-open]` and `pdd try --stop [STORY]`. STORY words are free text. `--timeout` is an option of kind `integer` from 1 to 120 and `--max-calls` from 1 to 100. `--request` (kind `uuid`) is hidden: no help form and no completion show it. These two routes are the one exception to the no-hosted-operation rule above: they call the PDD runtime through the [runtime client](runtime-client.prompt.md), and their help says that they use the person's gh login.
