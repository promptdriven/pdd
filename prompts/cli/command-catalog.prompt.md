# Alpha local command catalog

Own `src/command-catalog.mjs`; export only `PUBLIC_COMMAND_ROUTES`, `PUBLIC_COMMAND_IDS`, `PUBLIC_COMMAND_MANIFEST`, and `BUNDLED_WORKFLOW_NAMES` (feature, bug, small-change). Catalog the complete small alpha surface: root help, --version, --skill, completion bash|zsh workflow list [--json], and session [--agent codex|claude] [request text]. Each route has stable id, exact prefix, local disposition, operand/option specs and plain help forms. No excluded command, private schema/type, host flag or Runtime operations export remains. Help, parser and completion share this one authority.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

Catalog one local native route for each bundled workflow name. Each has the same optional --agent choices/default and request operands as session, and carries its exact workflow name in the local plan. No arbitrary path or workflow creation route.

Catalog workflow.run (`workflow run`) with required safe free workflow NAME and ISSUE number|owner/repo#positive-number|https://github.com/owner/repo/issues/positive-number; optional --agent codex|claude defaults codex. Catalog workflow.resume (`workflow resume`) with one UUIDv4 RUN_ID and optional --decision approve|skip. Resume has no agent override. No extra request text/native flags/status command.

For editable workflow execution, workflow.run NAME is a safe free workflow-name operand, not a three-name enum. The dedicated definition loader alone decides available definitions/semantic validity. Preserve the three bundled direct conversation shortcuts as separate foreground routes. Add workflow.attach: `pdd workflow attach RUN_ID`, one UUIDv4, no agent/decision/native/path flags; main resolves actual active saved identity or finite archived information. List describes validated project/bundled definitions; no private route.


## Publication: workflow runner preview

Label ONLY workflow.run, workflow.resume and workflow.attach help descriptions PREVIEW. Preserve every route ID, prefix, local disposition, operands/options/forms and parser/completion behavior. These commands remain in the published alpha but have not yet proved a real workflow PR. Do not label ordinary local guide/skill/session/list/completion as runner execution or imply the preview label proves success.
