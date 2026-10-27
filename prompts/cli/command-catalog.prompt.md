# Alpha local command catalog

Own `src/command-catalog.mjs`; export only `PUBLIC_COMMAND_ROUTES`, `PUBLIC_COMMAND_IDS`, `PUBLIC_COMMAND_MANIFEST`, and `BUNDLED_WORKFLOW_NAMES` (feature, bug, small-change). Catalog the complete small alpha surface: root help, --version, --skill, completion bash|zsh workflow list [--json], and session [--agent codex|claude] [request text]. Each route has stable id, exact prefix, local disposition, operand/option specs and plain help forms. Expose no excluded command, private schema/type, service flag or hosted execution operation. Help, parser and completion share this one authority.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

Catalog one local native route for each bundled workflow name. Each has the same optional --agent choices/default and request operands as session, and carries its exact workflow name in the local plan. No arbitrary path or workflow creation route.

Catalog workflow.run (`workflow run`) with required safe free workflow NAME and ISSUE number|owner/repo#positive-number|https://github.com/owner/repo/issues/positive-number; optional --agent codex|claude defaults codex. Catalog workflow.resume (`workflow resume`) with an optional saved-run reference and optional --decision approve|skip. Resume has no agent override. No extra request text or native flags.

For editable workflow execution, workflow.run NAME is a safe free workflow-name operand, not a three-name enum. The dedicated definition loader alone decides available definitions/semantic validity. Preserve the three bundled direct conversation shortcuts as separate foreground routes. Add workflow.attach: `pdd workflow attach ISSUE|RUN_ID`, one saved-run reference, no agent/decision/native/path flags; main resolves actual active saved identity or finite archived information. List describes validated project/bundled definitions; no private route.

Catalog the human short commands `workflow approve`, `workflow changes`, `workflow skip`, `workflow status`, and `workflow watch`. Their saved-run operand is an issue reference, unique eight-character run-ID prefix or full UUID; approve alone may omit it when exactly one run is waiting in the current repository. Status accepts only `--all`. Decision options are declared below; changes accepts optional request text. Resume and attach use the same reference grammar. Help uses issue/reference forms and never promises a UUID is required.


## Workflow runner help

Describe workflow.run, workflow.resume and workflow.attach without preview labels. Keep their route IDs, prefixes, local dispositions, operands/options/forms and parser/completion behavior consistent with their contracts.

Add workflow.decide: `pdd workflow decide ISSUE|RUN_ID --decision approve|changes|skip
[--text TEXT] --id UUID --expect-stage STAGE --expect-seq N [--yes] [--json]`.
It is the shared bound person-decision seam. All other public routes are preserved.

Short approve/changes/skip routes accept --yes, --json and the complete --via phone --phone PHONE_ID --approval TOKEN trio. Changes uses the shared proposal revision decision.
