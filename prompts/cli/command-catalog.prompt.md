# Alpha local command catalog

Own `src/command-catalog.mjs`; export only `PUBLIC_COMMAND_ROUTES`, `PUBLIC_COMMAND_IDS`, `PUBLIC_COMMAND_MANIFEST`, and `BUNDLED_WORKFLOW_NAMES` (feature, bug, small-change). Catalog the complete small alpha surface: root help, --version, --skill, completion bash|zsh workflow list [--json], and session [--agent codex|claude] [request text]. Each route has stable id, exact prefix, local disposition, operand/option specs and plain help forms. Expose no excluded command, private schema/type or hosted execution implementation. Optional command declarations are limited to the families below. Help, parser and completion share this one authority.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

Catalog one local native route for each bundled workflow name. Each has the same optional --agent choices/default and request operands as session, and carries its exact workflow name in the local plan. No arbitrary path or workflow creation route.

Catalog workflow.run (`workflow run`) with required safe free workflow NAME and ISSUE number|owner/repo#positive-number|https://github.com/owner/repo/issues/positive-number; optional --agent codex|claude defaults codex. Catalog workflow.resume (`workflow resume`) with one UUIDv4 RUN_ID and optional --decision approve|skip. Resume has no agent override. No extra request text/native flags/status command.

For editable workflow execution, workflow.run NAME is a safe free workflow-name operand, not a three-name enum. The dedicated definition loader alone decides available definitions/semantic validity. Preserve the three bundled direct conversation shortcuts as separate foreground routes. Add workflow.attach: `pdd workflow attach RUN_ID`, one UUIDv4, no agent/decision/native/path flags; main resolves actual active saved identity or finite archived information. List describes validated project/bundled definitions; no private route.


## Workflow runner help

Describe workflow.run, workflow.resume and workflow.attach without preview labels. Keep their route IDs, prefixes, local dispositions, operands/options/forms and parser/completion behavior consistent with their contracts.

## Optional client declarations

Mark these routes `optionalClient: true`; retain stable dotted IDs, hyphenated local dispositions and public forms. Help descriptions identify the optional client requirement. The catalog remains the sole source for parser, help and completion. Existing local routes are unchanged.

- `phone [--relay URL] [--name NAME] [--codex PATH] [--claude PATH] [--no-integrations]`.
- `link status [--json]`, restart, stop, logs, devices, `revoke ID_OR_NAME`, `uninstall [--forget]`, reset-identity, and internal run (no help form).
- `agents [--search TEXT]`, `open AGENT`; `agent show AGENT [--terminal]`, `send AGENT TEXT --id ACTION_ID`, `keys AGENT KEY [KEY ...] --id ACTION_ID`, `resume AGENT --id ACTION_ID`, `stop AGENT --how interrupt|exit|close --id ACTION_ID`, and `dismiss AGENT`.
- `setup [--no-phone]` and `join`.
- `fleet status`, `approve CODE`, `remove MEMBER`, `admissions MEMBER`, `tag MACHINE always-on|laptop`, `rename MACHINE NAME`, and `set-endpoints [--relay URL] [--keeper URL] [--app URL]`.
- `accounts`; `accounts add codex|claude|anthropic-key NAME [--from-pool] [--replace]`, `remove ACCOUNT`, `resign ACCOUNT`, delete-all, `mode TOOL [SETTING] [--machine MACHINE]`, `when-out TOOL [ask|continue|wait] [--machine MACHINE]`, `quota-decide QUESTION_ID --decision continue|wait --rev N`, migrate-sessions, `rotate github`, `policy TOOL [--machine MACHINE] [--pinned ACCOUNTS --then auto|wait] [--exclude ACCOUNTS]`, and `allow ACCOUNT on|off --machine MACHINE`. TOOL is codex|claude; QUESTION_ID is UUIDv4. Other unnamed operands and value options are text.

The optional client owns semantic service/account validation and effects. No status, doctor, update, settings, hosted runtime or new workflow route is introduced by this table.
