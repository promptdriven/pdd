# Local PDD Alpha command boundary

PDD Alpha supplies a guide and recipes for the user's existing coding-agent conversation. Keep `pdd` as the command name. Provide local discovery without hosted-service commands or private dependencies.

The local command surface includes help (root and known local command help), `--version`, `workflow list [--json]`, `completion bash|zsh` and `setup`. There is no `session` command and no `workflow feature|bug|small-change` chat launcher: people open Codex or Claude as usual and call a PDD skill by name (`/pdd-feature`, `/pdd-bug`, `/pdd-small-change`, `/pdd-prompting`). Unknown or excluded commands, including with help flags, refuse clearly with exit2 before effects. Do not look up installed service adapters, forward arbitrary argv, import private dependencies, implement authentication, make PDD service calls, change accounts or install services. The workflow runner routes (run, done, approve, changes, cancel, status, open) may use ordinary authenticated Git/GitHub tools and Herdr through the distinct runner. Expose only supported local command declarations and validators.

Keep one catalog authoritative for help/parser/completion. Parse before local reads. Success returns0; unsupported syntax2; missing guidance/local filesystem failure1. Do not echo untrusted input. Local discovery reads do not create project files; only [project setup](project-setup.prompt.md) writes one, on request. Full-access launch modes are owned by [area chats](workflow-chat.prompt.md); no global permission or configuration rewrite is performed. No hosted workflow service or fallback. Package metadata/lock must be dependency-free, retain bin `pdd`, include complete docs/skills/recipes/example and avoid lifecycle scripts. Source use and private temporary package-consumer tests are supported; registry publication/global installation are outside scope.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Source files implement these contracts; tests exercise observable behavior from the actual packed package.

pdd pastes no guide, skill or recipe text: the agent loads the skills on demand.

The package ships five skills in `skills/` (pdd-prompting, pdd-setup, pdd-small-change, pdd-bug, pdd-feature). The standard installer (`npx skills add promptdriven/pdd`) finds exactly these: keep every other SKILL.md out of the repo's `skills/` folder. Each pdd command first keeps the person's home copies current through [skills install](skills-install.prompt.md): it writes only to `~/.agents/skills/`, `~/.claude/skills/` and, when set, `$CLAUDE_CONFIG_DIR/skills/`, never to the person's repo, and an install failure never stops the command.

Workflow execution uses `pdd workflow run NAME ISSUE [--agent codex|claude]` and the runner routes done, approve, changes, cancel, status and open. The [runner](workflow-runner.prompt.md) owns run records, area chats, person approval and real GitHub PR effects. The CLI parses and dispatches. No user-supplied native-argument passthrough, hosted engine or auth/provider gate.

## PDD runtime

This is the one exception to the no-service rules above. Only `pdd check` and `pdd try` call the PDD runtime, with the user's gh token ([runtime client](runtime-client.prompt.md)). The token comes from `gh auth token` and stays in memory: never in files, logs, argv, URLs or error text. They send the repo's Git-visible files (with secret names refused) and keep run state outside the repo. No other command calls a hosted service or reads a token. The runtime address is one setting: `PDD_RUNTIME_URL`, else one default constant in the runtime client.
