# Local PDD Alpha command boundary

PDD Alpha supplies a guide and recipes for the user's existing coding-agent conversation. Keep `pdd` as the command name. Provide local discovery without hosted-service commands or private dependencies.

The local command surface includes help (root and known local command help), `--version`, `--skill`, `workflow list [--json]`, `completion bash|zsh`, `session [--agent codex|claude] [request text]`, and `workflow feature|bug|small-change [--agent codex|claude] [request text]`. Unknown or excluded commands, including with help flags, refuse clearly with exit2 before effects. Do not look up installed service adapters, forward arbitrary argv, import private dependencies, implement authentication, make PDD service calls, change accounts or install services. The workflow runner routes (run, done, approve, changes, cancel, status, open) may use ordinary authenticated Git/GitHub tools and Herdr through the distinct runner. Expose only supported local command declarations and validators.

Keep one catalog authoritative for help/parser/completion. Parse before local reads. Success returns0; unsupported syntax2; missing guidance/local filesystem failure1. Do not echo untrusted input. Local discovery reads do not create project files. Explicit session launches only the installed native Codex or Claude; native keeps the user’s existing environment/login and follows their conversation instructions. Full-access launch modes are owned by [native session](native-session.prompt.md) and [area chats](workflow-chat.prompt.md); no global permission or configuration rewrite is performed. No hosted workflow service or fallback. Package metadata/lock must be dependency-free, retain bin `pdd`, include complete docs/skills/recipes/example and avoid lifecycle scripts. Source use and private temporary package-consumer tests are supported; registry publication/global installation are outside scope.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Source files implement these contracts; tests exercise observable behavior from the actual packed package.

Named workflow shortcuts select exactly one bundled manual recipe and use the same ordinary native launcher. This is one conversation, not a managed or stage-separated runner, and no PR effect is automatic. Existing session still loads all bundled recipes.

Workflow execution uses `pdd workflow run NAME ISSUE [--agent codex|claude]` and the runner routes done, approve, changes, cancel, status and open. The [runner](workflow-runner.prompt.md) owns run records, area chats, person approval and real GitHub PR effects. The CLI parses and dispatches. No user-supplied native-argument passthrough, hosted engine or auth/provider gate.
