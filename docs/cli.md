# Local CLI

Use Node.js 22.16.0 or newer. From the package root:

```sh
node bin/pdd.mjs --help
node bin/pdd.mjs --version
node bin/pdd.mjs --skill
node bin/pdd.mjs session --help
node bin/pdd.mjs session --agent codex "Help me review my project."
node bin/pdd.mjs session --agent claude "Help me review my project."
node bin/pdd.mjs workflow run --help
node bin/pdd.mjs workflow resume --help
node bin/pdd.mjs workflow attach --help
node bin/pdd.mjs workflow feature --agent codex "Help me define a useful change."
node bin/pdd.mjs workflow bug --agent claude "Help me reproduce this failure."
node bin/pdd.mjs workflow small-change "Help me make a contained change."
node bin/pdd.mjs workflow list
node bin/pdd.mjs workflow list --json
node bin/pdd.mjs completion bash
node bin/pdd.mjs completion zsh
```

`help` and `-h` are alternatives to `--help`. The `pdd …` forms below describe command syntax. From another project or inside a native agent, invoke this package by its actual absolute entrypoint, such as `node /actual/package/bin/pdd.mjs`, retaining an absolute Node executable path when supplied. A native login shell can resolve bare `pdd` to a different installation despite the outer terminal's PATH. Local invocation avoids changing an existing global command.

`--skill` prints the complete canonical [Prompting guide](prompting-guide.md) first, then [the skill](../skills/pdd/SKILL.md) and every bundled Markdown reference, with their package paths. The actual conversation must load that complete guide before Story authoring. If output is truncated, read its files in complete sections.

`session [--agent codex|claude] [request text]` launches the installed native agent, defaulting to Codex, with a short first message (about 600 tokens). The message names the folder, inlines the core rules from the [pdd-prompting skill](../skills/pdd-prompting/SKILL.md), names the workflow skills and gives the absolute pdd command. It pastes no guide or workflow: the agent loads the skills on demand. The message is the native initial positional prompt, because the interactive Codex and Claude CLIs take no first message from stdin or a file. The launcher preserves cwd, native login and the inherited terminal/environment. It starts agents in full-access mode without approval prompts: Codex uses --no-daemon, --dangerously-bypass-approvals-and-sandbox and an invocation-only folder-trust override for the exact cwd; Claude uses --dangerously-skip-permissions. It does not select a model, copy credentials or write global configuration. No request text is required. Optional request words are joined into the last line of the message. `--` ends PDD options; arbitrary native flags are not forwarded. The native exit status is preserved; a missing executable exits 127. A missing pdd-prompting skill in the package refuses with exit 1 before launching. Native signal termination is reported as 128 plus its signal number. These invocations can use your native agent/provider allowance; they are not inert discovery commands.

`workflow feature|bug|small-change [--agent codex|claude] [request text]` opens one normal native conversation with the same message as `session`, plus a last line: `Use the pdd-NAME skill for this request.` Codex is the default. It uses the same launcher, cwd, environment, full-access mode and exit behavior as `session`. Optional `--` ends PDD options; no arbitrary skill paths or native flags are accepted. A valid name with `--help` returns usage without native launch; an unknown name returns exit 2 before effects. A missing selected skill in the package refuses with exit 1.

Every pdd command first keeps the four packaged skills current in `~/.agents/skills/` and `~/.claude/skills/`. It copies a skill when it is missing, from an older pdd version, or changed in the same version. It keeps a newer copy and any folder without the pdd marker file (`.pdd-skill.json`). It never writes them into the project. If the copy fails, pdd prints one warning line and runs the command as usual.

In that shortcut, stages are followed in one conversation; the command does not start separate agent sessions per stage, persist a managed workflow or publish PRs automatically. The person can request actual Git/GitHub publication later through the agent's normal tools. Local PR preparation alone supplies no URL or publication result.

For local GitHub issue execution, use `pdd workflow run NAME ISSUE [--agent codex|claude]`, default Codex. NAME is a safe lowercase/digit name beginning with a letter, with single hyphens between nonempty groups, up to 64 characters. The definition loader selects and validates project overrides or bundled definitions; the CLI does not limit names to three built-ins. ISSUE is a positive number, owner/repo#number or HTTPS GitHub issue URL resolved against the current repository. Use the actual package entrypoint from your project. The runner assigns a separate issue worktree/branch for stage execution. This command can perform agent work, push branches and create real PRs.

`pdd workflow resume RUN_ID [--decision approve|skip]` uses the saved UUIDv4 identity and its workflow snapshot, agent and issue worktree. Without a decision it inspects/reconciles or observes merge state and does not launch the next native stage or PR. Approval advances eligible work or applies to current human/optional work; skip is only for optional work. Merge waits inspect the actual saved PR and never merge. Exit 0 is completed, 2 waiting and 1 failed/recovery_required. Unknown native/PR outcomes never authorize blind relaunch/resend.

`pdd workflow attach RUN_ID` asks the runner to resolve the actual current active backend from the common-repository index. It attaches that live native terminal, not a new conversation. Attachment and stage acceptance/cleanup are mutually exclusive; new interaction invalidates earlier candidates. Archived stages produce finite information rather than a promise of a live pane. There is no agent override or arbitrary native flag passthrough.

The PDD controller remains foreground while issue stages use fresh native agents in owned background Herdr workspaces. Ready-before-submit, one durable prompt intent and the same agent's working-to-ready observation provide a candidate only. The runner validates the exact handoff, artifacts, revision and actual tests before acceptance and cleanup. Active/blocked backing panes still consume resources; completed accepted stages do not need permanent panes. There is no automatic progression after the controller exits. Explicit resume reconciles the saved original. See [workflow execution and recovery](workflows.md).

`workflow list [--json]` uses the authoritative definition loader. JSON returns `{ "workflows": [{ "name": "feature", "source": "bundled" }], "default": null }` with actual validated entries and source `project` or `bundled`. A complete valid project definition overrides the matching bundled name; an invalid override or unavailable loader refuses, without a legacy Markdown fallback. Listing is local discovery, not native/GitHub work. Bash/Zsh completion consumes this local listing as data, filters safe names and does not evaluate returned text.

Completion prints shell text to stdout; it does not modify shell configuration. Save or source it using your own shell's usual setup. The local native session command starts the installed agent with a short message; the agent loads the PDD skills on demand. The package provides local commands only. Unsupported operations must remain unsupported, with no hosted-service fallback.
