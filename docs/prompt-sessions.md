# Local native sessions and existing conversations

Open your normal agent in the project checkout. PDD Alpha can launch an installed native agent locally with the full canonical guide and bundled workflow content automatically loaded before any Story. It preserves the current working directory, existing native login and permissions. The `session` command opens one conversation; use the separate local issue runner for staged execution. Native account management and conversation resume remain with the installed agent.

## Launch the installed native agent

Use an installed `codex` or `claude` on PATH with its normal existing-user access. If setup is needed, follow official [Codex CLI](https://developers.openai.com/codex/cli/) or [Claude Code](https://code.claude.com/docs/en/overview) instructions. Already usable native tools require no new login. From the package root:

```sh
node bin/pdd.mjs session "Help me review my project before implementation."
node bin/pdd.mjs session --agent codex "Help me draft a reviewed behavior contract."
node bin/pdd.mjs session --agent claude "Help me draft a reviewed behavior contract."
```

The interface is `pdd session [--agent codex|claude] [request text]`, with Codex as default. Use `node bin/pdd.mjs` for local source use. From another project, run the actual absolute package entrypoint so that project's cwd is preserved. The launcher uses the installed native executable and inherited terminal/environment. It does not choose a model, override permission settings, copy credentials or rewrite global configuration. Missing required package context refuses before a child starts. Missing native tools exit 127, with no auto-install or private fallback. Request words are joined as one initial prompt; use `--` to end PDD options when needed. Native flags are not passed through. Native exit and interruption remain visible; do not restart uncertain agent work merely because the terminal closed.

For PDD commands inside the native conversation, use the same actual package entrypoint that launched it, including the supplied absolute Node path when present. For example, use `node /actual/package/bin/pdd.mjs workflow list --json` after replacing the package path. Do not assume bare `pdd` resolves to this alpha: the native login shell can select another installation despite the outer terminal's PATH. Keep the project cwd; no global profile change is needed.

The full guide goes into the native initial positional prompt first, followed by the skill, all its reference Markdown and every bundled manual workflow Markdown file. The recipe WORKFLOW and linked step contents are supplied, not just their paths. The package context also includes docs/workflows.md. The launcher adds no system/config/model/permission flags. The startup request tells the agent to read and apply that context before any Story. The `session` command supplies context without starting the issue workflow runner. `workflow run NAME ISSUE` separately creates a saved local run, fresh native sessions per agent stage and real PR stages; see [workflow guidance](workflows.md). Issue runner stages instead use fresh background Herdr agents in their assigned issue worktree. The foreground PDD controller validates readiness observations plus exact handoff/revision/files/tests before automatic handoff; it does not require a normal native exit after every stage. Use `workflow attach RUN_ID` for the actual active conversation. Controller exit stops PDD progression until explicit resume; completed archived panes are not live attach targets. Ordinary `session` remains foreground. Native agent behavior and platform compatibility still require actual acceptance on the installed tools.

## Load before writing a Story

In a locally launched session, have the agent apply the complete supplied guide before drafting. In a separately opened conversation, have it read the **entire [Prompting guide](prompting-guide.md)**, [skill entrypoint](../skills/pdd/SKILL.md) and [prompt-session reference](../skills/pdd/references/prompt-session.md) in the actual conversation before drafting any Story or prompt. Existing conversations need the same context. A link or schema check cannot replace loading the guide.

From the package root, `node bin/pdd.mjs --skill` prints the guide first and the complete bundled skill references. The agent must read the complete output; if the tool truncates it, read the files in complete sections. For another project, provide the actual absolute package path so references resolve. Do not duplicate the canonical guide or guess an installation command.

Ask the agent to explain the relevant guide method for your useful change, then draft the prompt, Story and independent cases. Use the [README's worked request](../README.md#open-an-ordinary-native-session) or the [ticket-status example](../examples/ticket-status/README.md). Review and revise those drafts before asking for implementation. Continue with real project tests and a local PR summary.

Reopen the conversation through your agent's normal controls. Preserve your actual project and context; reload the guide if it is no longer available to the agent. The local native launcher does not provide remote workflow status or original-request recovery; native reconnect and resume remain the agent's own controls.
