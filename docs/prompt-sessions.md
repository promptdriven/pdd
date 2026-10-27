# Local native sessions and existing conversations

Open your normal agent in the project checkout. PDD Alpha can launch an installed native agent locally with a short first message. The agent loads the PDD skills when it needs them: pdd-prompting before any prompt, Story or test case, and a workflow skill for workflow work. It preserves the current working directory and existing native login, and starts agents in full-access mode without approval prompts. It writes no global agent configuration. The `session` command opens one conversation; use the separate local issue runner for staged execution. Native account management and conversation resume remain with the installed agent.

## Launch the installed native agent

Use an installed `codex` or `claude` on PATH with its normal existing-user access. If setup is needed, follow official [Codex CLI](https://developers.openai.com/codex/cli/) or [Claude Code](https://code.claude.com/docs/en/overview) instructions. Already usable native tools require no new login. From the package root:

```sh
node bin/pdd.mjs session "Help me review my project before implementation."
node bin/pdd.mjs session --agent codex "Help me draft a reviewed behavior contract."
node bin/pdd.mjs session --agent claude "Help me draft a reviewed behavior contract."
```

The interface is `pdd session [--agent codex|claude] [request text]`, with Codex as default. Use `node bin/pdd.mjs` for local source use. From another project, run the actual absolute package entrypoint so that project's cwd is preserved. The launcher uses the installed native executable and inherited terminal/environment. Codex uses --no-daemon, --dangerously-bypass-approvals-and-sandbox and an invocation-only folder-trust override for the exact cwd; Claude uses --dangerously-skip-permissions. It does not choose a model, copy credentials or rewrite global configuration. Missing required package context refuses before a child starts. Missing native tools exit 127, with no auto-install or private fallback. Request words are joined as one initial prompt; use `--` to end PDD options when needed. Native flags are not passed through. Native exit and interruption remain visible; do not restart uncertain agent work merely because the terminal closed.

For PDD commands inside the native conversation, use the same actual package entrypoint that launched it, including the supplied absolute Node path when present. For example, use `node /actual/package/bin/pdd.mjs workflow list --json` after replacing the package path. Do not assume bare `pdd` resolves to this alpha: the native login shell can select another installation despite the outer terminal's PATH. Keep the project cwd; no global profile change is needed.

The first message is about 600 tokens. It names the folder, inlines the core rules of the [pdd-prompting skill](../skills/pdd-prompting/SKILL.md), names the workflow skills and gives the absolute pdd command. It pastes no guide or workflow. The launcher adds only the full-access and invocation-only trust options described above; it supplies no replacement system instructions or model selection. The `session` command does not start the issue workflow runner. `workflow run NAME ISSUE` is separate; see [workflow guidance](workflows.md). Native agent behavior and platform compatibility still require actual acceptance on the installed tools.

## Load before writing a Story

Every pdd command keeps the PDD skills in `~/.agents/skills/` (Codex) and `~/.claude/skills/` (Claude Code), so any chat can load them. Before the agent drafts a Story or prompt, it must read the **entire** `guide.md` of the pdd-prompting skill (the same text as the [Prompting guide](prompting-guide.md)) in the actual conversation. A link or schema check cannot replace loading the guide.

From the package root, `node bin/pdd.mjs --skill` prints the guide first and the complete bundled skill references. The agent must read the complete output; if the tool truncates it, read the files in complete sections. For another project, provide the actual absolute package path so references resolve. Do not duplicate the canonical guide or guess an installation command.

Ask the agent to explain the relevant guide method for your useful change, then draft the prompt, Story and independent cases. Use the [README's worked request](../README.md#open-an-ordinary-native-session) or the [ticket-status example](../examples/ticket-status/README.md). Review and revise those drafts before asking for implementation. Continue with real project tests and a local PR summary.

Reopen the conversation through your agent's normal controls. Preserve your actual project and context; reload the guide if it is no longer available to the agent. The local native launcher does not provide remote workflow status or original-request recovery; native reconnect and resume remain the agent's own controls.
