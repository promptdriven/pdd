# Run setup only with a ready workflow agent

Own `src/workflow-setup.mjs`; export module function `setupWithWorkflowAgent({cwd,env},ports)`. This is the setup admission adapter, independent of the shared CLI's command routing. It does not install skills, write agent files or start chats itself. The caller supplies its existing setup action; the shared CLI owner wires that action to this adapter separately.

Use [workflow readiness](workflow-agents.prompt.md) `checkWorkflowAgents({cwd,env},ports)` first, with the exact caller environment and its injectable native status process. A false result prints only the readiness owner's safe actionable message to ports.stderr and returns 1. An unavailable/thrown readiness result prints a generic status-command recovery instruction and returns 1. Neither case may call the setup action. Never print raw exception/authentication details.

With a ready selection, call `ports.setup({agent,cwd,env})` once and return its integer exit status unchanged. A ready optional alternative is sufficient; setup itself does not require a particular agent. The existing skills/project/MCP actions and consent policy remain with their owners. The adapter adds no consent for those actions and never performs login, logout, installation, model calls or workflow allocation. Missing/invalid setup callbacks or invalid replies fail finitely with exit 1; never retry an action that threw or returned a bad result because it may already have written configuration.

## Dependencies

- Load the [Prompting guide](../../docs/prompting-guide.md) for authoring/generation.
- Load [workflow agent readiness](workflow-agents.prompt.md) for generation/testing/runtime admission policy. Ports.run is its native status boundary; this adapter does not infer sign-in from files or parse status output.
- [Skills install](skills-install.prompt.md), [project setup](project-setup.prompt.md), and [agent MCP setup](agent-mcp-setup.prompt.md) retain their existing setup behavior. The caller's supplied setup action owns their execution.
- The [CLI](pdd-cli.prompt.md) owns public dispatch. Adding this adapter does not by itself change pdd setup; the pending shared-file wiring must be integrated before claiming the public command fixed.
