# PDD Alpha documentation

Start with the [README](../README.md). Before any Story or prompt authoring, have the actual agent conversation read the entire [Prompting guide](prompting-guide.md). The [pdd-prompting skill](../skills/pdd-prompting/SKILL.md) tells the agent to do this.

- [Usage guide](USAGE.md): install from the `alpha` branch, sessions, workflow runs, approvals, known limits and troubleshooting.
- [Local setup](setup.md): source and Node prerequisites.
- [Local native session or existing conversation](prompt-sessions.md): load the guide and work on a useful request.
- [Local issue workflows and recipes](workflows.md): fresh background native stages, issue worktrees, editable definitions, human decisions and GitHub PR steps.
- [Local CLI](cli.md): native sessions, issue run/resume/attach, help, skill output, listing and completion.
- [Evidence and checks](checks.md): what the results prove.
- [Complete ticket-status example](../examples/ticket-status/README.md): prompt, Story, independent cases, implementation and native tests.

The guide is canonical at `docs/prompting-guide.md`. Keep it complete and maintain links to that one file. `skills/pdd-prompting/guide.md` is a byte-for-byte copy for the skill; a test fails when the two differ, so copy the guide after each edit.
