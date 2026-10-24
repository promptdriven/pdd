# PDD Alpha documentation

Start with the [README](../README.md). Before any Story or prompt authoring, have the actual agent conversation read the entire [Prompting guide](prompting-guide.md) and [PDD skill](../skills/pdd/SKILL.md).

- [Local setup](setup.md): source and Node prerequisites.
- [Local native session or existing conversation](prompt-sessions.md): load the guide and work on a useful request.
- [Local issue workflows and recipes](workflows.md): fresh background native stages, issue worktrees, editable definitions, human decisions and GitHub PR steps.
- [Local CLI](cli.md): native sessions, issue run/resume/attach, help, skill output, listing and completion.
- [Evidence and checks](checks.md): what the results prove.
- [Complete ticket-status example](../examples/ticket-status/README.md): prompt, Story, independent cases, implementation and native tests.

The guide is canonical at `docs/prompting-guide.md`. Keep it complete and maintain links to that one file; do not ship a divergent guide inside the skill.
