# PDD documentation

Start with the [README](../README.md).

- [Build a whole product](build-a-whole-product.md): map a product and plan its runs.
- [Usage guide](USAGE.md): install, the PDD skills, setup, runs, gates, checks on the PDD interpreter, clean up and fixes.
- [Workflows in depth](workflows.md): areas, steps, gates, PR 1 and PR 2, the run folder, tests and your own workflows.
- [RUNBOOK.md](../RUNBOOK.md): what the agent does for `pdd test`, `pdd lint` and `pdd simulate`.
- [Interpreter boundaries](runtime-boundaries.md): offline review, server lint, native factory bindings and call-accounting evidence.
- [CLI reference](cli.md): every command, and how to run from a source checkout.
- [A GitHub App token for Autopilot](autopilot-github-app-token.md): a design note for a team that wants Autopilot to have its own GitHub limit.
- [Autopilot supervision discussion plan](autopilot-supervision-plan.md): proposed recovery scope, open decisions and acceptance sequence; implementation requires agreement.
- [Report a problem](ISSUES.md): how you or your agent files a clear issue about pdd.
- [Prompting guide](prompting-guide.md): the method. The [pdd-prompting skill](../skills/pdd-prompting/SKILL.md) has the same text in `guide.md`.
- [Story guide](story-guide.md): how to write a Story that a test can check. The pdd-prompting skill has the same text in `story-guide.md`.

The guide's source is `docs/prompting-guide.md`, and the Story guide's source is `docs/story-guide.md`. A test keeps the skill copies the same. Link to the guide. Do not copy its rules into other files.
