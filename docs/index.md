# PDD Alpha documentation

Start with the [README](../README.md).

- [Usage guide](USAGE.md): install, the PDD skills, setup, runs, gates, runtime checks, clean up and fixes.
- [Workflows in depth](workflows.md): areas, steps, gates, PR 1 and PR 2, the run folder, tests and your own workflows.
- [RUNBOOK.md](../RUNBOOK.md): what the agent does for `pdd check` and `pdd try`.
- [Runtime boundaries](runtime-boundaries.md): offline review, server lint, native factory bindings and call-accounting evidence.
- [CLI reference](cli.md): every command, and how to run from a source checkout.
- [Prompting guide](prompting-guide.md): the method. The [pdd-prompting skill](../skills/pdd-prompting/SKILL.md) has the same text in `guide.md`.

The guide's source is `docs/prompting-guide.md`. A test keeps `skills/pdd-prompting/guide.md` the same. Link to the guide. Do not copy its rules into other files.
