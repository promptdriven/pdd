# Project setup

Own `src/project-setup.mjs`. Export `setupProject({cwd, packageRoot})`. It does what the [pdd-setup skill](../../skills/pdd-setup/SKILL.md) tells an agent to do, without an agent: it adds or updates one short PDD block in the file that the project's agents read. `pdd setup` calls it.

## The block

The block is the fenced block in `<packageRoot>/skills/pdd-setup/SKILL.md`: from the line that is exactly `<!-- pdd:start -->` to the line that is exactly `<!-- pdd:end -->`. Read it from that file, so the skill and the command cannot drift apart. If the package has no `RUNBOOK.md`, leave out each block line that names `RUNBOOK.md`. If the skill has no such block, throw an error.

## Where it goes

| Project folder (`cwd`) | File |
| --- | --- |
| Has `CLAUDE.md` | `CLAUDE.md` |
| Has `AGENTS.md` and no `CLAUDE.md` | `AGENTS.md` |
| Has neither | Create `AGENTS.md` with only the block |

- The file has exactly one line `<!-- pdd:start -->` and, after it, one line `<!-- pdd:end -->`: replace those lines and the lines between them with the block. Keep all other text.
- The file has no marker line: add the block at the end, after one empty line. If the file does not end with a newline, add one first.
- Any other marker count or order: throw an error that names both markers, and write nothing.
- The file ends with a newline after the block.
- If the new text equals the old text, write nothing.

Return `{file, changed}`: the absolute file path and whether the file was written. Never paste the guide or a workflow. Never touch another file.

## Dependencies

Read the full [Prompting guide](../../docs/prompting-guide.md) before you change this prompt. Follow the [alpha boundary](public-boundary.prompt.md). The [CLI](pdd-cli.prompt.md) runs it for `pdd setup`.
