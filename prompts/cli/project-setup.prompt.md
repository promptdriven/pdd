# Project setup

Own `src/project-setup.mjs`. Export `setupProject({cwd, packageRoot})`, `ignorePddFolder({root})`, and `checkProjectReady({cwd, packageRoot})`. They do what the [pdd-setup skill](../../skills/pdd-setup/SKILL.md) tells an agent to do, without an agent: `setupProject` adds or updates one short PDD block in the file that the project's agents read, and `ignorePddFolder` keeps the local `.pdd/` folder out of Git. `pdd setup` calls both.

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

Return `{file, changed}`: the absolute file path and whether the file was written. Never paste the guide or a workflow. `setupProject` never touches another file.

## Ignore `.pdd/`

`pdd test` keeps its local cache in `.pdd/` at the Git root. That folder must never go into a commit. `ignorePddFolder({root})` gets the Git top-level folder and changes only `<root>/.gitignore`. Read the lines as Git does: drop spaces and a CR at the end of a line, and keep spaces at its start. An ignore line is `.pdd`, `.pdd/`, `/.pdd` or `/.pdd/`. A negation line is `!` and an ignore line. The last ignore or negation line counts, as in Git:

| `.gitignore` | Result |
| --- | --- |
| Does not exist | Create it with the one line `.pdd/` |
| Its last such line is an ignore line | Write nothing |
| Its last such line is a negation line | Write nothing, and return `negated: true`: the person keeps `.pdd/` in Git |
| Has no such line, but a line `!` for `.pdd` or a path in it: `!`, an optional `/` or `**/`, then `.pdd` and the line end, `/`, `*`, `?` or `[` (for example `!.pdd/config.json`) | Write nothing, and return `negated: true`: a `.pdd/` line after it would override the person's more specific rule |
| Has none of these lines | Append the line `.pdd/`. If the file does not end with a newline, append one first. Use CRLF for both when the file has a CRLF, else LF |
| Is not a regular file (a folder or a symbolic link) | Throw an error that names the file and says to add `.pdd/` by hand; write nothing |

Keep every old byte: read the file as bytes and only append. A file that is not valid UTF-8 keeps its bytes. Return `{file, changed, negated}`: the absolute `.gitignore` path, whether the file was written, and whether a negation line kept it unchanged.

## Readiness

`checkProjectReady` reads only: return true exactly when the selected project file contains the current complete block and, in a Git repository, the root ignore handling requires no write under the `.pdd/` rule above, including a respected negation. Outside Git the ignore condition is satisfied. Missing or malformed files return false. It does not change files, initialize a repository, read authentication or machine skills, or contact a service.

## Dependencies

Read the full [Prompting guide](../../docs/prompting-guide.md) before you change this prompt. Follow the [alpha boundary](public-boundary.prompt.md). The [CLI](pdd-cli.prompt.md) runs it for `pdd setup`.
