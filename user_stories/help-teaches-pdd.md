# Learn PDD from pdd help

I can run `pdd help` and see where the Prompting guide and the RUNBOOK are on my disk. I can run `pdd help prompting` and see, in a few short lines, how to write a prompt, a Story and its test, which commands check them and where to read more. I need no network and no PDD skills for this.

## Acceptance criteria

1. `pdd`, `pdd --help`, `pdd -h` and `pdd help` each name `pdd help prompting` and the full paths of the installed Prompting guide (`docs/prompting-guide.md`) and RUNBOOK (`RUNBOOK.md`), print nothing to stderr and exit with code 0.
2. `pdd help prompting` shows how to write a prompt file, `prompts/NAME.prompt.md`, with its `## Dependencies` section and its Runtime interface block, prints nothing to stderr and exits with code 0.
3. `pdd help prompting` shows how to write a Story file, `user_stories/STORY.md`, with its numbered acceptance criteria, and the Story's test file, `tests/STORY.json`, and exits with code 0.
4. `pdd help prompting` names the commands `pdd test`, `pdd lint` and `pdd approve`, and exits with code 0.
5. `pdd help prompting` names the full paths of the installed `docs/prompting-guide.md` and `RUNBOOK.md`, and exits with code 0.
6. `pdd prompting` is still an unknown command: it prints nothing to stdout, prints one line to stderr that says "Unknown command" and names `prompting`, and exits with code 2.
7. `pdd --help` and `pdd help prompting` never name a removed command ("pdd check", "pdd try" or "workflow start") and exit with code 0.

## What must not change

Root help keeps its first line, every help-form line in its order and the three closing lines. Only the help-form line of `pdd help prompting` and the three Learn PDD lines are new. `pdd WORDS --help`, such as `pdd test --help`, prints the same lines as before. `pdd help check` and `pdd help try` still print only the removal line and exit with code 2. Other unknown commands still exit with code 2. `pdd --version` still prints only the version.

## Rules to check

The two paths are full paths in the installed pdd package: the folder that holds the package.json of the pdd that runs, then `docs/prompting-guide.md` or `RUNBOOK.md`. Both files ship in the package. Forbidden: a relative path, a path in my repo or in the current folder, a web link, or a path to a file that does not exist.

Help is local. `pdd help` and `pdd help prompting` work with no network, no gh login, no runner and no PDD skills installed. Forbidden: a sign-in, a network or interpreter call, a PATH probe, a skill check or a written file.

`prompting` is a help topic, not a command. Forbidden: `pdd prompting` that runs something or prints help, and `pdd help prompting` with another word after it that prints the topic (it exits with code 2).

The new lines name only current commands. Forbidden: "pdd check", "pdd try" or "workflow start" in a help line.

The PDD interpreter cannot know the folder where pdd is installed. So the test file checks that the help names `/docs/prompting-guide.md` and `/RUNBOOK.md`. The code area adds Node tests: both paths are absolute and exist on disk, help works with no network and no PDD skills, and `pdd help prompting` with another word exits with code 2.
