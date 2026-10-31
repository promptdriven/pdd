# try

Budget a simulation for all planned interactions: reserve at least 3 times the worst-case total for those moves, their child calls and redraws. Set that ceiling with `pdd simulate STORY --max-calls N`; only calls that run are charged.

If the pdd-prompting skill has a RUNBOOK.md, run `pdd simulate STORY` as it says and show the shell, localhost URL and example request, or Simulator link before the gate, as applicable. Otherwise:
- If the repo has a safe local preview or demo, show the bug in it.
- Report what ran and what you saw. A link or a mockup is not a try.

Run `pdd simulate <story>` to automatically open a shell for a command-line program, localhost with an example request for HTTP routes, or the Simulator page for screens. Run `pdd simulate` for the whole project. Use `--page` to choose the page.

Use `pdd simulate <story> --cli` to print the launcher and PATH without opening a shell.
