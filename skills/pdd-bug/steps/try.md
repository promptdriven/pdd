# try

Budget a simulation for all planned interactions: reserve at least 3 times the worst-case total for those moves, their child calls and redraws. Set that ceiling with `pdd simulate STORY --max-calls N`; only calls that run are charged.

If the pdd-prompting skill has a RUNBOOK.md, run `pdd simulate STORY` as it says and give the person the Simulator link before the gate. Otherwise:
- If the repo has a safe local preview or demo, show the bug in it.
- Report what ran and what you saw. A link or a mockup is not a try.

To try a CLI, run `pdd simulate <story> --cli`, then run the command.
