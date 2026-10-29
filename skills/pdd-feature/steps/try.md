# try

Budget a Try for all planned interactions: reserve at least 3 times the worst-case total for those moves, their child calls and redraws. Set that ceiling with `pdd try STORY --max-calls N`; only calls that run are charged.

If the pdd-prompting skill has a RUNBOOK.md, run `pdd try STORY` as it says (with an app map, add `--new`) for each Story the person wants to try, and give the person each Try link before the gate. Otherwise:
- If the repo has a safe local preview or demo, use it to show the plan.
- Report what ran and what you saw. A link or a mockup is not a try.

To try a CLI, run `pdd try <story> --cli`, then run the command.
