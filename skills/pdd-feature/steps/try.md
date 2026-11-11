# try

Budget a simulation for all planned interactions: reserve at least 3 times the worst-case total for those moves, their child calls and redraws. Set that ceiling for a new simulation with `pdd simulate STORY --max-calls N` (use `--new` to replace an open one); only calls that run are charged.

If the pdd-prompting skill has a RUNBOOK.md, run `pdd simulate STORY` as it says (with an app map, add `--new`) for each Story the person wants to try, and show the shell, localhost URL and example request, or Simulator link before the gate, as applicable. Otherwise:
- If the repo has a safe local preview or demo, use it to show the plan.
- Report what ran and what you saw. A link or a mockup is not a try.

`pdd simulate <story>` selects shell, localhost, Screen or Form. `pdd simulate` opens the whole project. `--page` forces the page; `pdd simulate <story> --cli` prints launcher/PATH without opening a shell.

In a normal run, pdd skips this step itself. In strict mode, if no person is there to try it, run `pdd workflow done try --skipped "REASON"`. Never write run files such as try.md by hand.

Try tools: `try_open`, `try_state`, `try_run`, `try_check`, `try_save_case` if asked. AI calls; Simulator history.
