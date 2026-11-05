# See the results saved with each workflow step

I can inspect a workflow and see the results saved with each step, including when a step has none.

Issue: https://github.com/promptdriven/pdd/issues/2922

## Acceptance criteria

1. `pdd workflow status 2922` shows each step's saved pddResults and says "none" for a step without results.
2. `pdd workflow status 2922 --json` associates each step with its saved pddResults and explicitly represents a step without results.
3. `pdd workflow view 2922` shows each step's saved pddResults and says "none" for a step without results.

## Rules to check

A step with an absent results field and a step with an empty results list both have none. Results remain associated with their own step, including a step in an earlier area. Showing only run-wide results or a Story count must not hide the saved per-step results.

Keep existing status fields, grouping and refresh behavior, saved result formatting, and the passive local-read behavior of view. Agent notes remain separate from pdd's saved results.
