# prompt-story

- First read the pdd-prompting skill's guide.md in full and its RUNBOOK.md §2–§4. Copy the RUNBOOK examples: `*.prompt.md` with a Runtime interface block; the Story's test file, `tests/<story>.json` (RUNBOOK §2 names the folder when the repo already has tests/). Runtime tests are not the repo's unit tests; the code area adds those, so merging PR 1 never turns main red.
- Also read the RUNBOOK sections that fit: §6 a CLI, §7 a prompt that calls another, §9 money and dates, §13 a page or screen. For tests: §8 check paths, §10 the AI-call budget (over it, a test is refused at 0 calls), §18 ONE call for a whole move list, never 30 in a row.
- Find the prompt that owns the behavior. Change it only if it is wrong or incomplete. Change one prompt when you can. If none exists, write the SMALLEST prompt that owns only the issue's behavior (one function or one endpoint; a CLI has one program prompt), not the whole module.
- Write the Story in the person's words: the correct behavior and what must not change.
- For a page, check what it shows through its `render` operation (`{html}` and the facts it shows), with `count` or `equals`. It is never "browser-only, no runtime test".
- Keep the bug input as a case in the Story's test file, with its expected result from the requirement, not from the code. Write cases only for the issue's criteria.
- Put a precise rule (money, limits, permissions, state order) in the Story under `## Rules to check`, with its forbidden result.
- PR 1 holds only the prompt, the Story and its runtime test files, under about 200 lines for a small change.
