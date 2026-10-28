# prompt-story

- First read the pdd-prompting skill's guide.md in full and its RUNBOOK.md §2–§4. Copy the RUNBOOK examples: `prompts/<name>.prompt.md` with a Runtime interface block, and `tests/<story>.json`. Runtime tests are not the repo's unit tests; the code area adds those.
- Also read the RUNBOOK sections that fit: §6 for a CLI, §7 when one prompt calls another, §9 for money and dates, §13 for a screen and its app map. For tests, read §8 (check paths), §10 (AI-call budget: over it, a test is refused at 0 calls) and §18 (ONE call for a whole move list, never 30 in a row).
- Find the prompt that owns the behavior. Change it only if it is wrong or incomplete. Change one prompt when you can. If none exists, write the SMALLEST prompt that owns only the issue's behavior (one function or one endpoint), not the whole module.
- Write the Story in the person's words: the correct behavior and what must not change.
- Keep the bug input as a case in `tests/<story>.json`, with its expected result from the requirement, not from the code. Write cases only for the issue's criteria.
- Put a precise rule (money, limits, permissions, state order) in the Story under `## Rules to check`, with its forbidden result.
- PR 1 holds only the prompt, the Story and `tests/*.json`, under about 200 lines for a small change. Repo tests that fail on today's code go to PR 2, so merging PR 1 never turns main red.
