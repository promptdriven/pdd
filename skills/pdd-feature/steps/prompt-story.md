# prompt-story

- First read the pdd-prompting skill's guide.md in full and its RUNBOOK.md §2–§4. Copy the RUNBOOK examples: `prompts/<name>.prompt.md` with a Runtime interface block, and `tests/<story>.json`. Runtime tests are not the repo's unit tests; the code area adds those.
- Also read the RUNBOOK sections that fit: §6 for a CLI, §7 when one prompt calls another, §9 for money and dates, §13 for a screen and its app map. For tests, read §8 (check paths), §10 (AI-call budget: over it, a test is refused at 0 calls) and §18 (ONE call for a whole move list, never 30 in a row).
- Write or update the prompt that owns the behavior. Change one prompt when you can. If none exists, write the SMALLEST prompt that owns only the issue's behavior (one function or one endpoint), not the whole module.
- Write every Story in `user_stories/PLAN.md`, each with its own `tests/<story>.json`, in the person's words. Exact data (seeds, long boards) goes in the tests; the Story says it in plain words.
- If visual wrote an app map, write the prompts it names, and put its SVG in the screen prompt's `## Appearance`.
- Write cases only for the issue's criteria. Put a precise rule (money, limits, permissions, state order) in the Story under `## Rules to check`, with its forbidden result.
- PR 1 holds only the prompt, the Story and `tests/*.json`, under about 200 lines for a small change. Repo tests that fail on today's code go to PR 2, so merging PR 1 never turns main red.
