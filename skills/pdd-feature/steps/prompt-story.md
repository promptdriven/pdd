# prompt-story

- Before you write a prompt or a test file, read RUNBOOK.md §2–§4 (in the pdd-prompting skill): prompts are `prompts/<name>.prompt.md` with a Runtime interface block; tests are `tests/<story>.json` in the runtime's test format. Copy its example.
- Read the pdd-prompting skill's guide.md in full first.
- Write or update the prompt that owns the behavior: purpose, inputs, results, errors and limits. Change one prompt when you can. If none exists, write the SMALLEST prompt that owns only the issue's behavior (one function or one endpoint), not the whole module.
- Write every Story in `user_stories/PLAN.md`, each with its own `tests/<story>.json` (one Story when there is no plan). Write each Story in the person's words, with no function calls or type names: criteria that a person can see.
- Exact data (seeds, long boards) goes in the tests; the Story says it in plain words.
- Give each rule one owner prompt. For a CLI, that is the whole-CLI prompt or one module's prompt: say which.
- Write test cases in `tests/<story>.json` with inputs and expected results from the Story, cases only for the issue's criteria. Map each case to a criterion.
- If a criterion is a precise rule (money, limits, permissions, state order), add it to the Story under `## Rules to check`, in plain words, with its forbidden result.
- PR 1 holds only the prompt, the Story and `tests/*.json`. Repo tests that fail on today's code go to PR 2 (build). Keep PR 1 under about 200 lines for a small change.
