# prompt-story

- Read the pdd-prompting skill's guide.md in full first.
- Write or update the prompt that owns the behavior: purpose, inputs, results, errors and limits. If none exists, write the SMALLEST prompt that owns only the issue's behavior (one function or one endpoint), not the whole module.
- Write a Story with criteria that a person can see.
- Write test cases in `tests/<story>.json` with inputs and expected results from the Story, cases only for the issue's criteria. Map each case to a criterion.
- If a criterion is a precise rule (money, limits, permissions, state order), add it to the Story under `## Rules to check`, in plain words, with its forbidden result.
- PR 1 holds only the prompt, the Story and `tests/*.json`. Repo tests that fail on today's code go to PR 2 (build). Keep PR 1 under about 200 lines for a small change.
