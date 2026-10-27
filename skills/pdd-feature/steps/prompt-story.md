# prompt-story

- Read the pdd-prompting skill's guide.md in full first.
- Write or update the module prompt: purpose, inputs, results, errors and limits.
- Write a Story with criteria that a person can see.
- Write test cases in `tests/<story>.json` with inputs and expected results from the Story. Map each case to a criterion.
- If a criterion is a precise rule (money, limits, permissions, state order), add it to the Story under `## Rules to check`, in plain words, with its forbidden result.
- PR 1 holds only the prompt, the Story and `tests/*.json`. Repo tests that fail on today's code go to PR 2 (build).
