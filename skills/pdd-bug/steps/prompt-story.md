# prompt-story

- Read the pdd-prompting skill's guide.md in full first.
- Find the prompt that owns the behavior. Change it only if it is wrong or incomplete.
- In the Story, state the correct behavior and what must not change.
- Keep the bug input as a case in `tests/<story>.json`. Take its expected result from the requirement, not from the code. Add nearby edge and unaffected cases there.
- If a criterion is a precise rule (money, limits, permissions, state order), add it to the Story under `## Rules to check`, in plain words, with its forbidden result.
- PR 1 holds only the prompt, the Story and `tests/*.json`. Repo tests that fail on today's code go to PR 2 (build).
