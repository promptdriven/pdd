# prompt-story

- Read the pdd-prompting skill's guide.md in full first.
- Find the prompt that owns the behavior. Change it only if it is wrong or incomplete. Change one prompt when you can. If none exists, write the SMALLEST prompt that owns only the issue's behavior (one function or one endpoint), not the whole module.
- Write the Story in the person's words, with no function calls or type names: the correct behavior and what must not change.
- Give each rule one owner prompt. For a CLI, that is the whole-CLI prompt or one module's prompt: say which.
- Keep the bug input as a case in `tests/<story>.json`. Take its expected result from the requirement, not from the code. Write cases only for the issue's criteria.
- If a criterion is a precise rule (money, limits, permissions, state order), add it to the Story under `## Rules to check`, in plain words, with its forbidden result.
- PR 1 holds only the prompt, the Story and `tests/*.json`. Repo tests that fail on today's code go to PR 2 (build). Keep PR 1 under about 200 lines for a small change.
