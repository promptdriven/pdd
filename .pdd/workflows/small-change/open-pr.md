# Prepare one reviewable change

Show the diff, scope, owning prompt if changed, focused test results and rollback. Let the person review locally or request a branch/PR using normal Git/GitHub tools. Publish only when requested and under repository rules.

No separate prompt PR, private publisher or automatic PR gate is required. If the edit grows beyond the agreed impact, explain that before proceeding.

In `pdd workflow run`, this listed PR step is executed by the local runner using real Git push and GitHub PR creation. Starting the workflow authorizes its defined PR effects; optional prompt PR selection still requires the recorded choice. The native agent must not publish a duplicate PR. The runner requires a clean committed topic branch and records the actual URL/head; uncertain delivery is reconciled without blind repetition. Manual use retains the publication request described above.
