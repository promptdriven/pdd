# Prepare a separate prompt PR only if requested

If the person wants a separate prompt review, prepare a diff containing the prompt, Story and independent expected cases. Explain the behavior, compatibility and remaining questions. Otherwise keep these with the implementation in one change and continue.

In manual use, publish a branch or PR only when requested, using the person's normal Git/GitHub tools and repository rules. Reading this manual step alone does not publish anything. Do not add a separate prompt PR merely to satisfy a stage marker.

In `pdd workflow run`, this listed PR step is executed by the local runner using real Git push and GitHub PR creation. Starting the workflow authorizes its defined PR effects; optional prompt PR selection still requires the recorded choice. The native agent must not publish a duplicate PR. The runner requires a clean committed topic branch and records the actual URL/head; uncertain delivery is reconciled without blind repetition. Manual use retains the publication request described above.
