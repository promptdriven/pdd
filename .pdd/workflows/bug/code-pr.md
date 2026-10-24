# Prepare a code PR if requested

Show the implementation diff with the owning prompt, Story/cases and actual native test results. Explain limitations and a practical rollback. If prompt files already landed separately, link the accepted revision instead of silently changing it.

The person can review locally or request a branch/PR through normal Git/GitHub tools. Prepare the description first; publish only under that request and repository rules. Manual use has no automatic PR step; the local runner behavior is defined below. No private publisher is used.

In `pdd workflow run`, this listed PR step is executed by the local runner using real Git push and GitHub PR creation. Starting the workflow authorizes its defined PR effects; optional prompt PR selection still requires the recorded choice. The native agent must not publish a duplicate PR. The runner requires a clean committed topic branch and records the actual URL/head; uncertain delivery is reconciled without blind repetition. Manual use retains the publication request described above.
