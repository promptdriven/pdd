# plan

Review the map, boundaries, contracts, planned prompts and run order together.
Verify that every part crossing real HTTP, auth, database, CLI/OS or browser I/O
plans its thin native-boundary adapter prompt(s) and startup entrypoint alongside
its fake-port domain prompt(s), and that headless parts carry no UI screens.
Each run must name its Stories, part, slice and needs. Show which runs can start
in parallel. Put the files in the plan PR and state the open questions. Keep the
small path's PR to the map. After the PR, give `pdd product next`; normal feature
runs do the building. Do not start all runs automatically.
