# Test slice: clear-messages

1. Install the test tarball into a clean prefix: `PREFIX=$(mktemp -d) && npm install -g --prefix "$PREFIX" ./pdd-0.1.0.tgz`.
2. In a real TTY, run `$PREFIX/bin/pdd workflow run 81`; it prints `Name the workflow: pdd workflow run small-change 81 (or bug, feature). See: pdd workflow list.` and exits 2.
3. With an older `pdd` executable first on `PATH`, run `$PREFIX/bin/pdd --version`; 0.1.0 prints one stderr line, `Another pdd is first on PATH: PATH_TO_OLDER_PDD`, then prints `0.1.0` and keeps normal dispatch.
4. Start a workflow for an issue that already has a saved run, then repeat the command. The refusal names the run, workflow, stage, state and age and prints `pdd workflow resume RUN_ID --decision approve`; 0.1.0 does not offer `--replace`.
5. Roll back by deleting the clean prefix: `rm -rf "$PREFIX"` (the package install is isolated and does not modify the source checkout).
