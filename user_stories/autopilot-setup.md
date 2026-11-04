# Choose an Autopilot mode

As a repository maintainer, I can choose a mode during setup, so that the repository records my choice.

## Acceptance criteria

1. In a fresh Git repository, terminal setup with no mode answer saves off and an empty trust list.
2. A second terminal setup keeps off and makes no new mode save.
3. Setup without a terminal asks nothing and saves nothing.
4. Setup outside a Git repository asks nothing and saves nothing.

## Rules to check

- A failed file write reports a clear error, exits nonzero and leaves `pdd.json` unchanged. Native test: inject a failed write and inspect the original file.
- Setting a mode starts no run or interpreter. Native test: spy on workflow and interpreter dispatch.
