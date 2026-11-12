# Stop a simulation with its Story path

As a person trying my app, I want to stop the simulation with the Story path that started it or its short name, so that I can close the session promptly.

## Acceptance criteria

1. After I start a simulation with `pdd simulate user_stories/rehearsal/control-panel.md`, `pdd simulate --stop user_stories/rehearsal/control-panel.md` stops that saved simulation, prints `The Try link for "Control panel rehearsal" is stopped.`, and exits 0.
2. For the same saved simulation, `pdd simulate --stop control-panel` also stops it, prints the same confirmation, and exits 0.
3. The saved test path `tests/rehearsal/control-panel.json` and test name `control-panel` still identify the simulation. A stop also works on a branch where the original Story file is absent. With one saved simulation, `pdd simulate --stop` still stops it.
4. A stop removes only the selected saved simulation after the service confirms the stop. A DELETE response of 404 or 410 also counts as confirmation. An unconfirmed stop keeps the saved record and returns a nonzero exit. An unknown or ambiguous selector stops nothing and exits 2.

## Must not change

Keep existing short Story names, saved test paths, test basenames and no-argument selection with one saved simulation. Keep stopping when the Story file is absent, unique selection before authentication or a stop request, confirmed removal of only the selected saved record, and the owner's existing unknown-session recovery.

## Rules to check

The exact saved repository-relative Story path and the existing short name must identify the same simulation. Stop selection uses saved records, without requiring the Story file to exist on the current branch. Selection must be unique before authentication or a stop request. Confirmation must precede removal of the selected record; other saved records must stay unchanged. Never print a success confirmation or remove the record for an unconfirmed stop.

## Cases and Runtime boundary

[Synthetic native draft cases](../test/runtime/stop-simulation-by-story-path-cases.json) hold the issue-derived expectations and preservation controls. They require review before code work. They are not executable Runtime scenarios or completed native tests.

The owner is [Runtime client](../prompts/cli/runtime-client.prompt.md). Its real public `runTry` boundary has no Runtime interface. Git repository lookup, private saved-state files and their writes are native and unbound. The existing injected transport, authentication, clock and UUID ports can supply deterministic replies for native tests; they do not make the complete module executable on the interpreter. No interpreted prompt verdict or native replay pass is claimed.

This Story adds the exact saved repository-relative Story path to the stop selectors. It makes no new rule for absolute paths, path normalization or legacy records that have no saved Story path. The owner's existing unknown-session recovery and other simulation rules remain in force.
