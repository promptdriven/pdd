# Autopilot Universal Validator

As a repository maintainer running Autopilot,
I want every runtime change validated by real end-to-end execution with fail-closed gates and clear handling for external tool outages,
so that broken or unverified pull requests are never merged or marked ready to merge, and unavailable logins do not burn repair loops or block unrelated issues.

## Acceptance criteria

1. A runtime change with passing offline checks and passing real end-to-end execution is eligible to merge in auto mode or be marked would-merge in observe mode with recorded proof, and a documentation-only change needs no end-to-end run.
2. A runtime change whose real end-to-end check fails, or a bug fix whose regression check already passes on the base revision, stays unmerged and enters repair up to a maximum of three attempts before escalating for a person.
3. When an external tool or login is expired or unavailable, or no live runtime binding is available, validation stops with zero repair attempts, keeps the pull request open, parks it waiting for a person with the tool name and exact check command, frees the worker slot, and places that tool on cooldown.
4. While a tool is on cooldown, Autopilot skips claiming other issues that require that tool while still claiming unrelated issues, and once a health check succeeds or a person clears the wait, Autopilot resumes only the missing validation on the saved pull request head without rebuilding code.
5. When a change needs live human interaction or has no runnable end-to-end check, Autopilot stops and parks the pull request for a person in both auto and observe modes, frees the worker slot, and emits a three-line human verification card.
6. Validation linting flags silent validation skips and mock-only tests covering runtime boundaries, while passing boundary tests paired with real end-to-end coverage.

## Rules to check

- Never treat a documentation-only shortcut as valid for runtime code changes.
- Never allow a pull request to merge or be marked would-merge when required real end-to-end checks did not run and pass in full, in either auto or observe mode.
- Never spend repair attempts on an expired login, missing external tool, or unavailable live binding.
- Never rebuild code when resuming a parked pull request whose head revision has not changed.
