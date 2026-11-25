# Prove diff coverage split and formal mutation control

As a developer verifying a branch with `pdd prove`, I want opt-in `--coverage` and `--mutation-check` flags, so that I see diff-line coverage split across formal, vector, and full suites and catch surviving guard mutations without changing my working tree.

## Acceptance criteria

1. `pdd prove --coverage --base main --json` reports per-file and diff-line coverage split across `formal`, `vectors`, and `all` suites, exposing uncovered diff lines and formal-only vs. vector-only counts without altering default zero-flag `pdd prove` behavior.
2. `pdd prove --coverage --base main --json` parses unified diff hunks into added production line numbers and reports unimported touched production files as `0%` uncovered rather than hiding them.
3. `pdd prove --mutation-check --base main --json` selects 1 to 3 deterministic guard mutations prioritizing formal-covered guards and exits with code `0` (`Proved`) when the formal suite kills every mutation with a real assertion failure.
4. `pdd prove --mutation-check --base main --json` exits with code `3` (`Not proved`) and names the surviving guard when a formal-covered guard mutation survives the formal suite, ignoring syntax-only crashes as non-kills.
5. Running `pdd prove --coverage` or `pdd prove --mutation-check` (including when interrupted) runs strictly in an isolated temporary copy, writes zero files in the repository working tree, and leaves all working-tree files byte-identical.
6. Combining `--coverage` or `--mutation-check` with `--test` or `--expect` prints one usage error line to stderr, writes nothing to stdout, runs no tests, and exits with code `2`.

## Rules to check

- Forbidden: modifying or creating files inside the caller's repository working tree during `--coverage` or `--mutation-check`.
- Forbidden: counting a syntax, import, or compile crash as a killed mutation, or exiting `0` (`Proved`) when a formal-covered guard mutation survives.
- Forbidden: altering default zero-flag `pdd prove` output, JSON keys, or exit codes when neither `--coverage` nor `--mutation-check` is passed.

## What must not change

- Default `pdd prove [--base REF] [--timeout MIN] [--json]` and bug-contrast `pdd prove --base REF --test CMD --expect TEXT` keep their existing behavior and exit codes.
