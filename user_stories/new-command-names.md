# Use one name for each command

I can run `pdd test`, `pdd lint`, `pdd simulate` (short: `pdd sim`) and `pdd workflow run`. When I type an old name, `pdd check` or `pdd try`, pdd runs nothing and tells me the new name in one line.

## Acceptance criteria

1. `pdd --help` lists `pdd test`, `pdd lint`, `pdd simulate` and `pdd workflow run`, never says "pdd check", "pdd try" or "workflow start", prints nothing to stderr and exits with code 0.
2. `pdd test --help` lists the `pdd test` forms with --read, --retry, --fill-hash, --files and --screen, prints nothing to stderr and exits with code 0.
3. `pdd lint --help` lists the `pdd lint` forms, including `pdd lint --local`, prints nothing to stderr and exits with code 0.
4. `pdd check --help` prints nothing to stdout, prints one line to stderr that names `pdd check` and `pdd test`, and exits with code 2.
5. `pdd check --lint --help` and `pdd check new-command-names --lint` each print nothing to stdout, print one line to stderr that names `pdd check --lint` and `pdd lint`, and exit with code 2.
6. `pdd try --help` prints nothing to stdout, prints one line to stderr that names `pdd try` and `pdd simulate`, and exits with code 2.
7. `pdd help check` and `pdd help try` each print nothing to stdout, print one line to stderr that names the old and the new command, and exit with code 2.
8. `pdd check new-command-names --json`, `pdd check --bogus` and `pdd try new-command-names --new` each print nothing to stdout, print one line to stderr that names the old and the new command, and exit with code 2.
9. `pdd workflow run --help` prints the `pdd workflow run` help to stdout, prints nothing to stderr and exits with code 0.
10. `pdd workflow start --help` prints the same `pdd workflow run` help to stdout, never says "workflow start", prints nothing to stderr and exits with code 0.
11. `pdd workflow run 81` still prints only "Name the workflow: pdd workflow run small-change 81 (or bug, feature). See pdd workflow list." to stderr, prints nothing to stdout and exits with code 2.
12. `pdd workflow start 81` prints only the same line, "Name the workflow: pdd workflow run small-change 81 (or bug, feature). See pdd workflow list.", to stderr, prints nothing to stdout and exits with code 2.
13. `pdd test --bogus` prints a usage error to stderr, with no "Unknown command" and no "was removed", prints nothing to stdout and exits with code 2.
14. `pdd sim --help` prints the `pdd simulate` help to stdout, prints nothing to stderr and exits with code 0.

## What must not change

`pdd test`, `pdd lint` and `pdd simulate` keep every option, effect, exit code and stdout byte that they have today. `pdd test` keeps --read, --retry, --fill-hash, --files, --screen, --timeout, --max-calls, --details and --json, and with no Story it tests every Story. `pdd simulate` keeps --cli, --shell, --serve, --save-last, --stop, --tab, --app-map, --new, --no-open, --no-wait, --agent and --max-calls. The machine-read words keep `check` and `try`: the wire commands, the `/v1/try/…` paths, the `.pdd/try` folder, saved records and the workflow step names `check` and `try`. A server text that pdd prints as it got it stays as the server sent it, even when it names an old command. The MCP tool names of `pdd mcp` stay as they are.

## Rules to check

`pdd check` and `pdd try` are removed. Any input with them, with any options, help flags, unknown options, or after `pdd help`, exits with code 2, prints nothing to stdout and prints exactly one line to stderr. The line names the old and the new command: `pdd test`, or `pdd lint` when `--lint` is one of the options of `pdd check`, or `pdd simulate`. It runs nothing: no help, no sign-in, no file read, no interpreter call and no saved state. Forbidden: help on stdout, a second line, a usage error about another option, "Unknown command", an alias that still runs the old name, or any work before the refusal.

`pdd sim` and `pdd workflow start` are quiet forms of `pdd simulate` and `pdd workflow run`: the same plan and the same result, with no extra line. Help and shell completion show only `pdd test`, `pdd lint`, `pdd simulate` and `pdd workflow run`. `pdd test --lint` still works like `pdd lint`, and `--lint` and `--local` stay hidden on `pdd test`. Forbidden: a notice for a quiet form, a different result from the main name, `workflow start`, `check` or `try` in help or completion, or a new refusal for `pdd test --lint`.

No line that pdd prints names `pdd check` or `pdd try`, except the removal line. This covers next-step hints, errors, progress lines, status lines, PR text and the guide text. Forbidden: `Read the results later with: pdd check --read BATCH`, `Run pdd try <story> --new` or `pdd try:` in a line that pdd writes.

The new words are data in one place, so a later rename is one edit. The test file checks help, removal lines, quiet forms and usage errors. That nothing runs, completion and the hint lines need Node tests in the code area.
