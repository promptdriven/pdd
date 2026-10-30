# Use the new command names

I can run `pdd test`, `pdd lint`, `pdd simulate` (short: `pdd sim`) and `pdd workflow start`. My old commands still work, and each one tells me its new name.

## Acceptance criteria

1. `pdd --help` lists `pdd test`, `pdd lint`, `pdd simulate` and `pdd workflow start`, never says "pdd check", "pdd try" or "workflow run", prints nothing to stderr and exits with code 0.
2. `pdd test --help` lists the `pdd test` forms with --read, --retry, --fill-hash, --files and --screen, prints nothing to stderr and exits with code 0.
3. `pdd lint --help` lists the `pdd lint` forms, including `pdd lint --local`, prints nothing to stderr and exits with code 0.
4. `pdd check --help` prints the `pdd test` help to stdout, prints one notice line to stderr that names `pdd check` and `pdd test`, and exits with code 0.
5. `pdd check --lint --help` prints the `pdd lint` help to stdout, prints one notice line to stderr that names `pdd check --lint` and `pdd lint`, and exits with code 0.
6. `pdd try --help` prints the `pdd simulate` help to stdout, prints one notice line to stderr that names `pdd try` and `pdd simulate`, and exits with code 0.
7. `pdd workflow run --help` prints the `pdd workflow start` help to stdout, prints one notice line to stderr that names `pdd workflow run` and `pdd workflow start`, and exits with code 0.
8. `pdd workflow start 81` tells me on stderr to name the workflow with `pdd workflow start small-change 81`, prints nothing to stdout and exits with code 2.
9. `pdd workflow run 81` still prints only "Name the workflow: pdd workflow run small-change 81 (or bug, feature). See pdd workflow list." to stderr, with no notice, prints nothing to stdout and exits with code 2.
10. `pdd test --bogus` and `pdd check --bogus` each print a usage error to stderr, with no notice and no "Unknown command", print nothing to stdout and exit with code 2.
11. `pdd sim --help` prints the `pdd simulate` help to stdout, prints nothing to stderr and exits with code 0.

## What must not change

Each old name runs the same code as today, with the same options, effects, exit codes and stdout bytes. The notice goes only to stderr, so `--json` output and `pdd mcp` stdout stay exact. MCP tool names, workflow step names, `pdd run` and the next-step hints that name old commands stay as they are.

## Rules to check

`pdd test`, `pdd lint`, `pdd simulate` and `pdd workflow start` run the same code as `pdd check`, `pdd check --lint`, `pdd try` and `pdd workflow run`, with the same options. `pdd test` keeps --read, --retry, --fill-hash, --files, --screen, --timeout, --max-calls, --details and --json. `pdd lint` takes --local and the lint options. `pdd test --lint` works like `pdd lint` and prints no notice. Forbidden: an old name that changes its options, effects or exit code, or a new refusal for `pdd test --lint`.

An old name prints its notice once, on stderr, after a good parse and before any other line, also for its help. Forbidden: the notice on stdout, the notice twice, the notice on a parser usage error (exit 2 before the command runs) or the notice for a new name. A later refusal by the command itself may follow the notice.

Help and shell completion show only the new names. Old names still parse. Forbidden: an old name in `pdd --help`, in a help form or in the completion choices.

`pdd sim` is the short form of `pdd simulate`: the same code, and no notice. Forbidden: a notice for `pdd sim`, or a different result from `pdd simulate`.

The new words are data in one place, so a later rename is one edit. The test file checks help, notices and usage errors. The same code, the stdout of `--json` and `pdd mcp`, and completion need Node tests in the code area.
