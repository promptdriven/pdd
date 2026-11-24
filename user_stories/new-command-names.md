# Use one name for each command

As a developer using PDD in the terminal, I want `pdd test`, `pdd lint`, and direct `pdd <PROMPT.md|STORY|.>` execution while retired names (`check`, `try`, `simulate`, `sim`, `workflow`) refuse clearly, so that every command has one obvious form.

## Acceptance criteria

1. `pdd --help` lists `pdd <PROMPT.md|STORY|.>`, `pdd test`, and `pdd lint`, never says "pdd check", "pdd try", "pdd sim", "pdd simulate", or "Simulator", prints nothing to stderr, and exits with code 0.
2. `pdd test --help` lists the `pdd test` forms with `--read`, `--retry`, `--files`, and `--screen`, prints nothing to stderr, and exits with code 0.
3. `pdd lint --help` lists the `pdd lint` forms including `pdd lint --local`, prints nothing to stderr, and exits with code 0.
4. `pdd check`, `pdd check --lint`, `pdd try`, `pdd simulate`, `pdd sim` (with any options, help flags, or after `pdd help`) each print nothing to stdout, print one refusal line to stderr naming the removed command and replacement, and exit with code 2 without side effects.
5. `pdd test --bogus` prints a usage error to stderr with no "Unknown command" and no "was removed", prints nothing to stdout, and exits with code 2.
6. `pdd prompts/app.prompt.md`, `pdd .`, `pdd --product`, and `pdd --stop` parse directly to the Prompt Interpreter without a subcommand, while typos like `pdd statis` exit with code 2 and `Unknown command "statis"`.

## What must not change

`pdd test`, `pdd lint`, and direct `pdd <PROMPT.md|STORY|.>` keep every supported option, effect, exit code, and wire contract (`check` and `try` wire commands, `/v1/try/...` paths, `.pdd/try` folder, scenario `"simulation"` keys, and `try_*` MCP tool names). `pdd test --lint` still works like `pdd lint` with `--lint` and `--local` hidden on `pdd test`.

## Rules to check

- Retired names (`check`, `check --lint`, `try`, `simulate`, `sim`, `workflow`) run nothing before refusing with exit 2 and one stderr line. Forbidden: help on stdout, a second line, a usage error about another option, "Unknown command", or any alias that still runs a removed name.
- No user-facing line that pdd writes itself names `pdd check`, `pdd try`, `pdd sim`, `pdd simulate`, or "Simulator", except the removal lines.
- Core command names (`test`, `lint`, `run`) live in one shared table (`NAMES`).
