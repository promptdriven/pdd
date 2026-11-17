# Find commands and learn PDD from help

As a developer new to PDD, I want a short overview and help for the command I pick, so that I can get started without signing in or searching online.

## Acceptance criteria

1. `pdd`, `pdd --help`, `pdd -h` and `pdd help` each name `pdd help prompting` and the full paths of the installed Prompting guide (`docs/prompting-guide.md`) and RUNBOOK (`RUNBOOK.md`), print nothing to stderr and exit with code 0.
2. `pdd help prompting` shows how to write a prompt with `## Dependencies`, a Story with numbered acceptance criteria, and its test; it exits with code 0 and no stderr.
3. `pdd --help` opens with usage and starting examples, groups commands by purpose, and points to focused help rather than listing options like `--share` or approval examples.
4. `pdd help prompting` names `pdd test`, `pdd lint` and `pdd approve` and the full installed guide and RUNBOOK paths.
5. `pdd help autopilot` lists `pdd autopilot start`, and `pdd autopilot start --help` explains the `--share` range and default. `pdd help approve` shows the quoted `--said -` heredoc. All three exit with code 0 and no stderr.
6. `pdd prompting` is still an unknown command: it prints nothing to stdout, prints one line to stderr that says "Unknown command" and names `prompting`, and exits with code 2.

## What must not change

- Command names, options, defaults and what commands do stay the same. Removed commands still refuse to run; they do not appear in help.

## Rules to check

- Help never signs in, runs a command or modifies a file. The guide paths lead to the installed files, not the current checkout.

```pdd-boundary
prompts/cli/pdd-cli.prompt.md
prompts/cli/argument-parser.prompt.md
prompts/cli/command-catalog.prompt.md
prompts/cli/interpreter-version.prompt.md
```
