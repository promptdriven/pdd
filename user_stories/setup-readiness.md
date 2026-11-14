# Check whether a folder is ready

As a program managing a project folder, I want to check setup, so that I can decide whether the folder needs setup.

## Acceptance criteria

1. `pdd setup --check --json` prints `{"ready":true}` and exits 0 when the current project has its current PDD block and its Git root ignores `.pdd/` or has a respected negation that setup preserves.
2. `pdd setup --check --json` prints `{"ready":false}` and exits 0 when the block or ignore handling still needs setup; checking changes no file and starts no setup, authentication, agent status or network work.
3. `pdd setup --check` prints `Ready` or `Not ready` for the same conditions; `--json` without `--check` and `--check` combined with `--yes`, `--no-pair` or `--pair-code` exit 2 before setup effects.

```pdd-boundary
prompts/cli/pdd-cli.prompt.md
prompts/cli/interpreter-version.prompt.md
```

## Verification boundary

The Runtime scenario checks CLI routing using injected setup ports. Native tests must establish real file bytes, Git ignore handling and absence of external effects.
