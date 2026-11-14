# Set up a folder unattended

As a program managing a project folder, I want unattended setup, so that no person needs to visit the terminal.

## Acceptance criteria

1. `pdd setup --yes --no-pair` sets up a new folder without a prompt or pairing code, including when there is no terminal.
2. The same command in a ready folder exits 0 without changing any file or starting skill, authentication or pairing work.

```pdd-boundary
prompts/cli/pdd-cli.prompt.md
prompts/cli/interpreter-version.prompt.md
```

## Verification boundary

The Runtime scenario checks CLI routing using injected setup ports. Native tests must establish real file bytes, Git ignore handling and absence of external effects.
