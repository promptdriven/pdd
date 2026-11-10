# Set up project agent instructions and .pdd Git ignore through Runtime ports

I can update the project's agent instruction block in `CLAUDE.md` or `AGENTS.md` and keep `.pdd/` ignored in `.gitignore` through declared blob operations.

```pdd-boundary
prompts/cli/project-setup.prompt.md
```

## Acceptance criteria

1. `setupProject` updates the `pdd:start` to `pdd:end` marker block in `CLAUDE.md` under `cwd` when present (preserving surrounding text and dropping `RUNBOOK.md` lines when `RUNBOOK.md` under `packageRoot` does not exist), and creates `AGENTS.md` under `cwd` when neither file exists.
2. `setupProject` fails with `invalid_pdd_markers` without writing when the target file has reversed or duplicate marker lines.
3. `ignorePddFolder` appends `.pdd/` to `.gitignore` under `root` when no `.pdd` rule is present, returns `changed: false, negated: true` without writing when a negation rule such as `!.pdd/config.json` is present, and fails with `invalid_gitignore_target` when `.gitignore` under `root` is a symlink.
