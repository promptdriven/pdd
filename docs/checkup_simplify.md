# `pdd checkup simplify`

Conservative code cleanup via **Claude Code's bundled `/simplify`** skill. Claude's skill runs three review agents, aggregates findings, and applies quality and efficiency fixes. PDD can sample independent results and copy a conservatively selected verified candidate back to your working tree.

## Requirements

- A Claude Code release that provides the bundled `/simplify` skill
- A git repository with selected changed code: local/staged changes, or committed branch changes selected with `--since REF`

Install or update:

```bash
npm install -g @anthropic-ai/claude-code
claude update
claude --version
```

## Usage

```bash
# Preview files in scope (no Claude invocation)
pdd checkup simplify
pdd checkup simplify --since HEAD~1

# Run Claude Code /simplify (edits working copy)
pdd checkup simplify --apply
pdd checkup simplify --apply pdd/foo.py --verify
pdd checkup simplify --apply --since origin/main --attempts 3 --verify --evidence
```

**`--apply` is required** to invoke `/simplify`. Without it, PDD only lists eligible targets.

`--apply` runs each attempt in a detached temporary worktree created from the
same input state (attempts run sequentially today). Claude cannot overwrite unrelated local edits. PDD rejects
any candidate that writes outside the selected files, prefers candidates whose
`--verify` checks pass, and among those copies back the candidate affecting the
fewest selected files. Backups
are written to `.pdd/backups/simplify-<run_id>/`; candidate snapshots and the
selection report are retained under `.pdd/evidence/checkups/simplify-<run_id>/`.

## Git scope

Claude Code `/simplify` operates on a diff. PDD builds that diff in each
candidate worktree from the selected input files:

| PDD flag | Effect |
|----------|--------|
| `--since REF` | Selects changed files and uses `REF` as candidate baseline; use this for committed branch or PR changes |
| `--staged` | Limits to staged paths |
| `[path]` | Limits to a file or directory |
| `--attempts N` | Generates `N` independent candidates from the same baseline |

Without `--since`, selected files must have a local diff against `HEAD`.
`--apply --staged` refuses selected files that also have unstaged edits, so a
candidate never replaces work outside the staged snapshot.
`--attempts` greater than 1 requires `--verify` so PDD can reject unproven
candidates. Verification scoping is command-type aware:

- **format / lint** (for example `ruff format`, `ruff check`): append only the
  in-scope paths (`ruff format -- pdd/foo.py`).
- **typecheck** (`mypy`): run against the explicit changed files with
  `--follow-imports=skip` instead of `mypy pdd -- pdd/foo.py`.
- **test** (`pytest`): run colocated tests when discoverable (for example
  `pdd/checkup_simplify.py` → `tests/commands/test_checkup_simplify.py`);
  otherwise the configured pytest command is left unchanged for explicit user
  control.

`[tool.pdd.checkup.simplify]` defaults are loaded from the repository root, not
the current working directory, so invocations from subdirectories still honor
`max_files`, `attempts`, and `commands`.

## Evidence

With `--evidence`, writes `.pdd/evidence/checkups/simplify-<run_id>.json` including `engine`, `slash_command`, `claude_code_version`, and digest-detected `files_modified`.

## Configuration

Optional `[tool.pdd.checkup.simplify]` in `pyproject.toml`:

```toml
[tool.pdd.checkup.simplify]
max_files = 20
attempts = 3
focus = "focus on error handling"

[tool.pdd.checkup.simplify.commands]
format = "ruff format"
lint = "ruff check"
typecheck = "mypy pdd"
test = "pytest -q"
```

The `focus` string is appended to the `/simplify` invocation (for example,
`/simplify focus on error handling pdd/foo.py`). `CLAUDE_MODEL` may select a
less expensive Claude model; `--attempts` is the sampling mechanism when you
want several chances and a verified winner.

## Demo

Run the no-network demonstration, which stubs Claude's response while using the
real isolation, candidate selection, and evidence code paths:

```bash
python examples/checkup_simplify_example.py
```

Reference: [Claude Code command documentation](https://code.claude.com/docs/en/commands).

## Multi-provider profiles (reference)

The shipped command still uses Claude Code `/simplify` only. For Codex, Gemini, OpenCode, or IDE
agents that should follow the same conservative workflow, see
[checkup_simplify_providers.md](checkup_simplify_providers.md) and
`pdd/prompts/checkup_simplify_workflow_LLM.prompt`.
