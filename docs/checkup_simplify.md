# `pdd checkup simplify`

Conservative simplification pass over selected source files using the configured
agent provider (Claude Code, Codex, etc.).

## Usage

```bash
pdd checkup simplify [path] [--dry-run] [--apply] [--since REF] [--staged]
pdd checkup simplify --since HEAD~1 --evidence
pdd checkup simplify src/ --apply --verify
```

Default mode is **dry-run** (suggestions only). Use `--apply` to allow edits.

## Evidence

With `--evidence`, writes `.pdd/evidence/checkups/simplify-<run_id>.json`.

## Configuration

Optional `[tool.pdd.checkup.simplify]` in `pyproject.toml`:

```toml
[tool.pdd.checkup.simplify]
max_files = 20

[tool.pdd.checkup.simplify.commands]
format = "ruff format"
lint = "ruff check"
typecheck = "mypy pdd"
test = "pytest -q"
```
