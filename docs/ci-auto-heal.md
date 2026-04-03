# CI Auto-Heal

## Overview

The CI auto-heal workflow automatically detects prompt-code drift and runs `pdd update` (for stale prompts) and `pdd sync` (for stale examples) to fix it. It triggers on pull requests and pushes to `main`, keeping generated code in sync with prompts.

## Workflow File

`.github/workflows/auto-heal-drift.yml`

## Triggers

### Pull Requests

Triggers on `opened`, `synchronize`, and `reopened` events.

- Only heals modules whose `pdd/prompts/*_*.prompt` files changed in the PR (extracted from `git diff --name-only`)
- Passes `--modules` to limit scope to changed modules
- Commits fixes to the PR branch
- Uses concurrency groups keyed on PR number to cancel stale runs on force-pushes

### Push to Main

Triggers on pushes to the `main` branch.

- Heals ALL modules (no `--modules` filter)
- Commits fixes directly to `main`
- Skips execution if the triggering commit message starts with `chore: auto-heal` (prevents infinite loops)
- Uses `[skip ci]` in commit messages as an additional safeguard

## Infinite Loop Prevention

Two layers of protection prevent the workflow from triggering itself:

1. **PR path:** Commits made with `GITHUB_TOKEN` by GitHub Actions do not re-trigger workflows (built-in GitHub behavior).
2. **Main path:** The workflow checks if the triggering commit message starts with `chore: auto-heal` and skips if so. The auto-commit also includes `[skip ci]` in the message.

## Configuration

### Budget Cap

The healing script receives a `--budget-cap` value to limit LLM spend per run.

| Source | Variable | Default |
|--------|----------|---------|
| Repository variable | `PDD_BUDGET_CAP` | `5.00` |

Set via: **Settings → Secrets and variables → Actions → Variables → New repository variable**

### Permissions

The workflow requires:

| Permission | Purpose |
|------------|---------|
| `contents: write` | Push commits to branches |
| `pull-requests: write` | Push to PR branches |

These are configured in the workflow file itself. No additional repository settings are needed when using `GITHUB_TOKEN`.

## Prerequisites

The runner environment must have:

- Python 3.12+
- PDD CLI installed (`pip install -e .`)
- Project dependencies (`pip install -r requirements.txt`)

These are set up automatically by the workflow steps.

## Troubleshooting

### Workflow not triggering

- Verify the workflow file exists on the `main` branch
- Check that the PR event type is one of: `opened`, `synchronize`, `reopened`

### Auto-heal commits not appearing

- Check the workflow logs for `pdd sync` errors
- Verify the budget cap is sufficient for the modules being healed
- Ensure `GITHUB_TOKEN` has write permissions (Settings → Actions → General → Workflow permissions)

### Infinite loop on main

- If the workflow keeps re-triggering on main, verify the commit message check is working
- The `[skip ci]` tag in the commit message provides a second layer of protection
- Check that the `stefanzweifel/git-auto-commit-action` is using the correct commit message format

### No modules detected on PR

- The workflow extracts changed modules from `git diff --name-only`
- If no `pdd/prompts/*_*.prompt` files changed, the heal step is skipped
- This is expected behavior for documentation-only PRs

## Related

- [Public PR Testing](./PUBLIC_PR_TESTING.md) — Testing public PRs against private codebase
- [Workflow Integration](../README.md#workflow-integration) — PDD workflow patterns
