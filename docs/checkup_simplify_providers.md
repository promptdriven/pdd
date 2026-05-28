# Checkup simplify — multi-provider agent profiles

`pdd checkup simplify` ships **multi-engine runtime support**:

- **`--engine claude`** (default): Claude Code bundled `/simplify`
- **`--engine codex|gemini|opencode`**: the shared workflow prompt via PDD `run_agentic_task`
- **`--engine auto`**: Claude when installed, else the first available agentic provider

This document and the companion prompt assets describe provider setup, parity expectations, and
how the workflow prompt maps to each CLI.

## Shared workflow prompt

| Asset | Purpose |
|-------|---------|
| `pdd/prompts/checkup_simplify_workflow_LLM.prompt` | Provider-agnostic simplify behavior (quality → efficiency → consistency) |
| `pdd/prompts/checkup_simplify_invoke_claude_code_LLM.prompt` | Production Claude Code `/simplify` profile |
| `pdd/prompts/checkup_simplify_invoke_codex_LLM.prompt` | OpenAI Codex reference profile |
| `pdd/prompts/checkup_simplify_invoke_gemini_LLM.prompt` | Google Gemini / Antigravity reference profile |
| `pdd/prompts/checkup_simplify_invoke_opencode_LLM.prompt` | OpenCode reference profile |

Preprocess the workflow prompt (resolve `<include>` tags) and append:

1. The in-scope relative file list PDD selected.
2. Optional focus text from `[tool.pdd.checkup.simplify].focus`.

Run the agent **inside the candidate worktree** PDD created, not on your live working tree.

## Provider quick reference

| Provider | CLI | Model env (typical) | Notes |
|----------|-----|---------------------|-------|
| Claude Code | `claude` | `CLAUDE_MODEL` | `pdd checkup simplify --apply` (default engine) |
| OpenAI Codex | `codex` | `CODEX_MODEL` | `pdd checkup simplify --apply --engine codex` |
| Google Gemini | `gemini` / `agy` | `GEMINI_MODEL` | `pdd checkup simplify --apply --engine gemini` |
| OpenCode | `opencode` | `OPENCODE_MODEL` | `pdd checkup simplify --apply --engine opencode` |

## Parity checklist (any provider)

- [ ] Edit only files in the explicit allowlist.
- [ ] Prefer fewer touched files over broad refactors.
- [ ] Preserve behavior; skip risky semantic changes.
- [ ] Run PDD verification (`--verify`) before selecting a multi-attempt winner.
- [ ] Keep evidence/backups under `.pdd/` when using `pdd checkup simplify --evidence`.

## Cursor / IDE skill

Copy `docs/skills/checkup-simplify/SKILL.md` into your personal Cursor skills directory when you
want the same workflow available to the IDE agent without running the CLI.

Invoke-specific setup notes live in `checkup_simplify_invoke_*_LLM.prompt` (reference profiles for
humans and other LLM harnesses; runtime uses the shared workflow prompt for agentic engines).

See also: [checkup_simplify.md](checkup_simplify.md) for CLI usage and verification behavior.
