# Gemini Notes

> **Migration notice (issue #1182):** Google is sunsetting the consumer-tier
> Gemini CLI on **2026-06-18**. PDD now supports Google's successor CLI,
> **Antigravity (`agy`)**, selected via `PDD_AGENTIC_PROVIDER=antigravity`, or
> via `PDD_AGENTIC_PROVIDER=google` which prefers `agy` when present and falls
> back to the legacy `gemini` binary during the rollback window. New installs
> should use `agy` (install via Google's native Antigravity installer; auth
> via `ANTIGRAVITY_API_KEY` or `~/.antigravity/oauth_creds.json`). The legacy
> `gemini` paths in `SETUP_WITH_GEMINI.md` and elsewhere are preserved for
> existing users until Antigravity non-interactive auth, settings/MCP layout,
> and model-selection semantics are fully verified.

This repository contains the public PDD CLI.

## PDD CLI Development

- This is a Python CLI tool.
- Use `pip install -e ".[dev]"` for local development.
- The main entry point is `pdd/cli.py`.
- The CLI uses Click for command-line parsing.
- Keep private deployment and credential-backed workflow details out of this repository.
