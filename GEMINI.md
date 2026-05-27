# Gemini / Antigravity Notes

This repository contains the public PDD CLI.

> **Migration note (Issue #1152):** PDD now supports Google's new Antigravity CLI (`agy`) alongside the legacy Gemini CLI (`gemini`). Both map to the `google` agentic provider. Selection precedence: `PDD_AGENTIC_PROVIDER=antigravity` (pin Antigravity) > `PDD_GOOGLE_CLI=agy|gemini|auto` (binary picker; `auto` prefers `agy` when installed and credentialed, but uses legacy `gemini` when both binaries are installed and the only Google auth signal is `~/.gemini/oauth_creds.json`) > auto-detect. Antigravity can authenticate through OAuth, keyring-backed Google subscription sign-in, `ANTIGRAVITY_API_KEY`/`GOOGLE_API_KEY`, Vertex AI env auth, or PDD's compatibility bridge from `GEMINI_API_KEY`; legacy `gemini` remains the explicit rollback path and uses its own OAuth store or `GEMINI_API_KEY`/`GOOGLE_API_KEY`. Google announced consumer-tier Gemini CLI cutoff on **2026-06-18**.

## PDD CLI Development

- This is a Python CLI tool.
- Use `pip install -e ".[dev]"` for local development.
- The main entry point is `pdd/cli.py`.
- The CLI uses Click for command-line parsing.
- Keep private deployment and credential-backed workflow details out of this repository.
