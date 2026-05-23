# Gemini / Antigravity Notes

This repository contains the public PDD CLI.

> **Migration note (Issue #1152):** PDD now supports Google's new Antigravity CLI (`agy`) alongside the legacy Gemini CLI (`gemini`). Both map to the `google` agentic provider. Selection precedence: `PDD_AGENTIC_PROVIDER=antigravity` (pin Antigravity) > `PDD_GOOGLE_CLI=agy|gemini|auto` (binary picker; `auto` prefers `agy`) > auto-detect. The legacy `gemini` binary remains the rollback path until Antigravity auth/config is fully verified; Google announced consumer-tier Gemini CLI cutoff on **2026-06-18**.

## PDD CLI Development

- This is a Python CLI tool.
- Use `pip install -e ".[dev]"` for local development.
- The main entry point is `pdd/cli.py`.
- The CLI uses Click for command-line parsing.
- Keep private deployment and credential-backed workflow details out of this repository.
