# Gemini Notes

This repository contains the public PDD CLI.

## PDD CLI Development

- This is a Python CLI tool.
- Use `pip install -e ".[dev]"` for local development.
- The main entry point is `pdd/cli.py`.
- The CLI uses Click for command-line parsing.
- Keep private deployment and credential-backed workflow details out of this repository.
