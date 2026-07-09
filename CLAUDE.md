# Claude Code Notes

This repository contains the public PDD CLI. Keep changes focused on the open-source package and avoid adding private deployment or credential-backed workflow details.

## Prompt-First Workflow (Read First)
Prompts are the source of truth; code is regenerated from them. This block enforces the doctrine's #1 anti-pattern, Prompt Drift (`docs/prompt-driven-development-doctrine.md` "Anti-Patterns"; `CONTRIBUTING.md` "Core Philosophy").
- Behavior change: edit `pdd/prompts/<module>_python.prompt` first, regenerate with `pdd sync <module>` (or `make generate MODULE=<module>`), then adjust tests.
- If you edited `pdd/<module>.py` directly (hotfix): run `pdd update --sync-metadata` to back-propagate the change into the prompt and re-stamp the fingerprint BEFORE opening the PR; list the back-propagated units in the PR body.
- Never hand-edit `.pdd/meta/*.json` or `architecture.json`; use `pdd sync-architecture` or the fingerprint stamper (`scripts/stamp_fingerprints.py`).
- Tests accumulate: append tests; never delete passing tests when regenerating.

## Commands
- Install dependencies: `pip install -e ".[dev]"` or `pip install -e .`
- Run all tests: `pytest -vv tests/`
- Run one test file: `pytest -vv tests/test_module_name.py`
- Test with coverage: `make coverage`
- Generate module: `make generate MODULE=module_name`
- Fix module: `make fix MODULE=module_name`
- Crash fix: `make crash MODULE=module_name`
- Regression tests: `make regression`
- Lint check: `make lint` or `pylint pdd/<module>.py`

## Model Selection
- `llm_model.csv` has an `interactive_only` column. Rows marked `True` (e.g. `github_copilot/*`, `chatgpt/*`, `lm_studio/*`, `ollama/*`) require interactive human auth (device-flow OAuth or a ChatGPT subscription / `codex login` token) or a running local server and hang in non-interactive contexts (Cloud Run, CI, library import). `_select_model_candidates` skips them in the automatic candidate cascade by default; set `PDD_ALLOW_INTERACTIVE=1` from a terminal to opt in. An explicitly configured `PDD_MODEL_DEFAULT` is always honored.

## Code Style
- Python 3.12+, four-space indentation, and PEP 8 conventions.
- Use type hints for public functions.
- Keep imports grouped as standard library, third-party, then local.
- Functions should have docstrings when behavior or side effects are not obvious.
- Add tests for user-visible behavior and shared helper changes.
- Pydantic v2 is used for structured validation.
- The CLI is implemented with Click.
