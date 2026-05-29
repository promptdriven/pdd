# Claude Code Notes

This repository contains the public PDD CLI. Keep changes focused on the open-source package and avoid adding private deployment or credential-backed workflow details.

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
- `llm_model.csv` has an `interactive_only` column. Rows marked `True` (e.g. `github_copilot/*`, `lm_studio/*`, `ollama/*`) require interactive human auth or a running local server and hang in non-interactive contexts (Cloud Run, CI, library import). `_select_model_candidates` skips them in the automatic candidate cascade by default; set `PDD_ALLOW_INTERACTIVE=1` from a terminal to opt in. An explicitly configured `PDD_MODEL_DEFAULT` is always honored.

## Code Style
- Python 3.12+, four-space indentation, and PEP 8 conventions.
- Use type hints for public functions.
- Keep imports grouped as standard library, third-party, then local.
- Functions should have docstrings when behavior or side effects are not obvious.
- Add tests for user-visible behavior and shared helper changes.
- Pydantic v2 is used for structured validation.
- The CLI is implemented with Click.
