# Repository Guidelines

## Project Structure & Module Organization
Core CLI logic lives in `pdd/`, where each module aligns with a prompt template in `prompts/` (for example, `pdd/code_generator.py` pairs with `prompts/code_generator_python.prompt`). Generated examples drop into `context/`, CSV data into `data/`, and packaged artifacts into `dist/`. Public examples live under `examples/`, and central documentation, diagrams, and onboarding notes reside in `docs/`.

## Build, Test, and Development Commands
Activate the Conda environment once per session with `conda activate pdd`; all Makefile targets assume interpreter and deps from that env.
- `make test` runs the staging pytest suite defined in `tests/`.
- `make coverage` executes pytest with coverage; review the report before large merges.
- `make regression` or `make sync-regression` triggers the longer regression harnesses (optionally pass `TEST_NUM=42`).
- `make lint` wraps `pylint` checks; fix diagnostics instead of suppressing them.
- `make build` and `make install` create and install the CLI wheel locally for smoke checks.

## Coding Style & Naming Conventions
Use Python 3.12+, four-space indentation, and type annotations for public functions. Match module and file names to their prompt identifiers (`snake_case`), keep classes in `PascalCase`, and reserve `UPPER_SNAKE_CASE` for constants. Favor small, composable functions with docstrings summarizing side effects. Run `make lint` or `pylint pdd/<module>.py` before submitting to catch style regressions.

## Testing Guidelines
All automated tests live in `tests/test_*.py` and follow the pytest discovery rules pinned in `pytest.ini`. Name new tests `test_<module>_<behavior>` and colocate fixtures in the same file unless shared broadly. Use `pytest -k sync_main` for targeted runs while iterating, then `make coverage` to confirm branch coverage holds. Regression shells (`tests/regression.sh`, `tests/sync_regression.sh`) expect API access—flag them as `real` with the provided marker when applicable.

## Commit & Pull Request Guidelines
Commitizen is configured for Conventional Commits; prefer messages like `feat: improve sync verification loop`. Keep commits focused and reference related prompt paths when the change spans generated assets. Before opening a PR, run `make test` and `make lint`, describe the behavioral impact, link any tracked issues, and attach logs or screenshots for CLI UX tweaks.

## Configuration & Secrets
Run `pdd setup` once per machine to create `~/.pdd` credentials, and never commit keys or cache files (the repo `.gitignore` already excludes them). Use the public setup documentation to provision provider tokens. When recording logs for debugging, redact token strings and strip `litellm_cache.sqlite` before sharing artifacts.

## Security & Prompt Injection Sanitization
All agentic orchestrators (`change`, `bug`, `fix`, `test`, `checkup`, `sync`) route their inputs through `sanitize_agent_input(content, source)` in `pdd/agentic_common.py` before passing content to the agent. The utility detects and wraps two injection patterns:

- **R-INJ1 (file-read injection):** A sentence appended at the end of a task prompt telling the agent to read a file named `.agentic_prompt_<hex>.txt`. Detected only in the trailing 500 characters of the prompt; mid-content occurrences are ignored. Matched text is wrapped with `[UNTRUSTED CONTENT: file-read-injection]...[/UNTRUSTED CONTENT]`.
- **R-INJ2 (system-reminder injection):** `<system-reminder>...</system-reminder>` blocks embedded in tool results (grep output, search results, GitHub issue bodies). Each block is wrapped with `[UNTRUSTED CONTENT: system-reminder-injection]...[/UNTRUSTED CONTENT]`.

Content is never silently stripped — wrapping preserves the original text with an explicit trust boundary signal so the agent can reason about the label. Each detection is logged via `console.print`. The two call sites in `run_agentic_task` are the `instruction` argument (source label `"task_prompt"`) and the `PDD_USER_FEEDBACK` env var value (source label `"user_feedback"`).
