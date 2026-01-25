# Contributing to PDD CLI

Thank you for considering contributing to PDD CLI! This guide summarizes how we work and how you can have impact quickly.

## Overview
- PDD (Prompt‑Driven Development) treats prompts as the source of truth; code is regenerated from prompts and tests accumulate over time.
- We use Discord for real‑time discussion and GitHub Issues/Discussions for async collaboration.
- All contributions matter: docs, tests, bug fixes, features, tooling, and onboarding support.

## Core Philosophy
- Prompt is the source of truth.
- Regenerate rather than patch code manually when possible.
- Keep spec/README, prompts, code, examples, and tests in sync.
- Tests accumulate: append tests; don’t regenerate or remove them.
- Modular prompt graph: prompts compose via includes.

## The “Dev Unit”
Each complete change ideally includes four elements:
- Prompt: defines behavior (some compile‑time prompts are being open‑sourced over time).
- Code: generated/updated implementation.
- Example interface: usage examples that enable prompt composability.
- Tests: appended to relevant test files to reproduce bugs or validate features.

## Contribution Workflow
1) Get set up
- Fork the repository and clone your fork.
- Install prerequisites; prefer the PDD setup script when available (v0.57+). Docker is optional but helpful for consistency.
- Configure LLM/API keys as needed.

2) Choose work
- Browse GitHub Issues or open one describing your bug/feature/idea.
- Use Discord for quick feedback; GitHub Discussions for async/archival.

3) Define and test
- For features: update README/spec first; it drives prompts and implementation.
- For bugs: write a failing test that reproduces the issue before fixing.
- Append tests in the appropriate module under `tests/`.

4) Implement
- Prefer using PDD to regenerate code from prompts.
- If editing code directly, run `pdd update` to sync changes back into prompts (until all prompts are public, maintainers may help sync).
- Keep example interfaces updated to reflect new/changed behavior.
- Useful prompt tags when needed: `<include>`, `<pdv>`, `<shell>`, `<web>`.

5) Submit a PR
- Include the four dev‑unit elements when applicable: prompt, code, example, tests.
- Reference the related issue and summarize approach and implications.
- Expect review feedback; iterate until approved and merged.

## Communication Channels
- Discord: primary real‑time venue for questions and design discussions.
- GitHub Issues: track work, propose ideas, report bugs.
- GitHub Discussions: longer‑form, async conversations and announcements.

## Development Setup

1. Clone your fork:
   ```bash
   git clone https://github.com/your-username/pdd.git
   cd pdd
   ```
2. Create and activate a Conda environment (recommended):
   ```bash
   conda create -n pdd-dev python=3.12
   conda activate pdd-dev
   ```
   To use a different environment name, set the `PDD_CONDA_ENV` environment variable before running make commands:
   ```bash
   # Option 1: Export for the session
   export PDD_CONDA_ENV=my-env
   make <target>

   # Option 2: Set inline for a single command
   PDD_CONDA_ENV=my-env make build

   # Option 3: Pass as a make argument
   make test PDD_CONDA_ENV=my-env
   ```
3. Install dependencies in editable mode with dev extras:
   ```bash
   pip install -e .[dev]
   ```
   Note: Many Makefile targets (e.g., `make test`, `make coverage`, `make lint`) automatically install dev dependencies into the conda environment before each run.
4. Optional: Use Docker for reproducible environments, especially for tricky, environment‑dependent bugs.

## Running Tests
Run the test suite before submitting changes:
```bash
pytest
```
With coverage reporting:
```bash
pytest --cov=pdd
```

### Adding/Updating Tests (Strongly Encouraged)
- Location: put tests in `tests/` using `pytest` style (`test_*.py`).
- Red/green: commit a failing test first, then the fix that makes it pass.
- Regression focus: ensure the test fails without your change and passes with it.
- Coverage: exercise public APIs and edge cases related to your change.

## Building the Package
To build wheel and sdist:
1. Install build tools:
   ```bash
   pip install build
   ```
2. Build from project root:
   ```bash
   python -m build
   ```
Artifacts appear in `dist/`.

## Tools for Contributors
- IDEs: Cursor (great prompt autocomplete) or VS Code (PDD extension for syntax highlighting).
- CLIs: Kodex CLI and other LLM CLIs (e.g., Gemini); use what works for you.
- Docker: for reproducible bug reports and dev environments.

## Key PDD CLI Parameters
- `--strength`: model strength/size.
- `--temperature`: creativity vs. determinism.
- `--time`: thinking tokens/budget.

## Known Limitations and Roadmap
- Some compile‑time prompts are not yet open‑sourced (pending investor approval). Until then, code edits may require maintainers to sync prompts.
- `pdd sync` is alpha and currently focuses within a dev unit; cross‑unit syncing is planned.
- Contributors have varying LLM/model access, leading to variability; a future cloud version will standardize models and auto‑optimize cost/params.

## Good First Contributions
- Documentation improvements (clarity, setup steps, examples).
- Tests that reproduce a bug you hit.
- Small bug fixes with accompanying tests.
- Issue triage and creating well‑scoped issues.
- Dockerfile or setup enhancements.
- “Hello World” example: validate setup and try syncing/regenerating.

## Quality Tips
- Start with the spec: update README for feature changes.
- Discuss early in Discord/Issues to avoid rework and align on approach.
- Keep PRs focused and small; include tests.
- Use Docker for environment‑dependent bugs.
- Note parameters used (`--strength`, `--temperature`, `--time`) if relevant to reproducibility.

## Community and Support
- Setup help is available; “setup parties” are encouraged.
- Share user testimonials (short video) if PDD helps you.
- Participate in meetups and related community events when possible.

## Publishing a Release (Maintainers)
1. Ensure build artifacts are up‑to‑date (see Building the Package).
2. Install Twine if needed:
   ```bash
   pip install twine
   ```
3. Upload to PyPI with credentials:
   ```bash
   twine upload dist/*
   ```

## Pull Request Process
1. Remove stray build/install artifacts before committing.
2. Update `README.md` if you change the interface (env vars, commands, parameters, examples).
3. Bump the version in `pyproject.toml` (SemVer) when appropriate; reflect changes in `README.md` as needed.
4. Include tests in `tests/` that demonstrate the issue/feature and verify the behavior.
5. Aim to include dev‑unit elements (prompt/code/example/tests) when applicable.
6. Seek two maintainer reviews prior to merge, or request a reviewer to merge if you lack permissions.

Thank you for your contributions!
