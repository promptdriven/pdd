# PDD Prompt Linter — Tech Stack (No-LLM, No-Autofix)

This document defines a simple, readable tech stack for a modular prompt-linting tool with a backend + CLI + a lightweight UI.

## Non-Negotiable Constraints

- The tool must be **fully deterministic**.
- The tool must **not query/call any LLMs** or AI services.
- The tool must **not modify prompt files** (no autofix, no rewriting).

## Backend

- **Language:** Python
- **Framework:** FastAPI
- **Lint engine:** Pure Python (static rules + heuristics)
- **Models / validation:** Pydantic
- **Testing:** PyTest

## CLI

- **Language:** Python
- **CLI framework:** Typer (or argparse for minimal deps)
- **Distribution:** `pipx`-friendly package + console script `pddl`

## UI (Streamlit)

- **Framework:** Streamlit (Python)
- **Purpose:** Thin UI for linting prompts without using the CLI
- **Behavior:**
  - paste/upload prompt text
  - optional toggle for resolving includes (token estimation)
  - calls backend `POST /lint`
  - renders findings + copyable suggestion snippets
  - allows downloading JSON report

## API

- **Type:** REST
- **Endpoint:** `POST /lint`
- **Response:** structured JSON findings (`summary` + `findings`)

## Data Storage (Keep Simple)

- **MVP default:** none (stateless)
- **Optional:** Postgres (only if you want to store lint history, suppressions, or metrics)
  - ORM: SQLAlchemy
  - Local dev alternative: SQLite

## Authentication (Optional)

- **MVP default:** none (local dev / internal)
- If you deploy publicly:
  - **Provider:** Firebase Auth
  - **API Auth:** JWT tokens

## Infrastructure

- **Backend hosting:** Cloud Run (Google Cloud)
- **UI hosting (Streamlit):**
  - run as a separate Cloud Run service, or
  - run locally for internal use
- **Database (optional):** Cloud SQL (Postgres)

## Observability

- **Logging:** Cloud Logging (or stdout for local dev)
- **Tracing:** OpenTelemetry (optional)

## Repo Layout (practical & readable)

````

pdd-prompt-linter/
backend/        # FastAPI + lint engine + rules
cli/            # CLI wrapper
ui/             # Streamlit app
shared/         # rubric + prompt fixtures/examples

```

## Dev Defaults

- Backend: `uvicorn backend.app.main:app --reload`
- UI: `streamlit run ui/streamlit_app.py`
- Tests: `pytest -q`
