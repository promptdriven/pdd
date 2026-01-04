# PDD Prompt Linter — Technical Stack

## 1. Runtime
- Python 3.11+

---

## 2. Dependencies

CLI / Output:
- Typer
- Rich

Core:
- Pydantic v2

Backend:
- FastAPI
- Uvicorn

Frontend:
- Streamlit

LLM:
- LiteLLM (provider-agnostic)
- httpx (if needed)

---

## 3. Authentication

No tool-owned environment variables.

Provider-standard keys only:
- OPENAI_API_KEY
- ANTHROPIC_API_KEY
- GOOGLE_API_KEY

If no keys exist, run heuristics only.

---

## 4. Source Layout (thin wrappers + shared pipeline)

```text
src/
  cli/
    main.py              # parse args -> utils.pipeline.lint_file / lint_text
  backend/
    api.py               # FastAPI -> utils.pipeline.lint_text
  frontend/
    streamlit_app.py     # UI -> backend or utils.pipeline
  utils/
    pipeline.py          # orchestrator (single source of logic)
    rules.py             # all Guide-derived heuristics
    llm.py               # provider detect + cheap model + JSON validation + fallback
    report.py            # render text/json/md
    fix.py               # prompt rewrite scaffold
    models.py            # Pydantic schemas: Issue, Report, LLMResponse
    helpers.py           # tag detection, ratio heuristics, small text utils
```

---

## 5. Testing

* Heuristics: deterministic unit tests
* LLM: mocked calls only (no network in CI)
* Required failure tests:

  * no keys -> heuristics
  * timeout -> heuristics
  * invalid JSON -> heuristics
  * model not found -> fallback -> heuristics

---

## 6. Defaults

* LLM ON by default (if keys exist)
* Cheap model defaults (internal mapping)
* Token cap: 800
* Timeout: 20s
* Retries: 2

---

## 7. Security posture

* Treat prompt input as untrusted
* Never execute `<shell>` or fetch `<web>`
* Validate LLM output strictly
* Use atomic writes when `--in-place` is used
