# PDD Prompt Linter — Tool Specification (No-LLM, No-Autofix)

## 1) Overview

**Goal:** Build a simple, modular “prompt linter” for Prompt-Driven Development (PDD) prompts.

- It reads a `.prompt` file and returns **concrete, actionable feedback** to improve the prompt **according to the Prompt-Driven Development Prompting Guide** (the guide is the source of truth).
- It helps developers keep prompts minimal, explicit, modular, and reproducible.

**Hard constraints:**
- **No LLM usage.** The tool must **never** query/call any LLMs or AI services.
- **No autofix.** The tool must **not** modify prompt files or generate rewritten prompts. It only reports issues and suggestions.

## 2) Primary User Flows

### 2.1 CLI (default)

**Command:**
- `pddl lint path/to/module.prompt`

**Outputs:**
- Human-readable report in terminal (grouped by severity)
- Optional JSON report (for CI), e.g. `--format json`

### 2.2 Simple UI (Streamlit)

- Paste/upload a prompt
- Click **Lint**
- See lint issues + suggested edits (copyable snippets)
- Download JSON report

> The UI is intentionally thin. It calls the backend `/lint` endpoint.

## 3) Inputs and Outputs

### 3.1 Inputs

- A single prompt file (`*.prompt`, `*.md`, or plain text).
- Optional “context resolution” (for estimating context usage):
  - `--resolve-includes` resolves `<include>` / `<include-many>` locally and estimates total tokens
  - `--pdd-path` overrides `$PDD_PATH` for resolving paths (optional)

**Important:** Even if the prompt contains `<shell>` or `<web>`, the linter **must not execute/fetch** anything.

### 3.2 Outputs

The linter returns a structured findings object. This is the **canonical** representation used by CLI, API, and UI.

#### JSON schema (conceptual)

```json
{
  "file": "path/to/prompt.prompt",
  "summary": {
    "score": 82,
    "issues": { "error": 1, "warn": 4, "info": 6 },
    "estimated_tokens": 940,
    "resolved_tokens": 1320
  },
  "findings": [
    {
      "rule_id": "PDD001",
      "severity": "warn",
      "title": "Missing clear Role & Scope (1–2 sentences)",
      "message": "Prompt should start with a concise statement of what this module does and its boundary.",
      "evidence": { "line_start": 1, "line_end": 8 },
      "suggested_edits": [
        {
          "kind": "insert_section_scaffold",
          "snippet": "% Role & Scope\n  One–two sentences describing the module responsibility and boundary.\n"
        }
      ]
    }
  ]
}
````

#### Human-readable terminal output (example)

* Header: score, issue counts, token estimates
* Sections: Errors → Warnings → Info
* Each finding: rule id, title, evidence lines, suggested edit snippet(s)

## 4) Architecture

### 4.1 High-level components

* **Core Lint Engine (backend/shared):**

  * parses the prompt into a lightweight structure (sections, tags, line map)
  * runs deterministic rules/heuristics
  * emits structured findings

* **CLI (frontend A):**

  * reads a file
  * runs lint either in-process or via HTTP (configurable)
  * prints text or outputs JSON

* **API Server (backend):**

  * exposes `/lint` endpoint for UI + integrations

* **Streamlit App (frontend B):**

  * upload/paste prompt
  * calls backend `/lint`
  * renders results, provides download

### 4.2 Suggested repository layout

```
pdd-prompt-linter/
  backend/
    app/
      main.py                 # FastAPI entry
      api.py                  # routes: /lint
      core/
        lint_engine.py        # orchestrates parsing + rules
        parser.py             # sections/tags/line mapping
        include_resolver.py   # optional include resolution (token estimation)
        token_estimator.py    # simple token estimate
      rules/
        registry.py           # rule registration
        pdd001_role_scope.py
        pdd010_requirements.py
        pdd020_io_contract.py
        pdd030_includes.py
        pdd040_nondeterminism.py
        pdd050_size_goldilocks.py
        pdd060_attention.py
      models/
        findings.py           # Pydantic models
    tests/
      test_parser.py
      test_rules_*.py
      fixtures/
  cli/
    pddl.py                   # Typer/argparse CLI
  ui/
    streamlit_app.py          # Streamlit UI
  shared/
    rubric.md                 # distilled checklist text used in rule messages
    examples/
      good_prompt.prompt
      bad_prompt.prompt
  README.md
```

## 5) Rule System

### 5.1 Principles

* **Deterministic and offline:** No network calls are required for linting.
* **Guide-aligned:** Every rule maps to a concept in the prompting guide.
* **Actionable:** Each rule includes a suggested concrete edit or scaffold snippet.
* **No code-style enforcement:** The linter focuses on prompt structure and context engineering (not Python formatting, etc.).
* **No rewriting:** The linter may suggest improved structure, but does not produce rewritten prompts.

### 5.2 Severity levels

* **error:** likely to cause unusable generation or drift
* **warn:** strongly recommended changes
* **info:** optional improvements / educational

### 5.3 Scoring

Start at 100. Subtract:

* error: -15 each (cap -45)
* warn: -7 each (cap -35)
* info: -2 each (cap -20)

Minimum score 0. The score is heuristic.

### 5.4 Configuration

Support a simple config file, optional:

* `.pddl.yml` at repo root
* allows:

  * enabling/disabling rules
  * setting thresholds (token warning threshold)
  * setting allowed include roots

Example:

```yaml
enabled_rules:
  - PDD001
  - PDD010
  - PDD020
  - PDD030
  - PDD040
  - PDD050
disabled_rules:
  - PDD060
thresholds:
  max_resolved_tokens_warn: 4000
include_roots:
  - .
  - context
```

## 6) Lint Rules (MVP)

> IDs are stable so CI can ignore/suppress specific rules.

### Structure & Scope

* **PDD001 (warn): Missing clear Role & Scope (1–2 sentences)**

  * Detect: no early role/scope statement; or first paragraph is long and unscoped.
  * Suggest: add a short Role & Scope section near top.

* **PDD002 (warn): “One prompt = one module” likely violated**

  * Detect: multiple unrelated target files / modules referenced.
  * Suggest: split into multiple prompt files and define explicit interfaces/examples.

### Requirements Quality

* **PDD010 (error): Requirements section missing**

  * Detect: no “Requirements” or requirement-like list.
  * Suggest: add 5–10 behavioral, testable requirements.

* **PDD011 (warn): Requirements count likely off**

  * Detect: fewer than ~5 or more than ~10 requirements.
  * Suggest: consolidate edge cases; keep behavior-level requirements.

* **PDD012 (warn): Requirements are implementation steps**

  * Detect: “create a class”, “use helper function”, “loop over”, “import X”.
  * Suggest: rewrite to contracts/invariants/outcomes (WHAT, not HOW).

* **PDD013 (info): Excess negative constraints**

  * Detect: dense “do not / don’t / never”.
  * Suggest: prefer positive constraints (“validate”, “sanitize”, “return X on invalid”).

### Inputs/Outputs & Contracts

* **PDD020 (warn): Inputs/Outputs not explicit**

  * Detect: missing explicit IO contract (names, types, shapes).
  * Suggest: add an Inputs/Outputs section.

* **PDD021 (info): Missing error-handling contract**

  * Detect: no mention of expected failure cases and response semantics.
  * Suggest: add a requirement defining error behavior.

### Context Engineering & Includes

* **PDD030 (warn): Dependencies referenced without `<include>`**

  * Detect: mentions external/critical interfaces without including contract/example.
  * Suggest: use `<include>` or add minimal usage example under `context/`.

* **PDD031 (warn): Likely context dump**

  * Detect: large `<include-many>` or large resolved token count.
  * Suggest: replace full files with small “examples as interfaces”; extract relevant excerpts.

* **PDD032 (info): Missing shared preamble include**

  * Detect: no shared preamble referenced.
  * Suggest: include `context/project_preamble.prompt` (or equivalent) at the top.

### Determinism & PDD Directives

* **PDD040 (warn): Non-deterministic directives present**

  * Detect: `<shell>` or `<web>` tags.
  * Suggest: capture results in a static file and `<include>` that file instead.

### Prompt Size Heuristics (Goldilocks)

* **PDD050 (warn): Prompt likely too vague**

  * Detect: small prompt + missing IO/constraints.
  * Suggest: add IO contract + key constraints (security/perf/error handling).

* **PDD051 (warn): Prompt likely too detailed**

  * Detect: long prompt dominated by step-by-step implementation.
  * Suggest: move style to preamble, rely on tests/grounding, keep prompt to interfaces and behaviors.

### Hierarchy of Attention

* **PDD060 (info): Critical constraints not positioned well**

  * Detect: security/performance/output format constraints only appear mid-prompt.
  * Suggest: reiterate critical constraints near the end in an Instructions/Deliverables section.

## 7) API (backend)

### POST `/lint`

**Request:**

```json
{
  "prompt_text": "...",
  "options": {
    "resolve_includes": false,
    "pdd_path": null
  }
}
```

**Response:**

* canonical lint JSON object with `summary` + `findings`

## 8) CLI Contract

### Commands

* `pddl lint <file> [--format text|json] [--resolve-includes] [--config .pddl.yml]`
* `pddl rules` (list rules + short descriptions)
* `pddl explain <RULE_ID>` (show rationale + examples + suggested scaffolds)

### Exit codes (CI-friendly)

* `0` no errors
* `1` errors found
* `2` tool/runtime failure

## 9) UI Contract (Streamlit)

### Features

* Text area + file uploader
* Toggle: resolve includes (token estimation)
* Button: **Lint**
* Output:

  * summary (score, issue counts, token estimates)
  * findings list (filter by severity)
  * suggested edit snippets (copy buttons)
  * download JSON report

## 10) Testing

* Unit tests:

  * parser (sections, tags, line mapping)
  * include resolver (path security + bounded size)
  * token estimator (stable)
  * each rule (positive + negative fixtures)
* Golden tests:

  * CLI text output formatting
  * JSON output schema validation
* Regression prompts:

  * prompts that historically caused vagueness, over-specification, or non-determinism.

## 11) Security & Safety

* Treat prompts as untrusted input.
* If resolving includes:

  * restrict file reads to configured roots
  * block `../` traversal
  * enforce max file size and max total resolved bytes
* Never execute `<shell>` or fetch `<web>`.

## 12) Non-Goals (MVP)

* Not a full PDD compiler/preprocessor.
* Not a code linter for generated code.
* Not a prompt rewriter or generator.
* No LLM usage; no network dependency for linting.
* No automatic prompt modifications.
