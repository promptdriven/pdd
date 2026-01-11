# PDD Prompt Linter — Tool Specification

## 1. Purpose

The PDD Prompt Linter analyzes Prompt-Driven Development (PDD) prompt files and produces actionable suggestions to improve prompt quality.

**Normative rubric:**  
All prompting principles, evaluations, rules, and scoring MUST come from the **Prompt-Driven Development Prompting Guide**. The linter must not invent criteria that contradict the Guide.

The tool helps ensure prompts:
- Follow **One Prompt = One Module**
- Use the correct PDD anatomy (Role & Scope, Requirements, Dependencies via `<include>`)
- Apply disciplined context engineering (curated includes; avoid repo dumps)
- Make contracts explicit (Inputs/Outputs; constraints; error behavior)
- Produce testable requirements
- Avoid non-determinism (`<web>`, `<shell>`)
- Stay at the right abstraction level (10–30% heuristic)
- Place critical constraints where attention is highest (start/end)

**Non-goals**
- Code generation
- Executing prompts or directives
- PDD preprocessing
- Automatic test generation

---

## 2. Prompting Guide as the Rubric

### 2.1 What “compliance” means

A prompt is considered **compliant** when it aligns with the Prompt-Driven Development Prompting Guide and **delegates responsibility to the correct PDD layer**.

A compliant prompt exhibits the following behaviors:

- **Modularity**  
  One prompt maps to exactly one module or file with a clear, narrow responsibility.  
  Prompts that attempt to define multiple modules, workflows, or end-to-end systems are non-compliant.

- **Minimal, explicit context**  
  Context is provided deliberately using `<include>` or `<include-many>`.  
  Only essential interfaces, examples, or shared preambles are included.  
  Dumping large files, entire directories, or the full repository is non-compliant.

- **Requirements-first**  
  The core of the prompt is a list of **5–10 behavioral, testable requirements** describing *what* the module must do.  
  Requirements must avoid:
  - Step-by-step implementation instructions
  - Control-flow descriptions
  - Class hierarchies, helper layouts, or variable-level detail

- **Separation of concerns (critical)**  
  Responsibilities must be delegated correctly:
  - Coding style, formatting, naming → **shared preamble**
  - Implementation patterns and structure → **grounding**
  - Edge cases and regressions → **tests**
  
  Prompts that duplicate these concerns are considered over-specified.

- **Determinism**  
  Prompts must avoid non-deterministic directives such as `<web>` and `<shell>`.  
  When dynamic data is required, it should be captured once into a static file and included via `<include>`.

- **Attention hierarchy**  
  Critical constraints (e.g., security rules, output formats, invariants) must appear in high-attention positions:
  - At the beginning (preamble / role)
  - Or at the end (final instructions / deliverables)  
  Constraints buried mid-prompt are likely to be ignored (“middle loss”) and are non-compliant.

- **Abstraction level sanity check**  
  Prompts should operate at the level of **contracts, invariants, and outcomes**.  
  If a prompt reads like pseudocode, an implementation plan, or is harder to maintain than the generated code, it is non-compliant.

- **Regeneration mindset**  
  Prompts must be written assuming **full regeneration**, not incremental patching.  
  Instructions that only make sense as diffs, local edits, or “minimal changes” indicate a patch-based mindset and are non-compliant.

---

## 3. Source Layout (no package folder)

```text
src/
  cli/
    main.py
  backend/
    api.py
  frontend/
    streamlit_app.py
  utils/
    pipeline.py
    rules.py
    llm.py
    report.py
    fix.py
    models.py
    helpers.py
```

* `utils/pipeline.py` is the single orchestrator used by CLI, backend, and frontend.
* CLI / backend / frontend are intentionally thin wrappers.

---

## 4. Default Behavior (LLM-first with safe fallback)

* LLM analysis is **ON by default**
* Heuristics **always run**
* LLM output is **additive** and must align with the Guide
* If the LLM is unavailable or fails (no keys / timeout / invalid JSON / auth), the tool **falls back** to heuristics
* Linting must always succeed and return a report

---

## 5. Interfaces

### 5.1 CLI

```bash
python src/cli/main.py PROMPT_FILE [options]
```

Core flags:

* `--format text|json|md` (default: text)
* `--severity-threshold info|warning|error`
* `--fail-on warning|error`
* `--fix`
* `--in-place` (requires `--fix`)
* `--output PATH`
* `--assume-cloud-grounding / --assume-local`

LLM flags:

* `--llm / --no-llm` (default: `--llm`)
* `--llm-provider auto|openai|anthropic|google|custom`
* `--llm-model STRING`
* `--llm-base-url STRING`
* `--llm-timeout-seconds 20`
* `--llm-max-retries 2`
* `--llm-budget-tokens 800`

---

## 6. Provider Detection & Authentication

No tool-owned environment variables.

Supported provider keys:

* `OPENAI_API_KEY`
* `ANTHROPIC_API_KEY`
* `GOOGLE_API_KEY`

If no provider keys exist, the linter runs heuristics only.

---

## 7. Cheap-Model Requirement

Prompt linting is a low-complexity task.

Defaults MUST:

* Prefer small / cheap models
* Use a single one-shot call
* Enforce strict JSON output
* Cap tokens (default: 800)

If all LLM attempts fail → heuristics only.

---

## 8. LLM Output Contract

LLM must return **JSON only**:

```json
{
  "guide_alignment_summary": "string",
  "top_fixes": [
    { "title": "string", "rationale": "string", "priority": "high|medium|low" }
  ],
  "suggestions": [
    {
      "rule_id": "string",
      "title": "string",
      "rationale": "string",
      "before": "string",
      "after": "string",
      "priority": "high|medium|low"
    }
  ]
}
```

Invalid JSON or schema mismatch:

* Discard LLM output
* Emit `LLM002`
* Return heuristic-only report

---

## 9. Rule System (Guide-derived)

Rules cover:

* Modularity & scope
* Prompt anatomy
* Contracts & testability
* Context engineering
* Determinism
* Abstraction level
* Attention hierarchy
* Grounding sensitivity (cloud vs local)

---

## 10. Scoring (0–100)

| Category                | Weight |
| ----------------------- | -----: |
| Modularity & Anatomy    |     30 |
| Contracts & Testability |     20 |
| Context Engineering     |     20 |
| Determinism             |     15 |
| Abstraction & Attention |     15 |

Errors cap that category’s score at zero.

---

## 11. Fix Mode (`--fix`)

Produces a Guide-aligned rewritten prompt scaffold:

* Ensures Role/Scope, Requirements, Dependencies exist
* Converts vague requirements into testable ones
* Moves style rules into “Suggested preamble”
* Moves edge cases into “Suggested tests”
* Flags/removes nondeterministic tags
